//! Deviation tables and the interpolation that reads them.
//!
//! A deviation table records, for a set of compass headings, how far the ship's
//! compass card is displaced from magnetic north by the vessel's own magnetism:
//!
//! ```text
//! magnetic course = compass course + deviation(compass course)
//! ```
//!
//! Deviation is therefore a *periodic* function of the **compass** course, and
//! everything in this module treats it as such.
//!
//! # Interpolation methods
//!
//! | Method | Continuity | Nodes needed | Use when |
//! |---|---|---|---|
//! | [`InterpolationMethod::Linear`] | C⁰ | 2 | you want a result that can never overshoot the tabulated values |
//! | [`InterpolationMethod::Cubic`] | C² | 3 | the swing is dense and you want a smooth curve |
//! | [`InterpolationMethod::Parametric`] | analytic | 5 | you want the classical A–E coefficient model, or want to smooth a noisy swing |
//!
//! All three are periodic: the arc from the last node through `360°/0°` back to
//! the first node is a real interval, not a flat extrapolation.
//!
//! # Example
//!
//! ```rust
//! use bearingpro::{DeviationTable, InterpolationMethod};
//!
//! let mut table = DeviationTable::from_step(90)?;
//! table.set_deviation(0, 10.0)?;
//! table.set_deviation(180, -10.0)?;
//!
//! // Halfway between the 270° node (0.0) and the 0° node (10.0), the long way
//! // round through north — a segment the pre-1.0 implementation could not see.
//! let deviation = table.deviation_at(315.0, InterpolationMethod::Linear, None)?;
//! assert!((deviation.degrees() - 5.0).abs() < 1e-12);
//! # Ok::<(), bearingpro::NavigationError>(())
//! ```

use alloc::string::ToString;
use alloc::vec;
use alloc::vec::Vec;

use crate::angle::{
    ensure_range, wrap180, wrap360, Compass, Deviation, Direction, True, Variation,
    MAX_DEVIATION_DEG,
};
use crate::error::{NavigationError, Result};
use crate::linalg::{solve_cyclic_tridiagonal, solve_dense};
use crate::math;

/// Number of values [`DeviationTable::from_deviation_vec`] expects: 0° to 350° in 10° steps.
pub const STANDARD_TABLE_LEN: usize = 36;

/// The eight cardinal and intercardinal directions, with their compass courses.
pub const CARDINAL_DIRECTIONS: [(&str, i32); 8] = [
    ("N", 0),
    ("NE", 45),
    ("E", 90),
    ("SE", 135),
    ("S", 180),
    ("SW", 225),
    ("W", 270),
    ("NW", 315),
];

/// How to read deviation for a heading that is not a table node.
///
/// This enum is `#[non_exhaustive]`; match with a wildcard arm.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
#[non_exhaustive]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum InterpolationMethod {
    /// Periodic linear interpolation between neighbouring nodes.
    ///
    /// The default: it is exact at the nodes, never overshoots them, and needs
    /// only two nodes.
    #[default]
    Linear,
    /// Periodic cubic spline with continuous first and second derivatives.
    ///
    /// Exact at the nodes and smooth across `360°/0°`. Falls back to
    /// [`InterpolationMethod::Linear`] for tables with fewer than three nodes.
    Cubic,
    /// The classical five-coefficient deviation model, fitted by least squares.
    ///
    /// `δ = A + B·sin(y) + C·cos(y) + D·sin(2y) + E·cos(2y)`
    ///
    /// Unlike the others this is a *fit*, not an interpolation: it does not
    /// reproduce the nodes exactly, which is exactly what you want when the
    /// swing contains observation noise.
    Parametric,
    /// Periodic shape-preserving cubic, by the Fritsch–Carlson method.
    ///
    /// Smooth like [`InterpolationMethod::Cubic`], but it cannot overshoot:
    /// between two nodes the curve stays between their values, and it never
    /// invents a wiggle the data does not show. A cubic spline buys its second
    /// derivative by allowing both, which on a swing with an abrupt step can put
    /// the interpolated deviation outside anything that was ever observed.
    ///
    /// Slightly less smooth — continuous first derivative but not second — and
    /// the better default when the numbers matter more than the curve.
    ShapePreserving,
}

/// How to read the table, and with which coefficients.
///
/// Every conversion in [`crate::navigation_solutions`] takes
/// `impl Into<Interpolation>`, so passing a bare [`InterpolationMethod`] is
/// enough for the common case, and this struct is there when you need to pin
/// coefficients as well.
///
/// # Example
///
/// ```rust
/// use bearingpro::{
///     navigation_solutions::convert_compass_course_to_true_course, CompassCourse,
///     DeviationCoefficients, DeviationTable, Interpolation, InterpolationMethod, Variation,
/// };
///
/// let table = DeviationTable::from_deviation_vec(vec![0.0; 36])?;
/// let coefficients = DeviationCoefficients {
///     a: Some(1.0),
///     ..DeviationCoefficients::default()
/// };
///
/// // A bare method...
/// let plain = convert_compass_course_to_true_course(
///     CompassCourse::new(10.0)?,
///     Variation::ZERO,
///     &table,
///     InterpolationMethod::Linear,
/// )?;
/// assert_eq!(plain.deviation.degrees(), 0.0);
///
/// // ...or a method with coefficients held fixed.
/// let pinned = convert_compass_course_to_true_course(
///     CompassCourse::new(10.0)?,
///     Variation::ZERO,
///     &table,
///     Interpolation {
///         method: InterpolationMethod::Parametric,
///         coefficients: Some(&coefficients),
///     },
/// )?;
/// assert!((pinned.deviation.degrees() - 1.0).abs() < 1e-9);
/// # Ok::<(), bearingpro::NavigationError>(())
/// ```
#[derive(Debug, Clone, Copy, Default)]
pub struct Interpolation<'a> {
    /// Which method to use.
    pub method: InterpolationMethod,
    /// Coefficients to hold fixed, for [`InterpolationMethod::Parametric`].
    pub coefficients: Option<&'a DeviationCoefficients>,
}

impl From<InterpolationMethod> for Interpolation<'_> {
    fn from(method: InterpolationMethod) -> Self {
        Self {
            method,
            coefficients: None,
        }
    }
}

/// One heading of a swing, as it is actually observed.
///
/// Deviation is not measured directly. What is measured is a bearing of
/// something whose true direction is known — a transit, a distant object, the
/// azimuth of a heavenly body — taken by the compass on each heading in turn.
/// The deviation follows from the three:
///
/// ```text
/// deviation = reference bearing − variation − observed bearing
/// ```
///
/// # Example
///
/// ```rust
/// use bearingpro::{
///     CompassBearing, CompassCourse, DeviationTable, NavigationError, SwingObservation,
///     TrueBearing, Variation,
/// };
///
/// fn main() -> Result<(), NavigationError> {
///     let variation = Variation::new(-2.0)?;
///     // A transit whose charted direction is 045°T, observed from four headings.
///     let transit = TrueBearing::new(45.0)?;
///     let observations = [
///         (0.0, 48.5),
///         (90.0, 46.0),
///         (180.0, 45.5),
///         (270.0, 48.0),
///     ]
///     .into_iter()
///     .map(|(heading, observed)| {
///         Ok(SwingObservation {
///             compass_heading: CompassCourse::new(heading)?,
///             observed_bearing: CompassBearing::new(observed)?,
///             reference_bearing: transit,
///         })
///     })
///     .collect::<Result<Vec<_>, NavigationError>>()?;
///
///     let table = DeviationTable::from_swing(&observations, variation)?;
///
///     // On north the compass read 048.5 for something that is really 045.0,
///     // with 2°W variation: deviation is 045.0 − (−2.0) − 048.5 = −1.5°.
///     assert_eq!(table.deviation_at_node(0).unwrap().degrees(), -1.5);
///     Ok(())
/// }
/// ```
#[derive(Debug, Clone, Copy, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct SwingObservation {
    /// Heading the ship was steadied on, by compass.
    pub compass_heading: Direction<Compass>,
    /// Bearing of the reference object, as read from the same compass.
    pub observed_bearing: Direction<Compass>,
    /// True bearing the reference object is known to lie on.
    pub reference_bearing: Direction<True>,
}

impl SwingObservation {
    /// The deviation this observation implies, given the variation in force.
    ///
    /// # Errors
    ///
    /// Returns [`NavigationError::OutOfRange`] if the three bearings imply a
    /// deviation beyond half a turn, which means one of them is wrong.
    pub fn deviation(&self, variation: Variation) -> Result<Deviation> {
        Deviation::new(wrap180(
            self.reference_bearing.degrees()
                - variation.degrees()
                - self.observed_bearing.degrees(),
        ))
    }
}

/// One row of a deviation table.
#[derive(Debug, Clone, Copy, PartialEq)]
#[cfg_attr(
    feature = "serde",
    derive(serde::Serialize, serde::Deserialize),
    serde(try_from = "(i32, f64)", into = "(i32, f64)")
)]
pub struct DeviationNode {
    course: i32,
    deviation: f64,
}

impl DeviationNode {
    /// The compass course of this node, in `0..360` degrees.
    #[must_use]
    pub const fn course(&self) -> i32 {
        self.course
    }

    /// The tabulated deviation at this node.
    #[must_use]
    pub fn deviation(&self) -> Deviation {
        // The value was validated when it entered the table.
        Deviation::new(self.deviation).unwrap_or(Deviation::ZERO)
    }

    /// The tabulated deviation in degrees.
    #[must_use]
    pub const fn deviation_degrees(&self) -> f64 {
        self.deviation
    }
}

/// Coefficients for the parametric deviation model.
///
/// Any field left `None` is fitted from the table by least squares; any field
/// set to `Some` is held fixed and the remaining ones are fitted around it.
///
/// # Example
///
/// ```rust
/// use bearingpro::{DeviationCoefficients, DeviationTable, InterpolationMethod};
///
/// let table = DeviationTable::from_deviation_vec(vec![0.0; 36])?;
///
/// // Force a constant 1° index error, fit the rest.
/// let coefficients = DeviationCoefficients {
///     a: Some(1.0),
///     ..DeviationCoefficients::default()
/// };
///
/// let deviation = table.deviation_at(
///     250.0,
///     InterpolationMethod::Parametric,
///     Some(&coefficients),
/// )?;
/// assert!((deviation.degrees() - 1.0).abs() < 1e-9);
/// # Ok::<(), bearingpro::NavigationError>(())
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct DeviationCoefficients {
    /// Constant deviation, usually a compass index or alignment error.
    pub a: Option<f64>,
    /// Semicircular deviation in phase with `sin(course)`.
    pub b: Option<f64>,
    /// Semicircular deviation in phase with `cos(course)`.
    pub c: Option<f64>,
    /// Quadrantal deviation in phase with `sin(2·course)`.
    pub d: Option<f64>,
    /// Quadrantal deviation in phase with `cos(2·course)`.
    pub e: Option<f64>,
}

impl DeviationCoefficients {
    fn as_array(self) -> [Option<f64>; 5] {
        [self.a, self.b, self.c, self.d, self.e]
    }

    fn validate(self) -> Result<()> {
        for (name, value) in [
            ("coefficient A", self.a),
            ("coefficient B", self.b),
            ("coefficient C", self.c),
            ("coefficient D", self.d),
            ("coefficient E", self.e),
        ] {
            if let Some(value) = value {
                ensure_range(name, value, -MAX_DEVIATION_DEG, MAX_DEVIATION_DEG)?;
            }
        }
        Ok(())
    }
}

/// A fully determined set of deviation coefficients.
#[derive(Debug, Clone, Copy, PartialEq, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct SmithCoefficients {
    /// Constant deviation.
    pub a: f64,
    /// Semicircular deviation in phase with `sin(course)`.
    pub b: f64,
    /// Semicircular deviation in phase with `cos(course)`.
    pub c: f64,
    /// Quadrantal deviation in phase with `sin(2·course)`.
    pub d: f64,
    /// Quadrantal deviation in phase with `cos(2·course)`.
    pub e: f64,
}

impl SmithCoefficients {
    /// Evaluates the model at a compass course, in degrees.
    #[must_use]
    pub fn deviation_at(&self, course_degrees: f64) -> f64 {
        let basis = parametric_basis(course_degrees);
        self.a * basis[0]
            + self.b * basis[1]
            + self.c * basis[2]
            + self.d * basis[3]
            + self.e * basis[4]
    }

    /// Converts to the partially-specified form accepted by the interpolator.
    #[must_use]
    pub const fn as_input(&self) -> DeviationCoefficients {
        DeviationCoefficients {
            a: Some(self.a),
            b: Some(self.b),
            c: Some(self.c),
            d: Some(self.d),
            e: Some(self.e),
        }
    }

    fn from_array(values: [f64; 5]) -> Self {
        Self {
            a: values[0],
            b: values[1],
            c: values[2],
            d: values[3],
            e: values[4],
        }
    }
}

/// Summary of a swing, produced by [`DeviationTable::analyze`].
#[derive(Debug, Clone, Copy, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct DeviationAnalysis {
    /// Least-squares fit of the five-coefficient model.
    pub coefficients: SmithCoefficients,
    /// Root-mean-square distance between the tabulated values and the fit, in degrees.
    ///
    /// Large values mean the compass has deviation the classical model does not
    /// describe — or that the swing contains a bad observation.
    pub rms_residual: f64,
    /// Largest single residual, in degrees.
    pub max_residual: f64,
    /// Largest tabulated deviation magnitude, in degrees.
    pub max_abs_deviation: f64,
    /// Largest angular gap between adjacent nodes, in degrees, measured periodically.
    pub max_gap: f64,
    /// Steepest node-to-node slope, in degrees of deviation per degree of heading.
    ///
    /// See [`DeviationTable::max_slope`]; at or above `1.0` the table cannot be
    /// inverted uniquely.
    pub max_slope: f64,
    /// Number of nodes in the table.
    pub nodes: usize,
}

/// Deviation as a function of compass course.
///
/// The table keeps its nodes sorted and unique, so lookups are a binary search
/// and iteration order is deterministic. Every constructor validates its input:
/// a table that exists is always usable.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(
    feature = "serde",
    derive(serde::Serialize, serde::Deserialize),
    serde(try_from = "Vec<(i32, f64)>", into = "Vec<(i32, f64)>")
)]
pub struct DeviationTable {
    nodes: Vec<DeviationNode>,
}

impl Default for DeviationTable {
    /// A table of zero deviations from 0° to 350° in 10° steps.
    fn default() -> Self {
        Self {
            nodes: (0..STANDARD_TABLE_LEN)
                .map(|index| DeviationNode {
                    // `index < 36`, so this cannot overflow.
                    course: i32::try_from(index).unwrap_or(0) * 10,
                    deviation: 0.0,
                })
                .collect(),
        }
    }
}

impl DeviationTable {
    /// Builds a table of zero deviations with a fixed step between headings.
    ///
    /// # Errors
    ///
    /// Returns [`NavigationError::InvalidStep`] unless `step` is in `1..=180`.
    /// A step of `0` used to abort the process; a negative step used to produce a
    /// silent one-node table.
    pub fn from_step(step: i32) -> Result<Self> {
        if !(1..=180).contains(&step) {
            return Err(NavigationError::InvalidStep { step });
        }
        let stride = usize::try_from(step).unwrap_or(1);
        let nodes = (0..360)
            .step_by(stride)
            .map(|course| DeviationNode {
                course,
                deviation: 0.0,
            })
            .collect();
        Ok(Self { nodes })
    }

    /// Builds a table of zero deviations on the eight cardinal and intercardinal points.
    #[must_use]
    pub fn from_cardinal_directions() -> Self {
        let mut nodes: Vec<DeviationNode> = CARDINAL_DIRECTIONS
            .iter()
            .map(|&(_, course)| DeviationNode {
                course,
                deviation: 0.0,
            })
            .collect();
        nodes.sort_unstable_by_key(DeviationNode::course);
        Self { nodes }
    }

    /// Builds a table from explicit `(compass course, deviation)` pairs.
    ///
    /// Courses are normalised into `0..360` with Euclidean remainder, so `-350`
    /// becomes `10`. The pre-1.0 implementation used `%`, which left `-350` as a
    /// negative key that no lookup could ever match.
    ///
    /// # Errors
    ///
    /// - [`NavigationError::InsufficientNodes`] if fewer than two pairs remain.
    /// - [`NavigationError::DuplicateCourse`] if two pairs normalise to the same course.
    /// - [`NavigationError::NotFinite`] or [`NavigationError::OutOfRange`] for a bad deviation.
    pub fn from_vec(deviations: Vec<(i32, f64)>) -> Result<Self> {
        let mut nodes = Vec::with_capacity(deviations.len());
        for (course, deviation) in deviations {
            ensure_range(
                "deviation",
                deviation,
                -MAX_DEVIATION_DEG,
                MAX_DEVIATION_DEG,
            )?;
            nodes.push(DeviationNode {
                course: course.rem_euclid(360),
                deviation,
            });
        }
        Self::from_nodes(nodes)
    }

    /// Builds a table from 36 deviations for the headings 0°, 10°, … 350°.
    ///
    /// # Errors
    ///
    /// Returns [`NavigationError::UnexpectedTableLength`] unless exactly
    /// [`STANDARD_TABLE_LEN`] values are supplied. The pre-1.0 implementation
    /// silently zero-filled a short slice and silently dropped a long one.
    pub fn from_deviation_vec(deviations: Vec<f64>) -> Result<Self> {
        if deviations.len() != STANDARD_TABLE_LEN {
            return Err(NavigationError::UnexpectedTableLength {
                found: deviations.len(),
                expected: STANDARD_TABLE_LEN,
            });
        }
        let mut nodes = Vec::with_capacity(STANDARD_TABLE_LEN);
        for (index, deviation) in deviations.into_iter().enumerate() {
            ensure_range(
                "deviation",
                deviation,
                -MAX_DEVIATION_DEG,
                MAX_DEVIATION_DEG,
            )?;
            nodes.push(DeviationNode {
                course: i32::try_from(index).unwrap_or(0) * 10,
                deviation,
            });
        }
        Self::from_nodes(nodes)
    }

    /// Builds a table from the raw observations of a swing.
    ///
    /// This is the step that used to be the caller's problem: the library took a
    /// column of deviations, but a swing produces bearings, and turning one into
    /// the other by hand is where arithmetic slips get in.
    ///
    /// Headings are rounded to the nearest whole degree, so a swing steadied on
    /// 089.6° by compass becomes the 090° node.
    ///
    /// # Errors
    ///
    /// - [`NavigationError::InsufficientNodes`] for fewer than two observations.
    /// - [`NavigationError::DuplicateCourse`] if two observations round to the
    ///   same heading.
    /// - [`NavigationError::OutOfRange`] if an observation implies an impossible
    ///   deviation.
    pub fn from_swing(observations: &[SwingObservation], variation: Variation) -> Result<Self> {
        let mut nodes = Vec::with_capacity(observations.len());
        for observation in observations {
            let deviation = observation.deviation(variation)?;
            // A validated direction is in `[0, 360)`, so this cannot overflow.
            let heading = math::round_to_i32(observation.compass_heading.degrees());
            nodes.push(DeviationNode {
                course: heading.rem_euclid(360),
                deviation: deviation.degrees(),
            });
        }
        Self::from_nodes(nodes)
    }

    fn from_nodes(mut nodes: Vec<DeviationNode>) -> Result<Self> {
        nodes.sort_unstable_by_key(DeviationNode::course);
        if let Some(duplicate) = nodes
            .windows(2)
            .find(|pair| {
                pair.first().map(DeviationNode::course) == pair.last().map(DeviationNode::course)
            })
            .and_then(|pair| pair.first())
        {
            return Err(NavigationError::DuplicateCourse {
                course: duplicate.course,
            });
        }
        if nodes.len() < 2 {
            return Err(NavigationError::InsufficientNodes {
                found: nodes.len(),
                required: 2,
                context: "a deviation table",
            });
        }
        Ok(Self { nodes })
    }

    /// The table's nodes, sorted by compass course.
    #[must_use]
    pub fn nodes(&self) -> &[DeviationNode] {
        &self.nodes
    }

    /// Number of nodes in the table, always at least two.
    #[must_use]
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Always `false`: a table cannot be constructed empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Replaces the deviation at an existing node.
    ///
    /// The course is normalised into `0..360` first.
    ///
    /// # Errors
    ///
    /// - [`NavigationError::CourseNotInTable`] if the course is not a node; use
    ///   [`DeviationTable::insert_deviation`] to add one.
    /// - [`NavigationError::NotFinite`] or [`NavigationError::OutOfRange`] for a bad value.
    pub fn set_deviation(&mut self, course: i32, deviation: f64) -> Result<()> {
        ensure_range(
            "deviation",
            deviation,
            -MAX_DEVIATION_DEG,
            MAX_DEVIATION_DEG,
        )?;
        let course = course.rem_euclid(360);
        match self
            .nodes
            .binary_search_by_key(&course, DeviationNode::course)
        {
            Ok(index) => {
                if let Some(node) = self.nodes.get_mut(index) {
                    node.deviation = deviation;
                }
                Ok(())
            }
            Err(_) => Err(NavigationError::CourseNotInTable { course }),
        }
    }

    /// Sets the deviation at a course, adding the node if it does not exist yet.
    ///
    /// # Errors
    ///
    /// Returns [`NavigationError::NotFinite`] or [`NavigationError::OutOfRange`]
    /// for a deviation that is not a usable angle.
    pub fn insert_deviation(&mut self, course: i32, deviation: f64) -> Result<()> {
        ensure_range(
            "deviation",
            deviation,
            -MAX_DEVIATION_DEG,
            MAX_DEVIATION_DEG,
        )?;
        let course = course.rem_euclid(360);
        match self
            .nodes
            .binary_search_by_key(&course, DeviationNode::course)
        {
            Ok(index) => {
                if let Some(node) = self.nodes.get_mut(index) {
                    node.deviation = deviation;
                }
            }
            Err(index) => self
                .nodes
                .insert(index, DeviationNode { course, deviation }),
        }
        Ok(())
    }

    /// Sets the deviation on one of the eight cardinal points.
    ///
    /// # Errors
    ///
    /// - [`NavigationError::UnknownCardinalDirection`] for an unrecognised name.
    /// - [`NavigationError::CourseNotInTable`] if that point is not a node of this table.
    /// - [`NavigationError::NotFinite`] or [`NavigationError::OutOfRange`] for a bad value.
    pub fn set_deviation_by_direction(&mut self, direction: &str, deviation: f64) -> Result<()> {
        let course = cardinal_course(direction)?;
        self.set_deviation(course, deviation)
    }

    /// Reads the tabulated deviation on one of the eight cardinal points.
    ///
    /// Returns `None` if the name is unknown or that point is not a node.
    #[must_use]
    pub fn get_deviation_by_direction(&self, direction: &str) -> Option<Deviation> {
        let course = cardinal_course(direction).ok()?;
        self.deviation_at_node(course)
    }

    /// Reads the tabulated deviation at an exact node, without interpolating.
    #[must_use]
    pub fn deviation_at_node(&self, course: i32) -> Option<Deviation> {
        let course = course.rem_euclid(360);
        self.nodes
            .binary_search_by_key(&course, DeviationNode::course)
            .ok()
            .and_then(|index| self.nodes.get(index))
            .map(DeviationNode::deviation)
    }

    /// Largest gap between adjacent nodes, in degrees, measured around the full circle.
    #[must_use]
    pub fn max_gap(&self) -> f64 {
        let mut max_gap: f64 = 0.0;
        for pair in self.nodes.windows(2) {
            if let (Some(low), Some(high)) = (pair.first(), pair.last()) {
                max_gap = max_gap.max(f64::from(high.course - low.course));
            }
        }
        if let (Some(first), Some(last)) = (self.nodes.first(), self.nodes.last()) {
            max_gap = max_gap.max(360.0 - f64::from(last.course - first.course));
        }
        max_gap
    }

    /// Steepest node-to-node rate of change of deviation, in degrees per degree.
    ///
    /// This is what decides whether the table can be inverted. Once deviation
    /// changes by a full degree for each degree of heading, two different compass
    /// courses produce the same magnetic course, and asking "what compass course
    /// gives this true course" stops having a single answer. See
    /// [`DeviationTable::is_invertible`].
    #[must_use]
    pub fn max_slope(&self) -> f64 {
        let count = self.nodes.len();
        let mut steepest: f64 = 0.0;
        for index in 0..count {
            let span = if index + 1 < count {
                self.node_course(index + 1) - self.node_course(index)
            } else {
                360.0 - self.node_course(index) + self.node_course(0)
            };
            if span > 0.0 {
                let rise = self.node_value(index + 1) - self.node_value(index);
                steepest = steepest.max(math::abs(rise) / span);
            }
        }
        steepest
    }

    /// Whether a magnetic course maps back to exactly one compass course.
    ///
    /// False means the swing describes a compass that cannot be steered by over
    /// part of the circle, and should be re-swung or the compass re-adjusted.
    /// Conversions still work — [`crate::navigation_solutions::convert_true_course_to_compass_course`]
    /// returns *a* compass course that produces the requested true course — but it
    /// is no longer necessarily the one you started from.
    #[must_use]
    pub fn is_invertible(&self) -> bool {
        self.max_slope() < 1.0
    }

    /// Largest tabulated deviation magnitude, in degrees.
    #[must_use]
    pub fn max_abs_deviation(&self) -> f64 {
        self.nodes
            .iter()
            .fold(0.0_f64, |acc, node| acc.max(math::abs(node.deviation)))
    }

    /// Interpolates the deviation for one compass course.
    ///
    /// # Errors
    ///
    /// - [`NavigationError::NotFinite`] or [`NavigationError::OutOfRange`] if
    ///   `course_degrees` is not in `[0.0, 360.0]`.
    /// - [`NavigationError::InsufficientNodes`] or
    ///   [`NavigationError::SingularSystem`] if a parametric fit is impossible.
    pub fn deviation_at(
        &self,
        course_degrees: f64,
        method: InterpolationMethod,
        coefficients: Option<&DeviationCoefficients>,
    ) -> Result<Deviation> {
        ensure_range("course", course_degrees, 0.0, 360.0)?;
        let interpolator = self.prepare(method, coefficients)?;
        Deviation::new(self.evaluate(&interpolator, wrap360(course_degrees)))
    }

    /// Interpolates the deviation for several compass courses at once.
    ///
    /// Cheaper than repeated [`DeviationTable::deviation_at`] calls: the spline
    /// or the least-squares fit is built once for the whole batch.
    ///
    /// # Errors
    ///
    /// As [`DeviationTable::deviation_at`], for the first offending angle.
    pub fn interpolate_deviation(
        &self,
        courses_degrees: &[f64],
        method: InterpolationMethod,
        coefficients: Option<&DeviationCoefficients>,
    ) -> Result<Vec<f64>> {
        for &course in courses_degrees {
            ensure_range("course", course, 0.0, 360.0)?;
        }
        let interpolator = self.prepare(method, coefficients)?;
        Ok(courses_degrees
            .iter()
            .map(|&course| self.evaluate(&interpolator, wrap360(course)))
            .collect())
    }

    /// Fits the five-coefficient deviation model to the whole table by least squares.
    ///
    /// # Errors
    ///
    /// - [`NavigationError::InsufficientNodes`] if the table has fewer than five nodes.
    /// - [`NavigationError::SingularSystem`] if the nodes do not constrain the model,
    ///   for example when they all lie on one semicircle.
    pub fn smith_coefficients(&self) -> Result<SmithCoefficients> {
        self.fit_parametric(&DeviationCoefficients::default())
    }

    /// Summarises the table: fitted coefficients, residuals, extremes and node spacing.
    ///
    /// # Errors
    ///
    /// As [`DeviationTable::smith_coefficients`].
    pub fn analyze(&self) -> Result<DeviationAnalysis> {
        let coefficients = self.smith_coefficients()?;
        let mut sum_squares = 0.0;
        let mut max_residual: f64 = 0.0;
        for node in &self.nodes {
            let residual = node.deviation - coefficients.deviation_at(f64::from(node.course));
            sum_squares += residual * residual;
            max_residual = max_residual.max(math::abs(residual));
        }
        let count = self.nodes.len();
        // `from_nodes` guarantees at least two nodes, so this division is safe.
        let rms_residual = math::sqrt(sum_squares / math::count_to_f64(count.max(1)));
        Ok(DeviationAnalysis {
            coefficients,
            rms_residual,
            max_residual,
            max_abs_deviation: self.max_abs_deviation(),
            max_gap: self.max_gap(),
            max_slope: self.max_slope(),
            nodes: count,
        })
    }

    /// Builds whatever the chosen method needs before it can be evaluated.
    pub(crate) fn prepare(
        &self,
        method: InterpolationMethod,
        coefficients: Option<&DeviationCoefficients>,
    ) -> Result<Interpolator> {
        match method {
            InterpolationMethod::Linear => Ok(Interpolator::Linear),
            InterpolationMethod::Cubic => {
                // A cyclic spline system is only well posed from three nodes up.
                if self.nodes.len() < 3 {
                    return Ok(Interpolator::Linear);
                }
                match self.second_derivatives() {
                    Some(moments) => Ok(Interpolator::Cubic(moments)),
                    None => Err(NavigationError::SingularSystem {
                        context: "the periodic cubic spline",
                    }),
                }
            }
            InterpolationMethod::Parametric => {
                let requested = coefficients.copied().unwrap_or_default();
                Ok(Interpolator::Parametric(self.fit_parametric(&requested)?))
            }
            InterpolationMethod::ShapePreserving => {
                Ok(Interpolator::Hermite(self.shape_preserving_slopes()))
            }
        }
    }

    /// Evaluates a prepared interpolator. `course` must already be in `[0.0, 360.0)`.
    pub(crate) fn evaluate(&self, interpolator: &Interpolator, course: f64) -> f64 {
        match interpolator {
            Interpolator::Linear => self.evaluate_linear(course),
            Interpolator::Cubic(moments) => self.evaluate_cubic(moments, course),
            Interpolator::Parametric(coefficients) => coefficients.deviation_at(course),
            Interpolator::Hermite(slopes) => self.evaluate_hermite(slopes, course),
        }
    }

    /// Estimated uncertainty of an interpolated value at `course`, in degrees.
    ///
    /// For the two interpolating methods this is the classical `h²·|f''|/8` bound
    /// on linear interpolation error, approximated by the local second difference
    /// of the tabulated values. For the parametric fit it is the RMS residual,
    /// since that method does not pass through the nodes at all.
    pub(crate) fn uncertainty(&self, interpolator: &Interpolator, course: f64) -> f64 {
        match interpolator {
            Interpolator::Parametric(coefficients) => {
                let mut sum_squares = 0.0;
                for node in &self.nodes {
                    let residual =
                        node.deviation - coefficients.deviation_at(f64::from(node.course));
                    sum_squares += residual * residual;
                }
                math::sqrt(sum_squares / math::count_to_f64(self.nodes.len().max(1)))
            }
            Interpolator::Linear | Interpolator::Cubic(_) | Interpolator::Hermite(_) => {
                let segment = self.locate(course);
                let count = self.nodes.len();
                let second_difference = |centre: usize| {
                    let previous = self.node_value(centre + count - 1);
                    let current = self.node_value(centre);
                    let next = self.node_value(centre + 1);
                    math::abs(previous - 2.0 * current + next)
                };
                let left = second_difference(segment.index);
                let right = second_difference((segment.index + 1) % count);
                left.max(right) / 8.0
            }
        }
    }

    fn node_value(&self, index: usize) -> f64 {
        let count = self.nodes.len().max(1);
        self.nodes
            .get(index % count)
            .map_or(0.0, DeviationNode::deviation_degrees)
    }

    fn node_course(&self, index: usize) -> f64 {
        let count = self.nodes.len().max(1);
        self.nodes
            .get(index % count)
            .map_or(0.0, |node| f64::from(node.course))
    }

    /// Finds the segment containing `course`, treating the table as a closed circle.
    fn locate(&self, course: f64) -> Segment {
        let count = self.nodes.len();
        let first = self.node_course(0);
        let last = self.node_course(count.saturating_sub(1));
        let wrap_span = 360.0 - last + first;

        if course < first {
            // Between the last node and the first, having already passed 360°/0°.
            return Segment {
                index: count.saturating_sub(1),
                span: wrap_span,
                offset: course + 360.0 - last,
            };
        }

        let index = self
            .nodes
            .partition_point(|node| f64::from(node.course) <= course)
            .saturating_sub(1);

        if index >= count.saturating_sub(1) {
            Segment {
                index: count.saturating_sub(1),
                span: wrap_span,
                offset: course - last,
            }
        } else {
            let start = self.node_course(index);
            Segment {
                index,
                span: self.node_course(index + 1) - start,
                offset: course - start,
            }
        }
    }

    fn evaluate_linear(&self, course: f64) -> f64 {
        let segment = self.locate(course);
        let start_value = self.node_value(segment.index);
        let end_value = self.node_value(segment.index + 1);
        start_value + (end_value - start_value) * segment.fraction()
    }

    fn evaluate_cubic(&self, moments: &[f64], course: f64) -> f64 {
        let segment = self.locate(course);
        let count = self.nodes.len().max(1);
        let start_value = self.node_value(segment.index);
        let end_value = self.node_value(segment.index + 1);
        let start_moment = moments.get(segment.index % count).copied().unwrap_or(0.0);
        let end_moment = moments
            .get((segment.index + 1) % count)
            .copied()
            .unwrap_or(0.0);

        let span = segment.span;
        let slope =
            (end_value - start_value) / span - span * (2.0 * start_moment + end_moment) / 6.0;
        let offset = segment.offset;

        start_value
            + slope * offset
            + start_moment / 2.0 * offset * offset
            + (end_moment - start_moment) / (6.0 * span) * offset * offset * offset
    }

    /// Evaluates the shape-preserving cubic on the segment containing `course`.
    fn evaluate_hermite(&self, slopes: &[f64], course: f64) -> f64 {
        let segment = self.locate(course);
        let count = self.nodes.len().max(1);
        let start_value = self.node_value(segment.index);
        let end_value = self.node_value(segment.index + 1);
        let start_slope = slopes.get(segment.index % count).copied().unwrap_or(0.0);
        let end_slope = slopes
            .get((segment.index + 1) % count)
            .copied()
            .unwrap_or(0.0);

        // The cubic Hermite basis on the unit interval.
        let span = segment.span;
        let t = segment.fraction();
        let complement = 1.0 - t;
        let start_weight = (1.0 + 2.0 * t) * complement * complement;
        let start_tangent = t * complement * complement;
        let end_weight = t * t * (3.0 - 2.0 * t);
        let end_tangent = t * t * (t - 1.0);

        start_value * start_weight
            + span * start_slope * start_tangent
            + end_value * end_weight
            + span * end_slope * end_tangent
    }

    /// Node slopes for the shape-preserving cubic, by Fritsch–Carlson.
    ///
    /// Where the data turns, the slope is set to zero; elsewhere it is the
    /// weighted harmonic mean of the two neighbouring secants, which is what
    /// keeps the curve from overshooting.
    fn shape_preserving_slopes(&self) -> Vec<f64> {
        let count = self.nodes.len();
        let gap = |index: usize| {
            if index + 1 < count {
                self.node_course(index + 1) - self.node_course(index)
            } else {
                360.0 - self.node_course(index) + self.node_course(0)
            }
        };

        (0..count)
            .map(|index| {
                let previous = (index + count - 1) % count;
                let (before, after) = (gap(previous), gap(index));
                if before <= 0.0 || after <= 0.0 {
                    return 0.0;
                }
                let secant_before = (self.node_value(index) - self.node_value(previous)) / before;
                let secant_after = (self.node_value(index + 1) - self.node_value(index)) / after;

                // A turning point, or a flat spot: level the tangent so the
                // curve cannot bulge past the nodes on either side.
                if secant_before * secant_after <= 0.0 {
                    return 0.0;
                }
                let weight_before = 2.0 * after + before;
                let weight_after = after + 2.0 * before;
                (weight_before + weight_after)
                    / (weight_before / secant_before + weight_after / secant_after)
            })
            .collect()
    }

    /// Second derivatives of the periodic cubic spline, one per node.
    ///
    /// Solves the cyclic tridiagonal moment system; returns `None` if it is
    /// numerically singular.
    fn second_derivatives(&self) -> Option<Vec<f64>> {
        let count = self.nodes.len();
        if count < 3 {
            return None;
        }

        // Gap from node i to node i+1, the last one closing the circle.
        let gaps: Vec<f64> = (0..count)
            .map(|index| {
                if index + 1 < count {
                    self.node_course(index + 1) - self.node_course(index)
                } else {
                    360.0 - self.node_course(index) + self.node_course(0)
                }
            })
            .collect();

        let mut sub = vec![0.0; count];
        let mut diag = vec![0.0; count];
        let mut sup = vec![0.0; count];
        let mut rhs = vec![0.0; count];

        for index in 0..count {
            let previous = (index + count - 1) % count;
            let gap_before = *gaps.get(previous)?;
            let gap_after = *gaps.get(index)?;

            let slope_before = (self.node_value(index) - self.node_value(previous)) / gap_before;
            let slope_after = (self.node_value(index + 1) - self.node_value(index)) / gap_after;

            *sub.get_mut(index)? = gap_before;
            *diag.get_mut(index)? = 2.0 * (gap_before + gap_after);
            *sup.get_mut(index)? = gap_after;
            *rhs.get_mut(index)? = 6.0 * (slope_after - slope_before);
        }

        // Row 0 reaches back to node n-1 and row n-1 reaches forward to node 0;
        // those two entries live in the matrix corners, not on the diagonals.
        let corner_top_right = *sub.first()?;
        let corner_bottom_left = *sup.last()?;
        *sub.first_mut()? = 0.0;
        *sup.last_mut()? = 0.0;

        solve_cyclic_tridiagonal(
            &sub,
            &diag,
            &sup,
            corner_top_right,
            corner_bottom_left,
            &rhs,
        )
    }

    /// Least-squares fit of the parametric model, holding any supplied coefficient fixed.
    fn fit_parametric(&self, requested: &DeviationCoefficients) -> Result<SmithCoefficients> {
        requested.validate()?;
        let fixed = requested.as_array();
        let free: Vec<usize> = (0..5)
            .filter(|&index| fixed.get(index).copied().flatten().is_none())
            .collect();

        let mut resolved = [0.0_f64; 5];
        for (index, value) in fixed.iter().enumerate() {
            if let (Some(slot), Some(value)) = (resolved.get_mut(index), *value) {
                *slot = value;
            }
        }

        if free.is_empty() {
            return Ok(SmithCoefficients::from_array(resolved));
        }

        if self.nodes.len() < free.len() {
            return Err(NavigationError::InsufficientNodes {
                found: self.nodes.len(),
                required: free.len(),
                context: "a parametric deviation fit",
            });
        }

        // Normal equations over the free basis functions only, with the fixed
        // contribution subtracted from the observations first.
        let size = free.len();
        let mut normal = vec![0.0; size * size];
        let mut target = vec![0.0; size];

        for node in &self.nodes {
            let basis = parametric_basis(f64::from(node.course));
            let mut residual = node.deviation;
            for (index, value) in fixed.iter().enumerate() {
                if let Some(value) = *value {
                    residual -= value * basis.get(index).copied().unwrap_or(0.0);
                }
            }
            for (row, &row_index) in free.iter().enumerate() {
                let row_basis = basis.get(row_index).copied().unwrap_or(0.0);
                for (column, &column_index) in free.iter().enumerate() {
                    let column_basis = basis.get(column_index).copied().unwrap_or(0.0);
                    if let Some(cell) = normal.get_mut(row * size + column) {
                        *cell += row_basis * column_basis;
                    }
                }
                if let Some(cell) = target.get_mut(row) {
                    *cell += row_basis * residual;
                }
            }
        }

        let solution =
            solve_dense(&mut normal, &mut target, size).ok_or(NavigationError::SingularSystem {
                context: "a parametric deviation fit",
            })?;

        for (position, &index) in free.iter().enumerate() {
            if let (Some(slot), Some(value)) = (resolved.get_mut(index), solution.get(position)) {
                *slot = *value;
            }
        }

        Ok(SmithCoefficients::from_array(resolved))
    }
}

#[cfg(feature = "serde")]
impl TryFrom<(i32, f64)> for DeviationNode {
    type Error = NavigationError;

    /// Validates on the way in: a stored node cannot carry an impossible
    /// deviation or a course outside `0..360`.
    fn try_from((course, deviation): (i32, f64)) -> Result<Self> {
        ensure_range(
            "deviation",
            deviation,
            -MAX_DEVIATION_DEG,
            MAX_DEVIATION_DEG,
        )?;
        Ok(Self {
            course: course.rem_euclid(360),
            deviation,
        })
    }
}

#[cfg(feature = "serde")]
impl From<DeviationNode> for (i32, f64) {
    fn from(node: DeviationNode) -> Self {
        (node.course, node.deviation)
    }
}

#[cfg(feature = "serde")]
impl TryFrom<Vec<(i32, f64)>> for DeviationTable {
    type Error = NavigationError;

    /// Read back through [`DeviationTable::from_vec`], so a stored table is
    /// checked for duplicates, non-finite values and having enough nodes just as
    /// a freshly built one is.
    fn try_from(nodes: Vec<(i32, f64)>) -> Result<Self> {
        Self::from_vec(nodes)
    }
}

#[cfg(feature = "serde")]
impl From<DeviationTable> for Vec<(i32, f64)> {
    fn from(table: DeviationTable) -> Self {
        table
            .nodes
            .into_iter()
            .map(|node| (node.course, node.deviation))
            .collect()
    }
}

/// A prepared interpolator, built once and evaluated many times.
#[derive(Debug, Clone)]
pub(crate) enum Interpolator {
    Linear,
    Cubic(Vec<f64>),
    Parametric(SmithCoefficients),
    Hermite(Vec<f64>),
}

/// Where a course falls inside the table's ring of segments.
struct Segment {
    /// Index of the node the segment starts at.
    index: usize,
    /// Angular width of the segment, in degrees. Always greater than zero.
    span: f64,
    /// Distance from the segment start to the query point, in degrees.
    offset: f64,
}

impl Segment {
    fn fraction(&self) -> f64 {
        self.offset / self.span
    }
}

fn cardinal_course(direction: &str) -> Result<i32> {
    CARDINAL_DIRECTIONS
        .iter()
        .find(|&&(name, _)| name.eq_ignore_ascii_case(direction))
        .map(|&(_, course)| course)
        .ok_or_else(|| NavigationError::UnknownCardinalDirection {
            direction: direction.to_string(),
        })
}

/// The five basis functions of the parametric model at a course, in degrees.
fn parametric_basis(course_degrees: f64) -> [f64; 5] {
    let radians = math::to_radians(course_degrees);
    [
        1.0,
        math::sin(radians),
        math::cos(radians),
        math::sin(2.0 * radians),
        math::cos(2.0 * radians),
    ]
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::float_cmp, clippy::indexing_slicing)]
mod tests {
    use super::*;
    use alloc::vec;

    fn readme_table() -> DeviationTable {
        DeviationTable::from_deviation_vec(vec![
            -2.5, -0.5, 1.6, 4.4, -1.7, 0.0, 1.0, 0.3, -0.9, 0.5, -1.2, 0.8, -0.3, 1.7, -2.1, 0.4,
            -0.6, 1.2, -1.3, 0.0, 0.9, -1.1, 1.5, -0.7, -13.2, -15.7, -17.9, -19.2, -18.1, 1.8,
            -0.4, 0.7, -0.2, 1.4, -4.4, -2.9,
        ])
        .unwrap()
    }

    #[test]
    fn default_table_has_thirty_six_nodes() {
        let table = DeviationTable::default();
        assert_eq!(table.len(), STANDARD_TABLE_LEN);
        assert_eq!(table.deviation_at_node(0).unwrap().degrees(), 0.0);
        assert_eq!(table.deviation_at_node(350).unwrap().degrees(), 0.0);
        assert!(table.deviation_at_node(5).is_none());
    }

    #[test]
    fn from_step_rejects_zero_and_negative() {
        // Both of these used to abort the process or silently build a one-node table.
        assert_eq!(
            DeviationTable::from_step(0).unwrap_err(),
            NavigationError::InvalidStep { step: 0 }
        );
        assert_eq!(
            DeviationTable::from_step(-10).unwrap_err(),
            NavigationError::InvalidStep { step: -10 }
        );
        assert!(DeviationTable::from_step(181).is_err());
        assert_eq!(DeviationTable::from_step(180).unwrap().len(), 2);
        assert_eq!(DeviationTable::from_step(1).unwrap().len(), 360);
    }

    #[test]
    fn from_step_never_duplicates_north() {
        let table = DeviationTable::from_step(45).unwrap();
        assert_eq!(table.len(), 8);
        assert_eq!(table.nodes().last().unwrap().course(), 315);
    }

    #[test]
    fn empty_and_tiny_tables_are_rejected_not_paniced() {
        // The pre-1.0 code panicked with a subtract overflow on an empty table.
        assert!(matches!(
            DeviationTable::from_vec(vec![]).unwrap_err(),
            NavigationError::InsufficientNodes { found: 0, .. }
        ));
        assert!(matches!(
            DeviationTable::from_vec(vec![(0, 1.0)]).unwrap_err(),
            NavigationError::InsufficientNodes { found: 1, .. }
        ));
    }

    #[test]
    fn negative_courses_normalise_the_euclidean_way() {
        // `%` used to leave this as the unreachable key -350.
        let table = DeviationTable::from_vec(vec![(-350, 1.0), (180, 2.0)]).unwrap();
        assert_eq!(table.nodes().first().unwrap().course(), 10);
        assert_eq!(table.deviation_at_node(10).unwrap().degrees(), 1.0);
    }

    #[test]
    fn duplicate_courses_are_rejected() {
        assert_eq!(
            DeviationTable::from_vec(vec![(10, 1.0), (370, 2.0), (180, 0.0)]).unwrap_err(),
            NavigationError::DuplicateCourse { course: 10 }
        );
    }

    #[test]
    fn non_finite_deviations_are_rejected() {
        assert!(DeviationTable::from_vec(vec![(0, f64::NAN), (10, 0.0)]).is_err());
        assert!(DeviationTable::from_vec(vec![(0, f64::INFINITY), (10, 0.0)]).is_err());
        let mut table = DeviationTable::default();
        assert!(table.set_deviation(0, f64::NAN).is_err());
        assert!(table.set_deviation(0, 1e9).is_err());
    }

    #[test]
    fn from_deviation_vec_demands_the_full_swing() {
        // Short slices used to be silently zero-filled, long ones silently truncated.
        assert_eq!(
            DeviationTable::from_deviation_vec(vec![-2.5, -0.5]).unwrap_err(),
            NavigationError::UnexpectedTableLength {
                found: 2,
                expected: 36
            }
        );
        assert!(DeviationTable::from_deviation_vec(vec![0.0; 37]).is_err());
        assert!(DeviationTable::from_deviation_vec(vec![0.0; 36]).is_ok());
    }

    #[test]
    fn set_deviation_reports_unknown_nodes() {
        let mut table = DeviationTable::from_cardinal_directions();
        assert_eq!(
            table.set_deviation(50, -1.0).unwrap_err(),
            NavigationError::CourseNotInTable { course: 50 }
        );
        table.set_deviation(90, -1.0).unwrap();
        assert_eq!(table.deviation_at_node(90).unwrap().degrees(), -1.0);

        // ...but `insert_deviation` adds it, keeping the table sorted.
        table.insert_deviation(50, -1.0).unwrap();
        assert_eq!(table.deviation_at_node(50).unwrap().degrees(), -1.0);
        assert!(table
            .nodes()
            .windows(2)
            .all(|pair| pair[0].course() < pair[1].course()));
    }

    #[test]
    fn cardinal_directions_round_trip() {
        let mut table = DeviationTable::from_cardinal_directions();
        table.set_deviation_by_direction("N", -2.5).unwrap();
        table.set_deviation_by_direction("e", 1.0).unwrap();
        assert_eq!(
            table.get_deviation_by_direction("N").unwrap().degrees(),
            -2.5
        );
        assert_eq!(
            table.get_deviation_by_direction("E").unwrap().degrees(),
            1.0
        );
        assert_eq!(
            table.get_deviation_by_direction("SW").unwrap().degrees(),
            0.0
        );
        assert!(table.get_deviation_by_direction("XYZ").is_none());
        assert!(table.set_deviation_by_direction("XYZ", 1.0).is_err());
    }

    #[test]
    fn interpolation_rejects_bad_angles() {
        let table = DeviationTable::default();
        assert!(table
            .interpolate_deviation(&[400.0], InterpolationMethod::Linear, None)
            .is_err());
        assert!(table
            .interpolate_deviation(&[f64::NAN], InterpolationMethod::Linear, None)
            .is_err());
        assert!(table
            .interpolate_deviation(&[-1.0], InterpolationMethod::Cubic, None)
            .is_err());
        assert!(table
            .interpolate_deviation(&[0.0, 360.0], InterpolationMethod::Linear, None)
            .is_ok());
    }

    #[test]
    fn linear_interpolation_is_exact_at_nodes() {
        let table = readme_table();
        for node in table.nodes() {
            let value = table
                .deviation_at(f64::from(node.course()), InterpolationMethod::Linear, None)
                .unwrap();
            assert!((value.degrees() - node.deviation_degrees()).abs() < 1e-12);
        }
    }

    #[test]
    fn cubic_interpolation_is_exact_at_nodes() {
        let table = readme_table();
        for node in table.nodes() {
            let value = table
                .deviation_at(f64::from(node.course()), InterpolationMethod::Cubic, None)
                .unwrap();
            assert!(
                (value.degrees() - node.deviation_degrees()).abs() < 1e-9,
                "node {}: {} vs {}",
                node.course(),
                value.degrees(),
                node.deviation_degrees()
            );
        }
    }

    #[test]
    fn cubic_no_longer_flattens_the_first_segment() {
        // The old implementation returned -2.5 across the whole 0°..10° segment.
        let mut table = DeviationTable::from_step(10).unwrap();
        table.set_deviation(0, -2.5).unwrap();
        table.set_deviation(10, -1.5).unwrap();

        let midpoint = table
            .deviation_at(5.0, InterpolationMethod::Cubic, None)
            .unwrap()
            .degrees();
        assert!(
            midpoint > -2.5 && midpoint < -1.5,
            "midpoint should lie between the nodes, got {midpoint}"
        );
    }

    #[test]
    fn linear_interpolation_wraps_through_north() {
        // The old implementation clamped everything past the last node.
        let mut table = DeviationTable::from_step(10).unwrap();
        table.set_deviation(350, 10.0).unwrap();
        table.set_deviation(0, -10.0).unwrap();

        let midpoint = table
            .deviation_at(355.0, InterpolationMethod::Linear, None)
            .unwrap();
        assert!((midpoint.degrees() - 0.0).abs() < 1e-12);

        let quarter = table
            .deviation_at(352.5, InterpolationMethod::Linear, None)
            .unwrap();
        assert!((quarter.degrees() - 5.0).abs() < 1e-12);
    }

    #[test]
    fn cubic_spline_is_smooth_across_north() {
        let table = readme_table();
        let before = table
            .deviation_at(359.9, InterpolationMethod::Cubic, None)
            .unwrap()
            .degrees();
        let after = table
            .deviation_at(0.1, InterpolationMethod::Cubic, None)
            .unwrap()
            .degrees();
        assert!(
            (before - after).abs() < 0.05,
            "spline jumps across north: {before} vs {after}"
        );
    }

    #[test]
    fn cubic_spline_reproduces_a_sinusoid() {
        let values: Vec<f64> = (0..36)
            .map(|index| 5.0 * math::sin(math::to_radians(f64::from(index) * 10.0)))
            .collect();
        let table = DeviationTable::from_deviation_vec(values).unwrap();

        for course in [5.0, 17.5, 123.4, 250.0, 355.0] {
            let expected = 5.0 * math::sin(math::to_radians(course));
            let actual = table
                .deviation_at(course, InterpolationMethod::Cubic, None)
                .unwrap()
                .degrees();
            assert!(
                (actual - expected).abs() < 1e-3,
                "at {course}: {actual} vs {expected}"
            );
        }
    }

    #[test]
    fn linear_never_overshoots_its_nodes() {
        let table = readme_table();
        let low = table
            .nodes()
            .iter()
            .fold(f64::MAX, |acc, node| acc.min(node.deviation_degrees()));
        let high = table
            .nodes()
            .iter()
            .fold(f64::MIN, |acc, node| acc.max(node.deviation_degrees()));

        let mut course = 0.0;
        while course < 360.0 {
            let value = table
                .deviation_at(course, InterpolationMethod::Linear, None)
                .unwrap()
                .degrees();
            assert!(value >= low - 1e-12 && value <= high + 1e-12);
            course += 0.25;
        }
    }

    #[test]
    fn parametric_fit_recovers_known_coefficients() {
        // The old implementation ignored the deviation values entirely and
        // returned the table mean for every course.
        let truth = SmithCoefficients {
            a: 1.0,
            b: -2.0,
            c: 3.0,
            d: 0.5,
            e: -1.5,
        };
        let values: Vec<f64> = (0..36)
            .map(|index| truth.deviation_at(f64::from(index) * 10.0))
            .collect();
        let table = DeviationTable::from_deviation_vec(values).unwrap();

        let fitted = table.smith_coefficients().unwrap();
        assert!((fitted.a - truth.a).abs() < 1e-9);
        assert!((fitted.b - truth.b).abs() < 1e-9);
        assert!((fitted.c - truth.c).abs() < 1e-9);
        assert!((fitted.d - truth.d).abs() < 1e-9);
        assert!((fitted.e - truth.e).abs() < 1e-9);

        let analysis = table.analyze().unwrap();
        assert!(analysis.rms_residual < 1e-9);
        assert_eq!(analysis.nodes, 36);
        assert_eq!(analysis.max_gap, 10.0);
    }

    #[test]
    fn parametric_depends_on_the_deviation_values() {
        let flat = DeviationTable::from_deviation_vec(vec![0.0; 36]).unwrap();
        let values: Vec<f64> = (0..36)
            .map(|index| 5.0 * math::sin(math::to_radians(f64::from(index) * 10.0)))
            .collect();
        let sinusoid = DeviationTable::from_deviation_vec(values).unwrap();

        let flat_value = flat
            .deviation_at(90.0, InterpolationMethod::Parametric, None)
            .unwrap()
            .degrees();
        let sinusoid_value = sinusoid
            .deviation_at(90.0, InterpolationMethod::Parametric, None)
            .unwrap()
            .degrees();

        assert!(flat_value.abs() < 1e-9);
        assert!(
            (sinusoid_value - 5.0).abs() < 1e-9,
            "expected 5.0 at 090°, got {sinusoid_value}"
        );
    }

    #[test]
    fn parametric_is_not_constant_across_the_compass() {
        let table = readme_table();
        let north = table
            .deviation_at(0.0, InterpolationMethod::Parametric, None)
            .unwrap()
            .degrees();
        let west = table
            .deviation_at(270.0, InterpolationMethod::Parametric, None)
            .unwrap()
            .degrees();
        assert!((north - west).abs() > 1.0, "{north} vs {west}");
    }

    #[test]
    fn parametric_honours_fixed_coefficients() {
        let table = readme_table();
        let requested = DeviationCoefficients {
            a: Some(0.0),
            b: Some(0.0),
            c: Some(0.0),
            d: Some(0.0),
            e: Some(0.0),
        };
        let value = table
            .deviation_at(123.0, InterpolationMethod::Parametric, Some(&requested))
            .unwrap();
        assert_eq!(value.degrees(), 0.0);

        let partial = DeviationCoefficients {
            a: Some(2.0),
            ..DeviationCoefficients::default()
        };
        let fitted = table.fit_parametric(&partial).unwrap();
        assert_eq!(fitted.a, 2.0);
        assert!(fitted.b.abs() > 0.0 || fitted.c.abs() > 0.0);
    }

    #[test]
    fn parametric_needs_enough_nodes() {
        let table = DeviationTable::from_vec(vec![(0, 1.0), (180, -1.0)]).unwrap();
        assert!(matches!(
            table.smith_coefficients().unwrap_err(),
            NavigationError::InsufficientNodes { required: 5, .. }
        ));
    }

    #[test]
    fn parametric_rejects_absurd_fixed_coefficients() {
        let table = readme_table();
        let requested = DeviationCoefficients {
            a: Some(1e6),
            ..DeviationCoefficients::default()
        };
        assert!(table
            .deviation_at(0.0, InterpolationMethod::Parametric, Some(&requested))
            .is_err());
    }

    #[test]
    fn two_node_table_falls_back_from_cubic_to_linear() {
        let table = DeviationTable::from_vec(vec![(0, 0.0), (180, 4.0)]).unwrap();
        let value = table
            .deviation_at(90.0, InterpolationMethod::Cubic, None)
            .unwrap();
        assert!((value.degrees() - 2.0).abs() < 1e-12);
    }

    #[test]
    fn uneven_node_spacing_still_interpolates() {
        let table = DeviationTable::from_vec(vec![
            (0, 1.0),
            (7, -2.0),
            (93, 0.5),
            (200, -3.0),
            (201, -3.1),
            (355, 2.0),
        ])
        .unwrap();

        for method in [
            InterpolationMethod::Linear,
            InterpolationMethod::Cubic,
            InterpolationMethod::Parametric,
            InterpolationMethod::ShapePreserving,
        ] {
            let mut course = 0.0;
            while course < 360.0 {
                let value = table.deviation_at(course, method, None).unwrap();
                assert!(value.degrees().is_finite(), "{method:?} at {course}");
                course += 0.5;
            }
        }
    }

    #[test]
    fn shape_preserving_is_exact_at_nodes() {
        let table = readme_table();
        for node in table.nodes() {
            let value = table
                .deviation_at(
                    f64::from(node.course()),
                    InterpolationMethod::ShapePreserving,
                    None,
                )
                .unwrap();
            assert!((value.degrees() - node.deviation_degrees()).abs() < 1e-12);
        }
    }

    #[test]
    fn shape_preserving_never_overshoots_where_the_spline_does() {
        // This swing has a 12.5° step in it, which is exactly the situation a
        // natural cubic spline handles by bulging past the data.
        let table = readme_table();
        let low = table
            .nodes()
            .iter()
            .fold(f64::MAX, |acc, node| acc.min(node.deviation_degrees()));
        let high = table
            .nodes()
            .iter()
            .fold(f64::MIN, |acc, node| acc.max(node.deviation_degrees()));

        let mut spline_overshot = false;
        let mut course = 0.0;
        while course < 360.0 {
            let shaped = table
                .deviation_at(course, InterpolationMethod::ShapePreserving, None)
                .unwrap()
                .degrees();
            assert!(
                shaped >= low - 1e-12 && shaped <= high + 1e-12,
                "shape-preserving bulged to {shaped} at {course}"
            );

            let spline = table
                .deviation_at(course, InterpolationMethod::Cubic, None)
                .unwrap()
                .degrees();
            if spline < low - 1e-9 || spline > high + 1e-9 {
                spline_overshot = true;
            }
            course += 0.25;
        }

        assert!(
            spline_overshot,
            "the cubic spline was expected to overshoot on this swing"
        );
    }

    #[test]
    fn shape_preserving_stays_between_neighbouring_nodes() {
        // The stronger property: within any one segment the curve stays between
        // that segment's own two values.
        let table = readme_table();
        let nodes = table.nodes();
        for pair in nodes.windows(2) {
            let (start, end) = (pair[0], pair[1]);
            let (low, high) = if start.deviation_degrees() <= end.deviation_degrees() {
                (start.deviation_degrees(), end.deviation_degrees())
            } else {
                (end.deviation_degrees(), start.deviation_degrees())
            };

            let mut course = f64::from(start.course());
            while course <= f64::from(end.course()) {
                let value = table
                    .deviation_at(course, InterpolationMethod::ShapePreserving, None)
                    .unwrap()
                    .degrees();
                assert!(
                    value >= low - 1e-12 && value <= high + 1e-12,
                    "between {}° and {}° the curve reached {value}, outside [{low}, {high}]",
                    start.course(),
                    end.course()
                );
                course += 0.1;
            }
        }
    }

    #[test]
    fn shape_preserving_is_smooth_across_north() {
        let table = readme_table();
        let before = table
            .deviation_at(359.9, InterpolationMethod::ShapePreserving, None)
            .unwrap()
            .degrees();
        let after = table
            .deviation_at(0.1, InterpolationMethod::ShapePreserving, None)
            .unwrap()
            .degrees();
        assert!((before - after).abs() < 0.05, "{before} vs {after}");
    }

    #[test]
    fn shape_preserving_reproduces_a_gentle_curve() {
        let values: Vec<f64> = (0..36)
            .map(|index| 5.0 * math::sin(math::to_radians(f64::from(index) * 10.0)))
            .collect();
        let table = DeviationTable::from_deviation_vec(values).unwrap();

        for course in [5.0, 17.5, 123.4, 250.0, 355.0] {
            let expected = 5.0 * math::sin(math::to_radians(course));
            let actual = table
                .deviation_at(course, InterpolationMethod::ShapePreserving, None)
                .unwrap()
                .degrees();
            assert!(
                (actual - expected).abs() < 0.02,
                "at {course}: {actual} vs {expected}"
            );
        }
    }

    #[test]
    fn interpolate_batch_matches_single_lookups() {
        let table = readme_table();
        let courses = [0.0, 3.0, 45.5, 180.0, 259.9, 360.0];
        for method in [
            InterpolationMethod::Linear,
            InterpolationMethod::Cubic,
            InterpolationMethod::Parametric,
            InterpolationMethod::ShapePreserving,
        ] {
            let batch = table.interpolate_deviation(&courses, method, None).unwrap();
            for (index, &course) in courses.iter().enumerate() {
                let single = table.deviation_at(course, method, None).unwrap().degrees();
                assert!((batch[index] - single).abs() < 1e-12);
            }
        }
    }
}
