//! Course and bearing conversions, and the current triangle.
//!
//! # The sign convention
//!
//! Corrections are applied in one direction and removed in the other:
//!
//! ```text
//! magnetic course = compass course  + deviation(compass course)
//! true course     = magnetic course + variation
//! ```
//!
//! Deviation is a function of the **compass** course, which is what makes the
//! inverse problem interesting: going from a true course back to a compass course
//! means solving `CC + δ(CC) = MC` for `CC`, an implicit equation.
//! [`convert_true_course_to_compass_course`] solves it properly, so the two
//! directions really are inverses of each other. The pre-1.0 implementation read
//! the deviation at the *magnetic* course instead, which on a realistic swing put
//! the answer out by up to 10°.
//!
//! # Which functions can fail
//!
//! The conversions that only add or subtract a known correction take typed,
//! pre-validated arguments and therefore cannot fail at all — they return a value,
//! not a `Result`. Only the operations that read a deviation table, or solve an
//! implicit equation, return `Result`.

use crate::angle::{
    ensure_finite, ensure_range, wrap180, wrap360, Compass, Deviation, Direction, Frame, Gyro,
    GyroCourse, Magnetic, MagneticCourse, RelativeBearing, True, TrueCourse, Variation,
};
use crate::deviation::{DeviationTable, Interpolation, Interpolator};
use crate::error::{NavigationError, Result};
use crate::math;
use crate::position::Latitude;
use crate::units::{Angle, Speed};

/// A variation beyond this magnitude sets [`Advisories::large_variation`].
///
/// Chart variation is rarely this large outside high latitudes, so a bigger value
/// usually means a stale chart, a wrong sign, or a value that is really a deviation.
pub const LARGE_VARIATION_DEG: f64 = 15.0;

/// A deviation beyond this magnitude sets [`Advisories::large_deviation`].
///
/// A compass this far out should be adjusted rather than merely tabulated.
pub const LARGE_DEVIATION_DEG: f64 = 10.0;

/// A largest-gap beyond this many degrees sets [`Advisories::coarse_table`].
///
/// Interpolating a deviation curve across gaps wider than a cardinal quadrant is
/// guesswork whatever the method.
pub const COARSE_TABLE_GAP_DEG: f64 = 45.0;

/// Iterations allowed to the compass-course solver before it gives up.
const MAX_ITERATIONS: u32 = 64;

/// Convergence tolerance of the compass-course solver, in degrees.
const TOLERANCE_DEG: f64 = 1e-9;

/// Eastward speed of the Earth's surface at the equator, in knots.
///
/// Fifteen degrees of longitude an hour, sixty miles to the degree.
const EARTH_SURFACE_SPEED_KNOTS: f64 = 900.0;

/// Beyond this latitude [`gyro_speed_error`] refuses to answer.
///
/// The horizontal component of the Earth's rotation, which is what makes a
/// gyrocompass point north at all, vanishes at the pole. Well before that the
/// settling is too sluggish and the speed error too large for the correction to
/// mean anything, and ships in those latitudes steer by other means.
pub const MAX_GYRO_LATITUDE_DEG: f64 = 85.0;

/// Conditions worth a second look before acting on a result.
///
/// None of these is an error: the computation is exact for the data it was given.
/// They flag data that is unusual enough to be worth checking.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
// A set of independent flags is exactly what this is meant to be.
#[allow(clippy::struct_excessive_bools)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Advisories {
    /// Variation magnitude exceeds [`LARGE_VARIATION_DEG`].
    pub large_variation: bool,
    /// Interpolated deviation magnitude exceeds [`LARGE_DEVIATION_DEG`].
    pub large_deviation: bool,
    /// The table's widest gap exceeds [`COARSE_TABLE_GAP_DEG`].
    ///
    /// An eight-point swing at 45° spacing does not set this: that is the
    /// coarsest spacing in normal use, not an unusual one.
    pub coarse_table: bool,
    /// The table cannot be inverted uniquely; see [`crate::DeviationTable::is_invertible`].
    ///
    /// A true course converted back to a compass course is still a correct
    /// answer — it does produce the requested true course — but it is not
    /// necessarily the compass course you started from, because more than one
    /// heading produces the same result.
    pub non_invertible_table: bool,
}

impl Advisories {
    /// Whether any advisory is set.
    #[must_use]
    pub const fn any(self) -> bool {
        self.large_variation
            || self.large_deviation
            || self.coarse_table
            || self.non_invertible_table
    }
}

/// A converted course, with everything that went into it.
#[derive(Debug, Clone, Copy, PartialEq)]
#[cfg_attr(
    feature = "serde",
    derive(serde::Serialize, serde::Deserialize),
    serde(bound = "")
)]
pub struct CourseSolution<F: Frame> {
    /// The converted course.
    pub course: Direction<F>,
    /// Deviation used, interpolated at the compass course.
    pub deviation: Deviation,
    /// Variation used. Zero for conversions that do not involve true north.
    pub variation: Variation,
    /// Total correction applied, `variation + deviation`, in degrees.
    pub total_correction: f64,
    /// Rough uncertainty of the interpolated deviation, in degrees.
    ///
    /// For [`crate::InterpolationMethod::Linear`] and
    /// [`crate::InterpolationMethod::Cubic`] this is the classical interpolation
    /// error bound estimated from the local second difference of the table; for
    /// [`crate::InterpolationMethod::Parametric`] it is the RMS residual of the
    /// fit. It describes the interpolation only — it says nothing about how well
    /// the swing itself was observed.
    pub estimated_error: f64,
    /// Conditions worth checking before acting on the result.
    pub advisories: Advisories,
}

impl<F: Frame> CourseSolution<F> {
    /// Whether any advisory is set.
    ///
    /// Replaces the old `check_data_required` field, which only ever looked at the
    /// variation.
    #[must_use]
    pub const fn check_data_required(&self) -> bool {
        self.advisories.any()
    }
}

/// Course and speed made good over the ground.
#[derive(Debug, Clone, Copy, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct GroundTrack {
    /// Direction actually made good over the ground.
    pub course_over_ground: TrueCourse,
    /// Speed actually made good.
    pub speed_over_ground: Speed,
}

/// How to steer to make good a required track.
#[derive(Debug, Clone, Copy, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct SteeringSolution {
    /// Heading to steer through the water.
    pub heading: TrueCourse,
    /// Speed that will be made good along the track.
    pub speed_over_ground: Speed,
    /// Angle between the heading and the track; positive to starboard.
    pub drift_angle: Angle,
}

/// A current, as a set and a drift.
#[derive(Debug, Clone, Copy, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Current {
    /// Direction the current flows towards.
    ///
    /// Meaningless when `drift` is zero, in which case it is reported as `000°`.
    pub set: TrueCourse,
    /// Speed of the current.
    pub drift: Speed,
}

// ---------------------------------------------------------------------------
// Corrections that cannot fail
// ---------------------------------------------------------------------------

/// Applies variation: magnetic to true.
///
/// Works for courses and bearings alike — within one frame they are the same
/// quantity.
#[must_use]
pub fn magnetic_to_true(direction: MagneticCourse, variation: Variation) -> TrueCourse {
    Direction::<True>::from_degrees_wrapped(direction.degrees() + variation.degrees())
}

/// Removes variation: true to magnetic.
#[must_use]
pub fn true_to_magnetic(direction: TrueCourse, variation: Variation) -> MagneticCourse {
    Direction::<Magnetic>::from_degrees_wrapped(direction.degrees() - variation.degrees())
}

/// Applies deviation: compass to magnetic.
#[must_use]
pub fn compass_to_magnetic(
    direction: Direction<Compass>,
    deviation: Deviation,
) -> Direction<Magnetic> {
    Direction::<Magnetic>::from_degrees_wrapped(direction.degrees() + deviation.degrees())
}

/// Removes a known deviation: magnetic to compass.
///
/// Note that this takes the deviation as a given. To have it looked up in a table
/// — which requires solving for the compass course — use
/// [`convert_magnetic_course_to_compass_course`].
#[must_use]
pub fn magnetic_to_compass(
    direction: Direction<Magnetic>,
    deviation: Deviation,
) -> Direction<Compass> {
    Direction::<Compass>::from_degrees_wrapped(direction.degrees() - deviation.degrees())
}

/// Applies gyro error: gyro to true.
///
/// The error is east-positive, so that `true = gyro + error`, the same
/// convention [`Variation`] and [`Deviation`] use.
#[must_use]
pub fn gyro_to_true(direction: GyroCourse, error: Angle) -> TrueCourse {
    Direction::<True>::from_degrees_wrapped(direction.degrees() + error.degrees())
}

/// Removes gyro error: true to gyro.
#[must_use]
pub fn true_to_gyro(direction: TrueCourse, error: Angle) -> GyroCourse {
    Direction::<Gyro>::from_degrees_wrapped(direction.degrees() - error.degrees())
}

/// The gyro error implied by a bearing of something whose true direction is known.
///
/// The usual way to check a gyro: take it on a transit, a distant object, or the
/// azimuth of a heavenly body.
#[must_use]
pub fn gyro_error_from_transit(observed: Direction<Gyro>, reference: Direction<True>) -> Angle {
    Angle::from_degrees_unchecked(wrap180(reference.degrees() - observed.degrees()))
}

/// The speed error of a gyrocompass: the part of its error that the ship's own
/// motion causes.
///
/// A gyrocompass settles along the resultant of the Earth's eastward surface
/// velocity and the ship's own velocity, so a northerly course tilts its meridian
/// west and a southerly course tilts it east, in either hemisphere. The result is
/// east-positive, ready to be handed to [`gyro_to_true`].
///
/// This is only the speed error. Any residual instrument error has to be observed
/// and added; [`gyro_error_from_transit`] is how you get it.
///
/// # Errors
///
/// - [`NavigationError::NotFinite`] or [`NavigationError::OutOfRange`] for a
///   negative or non-finite speed.
/// - [`NavigationError::OutOfRange`] beyond [`MAX_GYRO_LATITUDE_DEG`], where a
///   gyrocompass does not settle usefully.
/// - [`NavigationError::Indeterminate`] if the ship outruns the Earth's own
///   surface speed westward, leaving no settling meridian at all.
///
/// # Example
///
/// ```rust
/// use bearingpro::navigation_solutions::gyro_speed_error;
/// use bearingpro::{Latitude, NavigationError, Speed, TrueCourse};
///
/// fn main() -> Result<(), NavigationError> {
///     // 20 knots due north in latitude 60°: a westerly error of about 2.5°.
///     let error = gyro_speed_error(
///         Latitude::from_degrees(60.0)?,
///         TrueCourse::new(0.0)?,
///         Speed::from_knots(20.0)?,
///     )?;
///     assert_eq!(format!("{:.2}", error.degrees()), "-2.54");
///
///     // Due south the error is easterly instead.
///     let southerly = gyro_speed_error(
///         Latitude::from_degrees(60.0)?,
///         TrueCourse::new(180.0)?,
///         Speed::from_knots(20.0)?,
///     )?;
///     assert!(southerly.degrees() > 0.0);
///     Ok(())
/// }
/// ```
pub fn gyro_speed_error(latitude: Latitude, course: TrueCourse, speed: Speed) -> Result<Angle> {
    ensure_speed("speed", speed)?;
    ensure_range(
        "latitude",
        latitude.degrees(),
        -MAX_GYRO_LATITUDE_DEG,
        MAX_GYRO_LATITUDE_DEG,
    )?;

    let knots = speed.knots();
    let course_radians = course.radians();
    // 900 knots is the Earth's eastward surface speed at the equator: 15° an
    // hour, 60 miles to the degree.
    let eastward = EARTH_SURFACE_SPEED_KNOTS * math::cos(latitude.radians())
        + knots * math::sin(course_radians);

    if eastward <= f64::EPSILON {
        return Err(NavigationError::Indeterminate {
            quantity: "the settling meridian of a gyrocompass at this latitude",
        });
    }

    let displacement = math::atan2(knots * math::cos(course_radians), eastward);
    Ok(Angle::from_degrees_unchecked(-math::to_degrees(
        displacement,
    )))
}

/// The angle from the ship's head clockwise to a bearing.
///
/// Both arguments must be in the same frame, which the type system enforces.
///
/// # Example
///
/// ```rust
/// use bearingpro::{navigation_solutions::calculate_course_angle, TrueCourse};
///
/// let course = TrueCourse::new(90.0)?;
/// let bearing = TrueCourse::new(180.0)?;
/// assert_eq!(calculate_course_angle(course, bearing).degrees(), 90.0);
/// # Ok::<(), bearingpro::NavigationError>(())
/// ```
#[must_use]
pub fn calculate_course_angle<F: Frame>(
    course: Direction<F>,
    bearing: Direction<F>,
) -> RelativeBearing {
    RelativeBearing::from_degrees_wrapped(bearing.degrees() - course.degrees())
}

/// Turns a relative bearing back into a bearing in the course's own frame.
#[must_use]
pub fn bearing_from_relative<F: Frame>(
    course: Direction<F>,
    relative: RelativeBearing,
) -> Direction<F> {
    Direction::<F>::from_degrees_wrapped(course.degrees() + relative.degrees())
}

// ---------------------------------------------------------------------------
// Conversions that read a deviation table
// ---------------------------------------------------------------------------

/// Compass course to true course, applying tabulated deviation and variation.
///
/// # Errors
///
/// Propagates any failure from the deviation table: a parametric fit that the
/// table cannot support, or an interpolated deviation that is not a usable angle.
///
/// # Example
///
/// ```rust
/// use bearingpro::{
///     navigation_solutions::convert_compass_course_to_true_course, CompassCourse,
///     DeviationTable, InterpolationMethod, Variation,
/// };
///
/// let mut table = DeviationTable::default();
/// table.set_deviation(0, -2.5)?;
/// table.set_deviation(10, -1.5)?;
///
/// let solution = convert_compass_course_to_true_course(
///     CompassCourse::new(5.0)?,
///     Variation::new(-10.0)?,
///     &table,
///     InterpolationMethod::Linear,
/// )?;
///
/// assert_eq!(format!("{:.2}", solution.course.degrees()), "353.00");
/// assert_eq!(format!("{:.2}", solution.deviation.degrees()), "-2.00");
/// # Ok::<(), bearingpro::NavigationError>(())
/// ```
pub fn convert_compass_course_to_true_course<'a>(
    compass_course: Direction<Compass>,
    variation: Variation,
    deviation_table: &DeviationTable,
    interpolation: impl Into<Interpolation<'a>>,
) -> Result<CourseSolution<True>> {
    let interpolation = interpolation.into();
    let interpolator = deviation_table.prepare(interpolation.method, interpolation.coefficients)?;
    let compass_degrees = compass_course.degrees();
    let deviation = deviation_at(deviation_table, &interpolator, compass_degrees)?;

    let course = Direction::<True>::from_degrees_wrapped(
        compass_degrees + deviation.degrees() + variation.degrees(),
    );

    Ok(build_solution(
        course,
        deviation,
        variation,
        deviation_table,
        &interpolator,
        compass_degrees,
    ))
}

/// True course to compass course, solving for the compass course the deviation
/// table is indexed by.
///
/// # Errors
///
/// - Any failure from the deviation table.
/// - [`NavigationError::NotConverged`] if the deviation curve is not invertible
///   near this heading, which means the table describes a compass that cannot be
///   steered by and should be re-swung.
///
/// # Example
///
/// ```rust
/// use bearingpro::{
///     navigation_solutions::{
///         convert_compass_course_to_true_course, convert_true_course_to_compass_course,
///     },
///     CompassCourse, DeviationTable, InterpolationMethod, Variation,
/// };
///
/// let table = DeviationTable::from_deviation_vec(vec![
///     -2.5, -0.5, 1.6, 4.4, -1.7, 0.0, 1.0, 0.3, -0.9, 0.5, -1.2, 0.8, -0.3, 1.7, -2.1, 0.4,
///     -0.6, 1.2, -1.3, 0.0, 0.9, -1.1, 1.5, -0.7, -13.2, -15.7, -17.9, -19.2, -18.1, 1.8,
///     -0.4, 0.7, -0.2, 1.4, -4.4, -2.9,
/// ])?;
/// let variation = Variation::new(-2.7)?;
///
/// // Out and back, over the steepest part of the curve.
/// let compass = CompassCourse::new(250.0)?;
/// let out = convert_compass_course_to_true_course(
///     compass, variation, &table, InterpolationMethod::Linear,
/// )?;
/// let back = convert_true_course_to_compass_course(
///     out.course, variation, &table, InterpolationMethod::Linear,
/// )?;
///
/// // The pre-1.0 implementation came back 9.63° adrift here.
/// assert!((back.course.degrees() - compass.degrees()).abs() < 1e-9);
/// # Ok::<(), bearingpro::NavigationError>(())
/// ```
pub fn convert_true_course_to_compass_course<'a>(
    true_course: Direction<True>,
    variation: Variation,
    deviation_table: &DeviationTable,
    interpolation: impl Into<Interpolation<'a>>,
) -> Result<CourseSolution<Compass>> {
    let interpolation = interpolation.into();
    let interpolator = deviation_table.prepare(interpolation.method, interpolation.coefficients)?;
    let magnetic_degrees = wrap360(true_course.degrees() - variation.degrees());

    let compass_degrees = solve_compass_course(deviation_table, &interpolator, magnetic_degrees)?;
    let deviation = deviation_at(deviation_table, &interpolator, compass_degrees)?;

    Ok(build_solution(
        Direction::<Compass>::from_degrees_wrapped(compass_degrees),
        deviation,
        variation,
        deviation_table,
        &interpolator,
        compass_degrees,
    ))
}

/// Compass course to magnetic course, applying tabulated deviation.
///
/// # Errors
///
/// As [`convert_compass_course_to_true_course`].
pub fn convert_compass_course_to_magnetic_course<'a>(
    compass_course: Direction<Compass>,
    deviation_table: &DeviationTable,
    interpolation: impl Into<Interpolation<'a>>,
) -> Result<CourseSolution<Magnetic>> {
    let solution = convert_compass_course_to_true_course(
        compass_course,
        Variation::ZERO,
        deviation_table,
        interpolation,
    )?;
    Ok(CourseSolution {
        course: solution.course.relabel::<Magnetic>(),
        deviation: solution.deviation,
        variation: Variation::ZERO,
        total_correction: solution.deviation.degrees(),
        estimated_error: solution.estimated_error,
        advisories: solution.advisories,
    })
}

/// Magnetic course to compass course, solving for the tabulated deviation.
///
/// # Errors
///
/// As [`convert_true_course_to_compass_course`].
pub fn convert_magnetic_course_to_compass_course<'a>(
    magnetic_course: Direction<Magnetic>,
    deviation_table: &DeviationTable,
    interpolation: impl Into<Interpolation<'a>>,
) -> Result<CourseSolution<Compass>> {
    convert_true_course_to_compass_course(
        magnetic_course.relabel::<True>(),
        Variation::ZERO,
        deviation_table,
        interpolation,
    )
}

// ---------------------------------------------------------------------------
// The current triangle
// ---------------------------------------------------------------------------

/// Course and speed over the ground, from a heading, a speed through the water,
/// and a current.
///
/// Speeds may be in any unit as long as they are all the same one.
///
/// # Errors
///
/// - [`NavigationError::NotFinite`] or [`NavigationError::OutOfRange`] for a
///   negative or non-finite speed.
/// - [`NavigationError::Indeterminate`] if the vessel's motion through the water
///   exactly cancels the current, leaving no direction to report.
///
/// # Example
///
/// ```rust
/// use bearingpro::{navigation_solutions::course_over_ground, Speed, TrueCourse};
///
/// // Steering due north at 10 knots, with 2 knots setting due east.
/// let track = course_over_ground(
///     TrueCourse::new(0.0)?,
///     Speed::from_knots(10.0)?,
///     TrueCourse::new(90.0)?,
///     Speed::from_knots(2.0)?,
/// )?;
///
/// assert_eq!(format!("{:.2}", track.course_over_ground.degrees()), "11.31");
/// assert_eq!(format!("{:.2}", track.speed_over_ground.knots()), "10.20");
/// # Ok::<(), bearingpro::NavigationError>(())
/// ```
pub fn course_over_ground(
    heading: TrueCourse,
    speed_through_water: Speed,
    set: TrueCourse,
    drift: Speed,
) -> Result<GroundTrack> {
    ensure_speed("speed through water", speed_through_water)?;
    ensure_speed("drift", drift)?;

    let (water_north, water_east) = components(heading, speed_through_water.knots());
    let (current_north, current_east) = components(set, drift.knots());

    let north = water_north + current_north;
    let east = water_east + current_east;
    let speed_over_ground = math::hypot(north, east);

    // Compare against the size of the inputs: two 5-knot vectors that cancel
    // leave a residue far above `f64::EPSILON` but still mean "not moving".
    if speed_over_ground <= cancellation_threshold(speed_through_water.knots(), drift.knots()) {
        return Err(NavigationError::Indeterminate {
            quantity: "course over ground",
        });
    }

    Ok(GroundTrack {
        course_over_ground: Direction::<True>::from_degrees_wrapped(math::to_degrees(math::atan2(
            east, north,
        ))),
        speed_over_ground: Speed::from_knots_unchecked(speed_over_ground),
    })
}

/// The heading to steer to make good a required track against a known current.
///
/// # Errors
///
/// - [`NavigationError::NotFinite`] or [`NavigationError::OutOfRange`] for a
///   negative or non-finite speed.
/// - [`NavigationError::CurrentTooStrong`] if no heading makes the track good —
///   the current can push the vessel off the track faster than it can steer back,
///   or can only carry it backwards along the track.
///
/// # Example
///
/// ```rust
/// use bearingpro::{navigation_solutions::course_to_steer, Speed, TrueCourse};
///
/// // To make good due north at 10 knots through the water, against 2 knots east.
/// let steering = course_to_steer(
///     TrueCourse::new(0.0)?,
///     Speed::from_knots(10.0)?,
///     TrueCourse::new(90.0)?,
///     Speed::from_knots(2.0)?,
/// )?;
///
/// assert_eq!(format!("{:.2}", steering.heading.degrees()), "348.46");
/// assert_eq!(format!("{:.2}", steering.speed_over_ground.knots()), "9.80");
/// # Ok::<(), bearingpro::NavigationError>(())
/// ```
pub fn course_to_steer(
    track: TrueCourse,
    speed_through_water: Speed,
    set: TrueCourse,
    drift: Speed,
) -> Result<SteeringSolution> {
    ensure_speed("speed through water", speed_through_water)?;
    ensure_speed("drift", drift)?;

    let through_water = speed_through_water.knots();
    let current = drift.knots();
    let too_strong = || NavigationError::CurrentTooStrong {
        drift: current,
        speed_through_water: through_water,
    };

    if through_water < f64::EPSILON {
        return Err(too_strong());
    }

    // Across-track components must cancel: V·sin(H − T) + D·sin(S − T) = 0.
    let current_offset = math::to_radians(track.signed_difference(set));
    let sine = -current * math::sin(current_offset) / through_water;

    if math::abs(sine) > 1.0 {
        return Err(too_strong());
    }

    let drift_angle = math::asin(sine);
    let speed_over_ground =
        through_water * math::cos(drift_angle) + current * math::cos(current_offset);

    if speed_over_ground <= 0.0 {
        return Err(too_strong());
    }

    Ok(SteeringSolution {
        heading: Direction::<True>::from_degrees_wrapped(
            track.degrees() + math::to_degrees(drift_angle),
        ),
        speed_over_ground: Speed::from_knots_unchecked(speed_over_ground),
        drift_angle: Angle::from_degrees_unchecked(math::to_degrees(drift_angle)),
    })
}

/// The current implied by the difference between water track and ground track.
///
/// # Errors
///
/// [`NavigationError::NotFinite`] or [`NavigationError::OutOfRange`] for a
/// negative or non-finite speed.
pub fn estimate_current(
    heading: TrueCourse,
    speed_through_water: Speed,
    course_over_ground: TrueCourse,
    speed_over_ground: Speed,
) -> Result<Current> {
    ensure_speed("speed through water", speed_through_water)?;
    ensure_speed("speed over ground", speed_over_ground)?;

    let (water_north, water_east) = components(heading, speed_through_water.knots());
    let (ground_north, ground_east) = components(course_over_ground, speed_over_ground.knots());

    let north = ground_north - water_north;
    let east = ground_east - water_east;
    let drift = math::hypot(north, east);

    let set = if drift
        <= cancellation_threshold(speed_through_water.knots(), speed_over_ground.knots())
    {
        Direction::<True>::NORTH
    } else {
        Direction::<True>::from_degrees_wrapped(math::to_degrees(math::atan2(east, north)))
    };

    Ok(Current {
        set,
        drift: Speed::from_knots_unchecked(drift),
    })
}

// ---------------------------------------------------------------------------
// Internals
// ---------------------------------------------------------------------------

fn components<F: Frame>(direction: Direction<F>, magnitude: f64) -> (f64, f64) {
    let radians = direction.radians();
    (
        magnitude * math::cos(radians),
        magnitude * math::sin(radians),
    )
}

/// Below what magnitude a sum of two vectors counts as having cancelled out.
///
/// Scaled to the inputs, because floating point cancellation leaves a residue
/// proportional to the operands rather than to `f64::EPSILON`.
fn cancellation_threshold(first: f64, second: f64) -> f64 {
    first.max(second) * 1e-12
}

/// Speeds in the current triangle must be finite and not sternway.
fn ensure_speed(parameter: &'static str, value: Speed) -> Result<()> {
    ensure_finite(parameter, value.knots())?;
    ensure_range(parameter, value.knots(), 0.0, f64::MAX)
}

fn deviation_at(
    table: &DeviationTable,
    interpolator: &Interpolator,
    compass_degrees: f64,
) -> Result<Deviation> {
    Deviation::new(table.evaluate(interpolator, compass_degrees))
}

fn build_solution<F: Frame>(
    course: Direction<F>,
    deviation: Deviation,
    variation: Variation,
    table: &DeviationTable,
    interpolator: &Interpolator,
    compass_degrees: f64,
) -> CourseSolution<F> {
    CourseSolution {
        course,
        deviation,
        variation,
        total_correction: variation.degrees() + deviation.degrees(),
        estimated_error: table.uncertainty(interpolator, compass_degrees),
        advisories: Advisories {
            large_variation: math::abs(variation.degrees()) > LARGE_VARIATION_DEG,
            large_deviation: math::abs(deviation.degrees()) > LARGE_DEVIATION_DEG,
            coarse_table: table.max_gap() > COARSE_TABLE_GAP_DEG,
            non_invertible_table: !table.is_invertible(),
        },
    }
}

/// Solves `compass + δ(compass) = magnetic` for the compass course.
///
/// Deviation is tabulated against the compass course, so this equation is
/// implicit and has to be solved rather than evaluated. A damped fixed-point
/// iteration handles every realistic swing in a handful of steps; the bracketing
/// fallback catches curves steep enough to make the plain iteration oscillate.
fn solve_compass_course(
    table: &DeviationTable,
    interpolator: &Interpolator,
    magnetic_degrees: f64,
) -> Result<f64> {
    let residual =
        |compass: f64| wrap180(compass + table.evaluate(interpolator, compass) - magnetic_degrees);

    let mut compass = magnetic_degrees;
    let mut damping = 1.0_f64;
    let mut previous_step = f64::MAX;

    for _ in 0..MAX_ITERATIONS {
        let step = -residual(compass);
        let magnitude = math::abs(step);

        if magnitude < TOLERANCE_DEG {
            return Ok(wrap360(compass));
        }
        // Oscillating rather than converging: take smaller bites.
        if magnitude >= previous_step {
            damping *= 0.5;
            if damping < 0.05 {
                break;
            }
        }
        previous_step = magnitude;
        compass = wrap360(compass + damping * step);
    }

    if let Some(bracketed) = bracket_and_bisect(&residual) {
        return Ok(bracketed);
    }

    Err(NavigationError::NotConverged {
        iterations: MAX_ITERATIONS,
        residual: math::abs(residual(compass)),
    })
}

/// Scans the whole circle for a sign change in the residual, then bisects it.
fn bracket_and_bisect(residual: &impl Fn(f64) -> f64) -> Option<f64> {
    /// Samples per degree; fine enough to bracket any physically sane curve.
    const SAMPLES: usize = 1440;
    /// Ignore sign changes that come from the ±180° wrap rather than from a root.
    const WRAP_GUARD_DEG: f64 = 90.0;
    const BISECTIONS: u32 = 80;

    let step = 360.0 / math::count_to_f64(SAMPLES);
    let mut low = 0.0;
    let mut low_value = residual(low);

    for index in 1..=SAMPLES {
        let high = step * math::count_to_f64(index) % 360.0;
        let high_value = residual(high);

        let brackets_root =
            (low_value <= 0.0 && high_value >= 0.0) || (low_value >= 0.0 && high_value <= 0.0);
        let near_a_root = math::abs(low_value) + math::abs(high_value) < WRAP_GUARD_DEG;

        if brackets_root && near_a_root {
            let (mut left, mut right) = (low, if high < low { high + 360.0 } else { high });
            let mut left_value = low_value;

            for _ in 0..BISECTIONS {
                let middle = (left + right) / 2.0;
                let middle_value = residual(wrap360(middle));
                if math::abs(middle_value) < TOLERANCE_DEG {
                    return Some(wrap360(middle));
                }
                if (left_value <= 0.0) == (middle_value <= 0.0) {
                    left = middle;
                    left_value = middle_value;
                } else {
                    right = middle;
                }
            }
            return Some(wrap360((left + right) / 2.0));
        }

        low = high;
        low_value = high_value;
    }

    None
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::float_cmp, clippy::indexing_slicing)]
mod tests {
    use super::*;
    use crate::deviation::{DeviationCoefficients, InterpolationMethod};
    use crate::CompassCourse;
    use alloc::format;
    use alloc::vec;
    use alloc::vec::Vec;

    fn readme_table() -> DeviationTable {
        DeviationTable::from_deviation_vec(vec![
            -2.5, -0.5, 1.6, 4.4, -1.7, 0.0, 1.0, 0.3, -0.9, 0.5, -1.2, 0.8, -0.3, 1.7, -2.1, 0.4,
            -0.6, 1.2, -1.3, 0.0, 0.9, -1.1, 1.5, -0.7, -13.2, -15.7, -17.9, -19.2, -18.1, 1.8,
            -0.4, 0.7, -0.2, 1.4, -4.4, -2.9,
        ])
        .unwrap()
    }

    /// A smooth swing whose deviation changes by well under a degree per degree
    /// of heading, so it can be inverted uniquely.
    fn realistic_table() -> DeviationTable {
        let truth = crate::SmithCoefficients {
            a: 2.0,
            b: 3.0,
            c: -4.0,
            d: 1.5,
            e: -0.5,
        };
        let values: Vec<f64> = (0..36)
            .map(|index| truth.deviation_at(f64::from(index) * 10.0))
            .collect();
        DeviationTable::from_deviation_vec(values).unwrap()
    }

    #[test]
    fn corrections_are_inverses_of_each_other() {
        let variation = Variation::new(-7.5).unwrap();
        let deviation = Deviation::new(3.25).unwrap();

        for degrees in [0.0, 1.0, 90.0, 183.7, 359.5] {
            let magnetic = MagneticCourse::new(degrees).unwrap();
            let back = true_to_magnetic(magnetic_to_true(magnetic, variation), variation);
            assert!(back.angular_distance(magnetic) < 1e-12);

            let compass = CompassCourse::new(degrees).unwrap();
            let round = magnetic_to_compass(compass_to_magnetic(compass, deviation), deviation);
            assert!(round.angular_distance(compass) < 1e-12);
        }
    }

    #[test]
    fn corrections_wrap_instead_of_going_negative() {
        // `calculate_compass_bearing(10.0, 1000.0)` used to return -270.0.
        let deviation = Deviation::new(170.0).unwrap();
        let compass = magnetic_to_compass(MagneticCourse::new(10.0).unwrap(), deviation);
        assert!((compass.degrees() - 200.0).abs() < 1e-12);
        assert!((0.0..360.0).contains(&compass.degrees()));
    }

    #[test]
    fn course_angle_is_measured_from_the_head() {
        let course = TrueCourse::new(90.0).unwrap();
        assert_eq!(
            calculate_course_angle(course, TrueCourse::new(180.0).unwrap()).degrees(),
            90.0
        );
        assert_eq!(
            calculate_course_angle(course, TrueCourse::new(45.0).unwrap()).degrees(),
            315.0
        );
        let relative = calculate_course_angle(course, TrueCourse::new(45.0).unwrap());
        assert!(
            bearing_from_relative(course, relative)
                .angular_distance(TrueCourse::new(45.0).unwrap())
                < 1e-12
        );
    }

    #[test]
    fn compass_to_true_matches_the_hand_calculation() {
        let mut table = DeviationTable::default();
        table.set_deviation(0, -2.5).unwrap();
        table.set_deviation(10, -1.5).unwrap();

        let solution = convert_compass_course_to_true_course(
            CompassCourse::new(5.0).unwrap(),
            Variation::new(-10.0).unwrap(),
            &table,
            InterpolationMethod::Linear,
        )
        .unwrap();

        assert_eq!(format!("{:.2}", solution.course.degrees()), "353.00");
        assert_eq!(format!("{:.2}", solution.deviation.degrees()), "-2.00");
        assert_eq!(format!("{:.2}", solution.total_correction), "-12.00");
        assert!(!solution.check_data_required());
    }

    #[test]
    fn round_trip_is_exact_for_every_method() {
        let table = realistic_table();
        assert!(table.is_invertible());
        let variation = Variation::new(-2.7).unwrap();

        for method in [
            InterpolationMethod::Linear,
            InterpolationMethod::Cubic,
            InterpolationMethod::Parametric,
        ] {
            let mut course = 0.0;
            while course < 360.0 {
                let compass = CompassCourse::new(course).unwrap();
                let out = convert_compass_course_to_true_course(compass, variation, &table, method)
                    .unwrap();
                let back =
                    convert_true_course_to_compass_course(out.course, variation, &table, method)
                        .unwrap();

                assert!(
                    back.course.angular_distance(compass) < 1e-6,
                    "{method:?} at {course}: came back {}",
                    back.course.degrees()
                );
                course += 0.5;
            }
        }
    }

    #[test]
    fn a_non_invertible_table_still_yields_a_course_that_checks_out() {
        // This swing changes by 12.5° of deviation over one 10° step, so two
        // compass courses share a magnetic course and the identity round trip
        // cannot hold for anyone. What must still hold is that the compass course
        // handed back really does produce the true course that was asked for.
        let table = readme_table();
        assert!(!table.is_invertible());
        let variation = Variation::new(-2.7).unwrap();

        for method in [
            InterpolationMethod::Linear,
            InterpolationMethod::Cubic,
            InterpolationMethod::Parametric,
        ] {
            let mut course = 0.0;
            while course < 360.0 {
                let requested = TrueCourse::new(course).unwrap();
                let compass =
                    convert_true_course_to_compass_course(requested, variation, &table, method)
                        .unwrap();
                let achieved = convert_compass_course_to_true_course(
                    compass.course,
                    variation,
                    &table,
                    method,
                )
                .unwrap();

                assert!(
                    achieved.course.angular_distance(requested) < 1e-6,
                    "{method:?} at {course}: steering {} makes good {}",
                    compass.course.degrees(),
                    achieved.course.degrees()
                );
                assert!(compass.advisories.non_invertible_table);
                course += 0.5;
            }
        }
    }

    #[test]
    fn round_trip_survives_the_steep_part_of_the_curve() {
        // The pre-1.0 implementation was 9.63° out at 250° compass.
        let table = readme_table();
        let variation = Variation::new(-2.7).unwrap();
        let compass = CompassCourse::new(250.0).unwrap();

        let out = convert_compass_course_to_true_course(
            compass,
            variation,
            &table,
            InterpolationMethod::Linear,
        )
        .unwrap();
        let back = convert_true_course_to_compass_course(
            out.course,
            variation,
            &table,
            InterpolationMethod::Linear,
        )
        .unwrap();

        assert!(back.course.angular_distance(compass) < 1e-9);
        assert!(out.advisories.large_deviation);
    }

    #[test]
    fn magnetic_round_trip_uses_the_same_solver() {
        let table = readme_table();
        for degrees in [0.0, 33.0, 180.0, 254.0, 359.0] {
            let compass = CompassCourse::new(degrees).unwrap();
            let magnetic = convert_compass_course_to_magnetic_course(
                compass,
                &table,
                InterpolationMethod::Cubic,
            )
            .unwrap();
            let back = convert_magnetic_course_to_compass_course(
                magnetic.course,
                &table,
                InterpolationMethod::Cubic,
            )
            .unwrap();
            assert!(back.course.angular_distance(compass) < 1e-6);
        }
    }

    #[test]
    fn solver_handles_a_steep_but_invertible_curve() {
        // Deviation changing by 0.9° per degree of heading: extreme, still invertible.
        let values: Vec<f64> = (0..36)
            .map(|index| {
                let course = f64::from(index) * 10.0;
                9.0 * math::sin(math::to_radians(course))
            })
            .collect();
        let table = DeviationTable::from_deviation_vec(values).unwrap();

        let mut course = 0.0;
        while course < 360.0 {
            let compass = CompassCourse::new(course).unwrap();
            let magnetic = convert_compass_course_to_magnetic_course(
                compass,
                &table,
                InterpolationMethod::Linear,
            )
            .unwrap();
            let back = convert_magnetic_course_to_compass_course(
                magnetic.course,
                &table,
                InterpolationMethod::Linear,
            )
            .unwrap();
            assert!(
                back.course.angular_distance(compass) < 1e-4,
                "at {course}: {} came back as {}",
                magnetic.course.degrees(),
                back.course.degrees()
            );
            course += 1.0;
        }
    }

    #[test]
    fn advisories_flag_unusual_data() {
        let quiet = convert_compass_course_to_true_course(
            CompassCourse::new(100.0).unwrap(),
            Variation::new(-2.7).unwrap(),
            &realistic_table(),
            InterpolationMethod::Linear,
        )
        .unwrap();
        assert!(!quiet.advisories.any());

        let loud = convert_compass_course_to_true_course(
            CompassCourse::new(270.0).unwrap(),
            Variation::new(-20.0).unwrap(),
            &readme_table(),
            InterpolationMethod::Linear,
        )
        .unwrap();
        assert!(loud.advisories.large_variation);
        assert!(loud.advisories.large_deviation);
        assert!(loud.advisories.non_invertible_table);
        assert!(!loud.advisories.coarse_table);

        // An eight-point swing is normal practice, not a coarse table...
        let cardinal = convert_compass_course_to_true_course(
            CompassCourse::new(10.0).unwrap(),
            Variation::ZERO,
            &DeviationTable::from_cardinal_directions(),
            InterpolationMethod::Linear,
        )
        .unwrap();
        assert!(!cardinal.advisories.coarse_table);

        // ...but four points is.
        let coarse = convert_compass_course_to_true_course(
            CompassCourse::new(10.0).unwrap(),
            Variation::ZERO,
            &DeviationTable::from_step(90).unwrap(),
            InterpolationMethod::Linear,
        )
        .unwrap();
        assert!(coarse.advisories.coarse_table);
    }

    #[test]
    fn estimated_error_is_zero_on_a_straight_curve() {
        let values: Vec<f64> = (0..36).map(|_| 1.0).collect();
        let table = DeviationTable::from_deviation_vec(values).unwrap();
        let solution = convert_compass_course_to_true_course(
            CompassCourse::new(37.0).unwrap(),
            Variation::ZERO,
            &table,
            InterpolationMethod::Linear,
        )
        .unwrap();
        assert!(solution.estimated_error < 1e-12);

        let bumpy = readme_table();
        let bumpy_solution = convert_compass_course_to_true_course(
            CompassCourse::new(255.0).unwrap(),
            Variation::ZERO,
            &bumpy,
            InterpolationMethod::Linear,
        )
        .unwrap();
        assert!(bumpy_solution.estimated_error > 0.0);
    }

    #[test]
    fn custom_coefficients_reach_the_conversion() {
        let table = readme_table();
        let coefficients = DeviationCoefficients {
            a: Some(0.0),
            b: Some(0.0),
            c: Some(0.0),
            d: Some(0.0),
            e: Some(0.0),
        };
        let solution = convert_compass_course_to_true_course(
            CompassCourse::new(123.0).unwrap(),
            Variation::ZERO,
            &table,
            Interpolation {
                method: InterpolationMethod::Parametric,
                coefficients: Some(&coefficients),
            },
        )
        .unwrap();
        assert_eq!(solution.deviation.degrees(), 0.0);
        assert_eq!(solution.course.degrees(), 123.0);
    }

    #[test]
    fn current_triangle_is_self_consistent() {
        let heading = TrueCourse::new(35.0).unwrap();
        let set = TrueCourse::new(150.0).unwrap();
        let through_water = Speed::from_knots(12.0).unwrap();
        let drift = Speed::from_knots(3.0).unwrap();
        let track = course_over_ground(heading, through_water, set, drift).unwrap();

        let current = estimate_current(
            heading,
            through_water,
            track.course_over_ground,
            track.speed_over_ground,
        )
        .unwrap();
        assert!(current.set.angular_distance(set) < 1e-9);
        assert!((current.drift.knots() - 3.0).abs() < 1e-9);

        let steering =
            course_to_steer(track.course_over_ground, through_water, set, drift).unwrap();
        assert!(steering.heading.angular_distance(heading) < 1e-9);
        assert!(
            (steering.speed_over_ground.knots() - track.speed_over_ground.knots()).abs() < 1e-9
        );
    }

    #[test]
    fn course_over_ground_matches_a_hand_calculation() {
        let track = course_over_ground(
            TrueCourse::new(0.0).unwrap(),
            Speed::from_knots(10.0).unwrap(),
            TrueCourse::new(90.0).unwrap(),
            Speed::from_knots(2.0).unwrap(),
        )
        .unwrap();
        assert_eq!(
            format!("{:.4}", track.course_over_ground.degrees()),
            "11.3099"
        );
        assert_eq!(format!("{:.4}", track.speed_over_ground.knots()), "10.1980");
    }

    #[test]
    fn current_triangle_validates_speeds() {
        let north = TrueCourse::NORTH;
        let one = Speed::from_knots(1.0).unwrap();
        let ten = Speed::from_knots(10.0).unwrap();
        let sternway = Speed::from_knots(-1.0).unwrap();

        assert!(course_over_ground(north, sternway, north, one).is_err());
        assert!(course_to_steer(north, ten, north, sternway).is_err());
        assert!(estimate_current(north, ten, north, sternway).is_err());
        // A non-finite speed cannot even be constructed.
        assert!(Speed::from_knots(f64::NAN).is_err());
        assert!(Speed::from_knots(f64::INFINITY).is_err());
    }

    #[test]
    fn dead_water_has_no_course_over_ground() {
        let track = course_over_ground(
            TrueCourse::new(0.0).unwrap(),
            Speed::from_knots(5.0).unwrap(),
            TrueCourse::new(180.0).unwrap(),
            Speed::from_knots(5.0).unwrap(),
        );
        assert_eq!(
            track.unwrap_err(),
            NavigationError::Indeterminate {
                quantity: "course over ground"
            }
        );
    }

    #[test]
    fn a_current_stronger_than_the_ship_is_reported() {
        let result = course_to_steer(
            TrueCourse::new(0.0).unwrap(),
            Speed::from_knots(2.0).unwrap(),
            TrueCourse::new(90.0).unwrap(),
            Speed::from_knots(10.0).unwrap(),
        );
        assert!(matches!(
            result.unwrap_err(),
            NavigationError::CurrentTooStrong { .. }
        ));

        // A following current stronger than the ship is fine.
        let following = course_to_steer(
            TrueCourse::new(0.0).unwrap(),
            Speed::from_knots(2.0).unwrap(),
            TrueCourse::new(0.0).unwrap(),
            Speed::from_knots(10.0).unwrap(),
        )
        .unwrap();
        assert!((following.speed_over_ground.knots() - 12.0).abs() < 1e-9);
    }

    #[test]
    fn gyro_corrections_are_inverses() {
        use crate::GyroCourse;
        let error = Angle::from_degrees(-1.5).unwrap();
        for degrees in [0.0, 1.0, 90.0, 359.5] {
            let gyro = GyroCourse::new(degrees).unwrap();
            let back = true_to_gyro(gyro_to_true(gyro, error), error);
            assert!(back.angular_distance(gyro) < 1e-12);
        }
    }

    #[test]
    fn gyro_error_comes_out_of_a_transit() {
        use crate::{GyroBearing, TrueBearing};
        let observed = GyroBearing::new(46.5).unwrap();
        let reference = TrueBearing::new(45.0).unwrap();
        let error = gyro_error_from_transit(observed, reference);
        assert!((error.degrees() + 1.5).abs() < 1e-12);
        // Applying it to the observation recovers the reference.
        assert!(gyro_to_true(observed, error).angular_distance(reference) < 1e-12);
    }

    #[test]
    fn gyro_speed_error_is_westerly_going_north_and_easterly_going_south() {
        let latitude = Latitude::from_degrees(60.0).unwrap();
        let speed = Speed::from_knots(20.0).unwrap();

        let north = gyro_speed_error(latitude, TrueCourse::NORTH, speed).unwrap();
        let south = gyro_speed_error(latitude, TrueCourse::SOUTH, speed).unwrap();
        assert!(north.degrees() < 0.0);
        assert!(south.degrees() > 0.0);
        assert!((north.degrees() + south.degrees()).abs() < 1e-9);

        // The same rule holds in the southern hemisphere.
        let southern = Latitude::from_degrees(-40.0).unwrap();
        assert!(
            gyro_speed_error(southern, TrueCourse::NORTH, speed)
                .unwrap()
                .degrees()
                < 0.0
        );

        // Due east or west there is no speed error, and stopped there is none at all.
        assert!(
            gyro_speed_error(latitude, TrueCourse::EAST, speed)
                .unwrap()
                .degrees()
                .abs()
                < 1e-12
        );
        assert!(
            gyro_speed_error(latitude, TrueCourse::NORTH, Speed::ZERO)
                .unwrap()
                .degrees()
                .abs()
                < 1e-12
        );
    }

    #[test]
    fn gyro_speed_error_grows_with_latitude_and_speed() {
        let slow = Speed::from_knots(10.0).unwrap();
        let fast = Speed::from_knots(25.0).unwrap();
        let low = Latitude::from_degrees(10.0).unwrap();
        let high = Latitude::from_degrees(70.0).unwrap();

        let a = gyro_speed_error(low, TrueCourse::NORTH, slow).unwrap();
        let b = gyro_speed_error(high, TrueCourse::NORTH, slow).unwrap();
        let c = gyro_speed_error(low, TrueCourse::NORTH, fast).unwrap();
        assert!(b.degrees() < a.degrees());
        assert!(c.degrees() < a.degrees());

        // At the pole the compass does not settle at all.
        assert!(gyro_speed_error(Latitude::NORTH_POLE, TrueCourse::NORTH, slow).is_err());
        assert!(
            gyro_speed_error(low, TrueCourse::NORTH, Speed::from_knots(-1.0).unwrap()).is_err()
        );
    }

    #[test]
    fn slack_water_leaves_the_current_direction_meaningless_but_defined() {
        let heading = TrueCourse::new(42.0).unwrap();
        let eight = Speed::from_knots(8.0).unwrap();
        let current = estimate_current(heading, eight, heading, eight).unwrap();
        assert_eq!(current.drift.knots(), 0.0);
        assert_eq!(current.set.degrees(), 0.0);
    }
}
