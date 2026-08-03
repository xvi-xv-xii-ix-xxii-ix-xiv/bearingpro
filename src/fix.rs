//! Fixing the ship's position from what can be seen and measured.
//!
//! A *position line* is the locus of points from which an observation would have
//! come out as it did. Two of them cross at a fix; three leave a cocked hat.
//! [`bearing_fix`] takes any number of them and returns the least-squares point,
//! which is the right answer when the bearings are equally trustworthy and no
//! systematic error is suspected.
//!
//! # What a position line is here
//!
//! A bearing line is taken to be a **rhumb line** drawn back from the object,
//! which is what a ruler on a Mercator chart draws and what
//! [`crate::sailings::rhumb_intersection`] solves exactly. The tempting
//! alternative — a great circle on the reciprocal bearing — is not the same
//! curve, because the reciprocal of a great circle's *initial* course is not the
//! course back along it. Over the ranges a visual fix is taken at the two agree
//! to a fraction of a cable, but the rhumb is the one the chartwork means.
//!
//! The least-squares fit and the circle work use a tangent plane at the observer,
//! which is exact enough for those ranges and quite wrong for an ocean passage.
//!
//! # Example
//!
//! ```rust
//! use bearingpro::fix::{bearing_fix, PositionLine};
//! use bearingpro::{NavigationError, Position, TrueBearing};
//!
//! fn main() -> Result<(), NavigationError> {
//!     // A lighthouse bearing 045°, a headland bearing 315°.
//!     let lighthouse = Position::from_degrees(50.20, -4.00)?;
//!     let headland = Position::from_degrees(50.20, -4.40)?;
//!
//!     let fix = bearing_fix(&[
//!         PositionLine::from_bearing_of(lighthouse, TrueBearing::new(45.0)?),
//!         PositionLine::from_bearing_of(headland, TrueBearing::new(315.0)?),
//!     ])?;
//!
//!     assert_eq!(format!("{}", fix.position), "50°04.3'N 004°12.0'W");
//!     Ok(())
//! }
//! ```

use alloc::vec;

use crate::angle::{ensure_range, Direction, RelativeBearing, True, TrueBearing, TrueCourse};
use crate::error::{NavigationError, Result};
use crate::linalg::solve_dense;
use crate::math;
use crate::position::{Latitude, Longitude, Position};
use crate::sailings::{
    great_circle, great_circle_destination, rhumb_destination, rhumb_intersection, rhumb_line,
};
use crate::units::{Angle, Distance};

/// Miles of visible horizon per square root of a metre of height, with mean refraction.
///
/// The coefficient is exposed because the books do not agree on it: 2.03 in the
/// Admiralty List of Lights, 2.12 from Bowditch's imperial 1.17√feet. This one is
/// the Admiralty Manual of Navigation's, for a refraction coefficient of 0.13.
pub const HORIZON_COEFFICIENT: f64 = 2.08;

/// A line of position: everywhere the ship could be, given one observation.
///
/// A rhumb line through `origin` in the direction `direction`, extending both
/// ways.
#[derive(Debug, Clone, Copy, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct PositionLine {
    /// A point the line passes through.
    pub origin: Position,
    /// The direction of the line from that point.
    pub direction: TrueBearing,
}

impl PositionLine {
    /// The position line from a bearing taken of a charted object.
    ///
    /// The ship lies somewhere along the *reciprocal* of the observed bearing,
    /// drawn from the object, which is the sign slip this constructor exists to
    /// prevent. The line is a rhumb line; see the module documentation.
    #[must_use]
    pub fn from_bearing_of(object: Position, observed: TrueBearing) -> Self {
        Self {
            origin: object,
            direction: observed.reciprocal(),
        }
    }

    /// A line through a point in a given direction, as drawn on the chart.
    #[must_use]
    pub const fn new(origin: Position, direction: TrueBearing) -> Self {
        Self { origin, direction }
    }

    /// The line transferred along the run of the ship, for a running fix.
    ///
    /// The whole line moves bodily with the ship: same direction, origin shifted
    /// by the course and distance run since it was observed. This is the
    /// parallel-ruler transfer of the chart room, and it carries the chart room's
    /// small approximation — the run is stepped off at the object's latitude
    /// rather than the ship's. Use [`PositionLine::transferred_between`] when both
    /// ends of the run are known and the difference matters.
    ///
    /// # Errors
    ///
    /// Propagates a rhumb-line failure, notably a run over a pole.
    pub fn transferred(self, course: TrueCourse, run: Distance) -> Result<Self> {
        Ok(Self {
            origin: rhumb_destination(self.origin, course, run)?,
            direction: self.direction,
        })
    }

    /// The line transferred by a run between two known positions.
    ///
    /// Exact: the line is translated on the Mercator chart by the same vector the
    /// ship moved, which is what "transfer the position line" means.
    ///
    /// # Errors
    ///
    /// Returns [`NavigationError::Indeterminate`] if any of the positions is at a
    /// pole, where the chart has no top.
    pub fn transferred_between(self, from: Position, to: Position) -> Result<Self> {
        if from.latitude().is_polar()
            || to.latitude().is_polar()
            || self.origin.latitude().is_polar()
        {
            return Err(NavigationError::Indeterminate {
                quantity: "a transfer through a pole",
            });
        }
        let east = from.longitude_difference(to).minutes();
        let north = to.latitude().isometric_minutes() - from.latitude().isometric_minutes();
        Ok(Self {
            origin: Position::new(
                Latitude::from_isometric_minutes(
                    self.origin.latitude().isometric_minutes() + north,
                ),
                Longitude::from_degrees_wrapped(self.origin.longitude().degrees() + east / 60.0),
            ),
            direction: self.direction,
        })
    }
}

/// A fix from several position lines, with how well they agreed.
#[derive(Debug, Clone, Copy, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Fix {
    /// The most probable position.
    pub position: Position,
    /// How many position lines went into it.
    pub lines: usize,
    /// Root-mean-square perpendicular distance from the fix to the lines.
    ///
    /// Zero for two lines, which always cross exactly. For three or more this is
    /// the measure of how well the observations agree.
    pub rms_residual: Distance,
    /// The largest single perpendicular distance to a line.
    pub greatest_residual: Distance,
}

/// The triangle three position lines leave, and the position taken from it.
#[derive(Debug, Clone, Copy, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CockedHat {
    /// The three pairwise intersections.
    pub vertices: [Position; 3],
    /// The least-squares position, which for three lines is the incentre-like
    /// point that minimises the squared distances to all three.
    pub most_probable: Position,
    /// The longest side of the triangle: the usual measure of a bad fix.
    pub greatest_side: Distance,
}

/// Distance off, worked from two bearings and the run between them.
#[derive(Debug, Clone, Copy, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TwoBearingDistance {
    /// Distance from the object when the second bearing was taken.
    pub at_second_bearing: Distance,
    /// Distance the object will be off when it comes abeam.
    pub abeam: Distance,
}

// ---------------------------------------------------------------------------
// Fixes from bearings
// ---------------------------------------------------------------------------

/// Where two position lines cross.
///
/// # Errors
///
/// - [`NavigationError::Parallel`] if the two lines have the same or reciprocal
///   direction, so they never cross or are the same line.
/// - [`NavigationError::Indeterminate`] if either line starts at a pole.
pub fn two_bearing_fix(first: PositionLine, second: PositionLine) -> Result<Position> {
    rhumb_intersection(
        first.origin,
        first.direction,
        second.origin,
        second.direction,
    )
}

/// The most probable position from any number of position lines.
///
/// Minimises the sum of the squared perpendicular distances to the lines, which
/// is the maximum-likelihood position when the bearings are independent and
/// equally good. It is not the right answer when a *systematic* error is
/// suspected — a compass error common to all the bearings moves the true position
/// outside the cocked hat, and no amount of least squares will find it.
///
/// # Errors
///
/// - [`NavigationError::InsufficientNodes`] for fewer than two lines.
/// - [`NavigationError::Parallel`] if the lines are all parallel, leaving the
///   position undetermined along their direction.
/// - [`NavigationError::Indeterminate`] within half a degree of a pole, where the
///   tangent plane the fit uses breaks down.
pub fn bearing_fix(lines: &[PositionLine]) -> Result<Fix> {
    if lines.len() < 2 {
        return Err(NavigationError::InsufficientNodes {
            found: lines.len(),
            required: 2,
            context: "a position fix",
        });
    }

    let chart = MercatorChart::about(lines)?;

    // On a Mercator chart every position line is straight, so each contributes
    // the exact equation n·x = n·p, where n is the unit normal to the line.
    // Least squares over all of them is a 2x2 normal system.
    let (mut east_east, mut east_north, mut north_north) = (0.0, 0.0, 0.0);
    let (mut east_offset, mut north_offset) = (0.0, 0.0);
    for line in lines {
        let (east, north) = chart.project(line.origin);
        let bearing = line.direction.radians();
        // The line runs along (sin B, cos B); its normal is (cos B, −sin B).
        let (normal_east, normal_north) = (math::cos(bearing), -math::sin(bearing));
        let offset = normal_east * east + normal_north * north;

        east_east += normal_east * normal_east;
        east_north += normal_east * normal_north;
        north_north += normal_north * normal_north;
        east_offset += normal_east * offset;
        north_offset += normal_north * offset;
    }

    let mut normal = vec![east_east, east_north, east_north, north_north];
    let mut target = vec![east_offset, north_offset];
    let solution = solve_dense(&mut normal, &mut target, 2).ok_or(NavigationError::Parallel {
        context: "the position lines",
    })?;
    let (east, north) = (
        solution.first().copied().unwrap_or(0.0),
        solution.get(1).copied().unwrap_or(0.0),
    );
    let position = chart.unproject(east, north);

    // Mercator distances are stretched by sec(latitude); undo that so the
    // residuals come out in miles on the ground.
    let scale = math::cos(position.latitude().radians());
    let mut sum_squares = 0.0;
    let mut greatest: f64 = 0.0;
    for line in lines {
        let (origin_east, origin_north) = chart.project(line.origin);
        let bearing = line.direction.radians();
        let residual = math::abs(
            math::cos(bearing) * (east - origin_east) - math::sin(bearing) * (north - origin_north),
        ) * scale;
        sum_squares += residual * residual;
        greatest = greatest.max(residual);
    }

    Ok(Fix {
        position,
        lines: lines.len(),
        rms_residual: Distance::from_nautical_miles_unchecked(math::sqrt(
            sum_squares / math::count_to_f64(lines.len()),
        )),
        greatest_residual: Distance::from_nautical_miles_unchecked(greatest),
    })
}

/// The cocked hat three position lines leave.
///
/// # Errors
///
/// As [`two_bearing_fix`] and [`bearing_fix`]: any pair of the three that fails
/// to cross makes the triangle undefined.
pub fn cocked_hat(lines: [PositionLine; 3]) -> Result<CockedHat> {
    let [first, second, third] = lines;
    let vertices = [
        two_bearing_fix(first, second)?,
        two_bearing_fix(second, third)?,
        two_bearing_fix(third, first)?,
    ];

    let [alpha, beta, gamma] = vertices;
    let mut greatest: f64 = 0.0;
    for (start, end) in [(alpha, beta), (beta, gamma), (gamma, alpha)] {
        greatest = greatest.max(great_circle(start, end)?.distance.nautical_miles());
    }

    Ok(CockedHat {
        vertices,
        most_probable: bearing_fix(&lines)?.position,
        greatest_side: Distance::from_nautical_miles_unchecked(greatest),
    })
}

/// A running fix: one position line carried forward by the run and crossed with a later one.
///
/// # Errors
///
/// As [`PositionLine::transferred`] and [`two_bearing_fix`].
pub fn running_fix(
    earlier: PositionLine,
    course: TrueCourse,
    run: Distance,
    later: PositionLine,
) -> Result<Position> {
    two_bearing_fix(earlier.transferred(course, run)?, later)
}

/// The ship's position from a bearing and a range of one object.
///
/// # Errors
///
/// Returns [`NavigationError::NotFinite`] for a non-finite range.
pub fn range_and_bearing_fix(
    object: Position,
    bearing: TrueBearing,
    range: Distance,
) -> Result<Position> {
    rhumb_destination(object, bearing.reciprocal(), range)
}

/// The ship's position from ranges of two objects, as by radar.
///
/// Two circles cross at two points; the one nearer `approximate` is returned,
/// which is what the radar screen makes obvious and the arithmetic does not.
///
/// # Errors
///
/// - [`NavigationError::OutOfRange`] for a negative range.
/// - [`NavigationError::NoSolution`] if the circles do not reach each other, or
///   one lies wholly inside the other.
/// - [`NavigationError::Indeterminate`] if the two objects are in the same place.
pub fn two_range_fix(
    first: Position,
    first_range: Distance,
    second: Position,
    second_range: Distance,
    approximate: Position,
) -> Result<Position> {
    ensure_range("range", first_range.nautical_miles(), 0.0, f64::MAX)?;
    ensure_range("range", second_range.nautical_miles(), 0.0, f64::MAX)?;

    let plane = TangentPlane::at(approximate)?;
    let (first_east, first_north) = plane.project(first)?;
    let (second_east, second_north) = plane.project(second)?;

    let (delta_east, delta_north) = (second_east - first_east, second_north - first_north);
    let separation = math::hypot(delta_east, delta_north);
    if separation < 1e-9 {
        return Err(NavigationError::Indeterminate {
            quantity: "a fix from two ranges of the same object",
        });
    }

    let (radius_one, radius_two) = (first_range.nautical_miles(), second_range.nautical_miles());
    if separation > radius_one + radius_two || separation < math::abs(radius_one - radius_two) {
        return Err(NavigationError::NoSolution {
            context: "a fix from two ranges that do not reach each other",
        });
    }

    // Distance from the first object to the foot of the common chord.
    let along = (radius_one * radius_one - radius_two * radius_two + separation * separation)
        / (2.0 * separation);
    let half_chord = math::sqrt((radius_one * radius_one - along * along).max(0.0));

    let (unit_east, unit_north) = (delta_east / separation, delta_north / separation);
    let (foot_east, foot_north) = (
        first_east + along * unit_east,
        first_north + along * unit_north,
    );

    let candidates = [
        plane.unproject(
            foot_east + half_chord * -unit_north,
            foot_north + half_chord * unit_east,
        )?,
        plane.unproject(
            foot_east - half_chord * -unit_north,
            foot_north - half_chord * unit_east,
        )?,
    ];

    let mut best = candidates[0];
    let mut best_distance = great_circle(approximate, best)?.distance.nautical_miles();
    for candidate in &candidates[1..] {
        let distance = great_circle(approximate, *candidate)?
            .distance
            .nautical_miles();
        if distance < best_distance {
            best = *candidate;
            best_distance = distance;
        }
    }
    Ok(best)
}

// ---------------------------------------------------------------------------
// Distance off, without a range finder
// ---------------------------------------------------------------------------

/// Distance off an object of known height, from the vertical angle it subtends.
///
/// Plain trigonometry: `distance = height / tan(angle)`. Below about twenty
/// minutes of arc the curvature of the Earth starts to matter and the tabulated
/// method should be used instead; the function does not stop you, because where
/// exactly that line falls depends on the height of eye.
///
/// # Errors
///
/// - [`NavigationError::OutOfRange`] unless the angle is in `(0°, 90°)`.
/// - [`NavigationError::OutOfRange`] for a negative height.
///
/// # Example
///
/// ```rust
/// use bearingpro::fix::distance_by_vertical_angle;
/// use bearingpro::{Angle, Distance, NavigationError};
///
/// fn main() -> Result<(), NavigationError> {
///     // A light 80 m high subtending 30 minutes of arc.
///     let off = distance_by_vertical_angle(
///         Distance::from_metres(80.0)?,
///         Angle::from_minutes(30.0)?,
///     )?;
///     assert_eq!(format!("{off:.2}"), "4.95 M");
///     Ok(())
/// }
/// ```
pub fn distance_by_vertical_angle(height: Distance, angle: Angle) -> Result<Distance> {
    ensure_range("height", height.nautical_miles(), 0.0, f64::MAX)?;
    ensure_range("vertical angle", angle.degrees(), f64::MIN_POSITIVE, 90.0)?;
    if angle.degrees() >= 90.0 {
        return Err(NavigationError::OutOfRange {
            parameter: "vertical angle",
            value: angle.degrees(),
            min: 0.0,
            max: 90.0,
        });
    }
    Ok(Distance::from_nautical_miles_unchecked(
        height.nautical_miles() / math::tan(angle.radians()),
    ))
}

/// Distance off, from two relative bearings of the same object and the run between them.
///
/// The general case of the special ones every mate learns: doubling the angle on
/// the bow is `θ₂ = 2θ₁`, and the four-point bearing is 45° then 90°.
///
/// Both bearings must be on the same bow, and the object must have drawn aft.
///
/// # Errors
///
/// - [`NavigationError::OutOfRange`] if the bearings are on opposite bows, if
///   either is dead ahead or dead astern, or if the object has not drawn aft.
/// - [`NavigationError::OutOfRange`] for a negative run.
///
/// # Example
///
/// ```rust
/// use bearingpro::fix::distance_by_two_bearings;
/// use bearingpro::{Distance, NavigationError, RelativeBearing};
///
/// fn main() -> Result<(), NavigationError> {
///     // The four-point bearing: 45° on the bow, then abeam, four miles run.
///     let off = distance_by_two_bearings(
///         RelativeBearing::new(45.0)?,
///         RelativeBearing::new(90.0)?,
///         Distance::from_nautical_miles(4.0)?,
///     )?;
///
///     // The classic result: the distance off abeam equals the run.
///     assert!((off.abeam.nautical_miles() - 4.0).abs() < 1e-9);
///     assert!((off.at_second_bearing.nautical_miles() - 4.0).abs() < 1e-9);
///     Ok(())
/// }
/// ```
pub fn distance_by_two_bearings(
    first: RelativeBearing,
    second: RelativeBearing,
    run: Distance,
) -> Result<TwoBearingDistance> {
    ensure_range("run", run.nautical_miles(), 0.0, f64::MAX)?;

    let (first_signed, second_signed) = (first.signed_degrees(), second.signed_degrees());
    if first_signed == 0.0 || second_signed == 0.0 {
        return Err(NavigationError::OutOfRange {
            parameter: "relative bearing",
            value: 0.0,
            min: f64::MIN_POSITIVE,
            max: 180.0,
        });
    }
    if first_signed.is_sign_positive() != second_signed.is_sign_positive() {
        return Err(NavigationError::OutOfRange {
            parameter: "relative bearing",
            value: second_signed,
            min: first_signed.signum() * f64::MIN_POSITIVE,
            max: first_signed.signum() * 180.0,
        });
    }

    let (first_angle, second_angle) = (math::abs(first_signed), math::abs(second_signed));
    if second_angle <= first_angle {
        return Err(NavigationError::OutOfRange {
            parameter: "second relative bearing",
            value: second_angle,
            min: first_angle,
            max: 180.0,
        });
    }

    let spread = math::to_radians(second_angle - first_angle);
    let at_second =
        run.nautical_miles() * math::sin(math::to_radians(first_angle)) / math::sin(spread);

    Ok(TwoBearingDistance {
        at_second_bearing: Distance::from_nautical_miles_unchecked(at_second),
        abeam: Distance::from_nautical_miles_unchecked(
            at_second * math::sin(math::to_radians(second_angle)),
        ),
    })
}

/// How far the visible horizon is, from a given height of eye.
///
/// # Errors
///
/// Returns [`NavigationError::OutOfRange`] for a negative height.
pub fn horizon_distance(height_of_eye: Distance) -> Result<Distance> {
    ensure_range(
        "height of eye",
        height_of_eye.nautical_miles(),
        0.0,
        f64::MAX,
    )?;
    Ok(Distance::from_nautical_miles_unchecked(
        HORIZON_COEFFICIENT * math::sqrt(height_of_eye.metres()),
    ))
}

/// The range at which a light of known height rises or dips.
///
/// Seeing a light appear over the horizon gives a range, and so a position line —
/// one of the few ways to get a distance off at night without a radar.
///
/// # Errors
///
/// Returns [`NavigationError::OutOfRange`] for a negative height.
pub fn dipping_distance(height_of_eye: Distance, height_of_light: Distance) -> Result<Distance> {
    Ok(horizon_distance(height_of_eye)? + horizon_distance(height_of_light)?)
}

// ---------------------------------------------------------------------------
// The tangent plane the fits are worked in
// ---------------------------------------------------------------------------

/// A plane centred on one position, in which distance and bearing from that
/// centre are exact.
///
/// The azimuthal equidistant projection. Circles of range about the centre come
/// out as true circles, which is what the range fixes need, and the distortion
/// away from the centre is second order in the distance.
struct TangentPlane {
    centre: Position,
}

impl TangentPlane {
    /// Sets a plane up at a position.
    fn at(centre: Position) -> Result<Self> {
        if centre.latitude().is_polar() {
            return Err(NavigationError::Indeterminate {
                quantity: "a tangent plane at the pole",
            });
        }
        Ok(Self { centre })
    }

    /// Miles east and north of the centre.
    fn project(&self, position: Position) -> Result<(f64, f64)> {
        let sailing = great_circle(self.centre, position)?;
        let distance = sailing.distance.nautical_miles();
        let bearing = sailing.initial_course.radians();
        Ok((distance * math::sin(bearing), distance * math::cos(bearing)))
    }

    /// Back from miles east and north to a position.
    fn unproject(&self, east: f64, north: f64) -> Result<Position> {
        let distance = math::hypot(east, north);
        if distance < 1e-12 {
            return Ok(self.centre);
        }
        let bearing =
            Direction::<True>::from_degrees_wrapped(math::to_degrees(math::atan2(east, north)));
        Ok(great_circle_destination(
            self.centre,
            bearing,
            Distance::from_nautical_miles_unchecked(distance),
        )?
        .position)
    }
}

/// The Mercator chart the bearing fits are worked on, in minutes of arc.
struct MercatorChart {
    longitude: f64,
}

impl MercatorChart {
    /// Centres a chart on the first of a set of position lines.
    fn about(lines: &[PositionLine]) -> Result<Self> {
        let first = lines.first().ok_or(NavigationError::InsufficientNodes {
            found: 0,
            required: 2,
            context: "a position fix",
        })?;
        for line in lines {
            if line.origin.latitude().is_polar() {
                return Err(NavigationError::Indeterminate {
                    quantity: "a Mercator chart reaching the pole",
                });
            }
        }
        Ok(Self {
            longitude: first.origin.longitude().degrees(),
        })
    }

    /// Minutes east of the reference meridian, and meridional parts north.
    fn project(&self, position: Position) -> (f64, f64) {
        (
            crate::angle::wrap180(position.longitude().degrees() - self.longitude) * 60.0,
            position.latitude().isometric_minutes(),
        )
    }

    /// Back from chart coordinates to a position.
    fn unproject(&self, east: f64, north: f64) -> Position {
        Position::new(
            Latitude::from_isometric_minutes(north),
            Longitude::from_degrees_wrapped(self.longitude + east / 60.0),
        )
    }
}

/// Convenience: a bearing line drawn straight out from a position.
#[must_use]
pub fn line_from(origin: Position, direction: TrueBearing) -> PositionLine {
    PositionLine::new(origin, direction)
}

/// Convenience: the rhumb-line bearing of one position from another.
///
/// The bearing a navigator plots, and the one [`PositionLine::from_bearing_of`]
/// expects.
///
/// # Errors
///
/// Propagates a rhumb-line failure, notably a position at a pole.
pub fn bearing_between(from: Position, to: Position) -> Result<Direction<True>> {
    Ok(rhumb_line(from, to)?.initial_course)
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::float_cmp, clippy::indexing_slicing)]
mod tests {
    use super::*;
    fn at(latitude: f64, longitude: f64) -> Position {
        Position::from_degrees(latitude, longitude).unwrap()
    }

    fn bearing(degrees: f64) -> TrueBearing {
        TrueBearing::new(degrees).unwrap()
    }

    /// Builds the position line an observer at `ship` would draw for `object`.
    fn observed(ship: Position, object: Position) -> PositionLine {
        PositionLine::from_bearing_of(object, bearing_between(ship, object).unwrap())
    }

    #[test]
    fn a_position_line_runs_back_from_the_object() {
        let object = at(50.0, -4.0);
        let line = PositionLine::from_bearing_of(object, bearing(45.0));
        assert_eq!(line.origin, object);
        assert!((line.direction.degrees() - 225.0).abs() < 1e-12);
    }

    #[test]
    fn two_bearings_recover_the_ship() {
        let ship = at(50.10, -4.20);
        let lighthouse = at(50.20, -4.00);
        let headland = at(50.20, -4.40);

        let position =
            two_bearing_fix(observed(ship, lighthouse), observed(ship, headland)).unwrap();
        assert!(
            rhumb_line(ship, position)
                .unwrap()
                .distance
                .nautical_miles()
                < 1e-9
        );
    }

    #[test]
    fn three_perfect_bearings_leave_no_cocked_hat() {
        let ship = at(50.10, -4.20);
        let objects = [at(50.30, -4.00), at(50.20, -4.50), at(49.95, -4.10)];
        let lines = [
            observed(ship, objects[0]),
            observed(ship, objects[1]),
            observed(ship, objects[2]),
        ];

        let hat = cocked_hat(lines).unwrap();
        assert!(hat.greatest_side.nautical_miles() < 1e-6);
        assert!(
            rhumb_line(ship, hat.most_probable)
                .unwrap()
                .distance
                .nautical_miles()
                < 1e-3
        );

        let fix = bearing_fix(&lines).unwrap();
        assert_eq!(fix.lines, 3);
        assert!(fix.rms_residual.nautical_miles() < 1e-6);
        assert!(fix.greatest_residual.nautical_miles() < 1e-6);
    }

    #[test]
    fn a_bad_bearing_opens_the_cocked_hat_and_shows_in_the_residual() {
        let ship = at(50.10, -4.20);
        let objects = [at(50.30, -4.00), at(50.20, -4.50), at(49.95, -4.10)];
        let mut lines = [
            observed(ship, objects[0]),
            observed(ship, objects[1]),
            observed(ship, objects[2]),
        ];
        // Spoil the third bearing by three degrees.
        lines[2] = PositionLine::new(lines[2].origin, lines[2].direction.offset(3.0).unwrap());

        let hat = cocked_hat(lines).unwrap();
        assert!(hat.greatest_side.nautical_miles() > 0.1);

        let fix = bearing_fix(&lines).unwrap();
        assert!(fix.rms_residual.nautical_miles() > 0.01);
        assert!(fix.greatest_residual >= fix.rms_residual);
        // The most probable position is still inside the triangle, near the ship.
        assert!(
            rhumb_line(ship, fix.position)
                .unwrap()
                .distance
                .nautical_miles()
                < 1.0
        );
    }

    #[test]
    fn a_fix_needs_at_least_two_lines() {
        let line = PositionLine::from_bearing_of(at(50.0, -4.0), bearing(90.0));
        assert!(matches!(
            bearing_fix(&[]).unwrap_err(),
            NavigationError::InsufficientNodes { found: 0, .. }
        ));
        assert!(matches!(
            bearing_fix(&[line]).unwrap_err(),
            NavigationError::InsufficientNodes { found: 1, .. }
        ));
    }

    #[test]
    fn parallel_bearings_give_no_fix() {
        let first = PositionLine::new(at(50.0, -4.0), bearing(90.0));
        let second = PositionLine::new(at(50.1, -4.0), bearing(90.0));
        assert!(matches!(
            bearing_fix(&[first, second]).unwrap_err(),
            NavigationError::Parallel { .. }
        ));
        // Reciprocal bearings are the same line, and no better.
        let reciprocal = PositionLine::new(at(50.1, -4.0), bearing(270.0));
        assert!(bearing_fix(&[first, reciprocal]).is_err());
    }

    #[test]
    fn a_running_fix_carries_the_first_line_forward() {
        let course = TrueCourse::new(90.0).unwrap();
        let run = Distance::from_nautical_miles(6.0).unwrap();

        let first_position = at(50.00, -4.50);
        let later_position = rhumb_destination(first_position, course, run).unwrap();
        let object = at(50.25, -4.20);

        let earlier = observed(first_position, object);
        let second_object = at(49.90, -4.10);
        let later = observed(later_position, second_object);

        // The parallel-ruler transfer carries the chart room's approximation.
        let fix = running_fix(earlier, course, run, later).unwrap();
        assert!(
            rhumb_line(later_position, fix)
                .unwrap()
                .distance
                .nautical_miles()
                < 0.05
        );

        // Transferring by the run itself is exact.
        let exact = two_bearing_fix(
            earlier
                .transferred_between(first_position, later_position)
                .unwrap(),
            later,
        )
        .unwrap();
        assert!(
            rhumb_line(later_position, exact)
                .unwrap()
                .distance
                .nautical_miles()
                < 1e-9
        );
    }

    #[test]
    fn a_transferred_line_keeps_its_direction() {
        let line = PositionLine::new(at(50.0, -4.0), bearing(123.0));
        let moved = line
            .transferred(
                TrueCourse::new(45.0).unwrap(),
                Distance::from_nautical_miles(10.0).unwrap(),
            )
            .unwrap();
        assert_eq!(moved.direction, line.direction);
        assert!(
            (rhumb_line(line.origin, moved.origin)
                .unwrap()
                .distance
                .nautical_miles()
                - 10.0)
                .abs()
                < 1e-9
        );
    }

    #[test]
    fn a_range_and_bearing_puts_the_ship_where_it_should() {
        let ship = at(50.0, -4.0);
        let object = at(50.2, -3.8);
        // The bearing and range as they would be observed and plotted.
        let sailing = rhumb_line(ship, object).unwrap();

        let fixed =
            range_and_bearing_fix(object, sailing.initial_course, sailing.distance).unwrap();
        assert!(rhumb_line(ship, fixed).unwrap().distance.nautical_miles() < 1e-9);
    }

    #[test]
    fn two_ranges_cross_where_the_ship_is() {
        let ship = at(50.10, -4.20);
        let first = at(50.30, -4.00);
        let second = at(50.05, -4.50);

        let first_range = great_circle(first, ship).unwrap().distance;
        let second_range = great_circle(second, ship).unwrap().distance;

        let fixed = two_range_fix(first, first_range, second, second_range, ship).unwrap();
        assert!(
            great_circle(ship, fixed).unwrap().distance.nautical_miles() < 1e-4,
            "{} off",
            great_circle(ship, fixed).unwrap().distance.nautical_miles()
        );
    }

    #[test]
    fn two_ranges_pick_the_solution_nearest_the_estimate() {
        let first = at(50.00, -4.00);
        let second = at(50.00, -4.20);
        let range = Distance::from_nautical_miles(8.0).unwrap();

        let northern = two_range_fix(first, range, second, range, at(50.2, -4.1)).unwrap();
        let southern = two_range_fix(first, range, second, range, at(49.8, -4.1)).unwrap();
        assert!(northern.latitude().degrees() > 50.0);
        assert!(southern.latitude().degrees() < 50.0);
    }

    #[test]
    fn ranges_that_do_not_reach_are_reported() {
        let first = at(50.0, -4.0);
        let second = at(50.0, -5.0);
        let tiny = Distance::from_nautical_miles(1.0).unwrap();
        assert!(matches!(
            two_range_fix(first, tiny, second, tiny, first).unwrap_err(),
            NavigationError::NoSolution { .. }
        ));

        // One circle wholly inside the other.
        let big = Distance::from_nautical_miles(100.0).unwrap();
        assert!(two_range_fix(first, big, second, tiny, first).is_err());

        // A negative range is nonsense.
        assert!(two_range_fix(
            first,
            Distance::from_nautical_miles(-1.0).unwrap(),
            second,
            tiny,
            first
        )
        .is_err());
    }

    #[test]
    fn vertical_angle_gives_the_distance_off() {
        // A 100 m light subtending exactly 1° is 100/tan(1°) m off.
        let off = distance_by_vertical_angle(
            Distance::from_metres(100.0).unwrap(),
            Angle::from_degrees(1.0).unwrap(),
        )
        .unwrap();
        let expected = 100.0 / (1.0_f64).to_radians().tan();
        assert!((off.metres() - expected).abs() < 1e-6);

        // Halving the angle roughly doubles the distance.
        let further = distance_by_vertical_angle(
            Distance::from_metres(100.0).unwrap(),
            Angle::from_degrees(0.5).unwrap(),
        )
        .unwrap();
        assert!((further.nautical_miles() / off.nautical_miles() - 2.0).abs() < 0.01);
    }

    #[test]
    fn vertical_angle_rejects_impossible_observations() {
        let height = Distance::from_metres(50.0).unwrap();
        assert!(distance_by_vertical_angle(height, Angle::ZERO).is_err());
        assert!(distance_by_vertical_angle(height, Angle::from_degrees(-1.0).unwrap()).is_err());
        assert!(distance_by_vertical_angle(height, Angle::from_degrees(90.0).unwrap()).is_err());
        assert!(distance_by_vertical_angle(
            Distance::from_metres(-1.0).unwrap(),
            Angle::from_degrees(1.0).unwrap()
        )
        .is_err());
    }

    #[test]
    fn the_four_point_bearing_gives_the_run_as_the_distance() {
        let run = Distance::from_nautical_miles(4.0).unwrap();
        let off = distance_by_two_bearings(
            RelativeBearing::new(45.0).unwrap(),
            RelativeBearing::new(90.0).unwrap(),
            run,
        )
        .unwrap();
        assert!((off.at_second_bearing.nautical_miles() - 4.0).abs() < 1e-9);
        assert!((off.abeam.nautical_miles() - 4.0).abs() < 1e-9);
    }

    #[test]
    fn doubling_the_angle_on_the_bow_gives_the_run_as_the_distance() {
        // Whenever the second angle is twice the first, the distance off at the
        // second bearing equals the run — that is the whole point of the rule.
        let run = Distance::from_nautical_miles(6.0).unwrap();
        for first in [20.0, 30.0, 40.0, 55.0] {
            let off = distance_by_two_bearings(
                RelativeBearing::new(first).unwrap(),
                RelativeBearing::new(first * 2.0).unwrap(),
                run,
            )
            .unwrap();
            assert!(
                (off.at_second_bearing.nautical_miles() - 6.0).abs() < 1e-9,
                "at {first}°"
            );
        }
    }

    #[test]
    fn two_bearings_work_on_the_port_bow_too() {
        let run = Distance::from_nautical_miles(4.0).unwrap();
        let starboard = distance_by_two_bearings(
            RelativeBearing::new(45.0).unwrap(),
            RelativeBearing::new(90.0).unwrap(),
            run,
        )
        .unwrap();
        let port = distance_by_two_bearings(
            RelativeBearing::new(315.0).unwrap(),
            RelativeBearing::new(270.0).unwrap(),
            run,
        )
        .unwrap();
        assert!((starboard.abeam.nautical_miles() - port.abeam.nautical_miles()).abs() < 1e-9);
    }

    #[test]
    fn two_bearings_refuse_nonsense() {
        let run = Distance::from_nautical_miles(4.0).unwrap();
        let forty_five = RelativeBearing::new(45.0).unwrap();
        let ninety = RelativeBearing::new(90.0).unwrap();

        // Opposite bows.
        assert!(
            distance_by_two_bearings(forty_five, RelativeBearing::new(300.0).unwrap(), run)
                .is_err()
        );
        // The object drawing forward instead of aft.
        assert!(distance_by_two_bearings(ninety, forty_five, run).is_err());
        // Dead ahead has no bearing to speak of.
        assert!(distance_by_two_bearings(RelativeBearing::AHEAD, ninety, run).is_err());
        // A negative run.
        assert!(distance_by_two_bearings(
            forty_five,
            ninety,
            Distance::from_nautical_miles(-4.0).unwrap()
        )
        .is_err());
    }

    #[test]
    fn the_horizon_is_where_the_books_put_it() {
        // Ten metres of height of eye: about 6.6 miles.
        let horizon = horizon_distance(Distance::from_metres(10.0).unwrap()).unwrap();
        assert!((horizon.nautical_miles() - 6.58).abs() < 0.01);

        // A light 100 m high seen from 10 m up dips at about 27.4 miles.
        let dipping = dipping_distance(
            Distance::from_metres(10.0).unwrap(),
            Distance::from_metres(100.0).unwrap(),
        )
        .unwrap();
        assert!((dipping.nautical_miles() - 27.38).abs() < 0.05);

        // No height, no horizon.
        assert_eq!(horizon_distance(Distance::ZERO).unwrap(), Distance::ZERO);
        assert!(horizon_distance(Distance::from_metres(-1.0).unwrap()).is_err());
    }

    #[test]
    fn a_fix_at_the_pole_is_refused_rather_than_fudged() {
        // A Mercator chart has no top, so a line starting exactly at the pole has
        // nowhere to be drawn.
        let polar = PositionLine::new(at(90.0, 0.0), bearing(90.0));
        let other = PositionLine::new(at(80.0, 90.0), bearing(180.0));
        assert!(matches!(
            bearing_fix(&[polar, other]).unwrap_err(),
            NavigationError::Indeterminate { .. }
        ));
        assert!(two_bearing_fix(polar, other).is_err());

        // Very near the pole is fine, though: the chart is only infinite at it.
        let near = PositionLine::new(at(89.99, 0.0), bearing(90.0));
        let crossing = PositionLine::new(at(89.99, 90.0), bearing(180.0));
        assert!(bearing_fix(&[near, crossing]).is_ok());
    }
}
