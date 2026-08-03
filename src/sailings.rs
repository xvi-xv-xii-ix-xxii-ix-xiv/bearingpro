//! Getting from one position to another: the sailings.
//!
//! | Function | Model | Path | Use when |
//! |---|---|---|---|
//! | [`rhumb_line`] | sphere | constant course | you intend to steer one course |
//! | [`great_circle`] | sphere | shortest on a sphere | ocean passages |
//! | [`geodesic`] | WGS-84 ellipsoid | shortest, exactly | you need the last metre |
//!
//! Spherical results use a mean Earth radius of 6371.0088 km, which is
//! [`EARTH_RADIUS`]. Against the ellipsoid that is worth up to about 0.5% on a
//! long leg, so [`geodesic`] is there when it matters.
//!
//! # Example
//!
//! ```rust
//! use bearingpro::sailings::{great_circle, rhumb_line};
//! use bearingpro::{NavigationError, Position};
//!
//! fn main() -> Result<(), NavigationError> {
//!     // The Lizard to Cape Race.
//!     let from = Position::from_degrees(49.95, -5.20)?;
//!     let to = Position::from_degrees(46.66, -53.07)?;
//!
//!     let direct = great_circle(from, to)?;
//!     let steered = rhumb_line(from, to)?;
//!
//!     // The great circle is shorter, but the course changes the whole way.
//!     assert!(direct.distance < steered.distance);
//!     assert!(direct.initial_course != direct.final_course);
//!     assert_eq!(steered.initial_course, steered.final_course);
//!     Ok(())
//! }
//! ```

use alloc::vec::Vec;
use core::f64::consts::{FRAC_PI_2, FRAC_PI_4, PI};

use crate::angle::{Direction, True, TrueCourse};
use crate::error::{NavigationError, Result};
use crate::math;
use crate::position::{
    Latitude, Longitude, Position, WGS84_FLATTENING, WGS84_SEMI_MAJOR_AXIS_METRES,
};
use crate::units::{Distance, METRES_PER_NAUTICAL_MILE};

/// Mean radius of the Earth, as used by the spherical sailings.
pub const EARTH_RADIUS: Distance =
    Distance::from_nautical_miles_unchecked(6_371_008.8 / METRES_PER_NAUTICAL_MILE);

/// Convergence tolerance of Vincenty's iterations, in radians.
const VINCENTY_TOLERANCE: f64 = 1e-12;
/// Iterations allowed before Vincenty gives up.
const VINCENTY_ITERATIONS: u32 = 200;
/// Below this angular separation two positions count as the same place.
const COINCIDENT: f64 = 1e-12;

/// The course and distance from one position to another.
#[derive(Debug, Clone, Copy, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Sailing {
    /// Course to steer on leaving. For a rhumb line this is the whole story.
    pub initial_course: TrueCourse,
    /// Course being made good on arrival.
    ///
    /// Equal to `initial_course` for a rhumb line; different for a great circle
    /// or a geodesic, which is why they have to be steered in legs.
    pub final_course: TrueCourse,
    /// Length of the track.
    pub distance: Distance,
}

/// A position reached, and the course being made good there.
#[derive(Debug, Clone, Copy, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Arrival {
    /// Where the track ends up.
    pub position: Position,
    /// Course being made good on arrival.
    pub final_course: TrueCourse,
}

/// Which side of a track a position lies on.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum TrackSide {
    /// On the track, within rounding.
    OnTrack,
    /// Left of the track, looking along it.
    Port,
    /// Right of the track, looking along it.
    Starboard,
}

/// How far a position lies from a leg, and how far along it.
#[derive(Debug, Clone, Copy, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CrossTrack {
    /// Perpendicular distance from the track. Never negative; see `side`.
    pub distance: Distance,
    /// Which side of the track the position is on.
    pub side: TrackSide,
    /// Distance from the start of the leg to the foot of the perpendicular.
    ///
    /// Negative if the position is behind the start of the leg, and greater than
    /// the leg length if it is beyond the end.
    pub along_track: Distance,
    /// Distance still to run to the end of the leg, along the track.
    pub to_run: Distance,
}

impl CrossTrack {
    /// The cross-track distance signed positive to starboard of the track.
    #[must_use]
    pub fn signed(&self) -> Distance {
        match self.side {
            TrackSide::Port => -self.distance,
            TrackSide::OnTrack | TrackSide::Starboard => self.distance,
        }
    }
}

// ---------------------------------------------------------------------------
// Rhumb line
// ---------------------------------------------------------------------------

/// Course and distance along a rhumb line: the track of constant course.
///
/// # Errors
///
/// Returns [`NavigationError::Indeterminate`] if either position is at a pole,
/// where a rhumb line degenerates.
pub fn rhumb_line(from: Position, to: Position) -> Result<Sailing> {
    if from.latitude().is_polar() || to.latitude().is_polar() {
        return Err(NavigationError::Indeterminate {
            quantity: "a rhumb line through a pole",
        });
    }

    let latitude_difference = to.latitude().radians() - from.latitude().radians();
    let longitude_difference = from.longitude_difference(to).radians();
    let stretched = stretched_difference(from.latitude(), to.latitude());

    // The east-west scale factor: dφ/dψ, which tends to cos φ as the two
    // latitudes converge and the ratio becomes 0/0.
    let scale = if math::abs(stretched) > 1e-12 {
        latitude_difference / stretched
    } else {
        math::cos(from.latitude().radians())
    };

    let angular = math::sqrt(
        latitude_difference * latitude_difference
            + scale * scale * longitude_difference * longitude_difference,
    );
    let course = Direction::<True>::from_degrees_wrapped(math::to_degrees(math::atan2(
        longitude_difference,
        stretched,
    )));

    Ok(Sailing {
        initial_course: course,
        final_course: course,
        distance: from_angular(angular),
    })
}

/// Where a rhumb line of a given course and distance ends up.
///
/// # Errors
///
/// - [`NavigationError::NotFinite`] for a non-finite distance.
/// - [`NavigationError::Indeterminate`] if the track would pass over a pole,
///   which a rhumb line cannot do.
pub fn rhumb_destination(
    from: Position,
    course: TrueCourse,
    distance: Distance,
) -> Result<Position> {
    let angular = to_angular(distance)?;
    let course_radians = course.radians();
    let latitude_difference = angular * math::cos(course_radians);
    let latitude_radians = from.latitude().radians() + latitude_difference;

    if math::abs(latitude_radians) > FRAC_PI_2 {
        return Err(NavigationError::Indeterminate {
            quantity: "a rhumb line beyond the pole",
        });
    }

    let latitude = Latitude::from_degrees_clamped(math::to_degrees(latitude_radians));
    let stretched = stretched_difference(from.latitude(), latitude);
    let scale = if math::abs(stretched) > 1e-12 {
        latitude_difference / stretched
    } else {
        math::cos(from.latitude().radians())
    };

    let longitude_difference = if math::abs(scale) < 1e-12 {
        0.0
    } else {
        angular * math::sin(course_radians) / scale
    };

    Ok(Position::new(
        latitude,
        Longitude::from_degrees_wrapped(
            from.longitude().degrees() + math::to_degrees(longitude_difference),
        ),
    ))
}

/// Difference of spherical isometric latitude, in radians.
fn stretched_difference(from: Latitude, to: Latitude) -> f64 {
    math::ln(math::tan(FRAC_PI_4 + to.radians() / 2.0))
        - math::ln(math::tan(FRAC_PI_4 + from.radians() / 2.0))
}

// ---------------------------------------------------------------------------
// Great circle
// ---------------------------------------------------------------------------

/// Course and distance along a great circle: the shortest track on a sphere.
///
/// For coincident positions the distance is zero and the courses are `000°`. For
/// antipodal positions every great circle between them is the same length and the
/// course is arbitrary; the one returned is whichever the arithmetic produces.
///
/// # Errors
///
/// Does not currently fail, but returns `Result` so that a future ellipsoidal
/// refinement does not become a breaking change.
pub fn great_circle(from: Position, to: Position) -> Result<Sailing> {
    let (from_latitude, to_latitude) = (from.latitude().radians(), to.latitude().radians());
    let longitude_difference = from.longitude_difference(to).radians();
    let latitude_difference = to_latitude - from_latitude;

    let half_latitude = math::sin(latitude_difference / 2.0);
    let half_longitude = math::sin(longitude_difference / 2.0);
    let chord = half_latitude * half_latitude
        + math::cos(from_latitude) * math::cos(to_latitude) * half_longitude * half_longitude;
    let angular = 2.0 * math::asin(math::sqrt(chord).min(1.0));

    Ok(Sailing {
        initial_course: initial_course(from, to),
        final_course: initial_course(to, from).reciprocal(),
        distance: from_angular(angular),
    })
}

/// Where a great circle of a given initial course and distance ends up.
///
/// # Errors
///
/// Returns [`NavigationError::NotFinite`] for a non-finite distance.
pub fn great_circle_destination(
    from: Position,
    course: TrueCourse,
    distance: Distance,
) -> Result<Arrival> {
    let angular = to_angular(distance)?;
    let latitude = from.latitude().radians();
    let course_radians = course.radians();

    let sine_latitude = math::sin(latitude) * math::cos(angular)
        + math::cos(latitude) * math::sin(angular) * math::cos(course_radians);
    let destination_latitude = math::asin(sine_latitude.clamp(-1.0, 1.0));
    let longitude_difference = math::atan2(
        math::sin(course_radians) * math::sin(angular) * math::cos(latitude),
        math::cos(angular) - math::sin(latitude) * sine_latitude,
    );

    let position = Position::new(
        Latitude::from_degrees_clamped(math::to_degrees(destination_latitude)),
        Longitude::from_degrees_wrapped(
            from.longitude().degrees() + math::to_degrees(longitude_difference),
        ),
    );

    Ok(Arrival {
        position,
        final_course: initial_course(position, from).reciprocal(),
    })
}

/// The point on a great circle at a given fraction of the way along it.
///
/// `fraction` is not restricted to `0..=1`; values outside it extrapolate.
///
/// # Errors
///
/// Returns [`NavigationError::NotFinite`] for a non-finite fraction, and
/// [`NavigationError::Indeterminate`] for antipodal positions, between which no
/// single great circle is defined.
pub fn great_circle_intermediate(from: Position, to: Position, fraction: f64) -> Result<Position> {
    crate::angle::ensure_finite("fraction", fraction)?;
    let angular = to_angular(great_circle(from, to)?.distance)?;

    if angular < COINCIDENT {
        return Ok(from);
    }
    if math::abs(angular - PI) < COINCIDENT {
        return Err(NavigationError::Indeterminate {
            quantity: "a great circle between antipodal positions",
        });
    }

    let sine = math::sin(angular);
    let start_weight = math::sin((1.0 - fraction) * angular) / sine;
    let end_weight = math::sin(fraction * angular) / sine;

    let [from_x, from_y, from_z] = from.to_unit_vector();
    let [to_x, to_y, to_z] = to.to_unit_vector();

    Position::from_unit_vector([
        start_weight * from_x + end_weight * to_x,
        start_weight * from_y + end_weight * to_y,
        start_weight * from_z + end_weight * to_z,
    ])
    .ok_or(NavigationError::Indeterminate {
        quantity: "a point on the great circle",
    })
}

/// Splits a great circle into legs of at most `interval`, for steering as rhumb lines.
///
/// The returned list starts at `from` and ends at `to`, so a track of `n` legs
/// comes back as `n + 1` positions.
///
/// # Errors
///
/// - [`NavigationError::OutOfRange`] if `interval` is not positive.
/// - [`NavigationError::Indeterminate`] for antipodal positions.
pub fn great_circle_waypoints(
    from: Position,
    to: Position,
    interval: Distance,
) -> Result<Vec<Position>> {
    if interval.nautical_miles() <= 0.0 {
        return Err(NavigationError::OutOfRange {
            parameter: "interval",
            value: interval.nautical_miles(),
            min: f64::MIN_POSITIVE,
            max: f64::MAX,
        });
    }

    let total = great_circle(from, to)?.distance.nautical_miles();
    let legs = math::ceil(total / interval.nautical_miles()).max(1.0);
    // A leg count beyond this is a request the caller did not mean to make.
    if legs > 1e6 {
        return Err(NavigationError::OutOfRange {
            parameter: "interval",
            value: interval.nautical_miles(),
            min: total / 1e6,
            max: f64::MAX,
        });
    }

    let count = math::to_usize(legs);
    let mut waypoints = Vec::with_capacity(count + 1);
    for step in 0..=count {
        let fraction = math::count_to_f64(step) / legs;
        waypoints.push(great_circle_intermediate(from, to, fraction)?);
    }
    Ok(waypoints)
}

/// The vertex of a great circle: its highest latitude, in the northern hemisphere.
///
/// The southern vertex is the antipode of this one. For a great circle along the
/// equator every point is a vertex and the one returned is arbitrary.
///
/// # Errors
///
/// Returns [`NavigationError::Indeterminate`] if the great circle degenerates.
pub fn great_circle_vertex(from: Position, initial_course: TrueCourse) -> Result<Position> {
    let pole = great_circle_pole(from, initial_course);
    let position = Position::from_unit_vector(pole).ok_or(NavigationError::Indeterminate {
        quantity: "the pole of the great circle",
    })?;

    let vertex_latitude = 90.0 - math::abs(position.latitude().degrees());
    let vertex_longitude = if position.latitude().degrees() >= 0.0 {
        position.longitude().degrees() + 180.0
    } else {
        position.longitude().degrees()
    };

    Ok(Position::new(
        Latitude::from_degrees_clamped(vertex_latitude),
        Longitude::from_degrees_wrapped(vertex_longitude),
    ))
}

/// Where two great circles, each given by a position and a course, cross.
///
/// Two great circles always cross at a pair of antipodal points; the one returned
/// is whichever lies nearer to the two given positions, which is what a position
/// fix wants.
///
/// # Errors
///
/// Returns [`NavigationError::Parallel`] if the two great circles are the same
/// circle, so that every point on it is an intersection.
pub fn intersection(
    first: Position,
    first_course: TrueCourse,
    second: Position,
    second_course: TrueCourse,
) -> Result<Position> {
    let a = great_circle_pole(first, first_course);
    let b = great_circle_pole(second, second_course);
    let line = cross(a, b);
    let magnitude = math::sqrt(dot(line, line));

    if magnitude < 1e-12 {
        return Err(NavigationError::Parallel {
            context: "the two great circles",
        });
    }

    let candidate = [
        line[0] / magnitude,
        line[1] / magnitude,
        line[2] / magnitude,
    ];
    // Of the two antipodal crossings, take the one on the same side as the
    // positions the lines were drawn from.
    let midpoint = {
        let [x1, y1, z1] = first.to_unit_vector();
        let [x2, y2, z2] = second.to_unit_vector();
        [x1 + x2, y1 + y2, z1 + z2]
    };
    let chosen = if dot(candidate, midpoint) >= 0.0 {
        candidate
    } else {
        [-candidate[0], -candidate[1], -candidate[2]]
    };

    Position::from_unit_vector(chosen).ok_or(NavigationError::Indeterminate {
        quantity: "the intersection of the two great circles",
    })
}

/// Where two rhumb lines, each given by a position and a course, cross.
///
/// This is the intersection a navigator gets by laying a ruler across a Mercator
/// chart, and it is computed the same way: on a Mercator projection a rhumb line
/// really is straight, so the crossing is an exact two-line intersection in
/// meridional parts and longitude rather than an approximation.
///
/// Unlike [`intersection`] the answer is unique — two rhumb lines cross once —
/// which is why the position fixes use this one.
///
/// # Errors
///
/// - [`NavigationError::Parallel`] if the two rhumb lines have the same or
///   reciprocal course, so they never cross or are the same line.
/// - [`NavigationError::Indeterminate`] if either position is at a pole.
pub fn rhumb_intersection(
    first: Position,
    first_course: TrueCourse,
    second: Position,
    second_course: TrueCourse,
) -> Result<Position> {
    if first.latitude().is_polar() || second.latitude().is_polar() {
        return Err(NavigationError::Indeterminate {
            quantity: "a rhumb line through a pole",
        });
    }

    // Mercator coordinates, in minutes: longitude east, meridional parts north.
    // Longitudes are measured from the first position so the antimeridian is not
    // a special case.
    let first_point = (0.0, first.latitude().isometric_minutes());
    let second_point = (
        first.longitude_difference(second).minutes(),
        second.latitude().isometric_minutes(),
    );

    // On a Mercator projection a course of C is the straight direction (sin C, cos C).
    let first_direction = (
        math::sin(first_course.radians()),
        math::cos(first_course.radians()),
    );
    let second_direction = (
        math::sin(second_course.radians()),
        math::cos(second_course.radians()),
    );

    let determinant =
        first_direction.0 * second_direction.1 - first_direction.1 * second_direction.0;
    if math::abs(determinant) < 1e-12 {
        return Err(NavigationError::Parallel {
            context: "the two rhumb lines",
        });
    }

    let offset = (
        second_point.0 - first_point.0,
        second_point.1 - first_point.1,
    );
    let along = (offset.0 * second_direction.1 - offset.1 * second_direction.0) / determinant;

    let crossing = (
        first_point.0 + along * first_direction.0,
        first_point.1 + along * first_direction.1,
    );

    if !crossing.0.is_finite() || !crossing.1.is_finite() {
        return Err(NavigationError::Indeterminate {
            quantity: "the crossing of these rhumb lines",
        });
    }

    Ok(Position::new(
        Latitude::from_isometric_minutes(crossing.1),
        Longitude::from_degrees_wrapped(first.longitude().degrees() + crossing.0 / 60.0),
    ))
}

/// How far a position lies off a leg, and how far along it.
///
/// # Errors
///
/// Returns [`NavigationError::Indeterminate`] if the leg has no length, so there
/// is no track to be off.
pub fn cross_track(
    position: Position,
    leg_start: Position,
    leg_end: Position,
) -> Result<CrossTrack> {
    let leg = great_circle(leg_start, leg_end)?;
    let leg_angular = to_angular(leg.distance)?;
    if leg_angular < COINCIDENT {
        return Err(NavigationError::Indeterminate {
            quantity: "the track of a zero-length leg",
        });
    }

    let to_position = great_circle(leg_start, position)?;
    let position_angular = to_angular(to_position.distance)?;
    let offset = math::to_radians(
        leg.initial_course
            .signed_difference(to_position.initial_course),
    );

    let across = math::asin((math::sin(position_angular) * math::sin(offset)).clamp(-1.0, 1.0));
    let cosine = math::cos(across);
    let along = if math::abs(cosine) < f64::EPSILON {
        0.0
    } else {
        let ratio = (math::cos(position_angular) / cosine).clamp(-1.0, 1.0);
        math::acos(ratio) * if math::cos(offset) < 0.0 { -1.0 } else { 1.0 }
    };

    let side = if math::abs(across) < 1e-12 {
        TrackSide::OnTrack
    } else if across > 0.0 {
        TrackSide::Starboard
    } else {
        TrackSide::Port
    };

    Ok(CrossTrack {
        distance: from_angular(math::abs(across)),
        side,
        along_track: from_angular(along),
        to_run: from_angular(leg_angular - along),
    })
}

// ---------------------------------------------------------------------------
// Geodesic, on the WGS-84 ellipsoid
// ---------------------------------------------------------------------------

/// Course and distance along the geodesic: the shortest track on the ellipsoid.
///
/// Vincenty's inverse solution, accurate to well under a millimetre.
///
/// # Errors
///
/// Returns [`NavigationError::NotConverged`] for very nearly antipodal positions,
/// where the iteration is known not to converge. Use [`great_circle`] there: at
/// half the Earth's circumference the difference between the models hardly
/// matters.
pub fn geodesic(from: Position, to: Position) -> Result<Sailing> {
    let flattening = WGS84_FLATTENING;
    let semi_major = WGS84_SEMI_MAJOR_AXIS_METRES;
    let semi_minor = semi_major * (1.0 - flattening);

    let longitude_difference = from.longitude_difference(to).radians();
    let reduced_from = math::atan((1.0 - flattening) * math::tan(from.latitude().radians()));
    let reduced_to = math::atan((1.0 - flattening) * math::tan(to.latitude().radians()));
    let (sin_from, cos_from) = (math::sin(reduced_from), math::cos(reduced_from));
    let (sin_to, cos_to) = (math::sin(reduced_to), math::cos(reduced_to));

    let mut lambda = longitude_difference;
    let mut sin_sigma = 0.0;
    let mut cos_sigma = 0.0;
    let mut sigma = 0.0;
    let mut cos_squared_alpha = 0.0;
    let mut cos_two_sigma_m = 0.0;
    let mut converged = false;

    for _ in 0..VINCENTY_ITERATIONS {
        let (sin_lambda, cos_lambda) = (math::sin(lambda), math::cos(lambda));
        let first = cos_to * sin_lambda;
        let second = cos_from * sin_to - sin_from * cos_to * cos_lambda;
        sin_sigma = math::sqrt(first * first + second * second);

        if sin_sigma < COINCIDENT {
            // Coincident positions: no distance, and no course to steer.
            return Ok(Sailing {
                initial_course: Direction::<True>::NORTH,
                final_course: Direction::<True>::NORTH,
                distance: Distance::ZERO,
            });
        }

        cos_sigma = sin_from * sin_to + cos_from * cos_to * cos_lambda;
        sigma = math::atan2(sin_sigma, cos_sigma);
        let sin_alpha = cos_from * cos_to * sin_lambda / sin_sigma;
        cos_squared_alpha = 1.0 - sin_alpha * sin_alpha;
        cos_two_sigma_m = if math::abs(cos_squared_alpha) < f64::EPSILON {
            0.0 // Equatorial track: the midpoint term drops out.
        } else {
            cos_sigma - 2.0 * sin_from * sin_to / cos_squared_alpha
        };

        let correction = flattening / 16.0
            * cos_squared_alpha
            * (4.0 + flattening * (4.0 - 3.0 * cos_squared_alpha));
        let previous = lambda;
        lambda = longitude_difference
            + (1.0 - correction)
                * flattening
                * sin_alpha
                * (sigma
                    + correction
                        * sin_sigma
                        * (cos_two_sigma_m
                            + correction
                                * cos_sigma
                                * (-1.0 + 2.0 * cos_two_sigma_m * cos_two_sigma_m)));

        if math::abs(lambda - previous) < VINCENTY_TOLERANCE {
            converged = true;
            break;
        }
    }

    if !converged {
        return Err(NavigationError::NotConverged {
            iterations: VINCENTY_ITERATIONS,
            residual: math::to_degrees(math::abs(lambda - longitude_difference)),
        });
    }

    let u_squared = cos_squared_alpha * (semi_major * semi_major - semi_minor * semi_minor)
        / (semi_minor * semi_minor);
    let a_series = 1.0
        + u_squared / 16384.0
            * (4096.0 + u_squared * (-768.0 + u_squared * (320.0 - 175.0 * u_squared)));
    let b_series =
        u_squared / 1024.0 * (256.0 + u_squared * (-128.0 + u_squared * (74.0 - 47.0 * u_squared)));
    let delta_sigma = delta_sigma(b_series, sin_sigma, cos_sigma, cos_two_sigma_m);

    let (sin_lambda, cos_lambda) = (math::sin(lambda), math::cos(lambda));
    Ok(Sailing {
        initial_course: Direction::<True>::from_degrees_wrapped(math::to_degrees(math::atan2(
            cos_to * sin_lambda,
            cos_from * sin_to - sin_from * cos_to * cos_lambda,
        ))),
        final_course: Direction::<True>::from_degrees_wrapped(math::to_degrees(math::atan2(
            cos_from * sin_lambda,
            -sin_from * cos_to + cos_from * sin_to * cos_lambda,
        ))),
        distance: Distance::from_nautical_miles_unchecked(
            semi_minor * a_series * (sigma - delta_sigma) / METRES_PER_NAUTICAL_MILE,
        ),
    })
}

/// Where a geodesic of a given initial course and distance ends up.
///
/// Vincenty's direct solution.
///
/// # Errors
///
/// - [`NavigationError::NotFinite`] for a non-finite distance.
/// - [`NavigationError::NotConverged`] if the iteration fails to settle.
pub fn geodesic_destination(
    from: Position,
    course: TrueCourse,
    distance: Distance,
) -> Result<Arrival> {
    crate::angle::ensure_finite("distance", distance.nautical_miles())?;
    let flattening = WGS84_FLATTENING;
    let semi_major = WGS84_SEMI_MAJOR_AXIS_METRES;
    let semi_minor = semi_major * (1.0 - flattening);
    let metres = distance.metres();

    let course_radians = course.radians();
    let (sin_course, cos_course) = (math::sin(course_radians), math::cos(course_radians));
    let reduced = math::atan((1.0 - flattening) * math::tan(from.latitude().radians()));
    let (sin_reduced, cos_reduced) = (math::sin(reduced), math::cos(reduced));

    let sigma_one = math::atan2(math::tan(reduced), cos_course);
    let sin_alpha = cos_reduced * sin_course;
    let cos_squared_alpha = 1.0 - sin_alpha * sin_alpha;
    let u_squared = cos_squared_alpha * (semi_major * semi_major - semi_minor * semi_minor)
        / (semi_minor * semi_minor);
    let a_series = 1.0
        + u_squared / 16384.0
            * (4096.0 + u_squared * (-768.0 + u_squared * (320.0 - 175.0 * u_squared)));
    let b_series =
        u_squared / 1024.0 * (256.0 + u_squared * (-128.0 + u_squared * (74.0 - 47.0 * u_squared)));

    let mut sigma = metres / (semi_minor * a_series);
    let mut cos_two_sigma_m = math::cos(2.0 * sigma_one + sigma);
    let mut converged = false;

    for _ in 0..VINCENTY_ITERATIONS {
        cos_two_sigma_m = math::cos(2.0 * sigma_one + sigma);
        let (sin_sigma, cos_sigma) = (math::sin(sigma), math::cos(sigma));
        let correction = delta_sigma(b_series, sin_sigma, cos_sigma, cos_two_sigma_m);
        let previous = sigma;
        sigma = metres / (semi_minor * a_series) + correction;
        if math::abs(sigma - previous) < VINCENTY_TOLERANCE {
            converged = true;
            break;
        }
    }

    if !converged {
        return Err(NavigationError::NotConverged {
            iterations: VINCENTY_ITERATIONS,
            residual: math::to_degrees(sigma),
        });
    }

    let (sin_sigma, cos_sigma) = (math::sin(sigma), math::cos(sigma));
    let numerator = sin_reduced * cos_sigma + cos_reduced * sin_sigma * cos_course;
    let denominator_term = sin_reduced * sin_sigma - cos_reduced * cos_sigma * cos_course;
    let latitude = math::atan2(
        numerator,
        (1.0 - flattening)
            * math::sqrt(sin_alpha * sin_alpha + denominator_term * denominator_term),
    );
    let lambda = math::atan2(
        sin_sigma * sin_course,
        cos_reduced * cos_sigma - sin_reduced * sin_sigma * cos_course,
    );
    let correction = flattening / 16.0
        * cos_squared_alpha
        * (4.0 + flattening * (4.0 - 3.0 * cos_squared_alpha));
    let longitude_difference = lambda
        - (1.0 - correction)
            * flattening
            * sin_alpha
            * (sigma
                + correction
                    * sin_sigma
                    * (cos_two_sigma_m
                        + correction
                            * cos_sigma
                            * (-1.0 + 2.0 * cos_two_sigma_m * cos_two_sigma_m)));

    Ok(Arrival {
        position: Position::new(
            Latitude::from_degrees_clamped(math::to_degrees(latitude)),
            Longitude::from_degrees_wrapped(
                from.longitude().degrees() + math::to_degrees(longitude_difference),
            ),
        ),
        final_course: Direction::<True>::from_degrees_wrapped(math::to_degrees(math::atan2(
            sin_alpha,
            -denominator_term,
        ))),
    })
}

/// The `Δσ` correction shared by Vincenty's direct and inverse solutions.
fn delta_sigma(b_series: f64, sin_sigma: f64, cos_sigma: f64, cos_two_sigma_m: f64) -> f64 {
    let cos_squared = cos_two_sigma_m * cos_two_sigma_m;
    let sin_squared = sin_sigma * sin_sigma;
    b_series
        * sin_sigma
        * (cos_two_sigma_m
            + b_series / 4.0
                * (cos_sigma * (-1.0 + 2.0 * cos_squared)
                    - b_series / 6.0
                        * cos_two_sigma_m
                        * (-3.0 + 4.0 * sin_squared)
                        * (-3.0 + 4.0 * cos_squared)))
}

// ---------------------------------------------------------------------------
// Shared helpers
// ---------------------------------------------------------------------------

/// Initial great-circle course from one position to another.
fn initial_course(from: Position, to: Position) -> TrueCourse {
    let (from_latitude, to_latitude) = (from.latitude().radians(), to.latitude().radians());
    let longitude_difference = from.longitude_difference(to).radians();
    Direction::<True>::from_degrees_wrapped(math::to_degrees(math::atan2(
        math::sin(longitude_difference) * math::cos(to_latitude),
        math::cos(from_latitude) * math::sin(to_latitude)
            - math::sin(from_latitude) * math::cos(to_latitude) * math::cos(longitude_difference),
    )))
}

/// Unit normal of the great circle through a position on a given course.
fn great_circle_pole(from: Position, course: TrueCourse) -> [f64; 3] {
    let (latitude, longitude) = (from.latitude().radians(), from.longitude().radians());
    let (sin_latitude, cos_latitude) = (math::sin(latitude), math::cos(latitude));
    let (sin_longitude, cos_longitude) = (math::sin(longitude), math::cos(longitude));
    let course_radians = course.radians();
    let (sin_course, cos_course) = (math::sin(course_radians), math::cos(course_radians));

    // The unit tangent at `from`, as east and north components in space.
    let east = [-sin_longitude, cos_longitude, 0.0];
    let north = [
        -sin_latitude * cos_longitude,
        -sin_latitude * sin_longitude,
        cos_latitude,
    ];
    let tangent = [
        sin_course * east[0] + cos_course * north[0],
        sin_course * east[1] + cos_course * north[1],
        sin_course * east[2] + cos_course * north[2],
    ];
    cross(from.to_unit_vector(), tangent)
}

fn cross(a: [f64; 3], b: [f64; 3]) -> [f64; 3] {
    [
        a[1] * b[2] - a[2] * b[1],
        a[2] * b[0] - a[0] * b[2],
        a[0] * b[1] - a[1] * b[0],
    ]
}

fn dot(a: [f64; 3], b: [f64; 3]) -> f64 {
    a[0] * b[0] + a[1] * b[1] + a[2] * b[2]
}

/// Converts an angle at the Earth's centre into a distance along the surface.
fn from_angular(radians: f64) -> Distance {
    Distance::from_nautical_miles_unchecked(radians * EARTH_RADIUS.nautical_miles())
}

/// Converts a surface distance into an angle at the Earth's centre.
fn to_angular(distance: Distance) -> Result<f64> {
    crate::angle::ensure_finite("distance", distance.nautical_miles())?;
    Ok(distance.nautical_miles() / EARTH_RADIUS.nautical_miles())
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::float_cmp, clippy::indexing_slicing)]
mod tests {
    use super::*;

    fn at(latitude: f64, longitude: f64) -> Position {
        Position::from_degrees(latitude, longitude).unwrap()
    }

    #[test]
    fn one_minute_of_latitude_is_one_mile() {
        let sailing = great_circle(at(0.0, 0.0), at(1.0 / 60.0, 0.0)).unwrap();
        // The mean-radius sphere makes this 1.0007 miles, not exactly 1.
        assert!((sailing.distance.nautical_miles() - 1.0).abs() < 0.001);
        assert!(sailing.initial_course.degrees().abs() < 1e-9);
    }

    #[test]
    fn a_degree_of_latitude_is_sixty_miles() {
        let sailing = great_circle(at(10.0, 30.0), at(11.0, 30.0)).unwrap();
        assert!((sailing.distance.nautical_miles() - 60.0).abs() < 0.1);
        assert!(sailing.initial_course.degrees().abs() < 1e-9);
        assert!(sailing.final_course.degrees().abs() < 1e-9);
    }

    #[test]
    fn quarter_of_the_globe_along_the_equator() {
        let sailing = great_circle(at(0.0, 0.0), at(0.0, 90.0)).unwrap();
        assert!((sailing.distance.nautical_miles() - 90.0 * 60.0).abs() < 10.0);
        assert!((sailing.initial_course.degrees() - 90.0).abs() < 1e-9);
    }

    #[test]
    fn great_circle_courses_change_along_the_track() {
        // A high-latitude crossing: the course swings a long way.
        let sailing = great_circle(at(50.0, -5.0), at(50.0, -50.0)).unwrap();
        assert!(sailing.initial_course.degrees() > 270.0);
        assert!(sailing.final_course.degrees() < 270.0);
        // Symmetric about the meridian halfway between.
        let out = 360.0 - sailing.initial_course.degrees();
        let back = 270.0 - sailing.final_course.degrees();
        assert!((out - (90.0 - back) - 0.0).abs() < 30.0);
    }

    #[test]
    fn great_circle_is_never_longer_than_the_rhumb_line() {
        for (from, to) in [
            (at(49.95, -5.2), at(46.66, -53.07)),
            (at(35.0, 139.0), at(37.8, -122.4)),
            (at(-33.9, 151.2), at(-34.6, -58.4)),
            (at(10.0, 0.0), at(-10.0, 30.0)),
        ] {
            let direct = great_circle(from, to).unwrap();
            let steered = rhumb_line(from, to).unwrap();
            assert!(
                direct.distance.nautical_miles() <= steered.distance.nautical_miles() + 1e-6,
                "{:?} vs {:?}",
                direct.distance,
                steered.distance
            );
        }
    }

    #[test]
    fn rhumb_line_along_a_meridian_and_a_parallel() {
        let meridian = rhumb_line(at(10.0, 20.0), at(11.0, 20.0)).unwrap();
        assert!((meridian.distance.nautical_miles() - 60.0).abs() < 0.1);
        assert!(meridian.initial_course.degrees().abs() < 1e-9);

        // Along a parallel the rhumb distance is the departure exactly.
        let parallel = rhumb_line(at(60.0, 0.0), at(60.0, 2.0)).unwrap();
        assert!((parallel.distance.nautical_miles() - 60.0).abs() < 0.1);
        assert!((parallel.initial_course.degrees() - 90.0).abs() < 1e-9);
    }

    #[test]
    fn rhumb_line_round_trips_through_its_destination() {
        for (from, course, distance) in [
            (at(0.0, 0.0), 45.0, 1000.0),
            (at(50.0, -5.0), 250.0, 2000.0),
            (at(-20.0, 170.0), 300.0, 1500.0),
            (at(60.0, 10.0), 180.0, 600.0),
        ] {
            let course = TrueCourse::new(course).unwrap();
            let distance = Distance::from_nautical_miles(distance).unwrap();
            let destination = rhumb_destination(from, course, distance).unwrap();
            let back = rhumb_line(from, destination).unwrap();

            assert!(
                (back.distance.nautical_miles() - distance.nautical_miles()).abs() < 1e-6,
                "{:?} vs {distance:?}",
                back.distance
            );
            assert!(back.initial_course.angular_distance(course) < 1e-9);
        }
    }

    #[test]
    fn rhumb_line_refuses_to_cross_a_pole() {
        let result = rhumb_destination(
            at(80.0, 0.0),
            TrueCourse::NORTH,
            Distance::from_nautical_miles(1000.0).unwrap(),
        );
        assert!(result.is_err());
        assert!(rhumb_line(at(90.0, 0.0), at(45.0, 0.0)).is_err());
    }

    #[test]
    fn great_circle_round_trips_through_its_destination() {
        for (from, course, distance) in [
            (at(0.0, 0.0), 45.0, 1000.0),
            (at(50.0, -5.0), 250.0, 3000.0),
            (at(-20.0, 170.0), 300.0, 1500.0),
        ] {
            let course = TrueCourse::new(course).unwrap();
            let distance = Distance::from_nautical_miles(distance).unwrap();
            let arrival = great_circle_destination(from, course, distance).unwrap();
            let back = great_circle(from, arrival.position).unwrap();

            assert!((back.distance.nautical_miles() - distance.nautical_miles()).abs() < 1e-6);
            assert!(back.initial_course.angular_distance(course) < 1e-9);
            assert!(back.final_course.angular_distance(arrival.final_course) < 1e-9);
        }
    }

    #[test]
    fn vertex_is_the_highest_latitude_on_the_track() {
        // Leaving the equator on 045 the vertex is 45N, a quadrant further east.
        let vertex = great_circle_vertex(at(0.0, 0.0), TrueCourse::new(45.0).unwrap()).unwrap();
        assert!((vertex.latitude().degrees() - 45.0).abs() < 1e-9);
        assert!((vertex.longitude().degrees() - 90.0).abs() < 1e-9);

        // Leaving on 315 it is the same latitude, a quadrant to the west.
        let westward = great_circle_vertex(at(0.0, 0.0), TrueCourse::new(315.0).unwrap()).unwrap();
        assert!((westward.latitude().degrees() - 45.0).abs() < 1e-9);
        assert!((westward.longitude().degrees() + 90.0).abs() < 1e-9);
    }

    #[test]
    fn vertex_is_never_beaten_by_a_point_on_the_track() {
        let from = at(35.0, 139.0);
        let course = TrueCourse::new(50.0).unwrap();
        let vertex = great_circle_vertex(from, course).unwrap();

        let mut distance = 0.0;
        while distance < 10_000.0 {
            let point = great_circle_destination(
                from,
                course,
                Distance::from_nautical_miles(distance).unwrap(),
            )
            .unwrap();
            assert!(
                point.position.latitude().degrees() <= vertex.latitude().degrees() + 1e-6,
                "at {distance} miles the track reaches {}, above the vertex {}",
                point.position.latitude().degrees(),
                vertex.latitude().degrees()
            );
            distance += 50.0;
        }
    }

    #[test]
    fn waypoints_span_the_track() {
        let from = at(49.95, -5.2);
        let to = at(46.66, -53.07);
        let total = great_circle(from, to).unwrap().distance;
        let waypoints =
            great_circle_waypoints(from, to, Distance::from_nautical_miles(300.0).unwrap())
                .unwrap();

        assert!(waypoints.len() >= 2);
        assert!(waypoints.first().unwrap().latitude().degrees() - from.latitude().degrees() < 1e-9);
        let last = waypoints.last().unwrap();
        assert!(great_circle(*last, to).unwrap().distance.nautical_miles() < 1e-6);

        // Every leg is within the requested interval, and they add up.
        let mut sum = 0.0;
        for pair in waypoints.windows(2) {
            let leg = great_circle(pair[0], pair[1]).unwrap();
            assert!(leg.distance.nautical_miles() <= 300.0 + 1e-6);
            sum += leg.distance.nautical_miles();
        }
        assert!((sum - total.nautical_miles()).abs() < 1e-6);
    }

    #[test]
    fn waypoints_reject_a_useless_interval() {
        let from = at(0.0, 0.0);
        let to = at(10.0, 10.0);
        assert!(great_circle_waypoints(from, to, Distance::ZERO).is_err());
        assert!(
            great_circle_waypoints(from, to, Distance::from_nautical_miles(-5.0).unwrap()).is_err()
        );
        assert!(
            great_circle_waypoints(from, to, Distance::from_nautical_miles(1e-9).unwrap()).is_err()
        );
    }

    #[test]
    fn intermediate_points_lie_on_the_track() {
        let from = at(10.0, 20.0);
        let to = at(-30.0, 100.0);
        let total = great_circle(from, to).unwrap().distance.nautical_miles();

        for fraction in [0.0, 0.25, 0.5, 0.75, 1.0] {
            let point = great_circle_intermediate(from, to, fraction).unwrap();
            let travelled = great_circle(from, point).unwrap().distance.nautical_miles();
            assert!((travelled - total * fraction).abs() < 1e-6, "at {fraction}");
        }
    }

    #[test]
    fn intersection_of_two_meridians_is_a_pole() {
        // Two meridians meet at the poles. Going north from both, that is the
        // north pole.
        let crossing = intersection(
            at(10.0, 0.0),
            TrueCourse::NORTH,
            at(10.0, 90.0),
            TrueCourse::NORTH,
        )
        .unwrap();
        assert!((crossing.latitude().degrees() - 90.0).abs() < 1e-6);
    }

    #[test]
    fn intersection_of_a_meridian_and_the_equator() {
        let crossing = intersection(
            at(-10.0, 30.0),
            TrueCourse::NORTH,
            at(0.0, 0.0),
            TrueCourse::EAST,
        )
        .unwrap();
        assert!(crossing.latitude().degrees().abs() < 1e-6);
        assert!((crossing.longitude().degrees() - 30.0).abs() < 1e-6);
    }

    #[test]
    fn parallel_great_circles_do_not_intersect() {
        let result = intersection(
            at(0.0, 0.0),
            TrueCourse::EAST,
            at(0.0, 40.0),
            TrueCourse::EAST,
        );
        assert!(matches!(
            result.unwrap_err(),
            NavigationError::Parallel { .. }
        ));
    }

    #[test]
    fn cross_track_is_zero_on_the_track() {
        let start = at(0.0, 0.0);
        let end = at(0.0, 10.0);
        let on_track = at(0.0, 5.0);
        let result = cross_track(on_track, start, end).unwrap();
        assert!(result.distance.nautical_miles() < 1e-6);
        assert_eq!(result.side, TrackSide::OnTrack);
        assert!((result.along_track.nautical_miles() - 300.4).abs() < 1.0);
    }

    #[test]
    fn cross_track_knows_which_side_it_is_on() {
        let start = at(0.0, 0.0);
        let end = at(0.0, 10.0); // steering due east
        let to_the_north = at(1.0, 5.0);
        let to_the_south = at(-1.0, 5.0);

        let north = cross_track(to_the_north, start, end).unwrap();
        // North of an easterly track is to port.
        assert_eq!(north.side, TrackSide::Port);
        assert!((north.distance.nautical_miles() - 60.0).abs() < 0.2);
        assert!(north.signed().nautical_miles() < 0.0);

        let south = cross_track(to_the_south, start, end).unwrap();
        assert_eq!(south.side, TrackSide::Starboard);
        assert!(south.signed().nautical_miles() > 0.0);
    }

    #[test]
    fn cross_track_along_and_to_run_add_up() {
        let start = at(50.0, -5.0);
        let end = at(50.0, -10.0);
        let leg = great_circle(start, end).unwrap().distance.nautical_miles();
        let position = at(50.2, -7.5);
        let result = cross_track(position, start, end).unwrap();
        assert!(
            (result.along_track.nautical_miles() + result.to_run.nautical_miles() - leg).abs()
                < 1e-6
        );
    }

    #[test]
    fn cross_track_can_be_behind_the_start() {
        let start = at(0.0, 0.0);
        let end = at(0.0, 10.0);
        let behind = at(0.0, -2.0);
        let result = cross_track(behind, start, end).unwrap();
        assert!(result.along_track.is_negative());
    }

    #[test]
    fn cross_track_needs_a_leg_with_length() {
        let point = at(1.0, 1.0);
        assert!(cross_track(point, at(0.0, 0.0), at(0.0, 0.0)).is_err());
    }

    #[test]
    fn geodesic_matches_the_published_vincenty_test_case() {
        // Vincenty's own worked example: Flinders Peak 37°57'03.72030"S
        // 144°25'29.52440"E to Buninyong 37°39'10.15610"S 143°55'35.38390"E.
        // On WGS-84 that is 54 972.271 m, leaving on 306°52'05.37". Vincenty
        // tabulates the azimuth at the far end as 127°10'25.07", which is the
        // reverse azimuth — the direction back to where you came from. The course
        // still being made good on arrival is its reciprocal, 307°10'25.07".
        let from = Position::from_degrees(-37.951_033_416_7, 144.424_867_888_9).unwrap();
        let to = Position::from_degrees(-37.652_821_138_9, 143.926_495_527_8).unwrap();
        let sailing = geodesic(from, to).unwrap();

        assert!(
            (sailing.distance.metres() - 54_972.271).abs() < 0.001,
            "{} m",
            sailing.distance.metres()
        );

        let initial = 306.0 + 52.0 / 60.0 + 5.37 / 3600.0;
        let reverse_azimuth = 127.0 + 10.0 / 60.0 + 25.07 / 3600.0;
        assert!(
            (sailing.initial_course.degrees() - initial).abs() < 1e-6,
            "initial {}",
            sailing.initial_course.degrees()
        );
        assert!(
            (sailing.final_course.reciprocal().degrees() - reverse_azimuth).abs() < 1e-6,
            "final {}",
            sailing.final_course.degrees()
        );
    }

    #[test]
    fn geodesic_round_trips_through_its_destination() {
        for (from, course, metres) in [
            (at(0.0, 0.0), 45.0, 1_000_000.0),
            (at(50.0, -5.0), 250.0, 3_000_000.0),
            (at(-20.0, 170.0), 300.0, 500_000.0),
            (at(60.0, 10.0), 180.0, 100_000.0),
        ] {
            let course = TrueCourse::new(course).unwrap();
            let distance = Distance::from_metres(metres).unwrap();
            let arrival = geodesic_destination(from, course, distance).unwrap();
            let back = geodesic(from, arrival.position).unwrap();

            assert!(
                (back.distance.metres() - metres).abs() < 1e-6,
                "{} vs {metres}",
                back.distance.metres()
            );
            assert!(back.initial_course.angular_distance(course) < 1e-9);
            assert!(back.final_course.angular_distance(arrival.final_course) < 1e-9);
        }
    }

    #[test]
    fn geodesic_and_great_circle_agree_to_within_the_flattening() {
        for (from, to) in [
            (at(49.95, -5.2), at(46.66, -53.07)),
            (at(0.0, 0.0), at(0.0, 40.0)),
            (at(-33.9, 151.2), at(35.0, 139.0)),
        ] {
            let sphere = great_circle(from, to).unwrap().distance.nautical_miles();
            let ellipsoid = geodesic(from, to).unwrap().distance.nautical_miles();
            let relative = (sphere - ellipsoid).abs() / ellipsoid;
            assert!(
                relative < 0.006,
                "{relative} between {sphere} and {ellipsoid}"
            );
        }
    }

    #[test]
    fn coincident_positions_have_no_distance() {
        let point = at(12.34, -56.78);
        assert_eq!(great_circle(point, point).unwrap().distance, Distance::ZERO);
        assert_eq!(rhumb_line(point, point).unwrap().distance, Distance::ZERO);
        assert_eq!(geodesic(point, point).unwrap().distance, Distance::ZERO);
    }

    #[test]
    fn tracks_across_the_antimeridian_take_the_short_way() {
        let from = at(0.0, 179.0);
        let to = at(0.0, -179.0);
        let sailing = great_circle(from, to).unwrap();
        assert!((sailing.distance.nautical_miles() - 120.0).abs() < 0.2);
        assert!((sailing.initial_course.degrees() - 90.0).abs() < 1e-9);

        let steered = rhumb_line(from, to).unwrap();
        assert!((steered.distance.nautical_miles() - 120.0).abs() < 0.2);

        let destination = rhumb_destination(
            from,
            TrueCourse::EAST,
            Distance::from_nautical_miles(120.0).unwrap(),
        )
        .unwrap();
        assert!(destination.longitude().degrees() < 0.0);
    }

    #[test]
    fn hostile_distances_are_errors_not_panics() {
        let from = at(10.0, 10.0);
        for value in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
            let distance = Distance::from_nautical_miles(value);
            assert!(distance.is_err());
        }
        // A distance far beyond the globe still produces a position, not a panic.
        let far = Distance::from_nautical_miles(1e9).unwrap();
        assert!(great_circle_destination(from, TrueCourse::EAST, far).is_ok());
        assert!(geodesic_destination(from, TrueCourse::EAST, far).is_ok());
    }
}
