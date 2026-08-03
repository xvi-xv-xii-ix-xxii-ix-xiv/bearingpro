//! Dead reckoning: where the ship will be, and where she probably is.
//!
//! A *dead reckoning* position uses only the course steered and the distance run.
//! An *estimated position* also allows for the current, and for the leeway the
//! wind causes. The two are kept apart here because they are kept apart at sea:
//! a DR is a statement about what was done, an EP a statement about what probably
//! happened.
//!
//! Tracks are rhumb lines, because that is what a ship steering one course
//! actually follows.
//!
//! # Example
//!
//! ```rust
//! use bearingpro::dead_reckoning::{dead_reckoning, estimated_position};
//! use bearingpro::navigation_solutions::Current;
//! use bearingpro::{NavigationError, Position, Speed, TrueCourse};
//! use core::time::Duration;
//!
//! fn main() -> Result<(), NavigationError> {
//!     let noon = Position::from_degrees(50.0, -5.0)?;
//!     let course = TrueCourse::new(270.0)?;
//!     let speed = Speed::from_knots(12.0)?;
//!     let four_hours = Duration::from_secs(4 * 3600);
//!
//!     // Steering due west at 12 knots for four hours: 48 miles of westing.
//!     let reckoned = dead_reckoning(noon, course, speed, four_hours)?;
//!     assert_eq!(format!("{reckoned}"), "50°00.0'N 006°14.6'W");
//!
//!     // With a knot of north-going current the ship also makes northing.
//!     let current = Current {
//!         set: TrueCourse::new(0.0)?,
//!         drift: Speed::from_knots(1.0)?,
//!     };
//!     let estimated = estimated_position(noon, course, speed, current, four_hours)?;
//!     assert!(estimated.position.latitude().degrees() > 50.0);
//!     Ok(())
//! }
//! ```

use core::time::Duration;

use crate::angle::{Direction, True, TrueCourse};
use crate::error::Result;
use crate::math;
use crate::navigation_solutions::{course_over_ground, Current, GroundTrack};
use crate::position::Position;
use crate::sailings::rhumb_destination;
use crate::units::{hours, Angle, Distance, Speed};

/// One course-and-distance leg of a traverse.
#[derive(Debug, Clone, Copy, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Leg {
    /// Course made good over this leg.
    pub course: TrueCourse,
    /// Distance run over this leg.
    pub distance: Distance,
}

/// An estimated position, with the ground track that produced it.
#[derive(Debug, Clone, Copy, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct EstimatedPosition {
    /// Where the ship is estimated to be.
    pub position: Position,
    /// Course and speed made good over the ground.
    pub track: GroundTrack,
    /// Distance made good over the ground.
    pub distance_made_good: Distance,
}

/// Where a ship gets to steering one course at one speed for a given time.
///
/// # Errors
///
/// Propagates any failure from the rhumb-line sailing: notably
/// [`crate::NavigationError::Indeterminate`] if the track would run over a pole.
pub fn dead_reckoning(
    from: Position,
    course: TrueCourse,
    speed: Speed,
    elapsed: Duration,
) -> Result<Position> {
    rhumb_destination(from, course, speed.distance_covered(elapsed))
}

/// Where a ship gets to running a given distance on one course.
///
/// # Errors
///
/// As [`dead_reckoning`].
pub fn dead_reckoning_by_distance(
    from: Position,
    course: TrueCourse,
    distance: Distance,
) -> Result<Position> {
    rhumb_destination(from, course, distance)
}

/// Where a ship probably is, allowing for the current.
///
/// # Errors
///
/// - [`crate::NavigationError::OutOfRange`] for sternway, which the current
///   triangle does not model.
/// - [`crate::NavigationError::Indeterminate`] if the ship's motion through the
///   water exactly cancels the current, leaving no track at all.
pub fn estimated_position(
    from: Position,
    heading: TrueCourse,
    speed: Speed,
    current: Current,
    elapsed: Duration,
) -> Result<EstimatedPosition> {
    let track = course_over_ground(heading, speed, current.set, current.drift)?;
    let distance_made_good = track.speed_over_ground.distance_covered(elapsed);
    Ok(EstimatedPosition {
        position: rhumb_destination(from, track.course_over_ground, distance_made_good)?,
        track,
        distance_made_good,
    })
}

/// Where a series of legs ends up, run one after another.
///
/// The traverse of the old traverse table: each leg is a rhumb line from where
/// the previous one left off.
///
/// # Errors
///
/// As [`dead_reckoning`], for the first leg that runs over a pole.
pub fn traverse(from: Position, legs: &[Leg]) -> Result<Position> {
    let mut position = from;
    for leg in legs {
        position = rhumb_destination(position, leg.course, leg.distance)?;
    }
    Ok(position)
}

/// The course through the water once leeway is allowed for.
///
/// The wind pushes the ship bodily to leeward, so the track through the water
/// lies to leeward of the heading. Which way that is depends on which bow the
/// wind is on, and this works it out: with the wind from the port bow the ship
/// crabs to starboard, and the other way about.
///
/// `leeway` is the leeway angle observed in the present conditions — the library
/// does not guess it from the wind strength, because it depends on the ship. Its
/// sign is ignored; only its magnitude is used.
///
/// # Example
///
/// ```rust
/// use bearingpro::dead_reckoning::water_track;
/// use bearingpro::{Angle, NavigationError, TrueCourse};
///
/// fn main() -> Result<(), NavigationError> {
///     let heading = TrueCourse::new(0.0)?;
///     let leeway = Angle::from_degrees(5.0)?;
///
///     // Wind on the port bow: the ship is set to starboard.
///     let from_port = water_track(heading, leeway, TrueCourse::new(315.0)?);
///     assert_eq!(from_port.degrees(), 5.0);
///
///     // Wind on the starboard bow: the other way.
///     let from_starboard = water_track(heading, leeway, TrueCourse::new(45.0)?);
///     assert_eq!(from_starboard.degrees(), 355.0);
///     Ok(())
/// }
/// ```
#[must_use]
pub fn water_track(heading: TrueCourse, leeway: Angle, wind_from: TrueCourse) -> TrueCourse {
    // Positive means the wind is coming from somewhere to starboard.
    let relative = heading.signed_difference(wind_from);
    let magnitude = math::abs(leeway.degrees());
    let applied = if relative > 0.0 {
        -magnitude
    } else {
        magnitude
    };
    Direction::<True>::from_degrees_wrapped(heading.degrees() + applied)
}

/// How long a passage takes at a given speed.
///
/// # Errors
///
/// Returns [`crate::NavigationError::Indeterminate`] if the speed is zero or
/// runs the wrong way.
pub fn passage_time(distance: Distance, speed: Speed) -> Result<Duration> {
    speed.time_to_cover(distance)
}

/// The speed needed to cover a distance in a given time.
///
/// # Errors
///
/// Returns [`crate::NavigationError::Indeterminate`] if no time is allowed.
pub fn speed_required(distance: Distance, available: Duration) -> Result<Speed> {
    let elapsed = hours(available);
    if elapsed <= 0.0 {
        return Err(crate::NavigationError::Indeterminate {
            quantity: "the speed required in no time at all",
        });
    }
    Speed::from_knots(distance.nautical_miles() / elapsed)
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::float_cmp, clippy::indexing_slicing)]
mod tests {
    use super::*;
    use crate::sailings::rhumb_line;
    use alloc::vec;

    fn at(latitude: f64, longitude: f64) -> Position {
        Position::from_degrees(latitude, longitude).unwrap()
    }

    #[test]
    fn dead_reckoning_runs_the_distance_it_should() {
        let from = at(50.0, -5.0);
        let course = TrueCourse::new(45.0).unwrap();
        let speed = Speed::from_knots(12.0).unwrap();
        let elapsed = Duration::from_secs(3 * 3600);

        let to = dead_reckoning(from, course, speed, elapsed).unwrap();
        let sailing = rhumb_line(from, to).unwrap();

        assert!((sailing.distance.nautical_miles() - 36.0).abs() < 1e-9);
        assert!(sailing.initial_course.angular_distance(course) < 1e-9);
    }

    #[test]
    fn northing_alone_changes_no_longitude() {
        let from = at(10.0, 20.0);
        let to = dead_reckoning(
            from,
            TrueCourse::NORTH,
            Speed::from_knots(10.0).unwrap(),
            Duration::from_secs(6 * 3600),
        )
        .unwrap();
        assert!((to.longitude().degrees() - 20.0).abs() < 1e-12);
        // Sixty miles of northing is one degree of latitude, near enough.
        assert!((to.latitude().degrees() - 11.0).abs() < 0.01);
    }

    #[test]
    fn a_traverse_adds_up_to_its_legs() {
        let from = at(0.0, 0.0);
        let legs = vec![
            Leg {
                course: TrueCourse::new(0.0).unwrap(),
                distance: Distance::from_nautical_miles(60.0).unwrap(),
            },
            Leg {
                course: TrueCourse::new(90.0).unwrap(),
                distance: Distance::from_nautical_miles(60.0).unwrap(),
            },
            Leg {
                course: TrueCourse::new(180.0).unwrap(),
                distance: Distance::from_nautical_miles(60.0).unwrap(),
            },
        ];

        let end = traverse(from, &legs).unwrap();
        // North then east then south: back on the equator, east of where we began.
        assert!(end.latitude().degrees().abs() < 1e-9);
        assert!(end.longitude().degrees() > 0.9);

        // Running the legs one at a time gives the same answer.
        let mut step = from;
        for leg in &legs {
            step = dead_reckoning_by_distance(step, leg.course, leg.distance).unwrap();
        }
        assert!(rhumb_line(step, end).unwrap().distance.nautical_miles() < 1e-9);

        // An empty traverse goes nowhere.
        assert_eq!(traverse(from, &[]).unwrap(), from);
    }

    #[test]
    fn a_traverse_that_closes_returns_to_its_start() {
        let from = at(45.0, 10.0);
        let there = Leg {
            course: TrueCourse::new(75.0).unwrap(),
            distance: Distance::from_nautical_miles(40.0).unwrap(),
        };
        let back = Leg {
            course: there.course.reciprocal(),
            distance: there.distance,
        };
        let end = traverse(from, &[there, back]).unwrap();
        assert!(rhumb_line(from, end).unwrap().distance.nautical_miles() < 1e-9);
    }

    #[test]
    fn the_current_moves_the_estimated_position_off_the_dead_reckoning() {
        let from = at(50.0, -5.0);
        let heading = TrueCourse::new(270.0).unwrap();
        let speed = Speed::from_knots(12.0).unwrap();
        let elapsed = Duration::from_secs(4 * 3600);

        let reckoned = dead_reckoning(from, heading, speed, elapsed).unwrap();
        let estimated = estimated_position(
            from,
            heading,
            speed,
            Current {
                set: TrueCourse::NORTH,
                drift: Speed::from_knots(1.0).unwrap(),
            },
            elapsed,
        )
        .unwrap();

        // Four hours of one knot northward is four miles of northing.
        let offset = rhumb_line(reckoned, estimated.position).unwrap();
        assert!((offset.distance.nautical_miles() - 4.0).abs() < 0.05);
        assert!(offset.initial_course.angular_distance(TrueCourse::NORTH) < 1.0);
    }

    #[test]
    fn with_no_current_the_estimate_is_the_reckoning() {
        let from = at(-20.0, 100.0);
        let heading = TrueCourse::new(200.0).unwrap();
        let speed = Speed::from_knots(15.0).unwrap();
        let elapsed = Duration::from_secs(7200);

        let reckoned = dead_reckoning(from, heading, speed, elapsed).unwrap();
        let estimated = estimated_position(
            from,
            heading,
            speed,
            Current {
                set: TrueCourse::NORTH,
                drift: Speed::ZERO,
            },
            elapsed,
        )
        .unwrap();

        assert!(
            rhumb_line(reckoned, estimated.position)
                .unwrap()
                .distance
                .nautical_miles()
                < 1e-9
        );
        assert!((estimated.distance_made_good.nautical_miles() - 30.0).abs() < 1e-9);
    }

    #[test]
    fn leeway_is_applied_away_from_the_wind() {
        let heading = TrueCourse::new(0.0).unwrap();
        let leeway = Angle::from_degrees(5.0).unwrap();

        // Wind from the port side pushes the ship to starboard.
        assert_eq!(
            water_track(heading, leeway, TrueCourse::new(270.0).unwrap()).degrees(),
            5.0
        );
        // Wind from starboard pushes her to port.
        assert_eq!(
            water_track(heading, leeway, TrueCourse::new(90.0).unwrap()).degrees(),
            355.0
        );
        // A negative leeway angle means the same thing as a positive one.
        assert_eq!(
            water_track(
                heading,
                Angle::from_degrees(-5.0).unwrap(),
                TrueCourse::new(270.0).unwrap()
            )
            .degrees(),
            5.0
        );
    }

    #[test]
    fn leeway_wraps_through_north() {
        let heading = TrueCourse::new(2.0).unwrap();
        let track = water_track(
            heading,
            Angle::from_degrees(10.0).unwrap(),
            TrueCourse::new(90.0).unwrap(),
        );
        assert!((track.degrees() - 352.0).abs() < 1e-12);
    }

    #[test]
    fn passage_time_and_speed_required_are_inverses() {
        let distance = Distance::from_nautical_miles(150.0).unwrap();
        let speed = Speed::from_knots(12.5).unwrap();
        let elapsed = passage_time(distance, speed).unwrap();
        assert_eq!(elapsed.as_secs(), 12 * 3600);
        assert!((speed_required(distance, elapsed).unwrap().knots() - 12.5).abs() < 1e-9);
    }

    #[test]
    fn impossible_passages_are_errors() {
        let distance = Distance::from_nautical_miles(150.0).unwrap();
        assert!(passage_time(distance, Speed::ZERO).is_err());
        assert!(speed_required(distance, Duration::ZERO).is_err());
    }

    #[test]
    fn a_track_over_the_pole_is_refused_not_fudged() {
        let from = at(89.0, 0.0);
        let result = dead_reckoning(
            from,
            TrueCourse::NORTH,
            Speed::from_knots(30.0).unwrap(),
            Duration::from_secs(10 * 3600),
        );
        assert!(result.is_err());
    }
}
