//! Relative motion: closest approach, radar plotting, and getting out of the way.
//!
//! Everything here is worked in the relative frame, where own ship sits still at
//! the origin and the other vessel does the moving. That is what a radar display
//! shows and what the plotting triangle solves.
//!
//! The geometry is plane. Over the few miles a collision situation develops in,
//! the curvature of the Earth does not come into it.
//!
//! # Example
//!
//! ```rust
//! use bearingpro::relative_motion::{closest_point_of_approach, Approach, Contact, Vessel};
//! use bearingpro::{Distance, NavigationError, Speed, TrueBearing, TrueCourse};
//!
//! fn main() -> Result<(), NavigationError> {
//!     let own = Vessel {
//!         course: TrueCourse::new(0.0)?,
//!         speed: Speed::from_knots(15.0)?,
//!     };
//!     // A ship 10 miles away on the starboard bow, crossing to port.
//!     let contact = Contact {
//!         bearing: TrueBearing::new(30.0)?,
//!         range: Distance::from_nautical_miles(10.0)?,
//!     };
//!     let target = Vessel {
//!         course: TrueCourse::new(270.0)?,
//!         speed: Speed::from_knots(15.0)?,
//!     };
//!
//!     match closest_point_of_approach(own, contact, target)? {
//!         Approach::Closing(cpa) => {
//!             assert_eq!(format!("{:.2}", cpa.distance.nautical_miles()), "2.59");
//!             assert_eq!(cpa.time_to_go.as_secs() / 60, 27);
//!         }
//!         other => panic!("expected a closing contact, got {other:?}"),
//!     }
//!     Ok(())
//! }
//! ```

use core::time::Duration;

use crate::angle::{wrap180, Direction, RelativeBearing, True, TrueBearing, TrueCourse};
use crate::error::{NavigationError, Result};
use crate::math;
use crate::units::{hours, Angle, Distance, Speed};

/// Below this relative speed the contact is treated as holding its position.
const STATIONARY_KNOTS: f64 = 1e-9;

/// A vessel's course and speed through the water.
#[derive(Debug, Clone, Copy, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Vessel {
    /// Course being made good.
    pub course: TrueCourse,
    /// Speed being made good.
    pub speed: Speed,
}

impl Vessel {
    /// The velocity as north and east components, in knots.
    fn velocity(self) -> (f64, f64) {
        let radians = self.course.radians();
        (
            self.speed.knots() * math::cos(radians),
            self.speed.knots() * math::sin(radians),
        )
    }

    /// Builds a vessel from north and east velocity components, in knots.
    fn from_velocity(north: f64, east: f64) -> Self {
        Self {
            course: Direction::<True>::from_degrees_wrapped(math::to_degrees(math::atan2(
                east, north,
            ))),
            speed: Speed::from_knots_unchecked(math::hypot(north, east)),
        }
    }
}

/// Where another vessel is, as seen from own ship.
#[derive(Debug, Clone, Copy, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Contact {
    /// True bearing of the other vessel from own ship.
    pub bearing: TrueBearing,
    /// Distance to the other vessel.
    pub range: Distance,
}

impl Contact {
    /// The contact's position as north and east offsets, in miles.
    fn offset(self) -> (f64, f64) {
        let radians = self.bearing.radians();
        (
            self.range.nautical_miles() * math::cos(radians),
            self.range.nautical_miles() * math::sin(radians),
        )
    }
}

/// The closest the other vessel will come, and when.
#[derive(Debug, Clone, Copy, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Cpa {
    /// Distance at the closest point of approach.
    pub distance: Distance,
    /// Time until it happens.
    pub time_to_go: Duration,
    /// Bearing the other vessel will be on then.
    pub bearing: TrueBearing,
}

/// How the range to another vessel is behaving.
///
/// A closest approach that lies in the past is a different thing from one in the
/// future, and this makes the caller notice the difference.
#[derive(Debug, Clone, Copy, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Approach {
    /// The range is closing; the closest point of approach is ahead.
    Closing(Cpa),
    /// The range is already opening; the closest approach is astern.
    Opening {
        /// The range now, which is the least it will be from here on.
        current_range: Distance,
    },
    /// There is no relative motion: the contact holds its bearing and range.
    Stationary {
        /// The unchanging range.
        range: Distance,
    },
}

/// What a radar plot yields about the other vessel.
#[derive(Debug, Clone, Copy, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TargetSolution {
    /// The other vessel's true course and speed.
    pub vessel: Vessel,
    /// Direction the contact is moving in relative to own ship.
    pub relative_course: TrueCourse,
    /// Speed at which the contact closes along that relative course.
    pub relative_speed: Speed,
    /// Aspect: own ship's bearing from the other vessel, relative to her head.
    ///
    /// Negative means own ship is on the other vessel's port side — red aspect —
    /// and positive means starboard, or green.
    pub aspect: Angle,
}

/// Courses that would open the closest approach to what was asked for.
#[derive(Debug, Clone, Copy, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Avoidance {
    /// The smallest alteration to starboard that achieves it, if one exists.
    pub starboard: Option<TrueCourse>,
    /// The smallest alteration to port that achieves it, if one exists.
    pub port: Option<TrueCourse>,
}

/// The closest the other vessel will come at present courses and speeds.
///
/// # Errors
///
/// Returns [`NavigationError::OutOfRange`] for a negative range, and
/// [`NavigationError::Indeterminate`] if the time to the closest approach is too
/// far off to represent.
pub fn closest_point_of_approach(
    own: Vessel,
    contact: Contact,
    target: Vessel,
) -> Result<Approach> {
    crate::angle::ensure_range("range", contact.range.nautical_miles(), 0.0, f64::MAX)?;

    let (offset_north, offset_east) = contact.offset();
    let (relative_north, relative_east) = relative_velocity(own, target);
    let relative_speed = math::hypot(relative_north, relative_east);

    if relative_speed < STATIONARY_KNOTS {
        return Ok(Approach::Stationary {
            range: contact.range,
        });
    }

    // The closest approach is where the relative track is nearest the origin.
    let closing_rate = offset_north * relative_north + offset_east * relative_east;
    let time = -closing_rate / (relative_speed * relative_speed);

    if time <= 0.0 {
        return Ok(Approach::Opening {
            current_range: contact.range,
        });
    }

    let (closest_north, closest_east) = (
        offset_north + relative_north * time,
        offset_east + relative_east * time,
    );

    Ok(Approach::Closing(Cpa {
        distance: Distance::from_nautical_miles_unchecked(math::hypot(closest_north, closest_east)),
        time_to_go: crate::units::duration_from_hours(time)?,
        bearing: Direction::<True>::from_degrees_wrapped(math::to_degrees(math::atan2(
            closest_east,
            closest_north,
        ))),
    }))
}

/// The other vessel's course and speed, from two plots of her and the time between.
///
/// The radar plotting triangle: the relative movement between the two plots gives
/// the relative velocity, and own ship's velocity added to it gives the other
/// vessel's.
///
/// # Errors
///
/// - [`NavigationError::OutOfRange`] for a negative range.
/// - [`NavigationError::Indeterminate`] if no time passed between the plots.
///
/// # Example
///
/// ```rust
/// use bearingpro::relative_motion::{target_from_plot, Contact, Vessel};
/// use bearingpro::{Distance, NavigationError, Speed, TrueBearing, TrueCourse};
/// use core::time::Duration;
///
/// fn main() -> Result<(), NavigationError> {
///     let own = Vessel {
///         course: TrueCourse::new(0.0)?,
///         speed: Speed::from_knots(10.0)?,
///     };
///     // Two plots six minutes apart.
///     let first = Contact {
///         bearing: TrueBearing::new(90.0)?,
///         range: Distance::from_nautical_miles(6.0)?,
///     };
///     let second = Contact {
///         bearing: TrueBearing::new(90.0)?,
///         range: Distance::from_nautical_miles(5.0)?,
///     };
///
///     let solution = target_from_plot(own, first, second, Duration::from_secs(360))?;
///
///     // She closes straight down the bearing at 10 knots while we make 10 to
///     // the north, so her own course must be 315 at just over 14 knots.
///     assert_eq!(format!("{:.1}", solution.vessel.course.degrees()), "315.0");
///     assert_eq!(format!("{:.2}", solution.vessel.speed.knots()), "14.14");
///
///     // We lie 45° on her port bow.
///     assert_eq!(format!("{:.1}", solution.aspect.degrees()), "-45.0");
///     Ok(())
/// }
/// ```
pub fn target_from_plot(
    own: Vessel,
    first: Contact,
    second: Contact,
    elapsed: Duration,
) -> Result<TargetSolution> {
    crate::angle::ensure_range("range", first.range.nautical_miles(), 0.0, f64::MAX)?;
    crate::angle::ensure_range("range", second.range.nautical_miles(), 0.0, f64::MAX)?;

    let interval = hours(elapsed);
    if interval <= 0.0 {
        return Err(NavigationError::Indeterminate {
            quantity: "a target's motion between two plots at the same moment",
        });
    }

    let (first_north, first_east) = first.offset();
    let (second_north, second_east) = second.offset();
    let (relative_north, relative_east) = (
        (second_north - first_north) / interval,
        (second_east - first_east) / interval,
    );

    let (own_north, own_east) = own.velocity();
    let vessel = Vessel::from_velocity(relative_north + own_north, relative_east + own_east);

    // Aspect: where own ship lies relative to the other vessel's head.
    let own_bearing_from_target = second.bearing.reciprocal();
    let aspect = Angle::from_degrees_unchecked(wrap180(
        own_bearing_from_target.degrees() - vessel.course.degrees(),
    ));

    Ok(TargetSolution {
        vessel,
        relative_course: Direction::<True>::from_degrees_wrapped(math::to_degrees(math::atan2(
            relative_east,
            relative_north,
        ))),
        relative_speed: Speed::from_knots_unchecked(math::hypot(relative_north, relative_east)),
        aspect,
    })
}

/// How far ahead the other vessel will cross own ship's track.
///
/// The bow crossing range: the distance from own ship, along her heading, to the
/// point where the other vessel cuts across it.
///
/// # Errors
///
/// - [`NavigationError::OutOfRange`] for a negative range.
/// - [`NavigationError::NoSolution`] if the other vessel never crosses ahead —
///   she is going the same way, or will pass astern.
pub fn bow_crossing_range(own: Vessel, contact: Contact, target: Vessel) -> Result<Distance> {
    crate::angle::ensure_range("range", contact.range.nautical_miles(), 0.0, f64::MAX)?;

    let (offset_north, offset_east) = contact.offset();
    let (relative_north, relative_east) = relative_velocity(own, target);
    let heading = own.course.radians();
    let (ahead_north, ahead_east) = (math::cos(heading), math::sin(heading));

    // Solve offset + relative·t = ahead·s for the time t and the range ahead s.
    let determinant = relative_north * (-ahead_east) - relative_east * (-ahead_north);
    if math::abs(determinant) < 1e-12 {
        return Err(NavigationError::NoSolution {
            context: "a crossing of own ship's track by a contact moving along it",
        });
    }

    let time = (-offset_north * -ahead_east + offset_east * -ahead_north) / determinant;
    let range_ahead = (relative_east * offset_north - relative_north * offset_east) / determinant;

    // A range ahead of zero means she passes over own ship, which is very much a
    // crossing ahead; only a negative one is astern. The tolerance is scaled to
    // the range, because a crossing exactly over the bow comes out of the
    // arithmetic as a very small number of either sign.
    let tolerance = contact.range.nautical_miles() * 1e-9;
    if time <= 0.0 || range_ahead < -tolerance {
        return Err(NavigationError::NoSolution {
            context: "a crossing ahead of own ship",
        });
    }

    let range_ahead = range_ahead.max(0.0);

    Ok(Distance::from_nautical_miles_unchecked(range_ahead))
}

/// The courses own ship could steer, at unchanged speed, to open the closest
/// approach to at least the distance asked for.
///
/// The manoeuvre a radar plot is worked for. Two limiting relative tracks just
/// graze the circle of the required passing distance; each is reached by its own
/// alteration, and the smallest one to each side is returned. Under the collision
/// regulations an alteration to starboard is usually the one to make, and it is
/// [`Avoidance::starboard`].
///
/// # Errors
///
/// - [`NavigationError::OutOfRange`] for a negative range or distance.
/// - [`NavigationError::NoSolution`] if the contact is already closer than the
///   distance asked for, or if no alteration at this speed can achieve it.
///
/// # Example
///
/// ```rust
/// use bearingpro::relative_motion::{closest_point_of_approach, course_for_cpa, Approach, Contact, Vessel};
/// use bearingpro::{Distance, NavigationError, Speed, TrueBearing, TrueCourse};
///
/// fn main() -> Result<(), NavigationError> {
///     let own = Vessel {
///         course: TrueCourse::new(0.0)?,
///         speed: Speed::from_knots(15.0)?,
///     };
///     let contact = Contact {
///         bearing: TrueBearing::new(10.0)?,
///         range: Distance::from_nautical_miles(8.0)?,
///     };
///     let target = Vessel {
///         course: TrueCourse::new(190.0)?,
///         speed: Speed::from_knots(12.0)?,
///     };
///
///     // As things stand she will pass very close.
///     let Approach::Closing(before) = closest_point_of_approach(own, contact, target)? else {
///         panic!("she is closing");
///     };
///     assert!(before.distance.nautical_miles() < 1.5);
///
///     // Two miles is wanted instead.
///     let wanted = Distance::from_nautical_miles(2.0)?;
///     let avoidance = course_for_cpa(own, contact, target, wanted)?;
///     let altered = avoidance.starboard.expect("a starboard alteration exists");
///
///     let after = closest_point_of_approach(
///         Vessel { course: altered, speed: own.speed },
///         contact,
///         target,
///     )?;
///     let Approach::Closing(after) = after else {
///         panic!("still closing, just further off");
///     };
///     assert!((after.distance.nautical_miles() - 2.0).abs() < 1e-6);
///     Ok(())
/// }
/// ```
pub fn course_for_cpa(
    own: Vessel,
    contact: Contact,
    target: Vessel,
    desired: Distance,
) -> Result<Avoidance> {
    crate::angle::ensure_range("range", contact.range.nautical_miles(), 0.0, f64::MAX)?;
    crate::angle::ensure_range("desired distance", desired.nautical_miles(), 0.0, f64::MAX)?;

    let range = contact.range.nautical_miles();
    let wanted = desired.nautical_miles();
    if range <= wanted {
        return Err(NavigationError::NoSolution {
            context: "opening a contact that is already inside the distance asked for",
        });
    }
    if own.speed.knots() <= 0.0 {
        return Err(NavigationError::NoSolution {
            context: "a manoeuvre by a vessel that is not moving",
        });
    }

    // The relative track must graze the circle of radius `wanted` about own ship,
    // so it must leave the contact's bearing by this much.
    let grazing = math::to_degrees(math::asin((wanted / range).clamp(-1.0, 1.0)));
    let away = contact.bearing.degrees() + 180.0;
    let (target_north, target_east) = target.velocity();
    let own_speed = own.speed.knots();

    let mut candidates: [Option<f64>; 4] = [None; 4];
    let mut count = 0;

    for relative_course in [away - grazing, away + grazing] {
        let radians = math::to_radians(relative_course);
        let (unit_north, unit_east) = (math::cos(radians), math::sin(radians));

        // Own velocity must be target velocity minus some positive multiple of
        // the required relative direction, and must have the right magnitude.
        let projection = target_north * unit_north + target_east * unit_east;
        let target_speed_squared = target_north * target_north + target_east * target_east;
        let discriminant = projection * projection - (target_speed_squared - own_speed * own_speed);
        if discriminant < 0.0 {
            continue;
        }
        let root = math::sqrt(discriminant);

        for relative_speed in [projection + root, projection - root] {
            if relative_speed <= 0.0 {
                continue;
            }
            let north = target_north - relative_speed * unit_north;
            let east = target_east - relative_speed * unit_east;
            if let Some(slot) = candidates.get_mut(count) {
                *slot = Some(math::to_degrees(math::atan2(east, north)));
            }
            count += 1;
        }
    }

    let mut starboard: Option<(f64, f64)> = None;
    let mut port: Option<(f64, f64)> = None;
    for candidate in candidates.iter().flatten() {
        let alteration = wrap180(candidate - own.course.degrees());
        if alteration > 0.0 {
            if starboard.map_or(true, |(best, _)| alteration < best) {
                starboard = Some((alteration, *candidate));
            }
        } else if alteration < 0.0 && port.map_or(true, |(best, _)| alteration > best) {
            port = Some((alteration, *candidate));
        }
    }

    if starboard.is_none() && port.is_none() {
        return Err(NavigationError::NoSolution {
            context: "a course at this speed that opens the closest approach that far",
        });
    }

    Ok(Avoidance {
        starboard: starboard.map(|(_, course)| Direction::<True>::from_degrees_wrapped(course)),
        port: port.map(|(_, course)| Direction::<True>::from_degrees_wrapped(course)),
    })
}

/// The relative bearing of a contact from own ship's head.
#[must_use]
pub fn relative_bearing_of(own: Vessel, contact: Contact) -> RelativeBearing {
    RelativeBearing::from_degrees_wrapped(contact.bearing.degrees() - own.course.degrees())
}

/// Relative velocity of the target with respect to own ship, in knots north and east.
fn relative_velocity(own: Vessel, target: Vessel) -> (f64, f64) {
    let (own_north, own_east) = own.velocity();
    let (target_north, target_east) = target.velocity();
    (target_north - own_north, target_east - own_east)
}

#[cfg(test)]
#[allow(
    clippy::unwrap_used,
    clippy::float_cmp,
    clippy::indexing_slicing,
    clippy::panic
)]
mod tests {
    use super::*;
    use alloc::format;

    fn vessel(course: f64, knots: f64) -> Vessel {
        Vessel {
            course: TrueCourse::new(course).unwrap(),
            speed: Speed::from_knots(knots).unwrap(),
        }
    }

    fn contact(bearing: f64, range: f64) -> Contact {
        Contact {
            bearing: TrueBearing::new(bearing).unwrap(),
            range: Distance::from_nautical_miles(range).unwrap(),
        }
    }

    fn closing(approach: Approach) -> Cpa {
        match approach {
            Approach::Closing(cpa) => cpa,
            other => panic!("expected a closing contact, got {other:?}"),
        }
    }

    #[test]
    fn a_head_on_contact_closes_to_nothing() {
        // Dead ahead, coming straight at us: CPA is zero, and soon.
        let own = vessel(0.0, 10.0);
        let target = vessel(180.0, 10.0);
        let cpa = closing(closest_point_of_approach(own, contact(0.0, 10.0), target).unwrap());

        assert!(cpa.distance.nautical_miles() < 1e-9);
        // Twenty knots of closing over ten miles is half an hour.
        assert!((cpa.time_to_go.as_secs_f64() - 1800.0).abs() < 1e-6);
    }

    #[test]
    fn a_contact_abeam_on_a_parallel_course_never_closes() {
        let own = vessel(0.0, 12.0);
        let target = vessel(0.0, 12.0);
        let approach = closest_point_of_approach(own, contact(90.0, 3.0), target).unwrap();
        assert!(matches!(approach, Approach::Stationary { .. }));
    }

    #[test]
    fn a_contact_astern_and_slower_is_opening() {
        let own = vessel(0.0, 20.0);
        let target = vessel(0.0, 8.0);
        let approach = closest_point_of_approach(own, contact(180.0, 4.0), target).unwrap();
        match approach {
            Approach::Opening { current_range } => {
                assert_eq!(current_range.nautical_miles(), 4.0);
            }
            other => panic!("expected an opening contact, got {other:?}"),
        }
    }

    #[test]
    fn the_cpa_matches_a_hand_worked_crossing() {
        // Own 000 at 15, contact 030 at 10 miles steering 270 at 15.
        let own = vessel(0.0, 15.0);
        let target = vessel(270.0, 15.0);
        let cpa = closing(closest_point_of_approach(own, contact(30.0, 10.0), target).unwrap());

        // Worked by hand: relative velocity (−15, −15) from an offset of
        // (8.660, 5.000) gives a CPA of 2.5882 miles in 27.32 minutes.
        assert_eq!(format!("{:.4}", cpa.distance.nautical_miles()), "2.5882");
        assert!((cpa.time_to_go.as_secs_f64() / 60.0 - 27.3205).abs() < 1e-3);
        assert!((cpa.bearing.degrees() - 315.0).abs() < 1e-9);
    }

    #[test]
    fn the_cpa_is_really_the_closest_the_contact_comes() {
        let own = vessel(20.0, 14.0);
        let target = vessel(250.0, 9.0);
        let start = contact(65.0, 12.0);
        let cpa = closing(closest_point_of_approach(own, start, target).unwrap());

        // Step the relative track along and confirm nothing beats the answer.
        let (north, east) = start.offset();
        let (relative_north, relative_east) = relative_velocity(own, target);
        let mut time = 0.0;
        while time < 3.0 {
            let range = math::hypot(north + relative_north * time, east + relative_east * time);
            assert!(
                range >= cpa.distance.nautical_miles() - 1e-9,
                "at {time} h the range is {range}, inside the CPA"
            );
            time += 0.001;
        }
    }

    #[test]
    fn a_plot_recovers_the_target_that_made_it() {
        let own = vessel(35.0, 16.0);
        let target = vessel(300.0, 11.0);
        let first = contact(80.0, 9.0);

        // Where the contact will be twelve minutes later.
        let elapsed = Duration::from_secs(720);
        let interval = hours(elapsed);
        let (north, east) = first.offset();
        let (relative_north, relative_east) = relative_velocity(own, target);
        let (later_north, later_east) = (
            north + relative_north * interval,
            east + relative_east * interval,
        );
        let second = Contact {
            bearing: TrueBearing::wrap(math::to_degrees(math::atan2(later_east, later_north)))
                .unwrap(),
            range: Distance::from_nautical_miles(math::hypot(later_north, later_east)).unwrap(),
        };

        let solution = target_from_plot(own, first, second, elapsed).unwrap();
        assert!(solution.vessel.course.angular_distance(target.course) < 1e-9);
        assert!((solution.vessel.speed.knots() - target.speed.knots()).abs() < 1e-9);
        assert!(solution.relative_speed.knots() > 0.0);
    }

    #[test]
    fn a_plot_needs_time_to_have_passed() {
        let own = vessel(0.0, 10.0);
        assert!(matches!(
            target_from_plot(own, contact(90.0, 6.0), contact(90.0, 5.0), Duration::ZERO)
                .unwrap_err(),
            NavigationError::Indeterminate { .. }
        ));
    }

    #[test]
    fn aspect_says_which_side_of_the_target_we_are_on() {
        // She closes straight down the bearing while we make 10 knots north, so
        // her course is 315 and we lie 45° on her port bow.
        let own = vessel(0.0, 10.0);
        let solution = target_from_plot(
            own,
            contact(90.0, 6.0),
            contact(90.0, 5.0),
            Duration::from_secs(360),
        )
        .unwrap();
        assert!((solution.vessel.course.degrees() - 315.0).abs() < 1e-9);
        assert!((solution.aspect.degrees() + 45.0).abs() < 1e-9);

        // With own ship stopped, the contact's relative track is her true one, so
        // a target closing from due east must be steering due west, and we are
        // dead ahead of her.
        let stopped = target_from_plot(
            vessel(0.0, 0.0),
            contact(90.0, 6.0),
            contact(90.0, 5.0),
            Duration::from_secs(360),
        )
        .unwrap();
        assert!((stopped.vessel.course.degrees() - 270.0).abs() < 1e-9);
        assert!(stopped.aspect.degrees().abs() < 1e-9);
    }

    #[test]
    fn a_crosser_cuts_ahead_at_a_computable_range() {
        // She is 10 miles due east, steering due west at 10 knots; we are stopped.
        let own = vessel(0.0, 0.0);
        let target = vessel(270.0, 10.0);
        let range = bow_crossing_range(own, contact(90.0, 10.0), target).unwrap();
        // Crossing our heading line at the origin: she passes right over us.
        assert!(range.nautical_miles() < 1e-9);

        // Offset her to the north-east and she crosses ahead.
        let target = vessel(270.0, 10.0);
        let ahead = bow_crossing_range(own, contact(45.0, 10.0), target).unwrap();
        assert!((ahead.nautical_miles() - 10.0 * (45.0_f64).to_radians().cos()).abs() < 1e-9);
    }

    #[test]
    fn a_contact_that_never_crosses_ahead_is_reported() {
        let own = vessel(0.0, 10.0);
        // Astern and going the other way: she will not cross ahead.
        let target = vessel(180.0, 10.0);
        assert!(matches!(
            bow_crossing_range(own, contact(180.0, 5.0), target).unwrap_err(),
            NavigationError::NoSolution { .. }
        ));

        // Moving straight along our heading line: no single crossing point.
        let same_way = vessel(0.0, 12.0);
        assert!(bow_crossing_range(own, contact(0.0, 5.0), same_way).is_err());
    }

    #[test]
    fn an_alteration_achieves_the_closest_approach_it_promises() {
        let own = vessel(0.0, 15.0);
        let target = vessel(190.0, 12.0);
        let start = contact(10.0, 8.0);
        let wanted = Distance::from_nautical_miles(2.0).unwrap();

        let avoidance = course_for_cpa(own, start, target, wanted).unwrap();
        for course in [avoidance.starboard, avoidance.port].into_iter().flatten() {
            let altered = Vessel {
                course,
                speed: own.speed,
            };
            let cpa = closing(closest_point_of_approach(altered, start, target).unwrap());
            assert!(
                (cpa.distance.nautical_miles() - 2.0).abs() < 1e-6,
                "steering {} gives a CPA of {}",
                course.degrees(),
                cpa.distance.nautical_miles()
            );
        }
    }

    #[test]
    fn alterations_are_found_on_both_bows_for_a_range_of_situations() {
        let own = vessel(0.0, 15.0);
        let wanted = Distance::from_nautical_miles(2.0).unwrap();

        for bearing in [5.0, 30.0, 60.0, 300.0, 330.0] {
            for target_course in [90.0, 180.0, 200.0, 270.0] {
                let target = vessel(target_course, 12.0);
                let start = contact(bearing, 8.0);
                let Ok(avoidance) = course_for_cpa(own, start, target, wanted) else {
                    continue;
                };
                assert!(
                    avoidance.starboard.is_some() || avoidance.port.is_some(),
                    "an empty avoidance should have been an error"
                );
                for course in [avoidance.starboard, avoidance.port].into_iter().flatten() {
                    let altered = Vessel {
                        course,
                        speed: own.speed,
                    };
                    match closest_point_of_approach(altered, start, target).unwrap() {
                        Approach::Closing(cpa) => assert!(
                            cpa.distance.nautical_miles() >= 2.0 - 1e-6,
                            "bearing {bearing}, target {target_course}: CPA {}",
                            cpa.distance.nautical_miles()
                        ),
                        // Opening at once is even better than the distance asked for.
                        Approach::Opening { .. } | Approach::Stationary { .. } => {}
                    }
                }
            }
        }
    }

    #[test]
    fn a_manoeuvre_that_cannot_work_is_reported() {
        let own = vessel(0.0, 15.0);
        let target = vessel(180.0, 12.0);

        // Already inside the distance asked for.
        assert!(matches!(
            course_for_cpa(
                own,
                contact(0.0, 1.0),
                target,
                Distance::from_nautical_miles(2.0).unwrap()
            )
            .unwrap_err(),
            NavigationError::NoSolution { .. }
        ));

        // Stopped, so no alteration is available at all.
        assert!(course_for_cpa(
            vessel(0.0, 0.0),
            contact(0.0, 8.0),
            target,
            Distance::from_nautical_miles(2.0).unwrap()
        )
        .is_err());

        // A slow ship cannot open a fast one as far as it might like.
        let slow = vessel(0.0, 2.0);
        let fast = vessel(0.0, 30.0);
        assert!(course_for_cpa(
            slow,
            contact(180.0, 3.0),
            fast,
            Distance::from_nautical_miles(2.9).unwrap()
        )
        .is_err());
    }

    #[test]
    fn relative_bearing_is_measured_from_the_head() {
        let own = vessel(45.0, 10.0);
        assert_eq!(relative_bearing_of(own, contact(90.0, 5.0)).degrees(), 45.0);
        assert_eq!(relative_bearing_of(own, contact(0.0, 5.0)).degrees(), 315.0);
    }

    #[test]
    fn hostile_input_is_refused_not_panicked_on() {
        let own = vessel(0.0, 10.0);
        let target = vessel(180.0, 10.0);
        let negative = Contact {
            bearing: TrueBearing::NORTH,
            range: Distance::from_nautical_miles(-1.0).unwrap(),
        };
        assert!(closest_point_of_approach(own, negative, target).is_err());
        assert!(bow_crossing_range(own, negative, target).is_err());
        assert!(course_for_cpa(own, negative, target, Distance::ZERO).is_err());
        assert!(course_for_cpa(
            own,
            contact(0.0, 5.0),
            target,
            Distance::from_nautical_miles(-1.0).unwrap()
        )
        .is_err());

        // An enormous range still gives an answer rather than an overflow.
        let far = contact(0.0, 1e6);
        assert!(closest_point_of_approach(own, far, target).is_ok());
    }
}
