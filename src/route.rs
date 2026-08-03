//! Passage planning: a chain of waypoints, and where you are along it.
//!
//! A [`Route`] is an ordered list of positions and the kind of track between
//! them. It answers the three questions a passage plan is made of: how far, how
//! long, and — once the ship is underway — how is she doing.
//!
//! # Example
//!
//! ```rust
//! use bearingpro::route::{LegKind, Route};
//! use bearingpro::{NavigationError, Position, Speed};
//!
//! fn main() -> Result<(), NavigationError> {
//!     let route = Route::new(
//!         vec![
//!             "50°06.0'N 001°30.0'W".parse::<Position>()?,
//!             "49°54.0'N 002°00.0'W".parse::<Position>()?,
//!             "49°42.0'N 002°45.0'W".parse::<Position>()?,
//!         ],
//!         LegKind::RhumbLine,
//!     )?;
//!
//!     assert_eq!(route.legs()?.len(), 2);
//!     assert_eq!(format!("{:.1}", route.total_distance()?.nautical_miles()), "54.2");
//!
//!     // At ten knots, how long is the passage?
//!     let elapsed = route.passage_time(Speed::from_knots(10.0)?)?;
//!     assert_eq!(elapsed.as_secs() / 60, 325);
//!     Ok(())
//! }
//! ```

use alloc::vec::Vec;
use core::time::Duration;

use crate::angle::TrueCourse;
use crate::error::{NavigationError, Result};
use crate::position::Position;
use crate::sailings::{
    cross_track, great_circle, great_circle_waypoints, rhumb_line, CrossTrack, Sailing,
};
use crate::units::{Distance, Speed};

/// What kind of track joins one waypoint to the next.
///
/// This enum is `#[non_exhaustive]`; match with a wildcard arm.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
#[non_exhaustive]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum LegKind {
    /// One course from waypoint to waypoint. What a ship actually steers.
    #[default]
    RhumbLine,
    /// The shortest track, whose course changes the whole way.
    ///
    /// Useful for measuring a passage; to steer it, break it into rhumb legs
    /// with [`Route::split_legs`].
    GreatCircle,
}

/// One leg of a route.
#[derive(Debug, Clone, Copy, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct RouteLeg {
    /// Which leg this is, counting from zero.
    pub index: usize,
    /// Where it starts.
    pub from: Position,
    /// Where it ends.
    pub to: Position,
    /// Course and distance along it.
    pub sailing: Sailing,
}

/// Where a ship is in relation to a route.
#[derive(Debug, Clone, Copy, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Progress {
    /// Index of the leg the ship is judged to be on.
    pub leg: usize,
    /// How far off that leg she is, and how far along it.
    pub cross_track: CrossTrack,
    /// Course to steer straight for the next waypoint.
    pub course_to_next: TrueCourse,
    /// Distance direct to the next waypoint.
    pub distance_to_next: Distance,
    /// Distance to the end of the route: the rest of this leg, plus the ones after.
    pub distance_to_end: Distance,
}

/// A planned passage.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(
    feature = "serde",
    derive(serde::Serialize, serde::Deserialize),
    serde(try_from = "StoredRoute", into = "StoredRoute")
)]
pub struct Route {
    waypoints: Vec<Position>,
    kind: LegKind,
}

impl Route {
    /// Builds a route from an ordered list of waypoints.
    ///
    /// # Errors
    ///
    /// Returns [`NavigationError::InsufficientNodes`] for fewer than two
    /// waypoints, since one position is a destination and not a passage.
    pub fn new(waypoints: Vec<Position>, kind: LegKind) -> Result<Self> {
        if waypoints.len() < 2 {
            return Err(NavigationError::InsufficientNodes {
                found: waypoints.len(),
                required: 2,
                context: "a route",
            });
        }
        Ok(Self { waypoints, kind })
    }

    /// The waypoints, in order.
    #[must_use]
    pub fn waypoints(&self) -> &[Position] {
        &self.waypoints
    }

    /// What kind of track joins the waypoints.
    #[must_use]
    pub const fn kind(&self) -> LegKind {
        self.kind
    }

    /// How many legs the route has: one fewer than the waypoints.
    #[must_use]
    pub fn leg_count(&self) -> usize {
        self.waypoints.len().saturating_sub(1)
    }

    /// The legs, each with its course and distance.
    ///
    /// # Errors
    ///
    /// Propagates a sailing failure, notably a rhumb line through a pole.
    pub fn legs(&self) -> Result<Vec<RouteLeg>> {
        self.waypoints
            .windows(2)
            .enumerate()
            .map(|(index, pair)| {
                let (from, to) = pair_of(pair)?;
                Ok(RouteLeg {
                    index,
                    from,
                    to,
                    sailing: self.sail(from, to)?,
                })
            })
            .collect()
    }

    /// Total distance from the first waypoint to the last.
    ///
    /// # Errors
    ///
    /// As [`Route::legs`].
    pub fn total_distance(&self) -> Result<Distance> {
        let mut total = 0.0;
        for pair in self.waypoints.windows(2) {
            let (from, to) = pair_of(pair)?;
            total += self.sail(from, to)?.distance.nautical_miles();
        }
        Ok(Distance::from_nautical_miles_unchecked(total))
    }

    /// How long the passage takes at a given speed.
    ///
    /// # Errors
    ///
    /// As [`Route::legs`], plus [`NavigationError::Indeterminate`] if the speed
    /// is zero or runs the wrong way.
    pub fn passage_time(&self, speed: Speed) -> Result<Duration> {
        speed.time_to_cover(self.total_distance()?)
    }

    /// The speed needed to run the whole route in a given time.
    ///
    /// # Errors
    ///
    /// As [`Route::legs`], plus [`NavigationError::Indeterminate`] if no time is
    /// allowed.
    pub fn speed_required(&self, available: Duration) -> Result<Speed> {
        crate::dead_reckoning::speed_required(self.total_distance()?, available)
    }

    /// The same route with every leg broken into pieces no longer than `interval`.
    ///
    /// This is how a great-circle route is made steerable: each piece is short
    /// enough that holding one course over it costs nothing worth having.
    ///
    /// # Errors
    ///
    /// - [`NavigationError::OutOfRange`] if `interval` is not positive, or is so
    ///   small that the route would not fit in memory.
    /// - Propagates a sailing failure.
    pub fn split_legs(&self, interval: Distance) -> Result<Self> {
        let mut waypoints = Vec::with_capacity(self.waypoints.len());
        for (index, pair) in self.waypoints.windows(2).enumerate() {
            let (from, to) = pair_of(pair)?;
            let pieces = match self.kind {
                LegKind::GreatCircle => great_circle_waypoints(from, to, interval)?,
                // A rhumb leg is already one course; still split it, so that a
                // route can be given a uniform maximum leg length.
                LegKind::RhumbLine => rhumb_waypoints(from, to, interval)?,
            };
            // Every piece but the first of each leg, so joins are not repeated.
            let skip = usize::from(index > 0);
            waypoints.extend(pieces.into_iter().skip(skip));
        }
        Self::new(waypoints, LegKind::RhumbLine)
    }

    /// Where a position is in relation to the route.
    ///
    /// The leg chosen is the one the ship is actually on — the first whose
    /// along-track distance falls within it. If she is off the end of every leg,
    /// the nearest leg is used instead, so the answer is always about something.
    ///
    /// # Errors
    ///
    /// Propagates a sailing failure, and returns
    /// [`NavigationError::Indeterminate`] if a leg has no length.
    pub fn progress(&self, position: Position) -> Result<Progress> {
        let mut best: Option<(usize, CrossTrack, bool)> = None;

        for (index, pair) in self.waypoints.windows(2).enumerate() {
            let (from, to) = pair_of(pair)?;
            let offset = cross_track(position, from, to)?;
            let leg_length = self.sail(from, to)?.distance.nautical_miles();
            let within = offset.along_track.nautical_miles() >= 0.0
                && offset.along_track.nautical_miles() <= leg_length;

            let better = match &best {
                None => true,
                Some((_, previous, previous_within)) => {
                    // A leg the ship is actually on always beats one she is not.
                    match (within, previous_within) {
                        (true, false) => true,
                        (false, true) => false,
                        _ => offset.distance.nautical_miles() < previous.distance.nautical_miles(),
                    }
                }
            };
            if better {
                best = Some((index, offset, within));
            }
        }

        let (leg, offset, _) = best.ok_or(NavigationError::InsufficientNodes {
            found: self.waypoints.len(),
            required: 2,
            context: "a route",
        })?;

        let next = self
            .waypoints
            .get(leg + 1)
            .copied()
            .ok_or(NavigationError::Indeterminate {
                quantity: "the waypoint after the last one",
            })?;
        let to_next = self.sail(position, next)?;

        // The rest of this leg, then the whole of every leg after it.
        let mut remaining = to_next.distance.nautical_miles();
        for pair in self.waypoints.windows(2).skip(leg + 1) {
            let (from, to) = pair_of(pair)?;
            remaining += self.sail(from, to)?.distance.nautical_miles();
        }

        Ok(Progress {
            leg,
            cross_track: offset,
            course_to_next: to_next.initial_course,
            distance_to_next: to_next.distance,
            distance_to_end: Distance::from_nautical_miles_unchecked(remaining),
        })
    }

    /// The sailing between two points, of whatever kind this route uses.
    fn sail(&self, from: Position, to: Position) -> Result<Sailing> {
        match self.kind {
            LegKind::RhumbLine => rhumb_line(from, to),
            LegKind::GreatCircle => great_circle(from, to),
        }
    }
}

/// How a route is written down, so that reading one back checks its invariant.
#[cfg(feature = "serde")]
#[derive(serde::Serialize, serde::Deserialize)]
struct StoredRoute {
    waypoints: Vec<Position>,
    kind: LegKind,
}

#[cfg(feature = "serde")]
impl TryFrom<StoredRoute> for Route {
    type Error = NavigationError;

    /// Read back through [`Route::new`], so a stored route with fewer than two
    /// waypoints is rejected rather than trusted.
    fn try_from(stored: StoredRoute) -> Result<Self> {
        Self::new(stored.waypoints, stored.kind)
    }
}

#[cfg(feature = "serde")]
impl From<Route> for StoredRoute {
    fn from(route: Route) -> Self {
        Self {
            waypoints: route.waypoints,
            kind: route.kind,
        }
    }
}

/// Splits a rhumb leg into pieces no longer than `interval`.
fn rhumb_waypoints(from: Position, to: Position, interval: Distance) -> Result<Vec<Position>> {
    if interval.nautical_miles() <= 0.0 {
        return Err(NavigationError::OutOfRange {
            parameter: "interval",
            value: interval.nautical_miles(),
            min: f64::MIN_POSITIVE,
            max: f64::MAX,
        });
    }

    let sailing = rhumb_line(from, to)?;
    let total = sailing.distance.nautical_miles();
    let pieces = crate::math::ceil(total / interval.nautical_miles()).max(1.0);
    if pieces > 1e6 {
        return Err(NavigationError::OutOfRange {
            parameter: "interval",
            value: interval.nautical_miles(),
            min: total / 1e6,
            max: f64::MAX,
        });
    }

    let count = crate::math::to_usize(pieces);
    let mut waypoints = Vec::with_capacity(count + 1);
    for step in 0..=count {
        let run = total * crate::math::count_to_f64(step) / pieces;
        waypoints.push(crate::sailings::rhumb_destination(
            from,
            sailing.initial_course,
            Distance::from_nautical_miles_unchecked(run),
        )?);
    }
    Ok(waypoints)
}

/// Pulls the two positions out of a `windows(2)` slice.
fn pair_of(pair: &[Position]) -> Result<(Position, Position)> {
    match (pair.first(), pair.last()) {
        (Some(from), Some(to)) => Ok((*from, *to)),
        _ => Err(NavigationError::InsufficientNodes {
            found: pair.len(),
            required: 2,
            context: "a route leg",
        }),
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::float_cmp, clippy::indexing_slicing)]
mod tests {
    use super::*;
    use crate::sailings::TrackSide;
    use alloc::vec;

    fn at(latitude: f64, longitude: f64) -> Position {
        Position::from_degrees(latitude, longitude).unwrap()
    }

    fn square() -> Route {
        // Sixty miles north, then sixty east, then sixty south.
        Route::new(
            vec![at(0.0, 0.0), at(1.0, 0.0), at(1.0, 1.0), at(0.0, 1.0)],
            LegKind::RhumbLine,
        )
        .unwrap()
    }

    #[test]
    fn a_route_needs_somewhere_to_go() {
        assert!(matches!(
            Route::new(vec![], LegKind::RhumbLine).unwrap_err(),
            NavigationError::InsufficientNodes { found: 0, .. }
        ));
        assert!(Route::new(vec![at(0.0, 0.0)], LegKind::RhumbLine).is_err());
        assert!(Route::new(vec![at(0.0, 0.0), at(1.0, 0.0)], LegKind::RhumbLine).is_ok());
    }

    #[test]
    fn legs_and_distances_add_up() {
        let route = square();
        assert_eq!(route.leg_count(), 3);

        let legs = route.legs().unwrap();
        assert_eq!(legs.len(), 3);
        assert_eq!(legs[0].index, 0);
        assert!(legs[0].sailing.initial_course.degrees().abs() < 1e-9);
        assert!((legs[1].sailing.initial_course.degrees() - 90.0).abs() < 1e-9);
        assert!((legs[2].sailing.initial_course.degrees() - 180.0).abs() < 1e-9);

        let summed: f64 = legs
            .iter()
            .map(|leg| leg.sailing.distance.nautical_miles())
            .sum();
        assert!((summed - route.total_distance().unwrap().nautical_miles()).abs() < 1e-9);
        // Sixty miles up, sixty across at the equator-ish, sixty down.
        assert!((summed - 180.0).abs() < 0.2);
    }

    #[test]
    fn the_schedule_works_both_ways() {
        let route = square();
        let speed = Speed::from_knots(12.0).unwrap();
        let elapsed = route.passage_time(speed).unwrap();
        let required = route.speed_required(elapsed).unwrap();
        assert!((required.knots() - 12.0).abs() < 1e-6);

        assert!(route.passage_time(Speed::ZERO).is_err());
        assert!(route.speed_required(Duration::ZERO).is_err());
    }

    #[test]
    fn a_great_circle_route_is_shorter_than_the_rhumb_one() {
        let waypoints = vec![at(49.95, -5.2), at(46.66, -53.07)];
        let direct = Route::new(waypoints.clone(), LegKind::GreatCircle).unwrap();
        let steered = Route::new(waypoints, LegKind::RhumbLine).unwrap();
        assert!(
            direct.total_distance().unwrap().nautical_miles()
                < steered.total_distance().unwrap().nautical_miles()
        );
        assert_eq!(direct.kind(), LegKind::GreatCircle);
    }

    #[test]
    fn splitting_a_great_circle_keeps_its_length_and_shortens_its_legs() {
        let route = Route::new(
            vec![at(49.95, -5.2), at(46.66, -53.07)],
            LegKind::GreatCircle,
        )
        .unwrap();
        let total = route.total_distance().unwrap().nautical_miles();

        let split = route
            .split_legs(Distance::from_nautical_miles(300.0).unwrap())
            .unwrap();
        assert_eq!(split.kind(), LegKind::RhumbLine);
        assert!(split.leg_count() > route.leg_count());

        for leg in split.legs().unwrap() {
            assert!(leg.sailing.distance.nautical_miles() <= 300.0 + 1e-6);
        }

        // Steering it as rhumb legs costs a little, but only a little.
        let steered = split.total_distance().unwrap().nautical_miles();
        assert!(steered >= total - 1e-6);
        assert!((steered - total) / total < 0.001, "{steered} vs {total}");
    }

    #[test]
    fn splitting_keeps_the_ends_where_they_were() {
        let route = square();
        let split = route
            .split_legs(Distance::from_nautical_miles(10.0).unwrap())
            .unwrap();
        let first = split.waypoints().first().copied().unwrap();
        let last = split.waypoints().last().copied().unwrap();
        assert!(
            rhumb_line(route.waypoints()[0], first)
                .unwrap()
                .distance
                .nautical_miles()
                < 1e-9
        );
        assert!(
            rhumb_line(*route.waypoints().last().unwrap(), last)
                .unwrap()
                .distance
                .nautical_miles()
                < 1e-6
        );
    }

    #[test]
    fn splitting_refuses_a_useless_interval() {
        let route = square();
        assert!(route.split_legs(Distance::ZERO).is_err());
        assert!(route
            .split_legs(Distance::from_nautical_miles(-1.0).unwrap())
            .is_err());
        assert!(route
            .split_legs(Distance::from_nautical_miles(1e-9).unwrap())
            .is_err());
    }

    #[test]
    fn progress_on_the_track_is_all_zeros_off_track() {
        let route = square();
        // Halfway up the first leg.
        let position = at(0.5, 0.0);
        let progress = route.progress(position).unwrap();

        assert_eq!(progress.leg, 0);
        assert_eq!(progress.cross_track.side, TrackSide::OnTrack);
        assert!(progress.cross_track.distance.nautical_miles() < 1e-6);
        assert!((progress.distance_to_next.nautical_miles() - 30.0).abs() < 0.1);
        assert!(progress.course_to_next.degrees().abs() < 1e-6);
        // Thirty miles left on this leg, plus the two after it.
        assert!((progress.distance_to_end.nautical_miles() - 150.0).abs() < 0.2);
    }

    #[test]
    fn progress_knows_which_side_of_the_track_the_ship_is_on() {
        let route = square();
        // A little east of the first leg, which runs due north: that is starboard.
        let east = route.progress(at(0.5, 0.05)).unwrap();
        assert_eq!(east.leg, 0);
        assert_eq!(east.cross_track.side, TrackSide::Starboard);
        assert!((east.cross_track.distance.nautical_miles() - 3.0).abs() < 0.05);

        let west = route.progress(at(0.5, -0.05)).unwrap();
        assert_eq!(west.cross_track.side, TrackSide::Port);
        assert!(west.cross_track.signed().is_negative());
    }

    #[test]
    fn progress_moves_from_leg_to_leg() {
        let route = square();
        assert_eq!(route.progress(at(0.2, 0.0)).unwrap().leg, 0);
        assert_eq!(route.progress(at(1.0, 0.5)).unwrap().leg, 1);
        assert_eq!(route.progress(at(0.5, 1.0)).unwrap().leg, 2);
    }

    #[test]
    fn the_distance_left_shrinks_all_the_way_along() {
        let route = square();
        let mut previous = f64::MAX;
        for step in 0..=20 {
            let latitude = f64::from(step) / 20.0;
            let progress = route.progress(at(latitude, 0.0)).unwrap();
            let remaining = progress.distance_to_end.nautical_miles();
            assert!(
                remaining <= previous + 1e-6,
                "at {latitude}° the distance left grew to {remaining}"
            );
            previous = remaining;
        }
    }

    #[test]
    fn a_ship_past_the_end_still_gets_an_answer() {
        let route = square();
        // Well beyond the last waypoint.
        let progress = route.progress(at(-1.0, 1.0)).unwrap();
        assert_eq!(progress.leg, 2);
        assert!(progress.distance_to_next.nautical_miles() > 0.0);
        assert!(progress.cross_track.along_track.nautical_miles() > 0.0);
    }

    #[test]
    fn a_ship_before_the_start_gets_a_negative_along_track() {
        let route = square();
        let progress = route.progress(at(-0.5, 0.0)).unwrap();
        assert_eq!(progress.leg, 0);
        assert!(progress.cross_track.along_track.is_negative());
    }

    #[test]
    fn a_route_with_a_repeated_waypoint_is_reported_not_divided_by_zero() {
        let route = Route::new(
            vec![at(10.0, 10.0), at(10.0, 10.0), at(11.0, 10.0)],
            LegKind::RhumbLine,
        )
        .unwrap();
        // The zero-length leg has no track to be off.
        assert!(route.progress(at(10.5, 10.0)).is_err());
        // Its length is still well defined, though.
        assert!(route.total_distance().unwrap().nautical_miles() > 59.0);
    }
}
