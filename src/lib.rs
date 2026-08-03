//! Marine navigation: compass corrections, the sailings, dead reckoning,
//! position fixing and collision avoidance.
//!
//! ```text
//! magnetic course = compass course  + deviation(compass course)
//! true course     = magnetic course + variation
//! ```
//!
//! # What the types do for you
//!
//! Every angle in this crate is a newtype that carries its reference frame:
//! [`CompassCourse`], [`MagneticCourse`], [`TrueCourse`], [`GyroCourse`],
//! [`Variation`], [`Deviation`], [`RelativeBearing`]. Passing a magnetic course
//! where a true one belongs, or a variation where a course belongs, does not
//! compile. Distances and speeds are types too — [`Distance`] and [`Speed`] — so
//! knots cannot be handed to something expecting metres per second.
//!
//! Each type also owns its range invariant: a [`Direction`] is always finite and
//! always in `[0°, 360°)`, a [`Latitude`] always in `[-90°, 90°]`. That is why
//! the pure corrections return a value rather than a `Result`.
//!
//! Nothing in this crate panics on caller-supplied data. Bad input comes back as
//! a [`NavigationError`].
//!
//! # Example
//!
//! ```rust
//! use bearingpro::{
//!     navigation_solutions::{
//!         convert_compass_course_to_true_course, convert_true_course_to_compass_course,
//!     },
//!     CompassCourse, DeviationTable, InterpolationMethod, TrueCourse, Variation,
//! };
//!
//! // A swing: deviation observed on every tenth of the compass, 000° to 350°.
//! let table = DeviationTable::from_deviation_vec(vec![
//!     -2.5, -0.5, 1.6, 4.4, -1.7, 0.0, 1.0, 0.3, -0.9, // 000°..080°
//!     0.5, -1.2, 0.8, -0.3, 1.7, -2.1, 0.4, -0.6, 1.2, // 090°..170°
//!     -1.3, 0.0, 0.9, -1.1, 1.5, -0.7, -13.2, -15.7, -17.9, // 180°..260°
//!     -19.2, -18.1, 1.8, -0.4, 0.7, -0.2, 1.4, -4.4, -2.9, // 270°..350°
//! ])?;
//!
//! let variation = Variation::new(-2.7)?;
//!
//! // What is the ship actually making good, steering 003° by the compass?
//! let solution = convert_compass_course_to_true_course(
//!     CompassCourse::new(3.0)?,
//!     variation,
//!     &table,
//!     InterpolationMethod::Cubic,
//! )?;
//! assert_eq!(format!("{}", solution.course), "358.2°T");
//!
//! // And back again: the inverse solves for the compass course the table is
//! // indexed by, so the two directions agree.
//! let back = convert_true_course_to_compass_course(
//!     solution.course,
//!     variation,
//!     &table,
//!     InterpolationMethod::Cubic,
//! )?;
//! assert!((back.course.degrees() - 3.0).abs() < 1e-9);
//!
//! // This particular swing jumps 12.5° between 230° and 240°, which is steeper
//! // than a compass can be steered by. The result says so instead of leaving
//! // you to discover it at sea.
//! assert!(solution.advisories.non_invertible_table);
//! # Ok::<(), bearingpro::NavigationError>(())
//! ```
//!
//! # Modules
//!
//! - [`angle`] — the frame-tagged angle types and their invariants.
//! - [`units`] — angles, distances and speeds, so the unit is never in doubt.
//! - [`position`] — latitude, longitude, and how a position is written down.
//! - [`deviation`] — deviation tables, periodic interpolation, coefficient fitting.
//! - [`navigation_solutions`] — course and bearing conversions, gyro error, the
//!   current triangle.
//! - [`sailings`] — rhumb line, great circle, WGS-84 geodesic, cross-track error.
//! - [`dead_reckoning`] — DR and estimated positions, traverses, leeway.
//! - [`fix`] — position lines, fixes, cocked hats, distance off.
//! - [`relative_motion`] — closest approach, radar plotting, the avoiding manoeuvre.
//! - [`route`] — passage plans: legs, distances, schedule, progress along the track.
//! - [`error`] — the single error type everything returns.
//!
//! # Which model is used where
//!
//! The spherical sailings use a mean Earth radius of 6371.0088 km;
//! [`sailings::geodesic`] uses the WGS-84 ellipsoid. Position lines are rhumb
//! lines and cross exactly on a Mercator chart; range fixes and relative motion
//! are worked in a plane. Each function's documentation says which applies.
//!
//! # Feature flags
//!
//! - `std` *(default)* — uses the standard library's floating point maths.
//! - `libm` — for `no_std` targets. Build with
//!   `--no-default-features --features libm`.
//! - `serde` — serialise and deserialise the value types. Deserialisation goes
//!   through the same validation as construction, so a stored file cannot
//!   produce a latitude of 500° or a deviation table with duplicate headings.
//!
//! The crate has no dependencies at all in its default configuration.

#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;

pub mod angle;
pub mod dead_reckoning;
pub mod deviation;
pub mod error;
pub mod fix;
mod linalg;
mod math;
pub mod navigation_solutions;
mod parse;
pub mod position;
pub mod relative_motion;
pub mod route;
pub mod sailings;
pub mod units;

/// Compiles and runs every example in `README.md` as part of `cargo test`.
///
/// The README used to document numbers that no longer matched the code — and,
/// worse, numbers that recorded the behaviour of bugs. Now it cannot drift.
#[cfg(doctest)]
#[doc = include_str!("../README.md")]
pub struct ReadmeExamples;

pub use angle::{
    wrap180, wrap360, Compass, CompassBearing, CompassCourse, Deviation, Direction, Frame, Gyro,
    GyroBearing, GyroCourse, Magnetic, MagneticBearing, MagneticCourse, RelativeBearing, Side,
    True, TrueBearing, TrueCourse, Variation, MAX_DEVIATION_DEG, MAX_VARIATION_DEG,
};
pub use dead_reckoning::{EstimatedPosition, Leg};
pub use deviation::{
    DeviationAnalysis, DeviationCoefficients, DeviationNode, DeviationTable, Interpolation,
    InterpolationMethod, SmithCoefficients, SwingObservation, CARDINAL_DIRECTIONS,
    STANDARD_TABLE_LEN,
};
pub use error::{NavigationError, Result};
pub use fix::{CockedHat, Fix, PositionLine, TwoBearingDistance};
pub use navigation_solutions::{
    Advisories, CourseSolution, Current, GroundTrack, SteeringSolution, COARSE_TABLE_GAP_DEG,
    LARGE_DEVIATION_DEG, LARGE_VARIATION_DEG,
};
pub use position::{EastWest, Latitude, Longitude, NorthSouth, Position};
pub use relative_motion::{Approach, Avoidance, Contact, Cpa, TargetSolution, Vessel};
pub use route::{LegKind, Progress, Route, RouteLeg};
pub use sailings::{Arrival, CrossTrack, Sailing, TrackSide, EARTH_RADIUS};
pub use units::{Angle, Distance, Speed};
