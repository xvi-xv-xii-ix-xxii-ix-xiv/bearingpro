//! Angles, distances and speeds as types rather than bare `f64`.
//!
//! The reason is the same one that gave [`crate::Direction`] its frame tag: a
//! function that takes `(f64, f64)` cannot tell knots from metres per second, and
//! neither can the compiler. Here it can.
//!
//! Distances are stored in nautical miles and speeds in knots, but that is an
//! implementation detail — construct and read them in whatever unit suits.
//!
//! # Example
//!
//! ```rust
//! use bearingpro::{Distance, NavigationError, Speed};
//! use core::time::Duration;
//!
//! let leg = Distance::from_nautical_miles(12.0)?;
//! assert_eq!(format!("{:.0}", leg.metres()), "22224");
//! assert_eq!(format!("{:.0}", leg.cables()), "120");
//!
//! let speed = Speed::from_knots(8.0)?;
//! let elapsed = speed.time_to_cover(leg)?;
//! assert_eq!(elapsed.as_secs(), 5400); // an hour and a half
//!
//! assert_eq!(speed.distance_covered(elapsed).nautical_miles(), 12.0);
//! # Ok::<(), NavigationError>(())
//! ```

use core::fmt;
use core::ops::{Add, Div, Mul, Neg, Sub};
use core::str::FromStr;
use core::time::Duration;

use crate::angle::{ensure_finite, wrap180};
use crate::error::{NavigationError, Result};
use crate::math;

/// Metres in an international nautical mile, by definition.
pub const METRES_PER_NAUTICAL_MILE: f64 = 1852.0;
/// Metres in a foot, by definition.
pub const METRES_PER_FOOT: f64 = 0.3048;
/// Metres in a fathom: six feet.
pub const METRES_PER_FATHOM: f64 = 6.0 * METRES_PER_FOOT;
/// Cables in a nautical mile, in the usual maritime convention.
pub const CABLES_PER_NAUTICAL_MILE: f64 = 10.0;
/// Seconds in an hour.
const SECONDS_PER_HOUR: f64 = 3600.0;

/// A plain angular magnitude, in degrees.
///
/// Unlike [`crate::Direction`] this is not a compass direction and is not wrapped
/// into `[0°, 360°)`: it is a difference, an error, or a subtended angle, and its
/// sign carries meaning. Use it for gyro error, sextant angles, leeway and the
/// like.
#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Default)]
#[cfg_attr(
    feature = "serde",
    derive(serde::Serialize, serde::Deserialize),
    serde(try_from = "f64", into = "f64")
)]
pub struct Angle(f64);

impl Angle {
    /// A zero angle.
    pub const ZERO: Self = Self(0.0);

    /// Creates an angle from degrees.
    ///
    /// # Errors
    ///
    /// Returns [`NavigationError::NotFinite`] for `NaN` or an infinity.
    pub fn from_degrees(value: f64) -> Result<Self> {
        ensure_finite("angle", value)?;
        Ok(Self(value))
    }

    /// Creates an angle from minutes of arc.
    ///
    /// # Errors
    ///
    /// Returns [`NavigationError::NotFinite`] for `NaN` or an infinity.
    pub fn from_minutes(value: f64) -> Result<Self> {
        ensure_finite("angle", value)?;
        Ok(Self(value / 60.0))
    }

    /// Creates an angle from degrees, minutes and seconds of arc.
    ///
    /// # Errors
    ///
    /// Returns [`NavigationError::NotFinite`] for `NaN` or an infinity.
    pub fn from_degrees_minutes_seconds(degrees: f64, minutes: f64, seconds: f64) -> Result<Self> {
        ensure_finite("angle", degrees)?;
        ensure_finite("angle", minutes)?;
        ensure_finite("angle", seconds)?;
        Ok(Self(degrees + minutes / 60.0 + seconds / 3600.0))
    }

    /// Creates an angle from radians.
    ///
    /// # Errors
    ///
    /// Returns [`NavigationError::NotFinite`] for `NaN` or an infinity.
    pub fn from_radians(value: f64) -> Result<Self> {
        ensure_finite("angle", value)?;
        Ok(Self(math::to_degrees(value)))
    }

    /// Builds an angle from a value already known to be finite.
    pub(crate) const fn from_degrees_unchecked(value: f64) -> Self {
        Self(value)
    }

    /// The angle in degrees.
    #[must_use]
    pub const fn degrees(self) -> f64 {
        self.0
    }

    /// The angle in minutes of arc.
    #[must_use]
    pub fn minutes(self) -> f64 {
        self.0 * 60.0
    }

    /// The angle in radians.
    #[must_use]
    pub fn radians(self) -> f64 {
        math::to_radians(self.0)
    }

    /// The magnitude of the angle.
    #[must_use]
    pub fn abs(self) -> Self {
        Self(math::abs(self.0))
    }

    /// The angle folded into `[-180°, 180°)`.
    #[must_use]
    pub fn normalised(self) -> Self {
        Self(wrap180(self.0))
    }
}

impl fmt::Display for Angle {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let precision = f.precision().unwrap_or(1);
        write!(f, "{:.precision$}°", self.0)
    }
}

impl Neg for Angle {
    type Output = Self;
    fn neg(self) -> Self {
        Self(-self.0)
    }
}

impl Add for Angle {
    type Output = Self;
    fn add(self, other: Self) -> Self {
        Self(self.0 + other.0)
    }
}

impl Sub for Angle {
    type Output = Self;
    fn sub(self, other: Self) -> Self {
        Self(self.0 - other.0)
    }
}

impl FromStr for Angle {
    type Err = NavigationError;

    /// Reads `1°30.5'`, `1 30 30`, `-2.7` and the like.
    ///
    /// An angle has no hemisphere, so only a sign is accepted.
    ///
    /// # Errors
    ///
    /// Returns [`NavigationError::Parse`] for anything unreadable, including a
    /// hemisphere letter.
    fn from_str(input: &str) -> Result<Self> {
        let parsed = crate::parse::sexagesimal("angle", input)?;
        if parsed.hemisphere.is_some() {
            return Err(crate::parse::parse_error("angle", input));
        }
        Self::from_degrees(parsed.signed(""))
    }
}

/// A distance, stored in nautical miles.
///
/// The sign is meaningful for the signed quantities in navigation — along-track
/// distance is negative before the start of a leg — so a distance is not
/// constrained to be positive. Functions that need a positive distance say so and
/// check it.
#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Default)]
#[cfg_attr(
    feature = "serde",
    derive(serde::Serialize, serde::Deserialize),
    serde(try_from = "f64", into = "f64")
)]
pub struct Distance(f64);

impl Distance {
    /// No distance.
    pub const ZERO: Self = Self(0.0);

    /// Creates a distance from nautical miles.
    ///
    /// # Errors
    ///
    /// Returns [`NavigationError::NotFinite`] for `NaN` or an infinity.
    pub fn from_nautical_miles(value: f64) -> Result<Self> {
        ensure_finite("distance", value)?;
        Ok(Self(value))
    }

    /// Creates a distance from cables, at ten to the nautical mile.
    ///
    /// # Errors
    ///
    /// Returns [`NavigationError::NotFinite`] for `NaN` or an infinity.
    pub fn from_cables(value: f64) -> Result<Self> {
        ensure_finite("distance", value)?;
        Ok(Self(value / CABLES_PER_NAUTICAL_MILE))
    }

    /// Creates a distance from metres.
    ///
    /// # Errors
    ///
    /// Returns [`NavigationError::NotFinite`] for `NaN` or an infinity.
    pub fn from_metres(value: f64) -> Result<Self> {
        ensure_finite("distance", value)?;
        Ok(Self(value / METRES_PER_NAUTICAL_MILE))
    }

    /// Creates a distance from kilometres.
    ///
    /// # Errors
    ///
    /// Returns [`NavigationError::NotFinite`] for `NaN` or an infinity.
    pub fn from_kilometres(value: f64) -> Result<Self> {
        ensure_finite("distance", value)?;
        Ok(Self(value * 1000.0 / METRES_PER_NAUTICAL_MILE))
    }

    /// Creates a distance from feet. Useful for charted heights of lights.
    ///
    /// # Errors
    ///
    /// Returns [`NavigationError::NotFinite`] for `NaN` or an infinity.
    pub fn from_feet(value: f64) -> Result<Self> {
        ensure_finite("distance", value)?;
        Ok(Self(value * METRES_PER_FOOT / METRES_PER_NAUTICAL_MILE))
    }

    /// Creates a distance from fathoms.
    ///
    /// # Errors
    ///
    /// Returns [`NavigationError::NotFinite`] for `NaN` or an infinity.
    pub fn from_fathoms(value: f64) -> Result<Self> {
        ensure_finite("distance", value)?;
        Ok(Self(value * METRES_PER_FATHOM / METRES_PER_NAUTICAL_MILE))
    }

    /// Creates a distance from minutes of arc on a great circle.
    ///
    /// This is the traditional definition of the nautical mile, and the reason
    /// latitude scales double as distance scales on a chart.
    ///
    /// # Errors
    ///
    /// Returns [`NavigationError::NotFinite`] for `NaN` or an infinity.
    pub fn from_arc_minutes(value: f64) -> Result<Self> {
        Self::from_nautical_miles(value)
    }

    /// Builds a distance from a value already known to be finite.
    pub(crate) const fn from_nautical_miles_unchecked(value: f64) -> Self {
        Self(value)
    }

    /// The distance in nautical miles.
    #[must_use]
    pub const fn nautical_miles(self) -> f64 {
        self.0
    }

    /// The distance in cables.
    #[must_use]
    pub fn cables(self) -> f64 {
        self.0 * CABLES_PER_NAUTICAL_MILE
    }

    /// The distance in metres.
    #[must_use]
    pub fn metres(self) -> f64 {
        self.0 * METRES_PER_NAUTICAL_MILE
    }

    /// The distance in kilometres.
    #[must_use]
    pub fn kilometres(self) -> f64 {
        self.0 * METRES_PER_NAUTICAL_MILE / 1000.0
    }

    /// The distance in feet.
    #[must_use]
    pub fn feet(self) -> f64 {
        self.0 * METRES_PER_NAUTICAL_MILE / METRES_PER_FOOT
    }

    /// The magnitude of the distance.
    #[must_use]
    pub fn abs(self) -> Self {
        Self(math::abs(self.0))
    }

    /// Whether the distance is negative.
    #[must_use]
    pub fn is_negative(self) -> bool {
        self.0 < 0.0
    }

    /// How long this distance takes at a given speed.
    ///
    /// # Errors
    ///
    /// Returns [`NavigationError::Indeterminate`] if the speed is zero or the
    /// two have opposite signs, so the distance is never covered.
    pub fn time_at(self, speed: Speed) -> Result<Duration> {
        speed.time_to_cover(self)
    }
}

impl fmt::Display for Distance {
    /// Formats in nautical miles, as `12.0 M`.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let precision = f.precision().unwrap_or(1);
        write!(f, "{:.precision$} M", self.0)
    }
}

impl Neg for Distance {
    type Output = Self;
    fn neg(self) -> Self {
        Self(-self.0)
    }
}

impl Add for Distance {
    type Output = Self;
    fn add(self, other: Self) -> Self {
        Self(self.0 + other.0)
    }
}

impl Sub for Distance {
    type Output = Self;
    fn sub(self, other: Self) -> Self {
        Self(self.0 - other.0)
    }
}

impl Mul<f64> for Distance {
    type Output = Self;
    fn mul(self, factor: f64) -> Self {
        Self(self.0 * factor)
    }
}

impl Div<f64> for Distance {
    type Output = Self;
    fn div(self, divisor: f64) -> Self {
        Self(self.0 / divisor)
    }
}

/// A speed, stored in knots.
///
/// Negative speeds mean sternway.
#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Default)]
#[cfg_attr(
    feature = "serde",
    derive(serde::Serialize, serde::Deserialize),
    serde(try_from = "f64", into = "f64")
)]
pub struct Speed(f64);

impl Speed {
    /// Stopped.
    pub const ZERO: Self = Self(0.0);

    /// Creates a speed from knots.
    ///
    /// # Errors
    ///
    /// Returns [`NavigationError::NotFinite`] for `NaN` or an infinity.
    pub fn from_knots(value: f64) -> Result<Self> {
        ensure_finite("speed", value)?;
        Ok(Self(value))
    }

    /// Creates a speed from metres per second.
    ///
    /// # Errors
    ///
    /// Returns [`NavigationError::NotFinite`] for `NaN` or an infinity.
    pub fn from_metres_per_second(value: f64) -> Result<Self> {
        ensure_finite("speed", value)?;
        Ok(Self(value * SECONDS_PER_HOUR / METRES_PER_NAUTICAL_MILE))
    }

    /// Creates a speed from kilometres per hour.
    ///
    /// # Errors
    ///
    /// Returns [`NavigationError::NotFinite`] for `NaN` or an infinity.
    pub fn from_kilometres_per_hour(value: f64) -> Result<Self> {
        ensure_finite("speed", value)?;
        Ok(Self(value * 1000.0 / METRES_PER_NAUTICAL_MILE))
    }

    /// Builds a speed from a value already known to be finite.
    pub(crate) const fn from_knots_unchecked(value: f64) -> Self {
        Self(value)
    }

    /// The speed in knots.
    #[must_use]
    pub const fn knots(self) -> f64 {
        self.0
    }

    /// The speed in metres per second.
    #[must_use]
    pub fn metres_per_second(self) -> f64 {
        self.0 * METRES_PER_NAUTICAL_MILE / SECONDS_PER_HOUR
    }

    /// The speed in kilometres per hour.
    #[must_use]
    pub fn kilometres_per_hour(self) -> f64 {
        self.0 * METRES_PER_NAUTICAL_MILE / 1000.0
    }

    /// The magnitude of the speed.
    #[must_use]
    pub fn abs(self) -> Self {
        Self(math::abs(self.0))
    }

    /// Whether the speed is negative, meaning sternway.
    #[must_use]
    pub fn is_negative(self) -> bool {
        self.0 < 0.0
    }

    /// How far this speed covers in a given time.
    #[must_use]
    pub fn distance_covered(self, elapsed: Duration) -> Distance {
        Distance(self.0 * elapsed.as_secs_f64() / SECONDS_PER_HOUR)
    }

    /// How long it takes to cover a distance at this speed.
    ///
    /// # Errors
    ///
    /// Returns [`NavigationError::Indeterminate`] if the speed is zero, or if the
    /// speed and the distance have opposite signs so the distance is never
    /// covered.
    pub fn time_to_cover(self, distance: Distance) -> Result<Duration> {
        let hours = distance.0 / self.0;
        if !hours.is_finite() || hours < 0.0 {
            return Err(NavigationError::Indeterminate {
                quantity: "time to cover the distance",
            });
        }
        Duration::try_from_secs_f64(hours * SECONDS_PER_HOUR).map_err(|_| {
            NavigationError::Indeterminate {
                quantity: "time to cover the distance",
            }
        })
    }
}

impl fmt::Display for Speed {
    /// Formats in knots, as `8.0 kn`.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let precision = f.precision().unwrap_or(1);
        write!(f, "{:.precision$} kn", self.0)
    }
}

impl Neg for Speed {
    type Output = Self;
    fn neg(self) -> Self {
        Self(-self.0)
    }
}

impl Add for Speed {
    type Output = Self;
    fn add(self, other: Self) -> Self {
        Self(self.0 + other.0)
    }
}

impl Sub for Speed {
    type Output = Self;
    fn sub(self, other: Self) -> Self {
        Self(self.0 - other.0)
    }
}

impl Mul<f64> for Speed {
    type Output = Self;
    fn mul(self, factor: f64) -> Self {
        Self(self.0 * factor)
    }
}

/// Converts a duration to hours, the unit knots and nautical miles agree on.
pub(crate) fn hours(elapsed: Duration) -> f64 {
    elapsed.as_secs_f64() / SECONDS_PER_HOUR
}

/// Converts hours to a duration, rejecting negative and unrepresentable values.
pub(crate) fn duration_from_hours(value: f64) -> Result<Duration> {
    if !value.is_finite() || value < 0.0 {
        return Err(NavigationError::Indeterminate {
            quantity: "elapsed time",
        });
    }
    Duration::try_from_secs_f64(value * SECONDS_PER_HOUR).map_err(|_| {
        NavigationError::Indeterminate {
            quantity: "elapsed time",
        }
    })
}

#[cfg(feature = "serde")]
impl TryFrom<f64> for Angle {
    type Error = NavigationError;

    /// Validates on the way in, so a stored value cannot be out of range.
    fn try_from(value: f64) -> Result<Self> {
        Self::from_degrees(value)
    }
}

#[cfg(feature = "serde")]
impl From<Angle> for f64 {
    fn from(value: Angle) -> Self {
        value.0
    }
}

#[cfg(feature = "serde")]
impl TryFrom<f64> for Distance {
    type Error = NavigationError;

    /// Validates on the way in, so a stored value cannot be out of range.
    fn try_from(value: f64) -> Result<Self> {
        Self::from_nautical_miles(value)
    }
}

#[cfg(feature = "serde")]
impl From<Distance> for f64 {
    fn from(value: Distance) -> Self {
        value.0
    }
}

#[cfg(feature = "serde")]
impl TryFrom<f64> for Speed {
    type Error = NavigationError;

    /// Validates on the way in, so a stored value cannot be out of range.
    fn try_from(value: f64) -> Result<Self> {
        Self::from_knots(value)
    }
}

#[cfg(feature = "serde")]
impl From<Speed> for f64 {
    fn from(value: Speed) -> Self {
        value.0
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::float_cmp, clippy::indexing_slicing)]
mod tests {
    use super::*;
    use alloc::format;

    #[test]
    fn distance_units_round_trip() {
        let distance = Distance::from_nautical_miles(1.0).unwrap();
        assert_eq!(distance.metres(), 1852.0);
        assert_eq!(distance.cables(), 10.0);
        assert!((distance.kilometres() - 1.852).abs() < 1e-12);
        assert!((distance.feet() - 6076.115).abs() < 1e-3);

        for constructor in [
            Distance::from_metres(1852.0),
            Distance::from_cables(10.0),
            Distance::from_kilometres(1.852),
            Distance::from_arc_minutes(1.0),
        ] {
            assert!((constructor.unwrap().nautical_miles() - 1.0).abs() < 1e-12);
        }

        assert!(
            (Distance::from_feet(6.0).unwrap().nautical_miles()
                - Distance::from_fathoms(1.0).unwrap().nautical_miles())
            .abs()
                < 1e-15
        );
    }

    #[test]
    fn speed_units_round_trip() {
        let speed = Speed::from_knots(1.0).unwrap();
        assert!((speed.metres_per_second() - 0.514_444_444).abs() < 1e-9);
        assert!((speed.kilometres_per_hour() - 1.852).abs() < 1e-12);
        assert!(
            (Speed::from_metres_per_second(0.514_444_444_444_444_4)
                .unwrap()
                .knots()
                - 1.0)
                .abs()
                < 1e-12
        );
    }

    #[test]
    fn distance_and_time_are_consistent() {
        let speed = Speed::from_knots(8.0).unwrap();
        let distance = Distance::from_nautical_miles(12.0).unwrap();
        let elapsed = speed.time_to_cover(distance).unwrap();
        assert_eq!(elapsed.as_secs(), 5400);
        assert!((speed.distance_covered(elapsed).nautical_miles() - 12.0).abs() < 1e-12);
        assert!((distance.time_at(speed).unwrap().as_secs_f64() - 5400.0).abs() < 1e-9);
    }

    #[test]
    fn impossible_times_are_errors_not_panics() {
        let distance = Distance::from_nautical_miles(10.0).unwrap();
        assert!(Speed::ZERO.time_to_cover(distance).is_err());
        assert!(Speed::from_knots(-5.0)
            .unwrap()
            .time_to_cover(distance)
            .is_err());
        assert!(Speed::from_knots(1e-300)
            .unwrap()
            .time_to_cover(Distance::from_nautical_miles(1e300).unwrap())
            .is_err());
    }

    #[test]
    fn non_finite_input_is_rejected() {
        for value in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
            assert!(Distance::from_nautical_miles(value).is_err());
            assert!(Distance::from_metres(value).is_err());
            assert!(Speed::from_knots(value).is_err());
            assert!(Angle::from_degrees(value).is_err());
            assert!(Angle::from_minutes(value).is_err());
            assert!(Angle::from_radians(value).is_err());
        }
    }

    #[test]
    fn angle_conversions() {
        let angle = Angle::from_degrees_minutes_seconds(1.0, 30.0, 0.0).unwrap();
        assert_eq!(angle.degrees(), 1.5);
        assert_eq!(angle.minutes(), 90.0);
        assert!((Angle::from_minutes(90.0).unwrap().degrees() - 1.5).abs() < 1e-12);
        assert!(
            (Angle::from_radians(core::f64::consts::PI)
                .unwrap()
                .degrees()
                - 180.0)
                .abs()
                < 1e-12
        );
        assert_eq!((-angle).abs(), angle);
        assert_eq!(
            Angle::from_degrees(370.0).unwrap().normalised().degrees(),
            10.0
        );
    }

    #[test]
    fn angles_parse_from_how_they_are_written() {
        assert_eq!("1.5".parse::<Angle>().unwrap().degrees(), 1.5);
        assert!(("1°30'".parse::<Angle>().unwrap().degrees() - 1.5).abs() < 1e-12);
        assert!(("1 30 00".parse::<Angle>().unwrap().degrees() - 1.5).abs() < 1e-12);
        assert!(("-2.7".parse::<Angle>().unwrap().degrees() + 2.7).abs() < 1e-12);
        // No hemispheres on a plain angle.
        assert!("1°30'N".parse::<Angle>().is_err());
        assert!("".parse::<Angle>().is_err());
        assert!("1 60".parse::<Angle>().is_err());
    }

    #[test]
    fn arithmetic_behaves() {
        let a = Distance::from_nautical_miles(3.0).unwrap();
        let b = Distance::from_nautical_miles(4.0).unwrap();
        assert_eq!((a + b).nautical_miles(), 7.0);
        assert_eq!((b - a).nautical_miles(), 1.0);
        assert_eq!((a * 2.0).nautical_miles(), 6.0);
        assert_eq!((b / 2.0).nautical_miles(), 2.0);
        assert!((a - b).is_negative());
        assert_eq!((a - b).abs().nautical_miles(), 1.0);
    }

    #[test]
    fn display_is_readable() {
        assert_eq!(
            format!("{}", Distance::from_nautical_miles(12.0).unwrap()),
            "12.0 M"
        );
        assert_eq!(format!("{:.2}", Speed::from_knots(8.5).unwrap()), "8.50 kn");
        assert_eq!(format!("{}", Angle::from_degrees(-1.25).unwrap()), "-1.2°");
    }
}
