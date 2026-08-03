//! Geographic position: latitude, longitude, and the pair of them.
//!
//! Both coordinates carry their invariant in the type. A [`Latitude`] is always
//! in `[-90°, 90°]`; a [`Longitude`] is always in `[-180°, 180°)` and wraps rather
//! than overflowing, so adding a westerly difference across the antimeridian
//! cannot produce a nonsense value.
//!
//! # Example
//!
//! ```rust
//! use bearingpro::{Latitude, Longitude, NavigationError, NorthSouth, Position};
//!
//! // Decimal degrees, or the degrees-and-minutes a chart is marked in.
//! let position = Position::new(
//!     Latitude::from_degrees_minutes(50, 45.3, NorthSouth::North)?,
//!     Longitude::from_degrees(-1.296_667)?,
//! );
//!
//! assert_eq!(format!("{position}"), "50°45.3'N 001°17.8'W");
//! assert_eq!(position.latitude().degrees(), 50.755);
//!
//! // Out of range is rejected; longitude wraps.
//! assert!(Latitude::from_degrees(91.0).is_err());
//! assert_eq!(Longitude::from_degrees(180.0)?.degrees(), -180.0);
//! # Ok::<(), NavigationError>(())
//! ```

use core::fmt;
use core::str::FromStr;

use crate::angle::{ensure_finite, ensure_range, wrap180};
#[cfg(feature = "serde")]
use crate::error::NavigationError;
use crate::error::Result;
use crate::math;
use crate::units::{Angle, Distance};

/// Flattening of the WGS-84 ellipsoid.
pub const WGS84_FLATTENING: f64 = 1.0 / 298.257_223_563;
/// Semi-major axis of the WGS-84 ellipsoid, in metres.
pub const WGS84_SEMI_MAJOR_AXIS_METRES: f64 = 6_378_137.0;
/// Squared first eccentricity of the WGS-84 ellipsoid, `f·(2 − f)`.
pub const WGS84_ECCENTRICITY_SQUARED: f64 = WGS84_FLATTENING * (2.0 - WGS84_FLATTENING);
/// First eccentricity of the WGS-84 ellipsoid, the square root of the above.
///
/// Spelled out because `sqrt` cannot be evaluated in a constant; a test checks
/// that it really is that square root.
const WGS84_ECCENTRICITY: f64 = 0.081_819_190_842_621_49;

/// Inverse hyperbolic tangent, built from the natural logarithm.
fn artanh(value: f64) -> f64 {
    0.5 * math::ln((1.0 + value) / (1.0 - value))
}

/// Which side of the equator a latitude lies on.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum NorthSouth {
    /// North of the equator.
    North,
    /// South of the equator.
    South,
}

impl NorthSouth {
    /// `1.0` for north, `-1.0` for south.
    #[must_use]
    pub const fn sign(self) -> f64 {
        match self {
            Self::North => 1.0,
            Self::South => -1.0,
        }
    }

    /// The single letter used on charts.
    #[must_use]
    pub const fn letter(self) -> char {
        match self {
            Self::North => 'N',
            Self::South => 'S',
        }
    }
}

/// Which side of the prime meridian a longitude lies on.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum EastWest {
    /// East of Greenwich.
    East,
    /// West of Greenwich.
    West,
}

impl EastWest {
    /// `1.0` for east, `-1.0` for west.
    #[must_use]
    pub const fn sign(self) -> f64 {
        match self {
            Self::East => 1.0,
            Self::West => -1.0,
        }
    }

    /// The single letter used on charts.
    #[must_use]
    pub const fn letter(self) -> char {
        match self {
            Self::East => 'E',
            Self::West => 'W',
        }
    }
}

/// Latitude, in `[-90°, 90°]`, north positive.
#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Default)]
#[cfg_attr(
    feature = "serde",
    derive(serde::Serialize, serde::Deserialize),
    serde(try_from = "f64", into = "f64")
)]
pub struct Latitude(f64);

impl Latitude {
    /// The equator.
    pub const EQUATOR: Self = Self(0.0);
    /// The north pole.
    pub const NORTH_POLE: Self = Self(90.0);
    /// The south pole.
    pub const SOUTH_POLE: Self = Self(-90.0);

    /// Creates a latitude from decimal degrees, north positive.
    ///
    /// # Errors
    ///
    /// Returns [`crate::NavigationError::NotFinite`] for `NaN` or an infinity, and
    /// [`crate::NavigationError::OutOfRange`] outside `[-90.0, 90.0]`.
    pub fn from_degrees(value: f64) -> Result<Self> {
        ensure_range("latitude", value, -90.0, 90.0)?;
        Ok(Self(value))
    }

    /// Creates a latitude from whole degrees and decimal minutes, as a chart marks it.
    ///
    /// # Errors
    ///
    /// As [`Latitude::from_degrees`], after combining the parts.
    pub fn from_degrees_minutes(
        degrees: u16,
        minutes: f64,
        hemisphere: NorthSouth,
    ) -> Result<Self> {
        ensure_finite("latitude minutes", minutes)?;
        let magnitude = f64::from(degrees) + minutes / 60.0;
        Self::from_degrees(magnitude * hemisphere.sign())
    }

    /// Builds a latitude from a value already known to be in range.
    pub(crate) fn from_degrees_clamped(value: f64) -> Self {
        Self(value.clamp(-90.0, 90.0))
    }

    /// The latitude in degrees, north positive.
    #[must_use]
    pub const fn degrees(self) -> f64 {
        self.0
    }

    /// The latitude in radians.
    #[must_use]
    pub fn radians(self) -> f64 {
        math::to_radians(self.0)
    }

    /// Which hemisphere the latitude is in. The equator counts as north.
    #[must_use]
    pub fn hemisphere(self) -> NorthSouth {
        if self.0 < 0.0 {
            NorthSouth::South
        } else {
            NorthSouth::North
        }
    }

    /// Whole degrees and decimal minutes, with the hemisphere.
    #[must_use]
    pub fn to_degrees_minutes(self) -> (u16, f64, NorthSouth) {
        split_degrees_minutes(self.0, 90)
            .map_or((0, 0.0, self.hemisphere()), |(degrees, minutes)| {
                (degrees, minutes, self.hemisphere())
            })
    }

    /// Whether this latitude is at a pole, where longitude stops meaning anything.
    #[must_use]
    pub fn is_polar(self) -> bool {
        math::abs(math::abs(self.0) - 90.0) < 1e-9
    }

    /// Meridional parts: the Mercator y-coordinate, in minutes of arc.
    ///
    /// This is what makes a rhumb line a straight line on a Mercator chart, and
    /// what the Mercator sailing tables tabulate. Computed on the WGS-84
    /// ellipsoid: at latitude 45° it gives 3013.6, where a spherical model would
    /// give 3029.9.
    ///
    /// Note that [`crate::sailings::rhumb_line`] uses a *spherical* model, so it
    /// will not agree with a Mercator sailing worked from these values to the last
    /// decimal. Use [`crate::sailings::geodesic`] when the ellipsoid matters.
    ///
    /// # Errors
    ///
    /// Returns [`crate::NavigationError::Indeterminate`] at a pole, where the
    /// value is infinite.
    pub fn meridional_parts(self) -> Result<f64> {
        if self.is_polar() {
            return Err(crate::NavigationError::Indeterminate {
                quantity: "meridional parts at the pole",
            });
        }
        // The ellipsoidal correction, exactly rather than as a truncated series:
        // the classic 23.268932·sinφ − … coefficients belong to Clarke 1866 and
        // are 1.4 minutes out at low latitudes on WGS-84.
        let eccentricity = WGS84_ECCENTRICITY;
        let sine = math::sin(self.radians());
        let correction = eccentricity * artanh(eccentricity * sine);
        Ok(self.isometric_minutes() - math::to_degrees(correction) * 60.0)
    }

    /// The latitude whose spherical isometric latitude is the given number of minutes.
    ///
    /// The inverse of [`Latitude::isometric_minutes`]: the Gudermannian function,
    /// which turns a Mercator y-coordinate back into a latitude.
    pub(crate) fn from_isometric_minutes(minutes: f64) -> Self {
        let radians = math::to_radians(minutes / 60.0);
        let latitude = 2.0 * math::atan(math::exp(radians)) - core::f64::consts::FRAC_PI_2;
        Self::from_degrees_clamped(math::to_degrees(latitude))
    }

    /// The spherical isometric latitude, in minutes of arc.
    ///
    /// The stretched latitude a Mercator projection of a sphere uses. This is the
    /// quantity the rhumb-line sailings in [`crate::sailings`] are built on.
    pub(crate) fn isometric_minutes(self) -> f64 {
        math::to_degrees(math::ln(math::tan(
            core::f64::consts::FRAC_PI_4 + self.radians() / 2.0,
        ))) * 60.0
    }
}

impl fmt::Display for Latitude {
    /// Formats as `50°45.3'N`, the way a position is written down.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let precision = f.precision().unwrap_or(1);
        let (degrees, minutes, hemisphere) = self.to_degrees_minutes();
        write!(
            f,
            "{degrees:02}°{minutes:0>width$.precision$}'{}",
            hemisphere.letter(),
            width = if precision == 0 { 2 } else { precision + 3 }
        )
    }
}

impl FromStr for Latitude {
    type Err = crate::NavigationError;

    /// Reads `50°45.3'N`, `N50 45 18`, `-33.9` and the like.
    ///
    /// A hemisphere letter or a sign, not both. See [`crate::position`] for the
    /// forms accepted.
    ///
    /// # Errors
    ///
    /// Returns [`crate::NavigationError::Parse`] for anything unreadable, or a
    /// hemisphere that is not north or south, and
    /// [`crate::NavigationError::OutOfRange`] beyond the poles.
    fn from_str(input: &str) -> Result<Self> {
        let parsed = crate::parse::sexagesimal("latitude", input)?;
        if let Some(letter) = parsed.hemisphere {
            if !matches!(letter, 'N' | 'S') {
                return Err(crate::parse::parse_error("latitude", input));
            }
        }
        Self::from_degrees(parsed.signed("S"))
    }
}

/// Longitude, in `[-180°, 180°)`, east positive.
///
/// Values outside the interval wrap rather than being rejected: adding a
/// difference of longitude across the antimeridian is an ordinary thing to do.
#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Default)]
#[cfg_attr(
    feature = "serde",
    derive(serde::Serialize, serde::Deserialize),
    serde(try_from = "f64", into = "f64")
)]
pub struct Longitude(f64);

impl Longitude {
    /// The prime meridian.
    pub const GREENWICH: Self = Self(0.0);

    /// Creates a longitude from decimal degrees, east positive, wrapping into range.
    ///
    /// # Errors
    ///
    /// Returns [`crate::NavigationError::NotFinite`] for `NaN` or an infinity.
    pub fn from_degrees(value: f64) -> Result<Self> {
        ensure_finite("longitude", value)?;
        Ok(Self(wrap180(value)))
    }

    /// Creates a longitude from whole degrees and decimal minutes.
    ///
    /// # Errors
    ///
    /// Returns [`crate::NavigationError::NotFinite`] for `NaN` or an infinity.
    pub fn from_degrees_minutes(degrees: u16, minutes: f64, hemisphere: EastWest) -> Result<Self> {
        ensure_finite("longitude minutes", minutes)?;
        let magnitude = f64::from(degrees) + minutes / 60.0;
        Self::from_degrees(magnitude * hemisphere.sign())
    }

    /// Builds a longitude from a value already known to be finite.
    pub(crate) fn from_degrees_wrapped(value: f64) -> Self {
        Self(wrap180(value))
    }

    /// The longitude in degrees, east positive.
    #[must_use]
    pub const fn degrees(self) -> f64 {
        self.0
    }

    /// The longitude in radians.
    #[must_use]
    pub fn radians(self) -> f64 {
        math::to_radians(self.0)
    }

    /// Which hemisphere the longitude is in. Greenwich counts as east.
    #[must_use]
    pub fn hemisphere(self) -> EastWest {
        if self.0 < 0.0 {
            EastWest::West
        } else {
            EastWest::East
        }
    }

    /// Whole degrees and decimal minutes, with the hemisphere.
    #[must_use]
    pub fn to_degrees_minutes(self) -> (u16, f64, EastWest) {
        split_degrees_minutes(self.0, 180)
            .map_or((0, 0.0, self.hemisphere()), |(degrees, minutes)| {
                (degrees, minutes, self.hemisphere())
            })
    }

    /// The shortest signed difference of longitude to another meridian, in `[-180°, 180°)`.
    ///
    /// Positive is eastward.
    #[must_use]
    pub fn difference_to(self, other: Self) -> Angle {
        Angle::from_degrees_unchecked(wrap180(other.0 - self.0))
    }
}

impl fmt::Display for Longitude {
    /// Formats as `001°17.8'W`.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let precision = f.precision().unwrap_or(1);
        let (degrees, minutes, hemisphere) = self.to_degrees_minutes();
        write!(
            f,
            "{degrees:03}°{minutes:0>width$.precision$}'{}",
            hemisphere.letter(),
            width = if precision == 0 { 2 } else { precision + 3 }
        )
    }
}

impl FromStr for Longitude {
    type Err = crate::NavigationError;

    /// Reads `001°17.8'W`, `W001 17 48`, `151.2` and the like.
    ///
    /// # Errors
    ///
    /// Returns [`crate::NavigationError::Parse`] for anything unreadable, or a
    /// hemisphere that is not east or west.
    fn from_str(input: &str) -> Result<Self> {
        let parsed = crate::parse::sexagesimal("longitude", input)?;
        if let Some(letter) = parsed.hemisphere {
            if !matches!(letter, 'E' | 'W') {
                return Err(crate::parse::parse_error("longitude", input));
            }
        }
        Self::from_degrees(parsed.signed("W"))
    }
}

/// A position on the Earth's surface.
#[derive(Debug, Clone, Copy, PartialEq, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Position {
    latitude: Latitude,
    longitude: Longitude,
}

impl Position {
    /// Where the equator crosses the prime meridian.
    pub const ORIGIN: Self = Self {
        latitude: Latitude::EQUATOR,
        longitude: Longitude::GREENWICH,
    };

    /// Creates a position from a latitude and a longitude.
    #[must_use]
    pub const fn new(latitude: Latitude, longitude: Longitude) -> Self {
        Self {
            latitude,
            longitude,
        }
    }

    /// Creates a position from decimal degrees.
    ///
    /// # Errors
    ///
    /// As [`Latitude::from_degrees`] and [`Longitude::from_degrees`].
    pub fn from_degrees(latitude: f64, longitude: f64) -> Result<Self> {
        Ok(Self::new(
            Latitude::from_degrees(latitude)?,
            Longitude::from_degrees(longitude)?,
        ))
    }

    /// The latitude.
    #[must_use]
    pub const fn latitude(self) -> Latitude {
        self.latitude
    }

    /// The longitude.
    #[must_use]
    pub const fn longitude(self) -> Longitude {
        self.longitude
    }

    /// Difference of latitude to another position, north positive.
    #[must_use]
    pub fn latitude_difference(self, other: Self) -> Angle {
        Angle::from_degrees_unchecked(other.latitude.0 - self.latitude.0)
    }

    /// Difference of longitude to another position, east positive, by the short way.
    #[must_use]
    pub fn longitude_difference(self, other: Self) -> Angle {
        self.longitude.difference_to(other.longitude)
    }

    /// Departure: the east-west distance between two meridians at the mean latitude.
    ///
    /// The plane-sailing approximation, good for short distances.
    #[must_use]
    pub fn departure(self, other: Self) -> Distance {
        let mean_latitude = (self.latitude.radians() + other.latitude.radians()) / 2.0;
        Distance::from_nautical_miles_unchecked(
            self.longitude_difference(other).minutes() * math::cos(mean_latitude),
        )
    }

    /// The position as a unit vector in an Earth-centred frame.
    ///
    /// The x-axis points at 0°N 0°E, the y-axis at 0°N 90°E, the z-axis at the
    /// north pole. This is the form the spherical geometry is actually done in.
    #[must_use]
    pub fn to_unit_vector(self) -> [f64; 3] {
        let (latitude, longitude) = (self.latitude.radians(), self.longitude.radians());
        let cos_latitude = math::cos(latitude);
        [
            cos_latitude * math::cos(longitude),
            cos_latitude * math::sin(longitude),
            math::sin(latitude),
        ]
    }

    /// Rebuilds a position from an Earth-centred vector, which need not be a unit vector.
    ///
    /// Returns `None` for the zero vector, which points nowhere.
    #[must_use]
    pub fn from_unit_vector(vector: [f64; 3]) -> Option<Self> {
        let [x, y, z] = vector;
        let horizontal = math::hypot(x, y);
        if horizontal < f64::MIN_POSITIVE && math::abs(z) < f64::MIN_POSITIVE {
            return None;
        }
        Some(Self::new(
            Latitude::from_degrees_clamped(math::to_degrees(math::atan2(z, horizontal))),
            Longitude::from_degrees_wrapped(math::to_degrees(math::atan2(y, x))),
        ))
    }
}

impl FromStr for Position {
    type Err = crate::NavigationError;

    /// Reads a latitude and a longitude, in that order.
    ///
    /// `50°45.3'N 001°17.8'W`, `N50 45.3 W001 17.8`, `50.755, -1.2967`.
    ///
    /// # Errors
    ///
    /// Returns [`crate::NavigationError::Parse`] if the two halves cannot be told
    /// apart or either is unreadable.
    fn from_str(input: &str) -> Result<Self> {
        let (latitude, longitude) = crate::parse::split_position(input)?;
        Ok(Self::new(latitude.parse()?, longitude.parse()?))
    }
}

impl fmt::Display for Position {
    /// Formats as `50°45.3'N 001°17.8'W`.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let precision = f.precision().unwrap_or(1);
        write!(
            f,
            "{:.precision$} {:.precision$}",
            self.latitude, self.longitude
        )
    }
}

/// Splits a signed decimal degree value into whole degrees and decimal minutes.
///
/// Returns `None` if the magnitude does not fit the expected bound, which cannot
/// happen for a validated latitude or longitude.
fn split_degrees_minutes(value: f64, maximum: u16) -> Option<(u16, f64)> {
    let magnitude = math::abs(value);
    let mut degrees = u16::try_from(math::to_usize(magnitude)).ok()?;
    let mut minutes = (magnitude - f64::from(degrees)) * 60.0;
    // Guard the rounding boundary: 10.99999' must not print as `10°60.0'`.
    if minutes >= 59.999_95 {
        minutes = 0.0;
        degrees = degrees.checked_add(1)?;
    }
    if degrees > maximum {
        return None;
    }
    Some((degrees, minutes))
}

#[cfg(feature = "serde")]
impl TryFrom<f64> for Latitude {
    type Error = NavigationError;

    /// Validates on the way in, so a stored value cannot be out of range.
    fn try_from(value: f64) -> Result<Self> {
        Self::from_degrees(value)
    }
}

#[cfg(feature = "serde")]
impl From<Latitude> for f64 {
    fn from(value: Latitude) -> Self {
        value.0
    }
}

#[cfg(feature = "serde")]
impl TryFrom<f64> for Longitude {
    type Error = NavigationError;

    /// Validates on the way in, so a stored value cannot be out of range.
    fn try_from(value: f64) -> Result<Self> {
        Self::from_degrees(value)
    }
}

#[cfg(feature = "serde")]
impl From<Longitude> for f64 {
    fn from(value: Longitude) -> Self {
        value.0
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::float_cmp, clippy::indexing_slicing)]
mod tests {
    use super::*;
    use alloc::format;

    #[test]
    fn latitude_validates() {
        assert!(Latitude::from_degrees(90.0).is_ok());
        assert!(Latitude::from_degrees(-90.0).is_ok());
        assert!(Latitude::from_degrees(90.000_001).is_err());
        assert!(Latitude::from_degrees(f64::NAN).is_err());
        assert!(Latitude::from_degrees(f64::INFINITY).is_err());
    }

    #[test]
    fn longitude_wraps_instead_of_failing() {
        assert_eq!(Longitude::from_degrees(180.0).unwrap().degrees(), -180.0);
        assert_eq!(Longitude::from_degrees(-180.0).unwrap().degrees(), -180.0);
        assert_eq!(Longitude::from_degrees(190.0).unwrap().degrees(), -170.0);
        assert_eq!(Longitude::from_degrees(-190.0).unwrap().degrees(), 170.0);
        assert_eq!(Longitude::from_degrees(720.5).unwrap().degrees(), 0.5);
        assert!(Longitude::from_degrees(f64::NAN).is_err());
    }

    #[test]
    fn degrees_and_minutes_round_trip() {
        let latitude = Latitude::from_degrees_minutes(50, 45.3, NorthSouth::North).unwrap();
        assert!((latitude.degrees() - 50.755).abs() < 1e-12);
        let (degrees, minutes, hemisphere) = latitude.to_degrees_minutes();
        assert_eq!(degrees, 50);
        assert!((minutes - 45.3).abs() < 1e-9);
        assert_eq!(hemisphere, NorthSouth::North);

        let longitude = Longitude::from_degrees_minutes(1, 17.8, EastWest::West).unwrap();
        assert!((longitude.degrees() + 1.296_666_667).abs() < 1e-9);
    }

    #[test]
    fn display_matches_chart_convention() {
        let position = Position::from_degrees(50.755, -1.296_666_667).unwrap();
        assert_eq!(format!("{position}"), "50°45.3'N 001°17.8'W");

        let southern = Position::from_degrees(-33.9, 151.2).unwrap();
        assert_eq!(format!("{southern}"), "33°54.0'S 151°12.0'E");

        // The rounding boundary must not produce 60.0 minutes.
        let boundary = Latitude::from_degrees(10.999_999_9).unwrap();
        assert_eq!(format!("{boundary}"), "11°00.0'N");
    }

    #[test]
    fn isometric_latitude_round_trips() {
        for degrees in [-85.0, -45.0, -0.5, 0.0, 0.5, 10.0, 45.0, 80.0, 89.0] {
            let latitude = Latitude::from_degrees(degrees).unwrap();
            let back = Latitude::from_isometric_minutes(latitude.isometric_minutes());
            assert!(
                (back.degrees() - degrees).abs() < 1e-9,
                "{degrees} came back as {}",
                back.degrees()
            );
        }
        // The poles are the limits, and clamp rather than overflow.
        assert!(Latitude::from_isometric_minutes(f64::INFINITY).is_polar());
        assert!(Latitude::from_isometric_minutes(f64::NEG_INFINITY).is_polar());
    }

    #[test]
    fn eccentricity_constant_is_the_square_root_it_claims_to_be() {
        let expected = WGS84_ECCENTRICITY_SQUARED.sqrt();
        assert!((WGS84_ECCENTRICITY - expected).abs() < 1e-15);
    }

    #[test]
    fn positions_read_back_from_what_they_print() {
        for (latitude, longitude) in [
            (50.755, -1.296_666_667),
            (-33.9, 151.2),
            (0.0, 0.0),
            (89.5, -179.5),
        ] {
            let position = Position::from_degrees(latitude, longitude).unwrap();
            let printed = alloc::format!("{position:.4}");
            let read: Position = printed.parse().unwrap();
            assert!(
                (read.latitude().degrees() - latitude).abs() < 1e-6,
                "{printed}"
            );
            assert!(
                read.longitude()
                    .difference_to(position.longitude())
                    .degrees()
                    .abs()
                    < 1e-6,
                "{printed}"
            );
        }
    }

    #[test]
    fn positions_parse_from_the_usual_forms() {
        let expected = Position::from_degrees(50.755, -1.296_666_667).unwrap();
        for input in [
            "50°45.3'N 001°17.8'W",
            "50 45.3 N 001 17.8 W",
            "N50°45.3' W001°17.8'",
            "50.755, -1.2966667",
            "50.755 -1.2966667",
        ] {
            let parsed: Position = input.parse().unwrap();
            assert!(
                (parsed.latitude().degrees() - expected.latitude().degrees()).abs() < 1e-6,
                "{input}"
            );
            assert!(
                (parsed.longitude().degrees() - expected.longitude().degrees()).abs() < 1e-6,
                "{input}"
            );
        }
    }

    #[test]
    fn the_wrong_hemisphere_letter_is_refused() {
        assert!("50°45.3'E".parse::<Latitude>().is_err());
        assert!("001°17.8'N".parse::<Longitude>().is_err());
        assert!("50°45.3'N".parse::<Longitude>().is_err());
        // And a latitude beyond the pole is still out of range.
        assert!("91 00.0 N".parse::<Latitude>().is_err());
        // A longitude past the antimeridian wraps, as it does everywhere else.
        assert_eq!("190".parse::<Longitude>().unwrap().degrees(), -170.0);
    }

    #[test]
    fn unreadable_input_is_an_error_not_a_panic() {
        for input in ["", "   ", "north", "50°45.3'N", "a b", "50 45.3 60.0"] {
            assert!(input.parse::<Position>().is_err(), "{input}");
        }

        // Two bare numbers are a latitude and a longitude, not one coordinate in
        // degrees and minutes: a position needs both halves, so that is the only
        // complete reading.
        let pair: Position = "50 45.3".parse().unwrap();
        assert_eq!(pair.latitude().degrees(), 50.0);
        assert_eq!(pair.longitude().degrees(), 45.3);
        for input in ["", "  ", "fifty", "50 60.0", "50 45 18 12"] {
            assert!(input.parse::<Latitude>().is_err(), "{input}");
            assert!(input.parse::<Longitude>().is_err(), "{input}");
        }
    }

    #[test]
    fn hemispheres() {
        assert_eq!(
            Latitude::from_degrees(0.0).unwrap().hemisphere(),
            NorthSouth::North
        );
        assert_eq!(
            Latitude::from_degrees(-0.1).unwrap().hemisphere(),
            NorthSouth::South
        );
        assert_eq!(
            Longitude::from_degrees(0.0).unwrap().hemisphere(),
            EastWest::East
        );
        assert_eq!(
            Longitude::from_degrees(-0.1).unwrap().hemisphere(),
            EastWest::West
        );
        assert!(Latitude::NORTH_POLE.is_polar());
        assert!(!Latitude::from_degrees(89.0).unwrap().is_polar());
    }

    #[test]
    fn longitude_difference_takes_the_short_way() {
        let west = Longitude::from_degrees(-179.0).unwrap();
        let east = Longitude::from_degrees(179.0).unwrap();
        assert!((west.difference_to(east).degrees() + 2.0).abs() < 1e-12);
        assert!((east.difference_to(west).degrees() - 2.0).abs() < 1e-12);
    }

    #[test]
    fn meridional_parts_match_the_tables() {
        // Meridional parts on WGS-84, from a independent evaluation of
        // a·[ln tan(π/4 + φ/2) − e·artanh(e sin φ)] in minutes of arc.
        for (degrees, expected) in [
            (10.0, 599.073),
            (30.0, 1876.862),
            (45.0, 3013.648),
            (60.0, 4507.404),
            (75.0, 6948.063),
        ] {
            let latitude = Latitude::from_degrees(degrees).unwrap();
            let parts = latitude.meridional_parts().unwrap();
            assert!(
                (parts - expected).abs() < 0.001,
                "at {degrees}°: {parts} vs {expected}"
            );
        }

        let latitude = Latitude::from_degrees(45.0).unwrap();
        // The spherical value the rhumb sailings use is measurably different.
        assert!((latitude.isometric_minutes() - 3029.9).abs() < 0.1);
        assert!(Latitude::EQUATOR.meridional_parts().unwrap().abs() < 1e-9);
        assert!(Latitude::NORTH_POLE.meridional_parts().is_err());

        // Symmetric about the equator.
        let south = Latitude::from_degrees(-45.0).unwrap();
        assert!((south.meridional_parts().unwrap() + 3013.648).abs() < 0.001);
    }

    #[test]
    fn unit_vectors_round_trip() {
        for (latitude, longitude) in [
            (0.0, 0.0),
            (45.0, 90.0),
            (-33.9, 151.2),
            (89.0, -179.0),
            (0.0, -180.0),
        ] {
            let position = Position::from_degrees(latitude, longitude).unwrap();
            let back = Position::from_unit_vector(position.to_unit_vector()).unwrap();
            assert!((back.latitude().degrees() - latitude).abs() < 1e-9);
            assert!(
                back.longitude()
                    .difference_to(position.longitude())
                    .degrees()
                    .abs()
                    < 1e-9
            );
        }
        assert!(Position::from_unit_vector([0.0, 0.0, 0.0]).is_none());
    }

    #[test]
    fn departure_matches_plane_sailing() {
        // One degree of longitude at 60° latitude is 30 miles of departure.
        let from = Position::from_degrees(60.0, 0.0).unwrap();
        let to = Position::from_degrees(60.0, 1.0).unwrap();
        assert!((from.departure(to).nautical_miles() - 30.0).abs() < 0.01);
        assert!((from.latitude_difference(to).degrees()).abs() < 1e-12);
    }
}
