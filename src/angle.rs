//! Angle types that carry their reference frame in the type system.
//!
//! Every quantity in this crate used to be a bare `f64`, which meant that
//! `calculate_true_bearing(bearing, variation)` and
//! `calculate_true_bearing(variation, bearing)` both compiled and both produced a
//! plausible-looking course. The types here make that mistake impossible: a
//! [`CompassCourse`] cannot be passed where a [`MagneticCourse`] is expected, and
//! a [`Variation`] cannot be passed where a course is expected.
//!
//! They also carry the range invariant. A [`Direction`] is always finite and
//! always in `[0°, 360°)`, so the functions that consume one cannot fail on
//! range grounds and do not return `Result` at all.
//!
//! # Example
//!
//! ```rust
//! use bearingpro::{CompassCourse, Deviation, MagneticCourse, Variation};
//!
//! let cc = CompassCourse::new(3.0)?;
//! let variation = Variation::new(-2.7)?;
//!
//! // Out-of-range and non-finite inputs are rejected at construction.
//! assert!(CompassCourse::new(400.0).is_err());
//! assert!(Variation::new(f64::NAN).is_err());
//!
//! // 360° is accepted and normalised to 0°.
//! assert_eq!(CompassCourse::new(360.0)?.degrees(), 0.0);
//!
//! // Arbitrary values can be wrapped explicitly when that is what you mean.
//! assert_eq!(MagneticCourse::wrap(-10.0)?.degrees(), 350.0);
//! # Ok::<(), bearingpro::NavigationError>(())
//! ```

use core::fmt;
use core::marker::PhantomData;

use crate::error::{NavigationError, Result};
use crate::math;

/// Largest magnitude accepted for a magnetic variation, in degrees.
pub const MAX_VARIATION_DEG: f64 = 180.0;

/// Largest magnitude accepted for a compass deviation, in degrees.
pub const MAX_DEVIATION_DEG: f64 = 180.0;

/// Normalises any finite angle into `[0.0, 360.0)`.
///
/// Unlike the `(angle + 360.0) % 360.0` idiom this is correct for every finite
/// input, including values below `-360°`.
#[must_use]
pub fn wrap360(degrees: f64) -> f64 {
    let remainder = degrees % 360.0;
    if remainder < 0.0 {
        let shifted = remainder + 360.0;
        // A remainder of, say, -1e-16 is nearer to 360 than the next `f64` below
        // it, so the addition rounds to exactly 360.0 and would escape the
        // half-open interval. That value belongs at the other end.
        if shifted >= 360.0 {
            0.0
        } else {
            shifted
        }
    } else {
        // Adding zero turns a `-0.0` remainder into `+0.0`.
        remainder + 0.0
    }
}

/// Normalises any finite angle into `[-180.0, 180.0)`.
#[must_use]
pub fn wrap180(degrees: f64) -> f64 {
    let wrapped = wrap360(degrees);
    if wrapped >= 180.0 {
        wrapped - 360.0
    } else {
        wrapped
    }
}

pub(crate) fn ensure_finite(parameter: &'static str, value: f64) -> Result<()> {
    if value.is_finite() {
        Ok(())
    } else {
        Err(NavigationError::NotFinite { parameter, value })
    }
}

pub(crate) fn ensure_range(parameter: &'static str, value: f64, min: f64, max: f64) -> Result<()> {
    ensure_finite(parameter, value)?;
    if value < min || value > max {
        return Err(NavigationError::OutOfRange {
            parameter,
            value,
            min,
            max,
        });
    }
    Ok(())
}

mod sealed {
    pub trait Sealed {}
}

/// The reference frame a [`Direction`] is measured from.
///
/// This trait is sealed: the three frames below are the only ones that exist.
pub trait Frame: sealed::Sealed + Copy + Clone + fmt::Debug + 'static {
    /// Human readable frame name, used in error and display output.
    const NAME: &'static str;
    /// Single-letter suffix used when formatting, as in `045.0°M`.
    const SUFFIX: char;
}

/// Measured from true (geographic) north.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct True;

/// Measured from magnetic north.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Magnetic;

/// Measured from the direction the ship's compass card calls north.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Compass;

/// Measured from the direction the gyrocompass calls north.
///
/// A gyrocompass has no deviation — it is not magnetic — but it does have a
/// single error, which is why it gets a frame of its own rather than sharing the
/// compass one.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Gyro;

impl sealed::Sealed for True {}
impl sealed::Sealed for Magnetic {}
impl sealed::Sealed for Compass {}
impl sealed::Sealed for Gyro {}

impl Frame for True {
    const NAME: &'static str = "true";
    const SUFFIX: char = 'T';
}

impl Frame for Magnetic {
    const NAME: &'static str = "magnetic";
    const SUFFIX: char = 'M';
}

impl Frame for Compass {
    const NAME: &'static str = "compass";
    const SUFFIX: char = 'C';
}

impl Frame for Gyro {
    const NAME: &'static str = "gyro";
    const SUFFIX: char = 'G';
}

/// A direction in `[0°, 360°)`, tagged with the frame it is measured from.
///
/// Courses and bearings share this type: within one frame they are the same
/// quantity and obey the same arithmetic. What the type prevents is mixing
/// *frames* — the error that actually puts a ship aground.
#[derive(Clone, Copy, PartialEq, PartialOrd, Default)]
pub struct Direction<F: Frame> {
    degrees: f64,
    frame: PhantomData<F>,
}

/// A course or bearing referred to true north.
pub type TrueCourse = Direction<True>;
/// A bearing referred to true north. Alias of [`TrueCourse`].
pub type TrueBearing = Direction<True>;
/// A course or bearing referred to magnetic north.
pub type MagneticCourse = Direction<Magnetic>;
/// A bearing referred to magnetic north. Alias of [`MagneticCourse`].
pub type MagneticBearing = Direction<Magnetic>;
/// A course or bearing as read from the ship's compass.
pub type CompassCourse = Direction<Compass>;
/// A bearing as read from the ship's compass. Alias of [`CompassCourse`].
pub type CompassBearing = Direction<Compass>;
/// A course as read from the gyrocompass.
pub type GyroCourse = Direction<Gyro>;
/// A bearing as read from the gyrocompass. Alias of [`GyroCourse`].
pub type GyroBearing = Direction<Gyro>;

impl<F: Frame> Direction<F> {
    /// Due north, `000°`.
    pub const NORTH: Self = Self::from_wrapped(0.0);
    /// Due east, `090°`.
    pub const EAST: Self = Self::from_wrapped(90.0);
    /// Due south, `180°`.
    pub const SOUTH: Self = Self::from_wrapped(180.0);
    /// Due west, `270°`.
    pub const WEST: Self = Self::from_wrapped(270.0);

    /// Builds a direction from a value already known to lie in `[0.0, 360.0)`.
    const fn from_wrapped(degrees: f64) -> Self {
        Self {
            degrees,
            frame: PhantomData,
        }
    }

    /// Wraps a value that is already known to be finite.
    ///
    /// Used inside the crate where the inputs are validated newtypes, so the
    /// result cannot be `NaN` and no `Result` is needed.
    pub(crate) fn from_degrees_wrapped(degrees: f64) -> Self {
        Self::from_wrapped(wrap360(degrees))
    }

    /// Creates a direction from a reading in `[0.0, 360.0]`, mapping `360.0` to `0.0`.
    ///
    /// Values outside that interval are rejected rather than wrapped, because a
    /// course of `400°` is far more likely to be a typo or a unit mix-up than a
    /// deliberate way of writing `040°`. Use [`Direction::wrap`] when wrapping is
    /// what you actually mean.
    ///
    /// # Errors
    ///
    /// Returns [`NavigationError::NotFinite`] for `NaN` or an infinity, and
    /// [`NavigationError::OutOfRange`] for anything outside `[0.0, 360.0]`.
    pub fn new(degrees: f64) -> Result<Self> {
        ensure_range("course", degrees, 0.0, 360.0)?;
        Ok(Self::from_wrapped(wrap360(degrees)))
    }

    /// Creates a direction from any finite value, normalising it into `[0.0, 360.0)`.
    ///
    /// # Errors
    ///
    /// Returns [`NavigationError::NotFinite`] for `NaN` or an infinity.
    pub fn wrap(degrees: f64) -> Result<Self> {
        ensure_finite("course", degrees)?;
        Ok(Self::from_wrapped(wrap360(degrees)))
    }

    /// The direction in degrees, always finite and always in `[0.0, 360.0)`.
    #[must_use]
    pub const fn degrees(self) -> f64 {
        self.degrees
    }

    /// The direction in radians, in `[0.0, 2π)`.
    #[must_use]
    pub fn radians(self) -> f64 {
        math::to_radians(self.degrees)
    }

    /// The reciprocal direction, 180° away.
    #[must_use]
    pub fn reciprocal(self) -> Self {
        Self::from_wrapped(wrap360(self.degrees + 180.0))
    }

    /// Shifts the direction by `delta` degrees, wrapping the result.
    ///
    /// # Errors
    ///
    /// Returns [`NavigationError::NotFinite`] if `delta` is not finite.
    pub fn offset(self, delta: f64) -> Result<Self> {
        ensure_finite("delta", delta)?;
        Ok(Self::from_wrapped(wrap360(self.degrees + delta)))
    }

    /// Signed shortest angle from `self` to `other`, in `[-180.0, 180.0)`.
    ///
    /// Positive means `other` lies clockwise of `self`.
    #[must_use]
    pub fn signed_difference(self, other: Self) -> f64 {
        wrap180(other.degrees - self.degrees)
    }

    /// Unsigned shortest angle between two directions, in `[0.0, 180.0]`.
    #[must_use]
    pub fn angular_distance(self, other: Self) -> f64 {
        math::abs(self.signed_difference(other))
    }

    /// Re-labels the frame without changing the numeric value.
    ///
    /// Private on purpose: outside this crate a frame change must go through a
    /// conversion in [`crate::navigation_solutions`], which applies the correct
    /// variation or deviation.
    pub(crate) const fn relabel<G: Frame>(self) -> Direction<G> {
        Direction::from_wrapped(self.degrees)
    }
}

impl<F: Frame> fmt::Display for Direction<F> {
    /// Formats as `045.0°T`, the way a course is written on a chart.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let precision = f.precision().unwrap_or(1);
        write!(
            f,
            "{:0>width$.precision$}°{}",
            self.degrees,
            F::SUFFIX,
            width = if precision == 0 { 3 } else { precision + 4 },
        )
    }
}

impl<F: Frame> fmt::Debug for Direction<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}({}°)", F::NAME, self.degrees)
    }
}

/// Magnetic variation: the angle from true north to magnetic north.
///
/// Positive is easterly. True course = magnetic course + variation.
#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Default)]
#[cfg_attr(
    feature = "serde",
    derive(serde::Serialize, serde::Deserialize),
    serde(try_from = "f64", into = "f64")
)]
pub struct Variation(f64);

impl Variation {
    /// No variation.
    pub const ZERO: Self = Self(0.0);

    /// Creates a variation from a value in `[-180.0, 180.0]` degrees.
    ///
    /// The old API accepted `±360°`, which is not a physically meaningful
    /// variation; anything beyond a half turn is now rejected.
    ///
    /// # Errors
    ///
    /// Returns [`NavigationError::NotFinite`] for `NaN` or an infinity, and
    /// [`NavigationError::OutOfRange`] outside `[-180.0, 180.0]`.
    pub fn new(degrees: f64) -> Result<Self> {
        ensure_range("variation", degrees, -MAX_VARIATION_DEG, MAX_VARIATION_DEG)?;
        Ok(Self(degrees))
    }

    /// The variation in degrees, positive easterly.
    #[must_use]
    pub const fn degrees(self) -> f64 {
        self.0
    }
}

impl fmt::Display for Variation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let precision = f.precision().unwrap_or(1);
        let hemisphere = if self.0 < 0.0 { 'W' } else { 'E' };
        write!(f, "{:.precision$}°{hemisphere}", math::abs(self.0))
    }
}

/// Compass deviation: the angle from magnetic north to compass north.
///
/// Positive is easterly. Magnetic course = compass course + deviation.
#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Default)]
#[cfg_attr(
    feature = "serde",
    derive(serde::Serialize, serde::Deserialize),
    serde(try_from = "f64", into = "f64")
)]
pub struct Deviation(f64);

impl Deviation {
    /// No deviation.
    pub const ZERO: Self = Self(0.0);

    /// Creates a deviation from a value in `[-180.0, 180.0]` degrees.
    ///
    /// # Errors
    ///
    /// Returns [`NavigationError::NotFinite`] for `NaN` or an infinity, and
    /// [`NavigationError::OutOfRange`] outside `[-180.0, 180.0]`.
    pub fn new(degrees: f64) -> Result<Self> {
        ensure_range("deviation", degrees, -MAX_DEVIATION_DEG, MAX_DEVIATION_DEG)?;
        Ok(Self(degrees))
    }

    /// The deviation in degrees, positive easterly.
    #[must_use]
    pub const fn degrees(self) -> f64 {
        self.0
    }
}

impl fmt::Display for Deviation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let precision = f.precision().unwrap_or(1);
        let hemisphere = if self.0 < 0.0 { 'W' } else { 'E' };
        write!(f, "{:.precision$}°{hemisphere}", math::abs(self.0))
    }
}

/// Which side of the bow something lies on.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Side {
    /// Dead ahead, within a rounding tolerance.
    Ahead,
    /// To starboard, `000°` to `180°` relative.
    Starboard,
    /// Dead astern, within a rounding tolerance.
    Astern,
    /// To port, `180°` to `360°` relative.
    Port,
}

/// A bearing measured clockwise from the ship's head, in `[0°, 360°)`.
#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Default)]
#[cfg_attr(
    feature = "serde",
    derive(serde::Serialize, serde::Deserialize),
    serde(try_from = "f64", into = "f64")
)]
pub struct RelativeBearing(f64);

impl RelativeBearing {
    /// Dead ahead.
    pub const AHEAD: Self = Self(0.0);
    /// Right abeam.
    pub const ABEAM_STARBOARD: Self = Self(90.0);
    /// Dead astern.
    pub const ASTERN: Self = Self(180.0);
    /// Left abeam.
    pub const ABEAM_PORT: Self = Self(270.0);

    /// Creates a relative bearing from a value in `[0.0, 360.0]`, mapping `360.0` to `0.0`.
    ///
    /// # Errors
    ///
    /// Returns [`NavigationError::NotFinite`] for `NaN` or an infinity, and
    /// [`NavigationError::OutOfRange`] outside `[0.0, 360.0]`.
    pub fn new(degrees: f64) -> Result<Self> {
        ensure_range("relative bearing", degrees, 0.0, 360.0)?;
        Ok(Self(wrap360(degrees)))
    }

    /// Creates a relative bearing from any finite value, normalising it into `[0.0, 360.0)`.
    ///
    /// # Errors
    ///
    /// Returns [`NavigationError::NotFinite`] for `NaN` or an infinity.
    pub fn wrap(degrees: f64) -> Result<Self> {
        ensure_finite("relative bearing", degrees)?;
        Ok(Self(wrap360(degrees)))
    }

    /// Wraps a value that is already known to be finite.
    pub(crate) fn from_degrees_wrapped(degrees: f64) -> Self {
        Self(wrap360(degrees))
    }

    /// The relative bearing in degrees, in `[0.0, 360.0)`.
    #[must_use]
    pub const fn degrees(self) -> f64 {
        self.0
    }

    /// The relative bearing as a signed angle in `[-180.0, 180.0)`.
    ///
    /// Positive is to starboard, negative to port.
    #[must_use]
    pub fn signed_degrees(self) -> f64 {
        wrap180(self.0)
    }

    /// Which side of the bow the object lies on.
    #[must_use]
    pub fn side(self) -> Side {
        const TOLERANCE: f64 = 1e-9;
        let signed = self.signed_degrees();
        if math::abs(signed) < TOLERANCE {
            Side::Ahead
        } else if math::abs(math::abs(signed) - 180.0) < TOLERANCE {
            Side::Astern
        } else if signed > 0.0 {
            Side::Starboard
        } else {
            Side::Port
        }
    }
}

impl fmt::Display for RelativeBearing {
    /// Formats as `030.0° green` / `045.0° red`, the way a relative bearing is reported.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let precision = f.precision().unwrap_or(1);
        let magnitude = math::abs(self.signed_degrees());
        match self.side() {
            Side::Ahead => write!(f, "dead ahead"),
            Side::Astern => write!(f, "dead astern"),
            Side::Starboard => write!(f, "{magnitude:.precision$}° green"),
            Side::Port => write!(f, "{magnitude:.precision$}° red"),
        }
    }
}

#[cfg(feature = "serde")]
impl TryFrom<f64> for Variation {
    type Error = NavigationError;

    /// Validates on the way in, so a stored value cannot be out of range.
    fn try_from(value: f64) -> Result<Self> {
        Self::new(value)
    }
}

#[cfg(feature = "serde")]
impl From<Variation> for f64 {
    fn from(value: Variation) -> Self {
        value.0
    }
}

#[cfg(feature = "serde")]
impl TryFrom<f64> for Deviation {
    type Error = NavigationError;

    /// Validates on the way in, so a stored value cannot be out of range.
    fn try_from(value: f64) -> Result<Self> {
        Self::new(value)
    }
}

#[cfg(feature = "serde")]
impl From<Deviation> for f64 {
    fn from(value: Deviation) -> Self {
        value.0
    }
}

#[cfg(feature = "serde")]
impl TryFrom<f64> for RelativeBearing {
    type Error = NavigationError;

    /// Validates on the way in, so a stored value cannot be out of range.
    fn try_from(value: f64) -> Result<Self> {
        Self::new(value)
    }
}

#[cfg(feature = "serde")]
impl From<RelativeBearing> for f64 {
    fn from(value: RelativeBearing) -> Self {
        value.0
    }
}

#[cfg(feature = "serde")]
impl<F: Frame> serde::Serialize for Direction<F> {
    /// Written as plain degrees; the frame lives in the type, not the data.
    fn serialize<S: serde::Serializer>(
        &self,
        serializer: S,
    ) -> core::result::Result<S::Ok, S::Error> {
        serializer.serialize_f64(self.degrees)
    }
}

#[cfg(feature = "serde")]
impl<'de, F: Frame> serde::Deserialize<'de> for Direction<F> {
    /// Read back through [`Direction::new`], so a stored direction outside
    /// `[0°, 360°]` is rejected rather than trusted.
    fn deserialize<D: serde::Deserializer<'de>>(
        deserializer: D,
    ) -> core::result::Result<Self, D::Error> {
        let degrees = f64::deserialize(deserializer)?;
        Self::new(degrees).map_err(serde::de::Error::custom)
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::float_cmp, clippy::indexing_slicing)]
mod tests {
    use super::*;
    use alloc::format;

    #[test]
    fn wrap360_is_correct_below_minus_360() {
        // The old `(x + 360.0) % 360.0` returned -40.0 here.
        assert_eq!(wrap360(-400.0), 320.0);
        assert_eq!(wrap360(-720.0), 0.0);
        assert_eq!(wrap360(-0.0), 0.0);
        assert_eq!(wrap360(0.0), 0.0);
        assert_eq!(wrap360(360.0), 0.0);
        assert_eq!(wrap360(725.0), 5.0);
        assert!(wrap360(-1e15).is_finite());
    }

    #[test]
    fn wrap360_keeps_tiny_negatives_off_the_far_end() {
        // These round to exactly 360.0 when 360 is added naively.
        for value in [-1e-16, -1e-18, -f64::MIN_POSITIVE, -1e-14] {
            let wrapped = wrap360(value);
            assert!(
                (0.0..360.0).contains(&wrapped),
                "{value} wrapped to {wrapped}"
            );
        }
        assert_eq!(wrap360(-1e-16), 0.0);
        // A negative big enough to represent still lands just below 360.
        assert!(wrap360(-1e-10) < 360.0);
        assert!(wrap360(-1e-10) > 359.999);
    }

    #[test]
    fn wrap360_never_leaves_the_interval() {
        let mut value = -2000.0;
        while value < 2000.0 {
            let wrapped = wrap360(value);
            assert!((0.0..360.0).contains(&wrapped), "{value} -> {wrapped}");
            value += 0.37;
        }
    }

    #[test]
    fn wrap180_is_symmetric() {
        assert_eq!(wrap180(0.0), 0.0);
        assert_eq!(wrap180(90.0), 90.0);
        assert_eq!(wrap180(180.0), -180.0);
        assert_eq!(wrap180(190.0), -170.0);
        assert_eq!(wrap180(-190.0), 170.0);
    }

    #[test]
    fn direction_rejects_bad_input() {
        assert!(TrueCourse::new(f64::NAN).is_err());
        assert!(TrueCourse::new(f64::INFINITY).is_err());
        assert!(TrueCourse::new(-0.1).is_err());
        assert!(TrueCourse::new(400.0).is_err());
        assert!(TrueCourse::wrap(f64::NAN).is_err());
    }

    #[test]
    fn direction_normalises() {
        assert_eq!(TrueCourse::new(360.0).unwrap().degrees(), 0.0);
        assert_eq!(TrueCourse::wrap(-10.0).unwrap().degrees(), 350.0);
        assert_eq!(TrueCourse::wrap(730.0).unwrap().degrees(), 10.0);
    }

    #[test]
    fn reciprocal_round_trips() {
        for degrees in [0.0, 45.0, 179.0, 180.0, 359.9] {
            let direction = TrueCourse::new(degrees).unwrap();
            assert!((direction.reciprocal().reciprocal().degrees() - degrees).abs() < 1e-12);
        }
    }

    #[test]
    fn signed_difference_takes_the_short_way() {
        let a = TrueCourse::new(350.0).unwrap();
        let b = TrueCourse::new(10.0).unwrap();
        assert!((a.signed_difference(b) - 20.0).abs() < 1e-12);
        assert!((b.signed_difference(a) + 20.0).abs() < 1e-12);
        assert!((a.angular_distance(b) - 20.0).abs() < 1e-12);
    }

    #[test]
    fn variation_and_deviation_validate() {
        assert!(Variation::new(-181.0).is_err());
        assert!(Variation::new(f64::NAN).is_err());
        assert!(Variation::new(180.0).is_ok());
        assert!(Deviation::new(f64::INFINITY).is_err());
        assert_eq!(Deviation::ZERO.degrees(), 0.0);
    }

    #[test]
    fn relative_bearing_sides() {
        assert_eq!(RelativeBearing::new(0.0).unwrap().side(), Side::Ahead);
        assert_eq!(RelativeBearing::new(90.0).unwrap().side(), Side::Starboard);
        assert_eq!(RelativeBearing::new(180.0).unwrap().side(), Side::Astern);
        assert_eq!(RelativeBearing::new(270.0).unwrap().side(), Side::Port);
        assert!((RelativeBearing::new(270.0).unwrap().signed_degrees() + 90.0).abs() < 1e-12);
    }

    #[test]
    fn display_is_chart_style() {
        assert_eq!(format!("{}", TrueCourse::new(45.0).unwrap()), "045.0°T");
        assert_eq!(
            format!("{}", MagneticCourse::new(357.89).unwrap()),
            "357.9°M"
        );
        assert_eq!(format!("{}", Variation::new(-2.7).unwrap()), "2.7°W");
        assert_eq!(format!("{}", Deviation::new(1.5).unwrap()), "1.5°E");
        assert_eq!(
            format!("{}", RelativeBearing::new(300.0).unwrap()),
            "60.0° red"
        );
    }
}
