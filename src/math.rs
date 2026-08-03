//! Floating point primitives, routed to `std` or to `libm` depending on features.
//!
//! Keeping every transcendental call behind this module is what lets the crate
//! compile as `no_std`: with `default-features = false, features = ["libm"]` the
//! same code links against the pure-Rust `libm` implementations instead.

#[cfg(feature = "std")]
mod imp {
    pub(crate) fn sin(x: f64) -> f64 {
        x.sin()
    }
    pub(crate) fn cos(x: f64) -> f64 {
        x.cos()
    }
    pub(crate) fn asin(x: f64) -> f64 {
        x.asin()
    }
    pub(crate) fn atan2(y: f64, x: f64) -> f64 {
        y.atan2(x)
    }
    pub(crate) fn sqrt(x: f64) -> f64 {
        x.sqrt()
    }
    pub(crate) fn abs(x: f64) -> f64 {
        x.abs()
    }
    pub(crate) fn tan(x: f64) -> f64 {
        x.tan()
    }
    pub(crate) fn atan(x: f64) -> f64 {
        x.atan()
    }
    pub(crate) fn acos(x: f64) -> f64 {
        x.acos()
    }
    pub(crate) fn ln(x: f64) -> f64 {
        x.ln()
    }
    pub(crate) fn exp(x: f64) -> f64 {
        x.exp()
    }
    pub(crate) fn hypot(x: f64, y: f64) -> f64 {
        x.hypot(y)
    }
    pub(crate) fn round(x: f64) -> f64 {
        x.round()
    }
    pub(crate) fn ceil(x: f64) -> f64 {
        x.ceil()
    }
    pub(crate) fn trunc(x: f64) -> f64 {
        x.trunc()
    }
}

#[cfg(all(not(feature = "std"), feature = "libm"))]
mod imp {
    pub(crate) fn sin(x: f64) -> f64 {
        libm::sin(x)
    }
    pub(crate) fn cos(x: f64) -> f64 {
        libm::cos(x)
    }
    pub(crate) fn asin(x: f64) -> f64 {
        libm::asin(x)
    }
    pub(crate) fn atan2(y: f64, x: f64) -> f64 {
        libm::atan2(y, x)
    }
    pub(crate) fn sqrt(x: f64) -> f64 {
        libm::sqrt(x)
    }
    pub(crate) fn abs(x: f64) -> f64 {
        libm::fabs(x)
    }
    pub(crate) fn tan(x: f64) -> f64 {
        libm::tan(x)
    }
    pub(crate) fn atan(x: f64) -> f64 {
        libm::atan(x)
    }
    pub(crate) fn acos(x: f64) -> f64 {
        libm::acos(x)
    }
    pub(crate) fn ln(x: f64) -> f64 {
        libm::log(x)
    }
    pub(crate) fn exp(x: f64) -> f64 {
        libm::exp(x)
    }
    pub(crate) fn hypot(x: f64, y: f64) -> f64 {
        libm::hypot(x, y)
    }
    pub(crate) fn round(x: f64) -> f64 {
        libm::round(x)
    }
    pub(crate) fn ceil(x: f64) -> f64 {
        libm::ceil(x)
    }
    pub(crate) fn trunc(x: f64) -> f64 {
        libm::trunc(x)
    }
}

#[cfg(not(any(feature = "std", feature = "libm")))]
compile_error!(
    "bearingpro needs floating point math: enable the default `std` feature, \
     or build with `--no-default-features --features libm` for `no_std` targets"
);

pub(crate) use imp::{
    abs, acos, asin, atan, atan2, ceil, cos, exp, hypot, ln, round, sin, sqrt, tan, trunc,
};

/// Degrees per radian, for `to_radians` without depending on `std`.
const DEGREES_PER_RADIAN: f64 = 180.0 / core::f64::consts::PI;

/// Converts degrees to radians.
pub(crate) fn to_radians(degrees: f64) -> f64 {
    degrees / DEGREES_PER_RADIAN
}

/// Converts radians to degrees.
pub(crate) fn to_degrees(radians: f64) -> f64 {
    radians * DEGREES_PER_RADIAN
}

/// Whether a value is a whole number.
///
/// An exact comparison is the right one here: the question is precisely whether
/// there is a fractional part, not whether there is nearly one.
#[allow(clippy::float_cmp)]
pub(crate) fn is_integral(value: f64) -> bool {
    value == trunc(value)
}

/// Rounds a value that is known to be within `i32`'s range to an `i32`.
///
/// The callers all pass angles bounded by 360, so nothing is lost.
#[allow(clippy::cast_possible_truncation)]
pub(crate) fn round_to_i32(value: f64) -> i32 {
    let rounded = round(value);
    if rounded > f64::from(i32::MAX) || rounded < f64::from(i32::MIN) {
        return 0;
    }
    rounded as i32
}

/// Truncates a non-negative value that is known to be small into a `usize`.
///
/// The callers bound the value first; anything unreasonable comes back as zero.
#[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
pub(crate) fn to_usize(value: f64) -> usize {
    // A NaN compares false against everything, so it fails the range test and
    // falls into the guard rather than through it.
    if !(0.0..=1e9).contains(&value) {
        return 0;
    }
    value as usize
}

/// Converts a count to a float.
///
/// Counts here are node counts and loop bounds, orders of magnitude below the
/// 2^53 where `f64` stops representing integers exactly.
#[allow(clippy::cast_precision_loss)]
pub(crate) fn count_to_f64(count: usize) -> f64 {
    count as f64
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn radian_conversion_round_trips() {
        for degrees in [0.0, 1.0, 45.0, 90.0, 180.0, 359.9] {
            let back = to_degrees(to_radians(degrees));
            assert!((back - degrees).abs() < 1e-12);
        }
    }

    #[test]
    fn trig_matches_known_values() {
        assert!(abs(sin(to_radians(90.0)) - 1.0) < 1e-12);
        assert!(abs(cos(to_radians(180.0)) + 1.0) < 1e-12);
        assert!(abs(to_degrees(atan2(1.0, 0.0)) - 90.0) < 1e-12);
        assert!(abs(hypot(3.0, 4.0) - 5.0) < 1e-12);
        assert!(abs(sqrt(9.0) - 3.0) < 1e-12);
        assert!(abs(to_degrees(asin(0.5)) - 30.0) < 1e-12);
    }
}
