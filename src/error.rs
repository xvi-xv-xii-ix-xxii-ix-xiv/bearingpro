//! Error types shared by every fallible operation in this crate.
//!
//! The crate exposes a single error enum, [`NavigationError`]. Earlier versions
//! returned `Result<_, String>` from parts of the deviation API; that is gone, so
//! callers can now match on a failure instead of parsing a message.
//!
//! [`NavigationError`] is `#[non_exhaustive]`: new variants may be added without a
//! breaking release, so always include a wildcard arm when matching.

use alloc::string::String;
use core::fmt;

/// Result alias used throughout the crate.
pub type Result<T> = core::result::Result<T, NavigationError>;

/// Every way a navigation computation can fail.
///
/// No operation in this crate panics on caller-supplied data; anything that could
/// go wrong is reported through this type.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum NavigationError {
    /// A parameter was `NaN` or infinite.
    NotFinite {
        /// Name of the offending parameter.
        parameter: &'static str,
        /// The value that was supplied.
        value: f64,
    },

    /// A parameter was finite but outside its permitted interval.
    OutOfRange {
        /// Name of the offending parameter.
        parameter: &'static str,
        /// The value that was supplied.
        value: f64,
        /// Smallest accepted value, inclusive.
        min: f64,
        /// Largest accepted value, inclusive.
        max: f64,
    },

    /// A deviation table was requested with a step outside `1..=180` degrees.
    InvalidStep {
        /// The step that was supplied, in degrees.
        step: i32,
    },

    /// An operation needed more table nodes than were available.
    ///
    /// A table needs at least two nodes to interpolate at all, at least three for
    /// the periodic cubic spline, and at least as many nodes as there are free
    /// coefficients for a parametric fit.
    InsufficientNodes {
        /// Number of nodes present in the table.
        found: usize,
        /// Number of nodes the operation requires.
        required: usize,
        /// What needed the nodes.
        context: &'static str,
    },

    /// Two entries normalised to the same compass course.
    DuplicateCourse {
        /// The course, in degrees, that appeared twice.
        course: i32,
    },

    /// The compass course is not one of the table's nodes.
    CourseNotInTable {
        /// The normalised course, in degrees, that was looked up.
        course: i32,
    },

    /// The string was not one of the eight supported cardinal directions.
    UnknownCardinalDirection {
        /// The direction string that was supplied.
        direction: String,
    },

    /// A slice of deviations did not have the length the constructor requires.
    UnexpectedTableLength {
        /// Number of values that were supplied.
        found: usize,
        /// Number of values that were expected.
        expected: usize,
    },

    /// A linear system had no numerically usable solution.
    ///
    /// For a parametric fit this means the sample courses do not constrain the
    /// requested coefficients — for example, fitting five coefficients to nodes
    /// that all lie on one semicircle.
    SingularSystem {
        /// What was being solved.
        context: &'static str,
    },

    /// An iterative solver failed to reach the requested tolerance.
    ///
    /// For the compass-course inverse this means the deviation curve is not
    /// invertible near the requested course: it changes by more than one degree
    /// per degree of heading, so several compass courses map to the same magnetic
    /// course. Such a table describes a compass that cannot be steered by and
    /// should be re-swung.
    NotConverged {
        /// Number of iterations that were performed.
        iterations: u32,
        /// Size of the remaining residual, in degrees.
        residual: f64,
    },

    /// Two lines or circles never meet, so there is nothing to intersect.
    Parallel {
        /// What failed to intersect.
        context: &'static str,
    },

    /// The problem has no solution for these inputs.
    ///
    /// Unlike [`NavigationError::Indeterminate`], which means the answer is
    /// undefined, this means the answer definitely does not exist: no course
    /// achieves the requested closest approach, no circle passes through the
    /// given points.
    NoSolution {
        /// What could not be solved.
        context: &'static str,
    },

    /// A string could not be read as the value it was meant to be.
    Parse {
        /// What was being read: `"latitude"`, `"position"`, and so on.
        what: &'static str,
        /// What was offered, truncated if it was long.
        input: String,
    },

    /// A quantity is mathematically undefined for the given inputs.
    Indeterminate {
        /// Name of the quantity that could not be determined.
        quantity: &'static str,
    },

    /// The current is too strong for the vessel to make good the requested track.
    CurrentTooStrong {
        /// Speed of the current, in the caller's speed unit.
        drift: f64,
        /// Speed of the vessel through the water, in the same unit.
        speed_through_water: f64,
    },
}

impl fmt::Display for NavigationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NotFinite { parameter, value } => {
                write!(f, "{parameter} must be a finite number, got {value}")
            }
            Self::OutOfRange {
                parameter,
                value,
                min,
                max,
            } => write!(
                f,
                "{parameter} out of range: {value}. Must be between {min} and {max} degrees"
            ),
            Self::InvalidStep { step } => write!(
                f,
                "invalid deviation table step: {step}. Must be between 1 and 180 degrees"
            ),
            Self::InsufficientNodes {
                found,
                required,
                context,
            } => write!(
                f,
                "{context} needs at least {required} deviation nodes, table has {found}"
            ),
            Self::DuplicateCourse { course } => {
                write!(f, "duplicate compass course in deviation table: {course}")
            }
            Self::CourseNotInTable { course } => write!(
                f,
                "compass course {course} is not a node of this deviation table"
            ),
            Self::UnknownCardinalDirection { direction } => write!(
                f,
                "unknown cardinal direction: {direction}. Expected one of N, NE, E, SE, S, SW, W, NW"
            ),
            Self::UnexpectedTableLength { found, expected } => write!(
                f,
                "expected {expected} deviation values, got {found}"
            ),
            Self::SingularSystem { context } => {
                write!(f, "singular system while solving {context}")
            }
            Self::NotConverged {
                iterations,
                residual,
            } => write!(
                f,
                "solver did not converge after {iterations} iterations, residual {residual} degrees"
            ),
            Self::Parse { what, input } => {
                write!(f, "could not read {input:?} as a {what}")
            }
            Self::Parallel { context } => write!(f, "{context} never meet"),
            Self::NoSolution { context } => {
                write!(f, "no solution exists for {context}")
            }
            Self::Indeterminate { quantity } => {
                write!(f, "{quantity} is indeterminate for these inputs")
            }
            Self::CurrentTooStrong {
                drift,
                speed_through_water,
            } => write!(
                f,
                "current of {drift} is too strong for a speed through water of {speed_through_water}"
            ),
        }
    }
}

// `std::error::Error` has been a re-export of `core::error::Error` since Rust
// 1.81, so this single impl covers both `std` and `no_std` builds.
impl core::error::Error for NavigationError {}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::string::ToString;

    #[test]
    fn every_variant_has_a_message() {
        let errors = [
            NavigationError::NotFinite {
                parameter: "course",
                value: f64::NAN,
            },
            NavigationError::OutOfRange {
                parameter: "course",
                value: 400.0,
                min: 0.0,
                max: 360.0,
            },
            NavigationError::InvalidStep { step: 0 },
            NavigationError::InsufficientNodes {
                found: 1,
                required: 2,
                context: "interpolation",
            },
            NavigationError::DuplicateCourse { course: 10 },
            NavigationError::CourseNotInTable { course: 50 },
            NavigationError::UnknownCardinalDirection {
                direction: "XYZ".to_string(),
            },
            NavigationError::UnexpectedTableLength {
                found: 5,
                expected: 36,
            },
            NavigationError::SingularSystem {
                context: "parametric fit",
            },
            NavigationError::NotConverged {
                iterations: 64,
                residual: 1.0,
            },
            NavigationError::Parse {
                what: "latitude",
                input: "north-ish".to_string(),
            },
            NavigationError::Parallel {
                context: "the two great circles",
            },
            NavigationError::NoSolution {
                context: "a course achieving that closest approach",
            },
            NavigationError::Indeterminate {
                quantity: "course over ground",
            },
            NavigationError::CurrentTooStrong {
                drift: 10.0,
                speed_through_water: 2.0,
            },
        ];

        for error in &errors {
            assert!(!error.to_string().is_empty());
        }
    }

    #[test]
    fn errors_compare_by_value() {
        let a = NavigationError::InvalidStep { step: 0 };
        let b = NavigationError::InvalidStep { step: 0 };
        let c = NavigationError::InvalidStep { step: -1 };
        assert_eq!(a, b);
        assert_ne!(a, c);
    }
}
