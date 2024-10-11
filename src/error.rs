use std::fmt;

/// Custom error type for navigation-related tasks.
///
/// These errors represent invalid inputs or conditions encountered during the process
/// of converting or calculating maritime courses and bearings.
#[derive(Debug, Clone)]
pub enum NavigationError {
    /// Error when an invalid compass course (CC) is provided.
    /// Compass Course must be a multiple of 10 and between 0° and 350°.
    InvalidCompassCourse(i32),

    /// Error when deviation values are not properly initialized or missing for a given compass course.
    DeviationNotInitialized(i32),

    /// Error when a provided course (TC, CC, or MC) is outside the valid range of 0° to 360°.
    CourseOutOfRange(f64),

    /// Error when the declination value is out of the range of -360° to 360°.
    DeclinationOutOfRange(f64),
}

impl fmt::Display for NavigationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NavigationError::InvalidCompassCourse(cc) => {
                write!(
                    f,
                    "Invalid compass course: {}. Must be a multiple of 10.",
                    cc
                )
            }
            NavigationError::DeviationNotInitialized(cc) => {
                write!(f, "Deviation for compass course {} is not initialized.", cc)
            }
            NavigationError::CourseOutOfRange(course) => {
                write!(
                    f,
                    "Course out of range: {}. Course must be between 0 and 360 degrees.",
                    course
                )
            }
            NavigationError::DeclinationOutOfRange(decl) => {
                write!(f, "Declination out of range: {}. Declination must be between -360 and 360 degrees.", decl)
            }
        }
    }
}

impl std::error::Error for NavigationError {}
