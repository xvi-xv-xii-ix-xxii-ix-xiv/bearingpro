use crate::deviation::{DeviationTable, InterpolationMethod};
use crate::error::NavigationError;

/// Represents the result of a navigation task, containing the calculated course,
/// the applied deviation, and a flag indicating if further data verification is recommended.
pub struct NavigationResult {
    pub course: f64,    // Calculated course (either True Course or Compass Course)
    pub deviation: f64, // Deviation value applied in the calculation
    pub check_data_required: bool, // Flag to indicate if additional verification is needed
}

/// Converts a Compass Course (CC) to a True Course (TC) by applying declination and deviation.
///
/// The True Course (TC) is the actual geographical direction in which the vessel is moving,
/// while the Compass Course (CC) is the direction indicated by the ship's compass, subject to error from magnetic deviation.
/// The declination (also called magnetic variation) is the difference between true north and magnetic north.
///
/// # Arguments
///
/// * `cc` - Compass Course (in degrees).
/// * `decl` - Magnetic declination (in degrees).
/// * `dev_table` - Reference to the deviation table used for correction.
/// * `method` - Method for interpolating deviation (`InterpolationMethod::Linear` or `InterpolationMethod::Cubic`).
///
/// # Returns
///
/// `Ok(NavigationResult)` with the computed True Course (TC) and the applied deviation value,
/// as well as a flag indicating whether further checks are recommended.
///
/// # Errors
///
/// Returns a `NavigationError` if:
/// - The Compass Course (CC) is out of the 0° to 360° range.
/// - The magnetic declination (decl) is out of the valid range (-360° to 360°).
/// - The deviation data is missing or improperly initialized.
///
/// # Example
///
/// ```rust
/// use bearingpro::deviation::{DeviationTable, InterpolationMethod};
/// use bearingpro::navigation_solutions::convert_compass_course_to_true_course;
///
/// let mut dev_table = DeviationTable::default();
/// dev_table.set_deviation(0, -2.5).unwrap();
///
/// let cc = 3.0;
/// let decl = -10.0;
/// let result = convert_compass_course_to_true_course(cc, decl, &dev_table, InterpolationMethod::Linear).unwrap();
/// assert_eq!(format!("{:.2}", result.course), "351.25");
/// ```
pub fn convert_compass_course_to_true_course(
    cc: f64,
    decl: f64,
    dev_table: &DeviationTable,
    method: InterpolationMethod,
) -> Result<NavigationResult, NavigationError> {
    let cc = if cc == 360.0 { 0.0 } else { cc }; // Normalize 360° to 0°
    if !(0.0..360.0).contains(&cc) {
        return Err(NavigationError::CourseOutOfRange(cc));
    }

    if !(-360.0..=360.0).contains(&decl) {
        return Err(NavigationError::DeclinationOutOfRange(decl));
    }

    let check_data_required = decl.abs() > 15.0;

    // Interpolating deviation for the given compass course using the chosen method
    let deviation = dev_table
        .interpolate_deviation(&[cc], method, None)
        .map_err(|_| NavigationError::DeviationNotInitialized(cc.round() as i32))?[0];

    let tc = cc + (decl + deviation);

    Ok(NavigationResult {
        course: normalize_course(tc),
        deviation,
        check_data_required,
    })
}

/// Converts a True Course (TC) to a Compass Course (CC) using declination and deviation.
///
/// This function is typically used when converting from the geographical True Course (TC)
/// to the ship's Compass Course (CC), taking into account the magnetic declination and deviation.
///
/// # Arguments
///
/// * `tc` - True Course (in degrees).
/// * `decl` - Magnetic declination (in degrees).
/// * `dev_table` - Reference to the deviation table used for correction.
/// * `method` - Method for interpolating deviation (`InterpolationMethod::Linear` or `InterpolationMethod::Cubic`).
///
/// # Returns
///
/// `Ok(NavigationResult)` with the computed Compass Course (CC), the applied deviation value,
/// and a flag indicating whether further checks are required.
///
/// # Errors
///
/// Returns a `NavigationError` if:
/// - The True Course (TC) is out of the 0° to 360° range.
/// - The magnetic declination (decl) is out of the valid range (-360° to 360°).
/// - The deviation data is missing or improperly initialized.
///
/// # Example
///
/// ```rust
/// use bearingpro::deviation::{DeviationTable, InterpolationMethod};
/// use bearingpro::navigation_solutions::convert_true_course_to_compass_course;
///
/// let mut dev_table = DeviationTable::default();
/// dev_table.set_deviation(250, -15.7).unwrap();
///
/// let tc = 256.0;
/// let decl = 0.7;
/// let result = convert_true_course_to_compass_course(tc, decl, &dev_table, InterpolationMethod::Cubic).unwrap();
/// assert_eq!(format!("{:.2}", result.course), "271.37");
/// ```
pub fn convert_true_course_to_compass_course(
    tc: f64,
    decl: f64,
    dev_table: &DeviationTable,
    method: InterpolationMethod,
) -> Result<NavigationResult, NavigationError> {
    let tc = normalize_course(tc); // Normalize TC to the [0°, 360°) range
    if !(0.0..360.0).contains(&tc) {
        return Err(NavigationError::CourseOutOfRange(tc));
    }

    if !(-360.0..=360.0).contains(&decl) {
        return Err(NavigationError::DeclinationOutOfRange(decl));
    }

    let check_data_required = decl.abs() > 15.0;

    let mc = normalize_course(tc - decl); // Magnetic Course (MC), normalized
    let deviation = dev_table
        .interpolate_deviation(&[mc], method, None)
        .map_err(|_| NavigationError::DeviationNotInitialized(mc.round() as i32))?[0];
    let cc = normalize_course(mc - deviation);

    Ok(NavigationResult {
        course: cc,
        deviation,
        check_data_required,
    })
}

/// Computes the Magnetic Course (MC) from the True Course (TC) by applying magnetic declination.
///
/// The Magnetic Course is the course relative to the magnetic north, as opposed to the geographical north.
///
/// # Arguments
///
/// * `tc` - True Course (in degrees).
/// * `decl` - Magnetic declination (in degrees).
///
/// # Returns
///
/// `Ok(f64)` with the computed Magnetic Course (MC), or a `NavigationError` if the input is invalid.
///
/// # Errors
///
/// Returns a `NavigationError` if the True Course (TC) or declination is out of valid ranges.
///
/// # Example
///
/// ```rust
/// use bearingpro::navigation_solutions::calculate_magnetic_course;
///
/// let tc = 100.0;
/// let decl = 10.0;
/// let mc = calculate_magnetic_course(tc, decl).unwrap();
/// assert_eq!(mc, 90.0);
/// ```
pub fn calculate_magnetic_course(tc: f64, decl: f64) -> Result<f64, NavigationError> {
    if !(0.0..=360.0).contains(&tc) {
        return Err(NavigationError::CourseOutOfRange(tc));
    }

    if !(-360.0..=360.0).contains(&decl) {
        return Err(NavigationError::DeclinationOutOfRange(decl));
    }

    let mc = tc - decl;
    Ok(normalize_course(mc))
}

/// Calculates the course angle between the True Course (TC) and a given bearing (θ).
///
/// The Course Angle is the angular difference between the ship's True Course and a bearing, measured clockwise.
///
/// # Arguments
///
/// * `tc` - True Course (in degrees).
/// * `bearing` - Bearing to the object or waypoint (in degrees).
///
/// # Returns
///
/// `Ok(f64)` with the calculated course angle, or a `NavigationError` if the input values are out of range.
///
/// # Example
///
/// ```rust
/// use bearingpro::navigation_solutions::calculate_course_angle;
///
/// let tc = 90.0;
/// let bearing = 180.0;
/// let course_angle = calculate_course_angle(tc, bearing).unwrap();
/// assert_eq!(course_angle, 90.0);
/// ```
pub fn calculate_course_angle(tc: f64, bearing: f64) -> Result<f64, NavigationError> {
    if !(0.0..=360.0).contains(&tc) || !(0.0..=360.0).contains(&bearing) {
        return Err(NavigationError::CourseOutOfRange(tc));
    }

    let cu = bearing - tc;
    Ok(normalize_course(cu))
}

/// Converts a Magnetic Bearing (MB) to a True Bearing (TB) using the magnetic declination.
///
/// True Bearing is the direction of an object relative to true north, while Magnetic Bearing is relative to magnetic north.
///
/// # Arguments
///
/// * `mb` - Magnetic Bearing (in degrees).
/// * `decl` - Magnetic declination (in degrees).
///
/// # Returns
///
/// `Ok(f64)` with the True Bearing (TB), or a `NavigationError` if inputs are invalid.
///
/// # Example
///
/// ```rust
/// use bearingpro::navigation_solutions::calculate_true_bearing;
///
/// let mb = 100.0;
/// let decl = 10.0;
/// let tb = calculate_true_bearing(mb, decl).unwrap();
/// assert_eq!(tb, 110.0);
/// ```
pub fn calculate_true_bearing(mb: f64, decl: f64) -> Result<f64, NavigationError> {
    if !(0.0..=360.0).contains(&mb) {
        return Err(NavigationError::CourseOutOfRange(mb));
    }

    if !(-360.0..=360.0).contains(&decl) {
        return Err(NavigationError::DeclinationOutOfRange(decl));
    }

    let tb = mb + decl;
    Ok(normalize_course(tb))
}

/// Converts a Magnetic Bearing (MB) to a Compass Bearing (CB) using deviation.
///
/// Compass Bearing (CB) is the bearing relative to the ship's compass, which can be affected by the ship's magnetic field (deviation).
///
/// # Arguments
///
/// * `mb` - Magnetic Bearing (in degrees).
/// * `deviation` - Deviation value (in degrees).
///
/// # Returns
///
/// `Ok(f64)` with the Compass Bearing (CB), or a `NavigationError` if the input is invalid.
///
/// # Example
///
/// ```rust
/// use bearingpro::navigation_solutions::calculate_compass_bearing;
///
/// let mb = 100.0;
/// let deviation = 5.0;
/// let cb = calculate_compass_bearing(mb, deviation).unwrap();
/// assert_eq!(cb, 95.0);
/// ```
pub fn calculate_compass_bearing(mb: f64, deviation: f64) -> Result<f64, NavigationError> {
    if !(0.0..=360.0).contains(&mb) {
        return Err(NavigationError::CourseOutOfRange(mb));
    }

    let cb = mb - deviation;
    Ok(normalize_course(cb))
}

/// Normalizes any course value to the 0°-360° range.
///
/// This function ensures that a course angle (whether TC, CC, or MC) is within the valid range
/// of 0° to 360° by applying modulo arithmetic.
fn normalize_course(course: f64) -> f64 {
    (course + 360.0) % 360.0
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::deviation::{DeviationTable, InterpolationMethod};

    #[test]
    fn test_convert_compass_course_to_true_course_linear() {
        let mut dev_table = DeviationTable::default();
        dev_table.set_deviation(0, -2.5).unwrap();
        dev_table.set_deviation(10, -1.5).unwrap();

        let cc = 5.0;
        let decl = -10.0;
        let result = convert_compass_course_to_true_course(
            cc,
            decl,
            &dev_table,
            InterpolationMethod::Linear,
        )
        .unwrap();
        assert_eq!(format!("{:.2}", result.course), "353.00"); // Checking course
        assert_eq!(format!("{:.2}", result.deviation), "-2.00"); // Checking deviation
        assert!(!result.check_data_required); // Checking flag
    }

    #[test]
    fn test_convert_compass_course_to_true_course_cubic() {
        let mut dev_table = DeviationTable::default();
        dev_table.set_deviation(0, -2.5).unwrap();
        dev_table.set_deviation(10, -1.5).unwrap();

        let cc = 5.0;
        let decl = -10.0;
        let result =
            convert_compass_course_to_true_course(cc, decl, &dev_table, InterpolationMethod::Cubic)
                .unwrap();
        assert!(result.course > 351.0 && result.course < 353.0); // Expect slightly different value with cubic interpolation
        assert!(result.deviation > -2.6 && result.deviation < -1.5); // Checking deviation
        assert!(!result.check_data_required);
    }

    #[test]
    fn test_convert_true_course_to_compass_course_linear() {
        let mut dev_table = DeviationTable::default();
        dev_table.set_deviation(250, -15.7).unwrap();
        dev_table.set_deviation(260, -17.9).unwrap();

        let tc = 256.0;
        let decl = 0.7;
        let result = convert_true_course_to_compass_course(
            tc,
            decl,
            &dev_table,
            InterpolationMethod::Linear,
        )
        .unwrap();
        assert_eq!(format!("{:.2}", result.course), "272.17"); // Checking course
        assert_eq!(format!("{:.2}", result.deviation), "-16.87"); // Checking deviation
        assert!(!result.check_data_required);
    }

    #[test]
    fn test_convert_true_course_to_compass_course_cubic() {
        let mut dev_table = DeviationTable::default();
        dev_table.set_deviation(250, -15.7).unwrap();
        dev_table.set_deviation(260, -17.9).unwrap();

        let tc = 256.0;
        let decl = 0.7;
        let result =
            convert_true_course_to_compass_course(tc, decl, &dev_table, InterpolationMethod::Cubic)
                .unwrap();
        assert!(result.course > 271.0 && result.course < 272.0); // Expect slightly different value with cubic interpolation
        assert!(result.deviation > -17.9 && result.deviation < -15.7); // Checking deviation
        assert!(!result.check_data_required);
    }

    #[test]
    fn test_invalid_compass_course_out_of_range() {
        let mut dev_table = DeviationTable::default();
        dev_table.set_deviation(0, -2.5).unwrap();

        let cc = 400.0; // Invalid compass course out of range
        let decl = -10.0;
        let result = convert_compass_course_to_true_course(
            cc,
            decl,
            &dev_table,
            InterpolationMethod::Linear,
        );
        assert!(result.is_err()); // Should result in an error
    }

    #[test]
    fn test_invalid_declination_out_of_range() {
        let mut dev_table = DeviationTable::default();
        dev_table.set_deviation(0, -2.5).unwrap();

        let cc = 0.0;
        let decl = -400.0; // Invalid declination out of range
        let result = convert_compass_course_to_true_course(
            cc,
            decl,
            &dev_table,
            InterpolationMethod::Linear,
        );
        assert!(result.is_err()); // Should result in an error
    }

    #[test]
    fn test_calculate_magnetic_course() {
        let tc = 100.0;
        let decl = 10.0;
        let mc = calculate_magnetic_course(tc, decl).unwrap();
        assert_eq!(mc, 90.0); // Checking magnetic course calculation
    }

    #[test]
    fn test_calculate_course_angle() {
        let tc = 90.0;
        let bearing = 180.0;
        let course_angle = calculate_course_angle(tc, bearing).unwrap();
        assert_eq!(course_angle, 90.0); // Checking course angle calculation
    }

    #[test]
    fn test_calculate_true_bearing() {
        let mb = 100.0;
        let decl = 10.0;
        let tb = calculate_true_bearing(mb, decl).unwrap();
        assert_eq!(tb, 110.0); // Checking true bearing calculation
    }

    #[test]
    fn test_calculate_compass_bearing() {
        let mb = 100.0;
        let deviation = 5.0;
        let cb = calculate_compass_bearing(mb, deviation).unwrap();
        assert_eq!(cb, 95.0); // Checking compass bearing calculation
    }
}
