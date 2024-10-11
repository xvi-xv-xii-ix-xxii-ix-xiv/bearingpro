use std::collections::HashMap;

/// Enum to define the interpolation methods available for calculating deviation.
///
/// - **Linear**: Simple linear interpolation between two known deviation values.
/// - **Cubic**: Cubic spline interpolation, providing smoother results for continuous deviation data.
/// - **Parametric**: Parametric interpolation using user-defined coefficients for greater flexibility.
#[derive(Debug, Clone, Copy)]
pub enum InterpolationMethod {
    Linear,
    Cubic,
    Parametric,
}

/// Structure to hold deviation coefficients in the δ calculation formula.
///
/// The formula used is:
///
/// δ = A + B * sin(y) + C * cos(y) + D * sin(2y) + E * cos(2y)
///
/// Users can provide their own coefficients or allow the system to calculate them.
///
/// # Example
///
/// ```rust
/// let coeffs = bearingpro::deviation::DeviationCoefficients {
///     a: Some(1.0),
///     b: Some(-0.5),
///     c: None, // Will be calculated automatically
///     d: None, // Will be calculated automatically
///     e: None, // Will be calculated automatically
/// };
///
/// let dev_table = bearingpro::deviation::DeviationTable::from_step(10);
///
/// let deviations = dev_table.interpolate_deviation(&[250.0], bearingpro::deviation::InterpolationMethod::Parametric, Some(coeffs));
/// ```
#[derive(Debug, Clone)]
pub struct DeviationCoefficients {
    pub a: Option<f64>, // A: Base or constant deviation
    pub b: Option<f64>, // B: Sine deviation
    pub c: Option<f64>, // C: Cosine deviation
    pub d: Option<f64>, // D: Harmonic sine deviation
    pub e: Option<f64>, // E: Harmonic cosine deviation
}

/// A table containing deviation values for specific compass courses.
///
/// The `DeviationTable` allows for easy storage, retrieval, and interpolation of deviation values.
/// It is typically used to correct compass errors caused by the ship's internal magnetic influence,
/// enabling accurate compass course readings.
///
/// The table can be initialized with custom steps (e.g., 10°, 45°, or predefined cardinal directions like N, NE, E).
#[derive(Debug, Clone)]
pub struct DeviationTable {
    table: HashMap<i32, f64>, // Mapping of Compass Course (CC) to deviation values
}

impl Default for DeviationTable {
    /// Default constructor creates a deviation table with courses from 0° to 350° in 10° intervals.
    ///
    /// # Example
    ///
    /// ```rust
    /// let dev_table = bearingpro::deviation::DeviationTable::default();
    /// ```
    fn default() -> Self {
        Self::from_step(10)
    }
}

impl DeviationTable {
    /// Creates a new deviation table with a custom step between courses (e.g., 10°, 45°, etc.).
    ///
    /// # Arguments
    ///
    /// * `step` - Step in degrees between compass courses (e.g., 10 for 10° step, 45 for cardinal directions).
    ///
    /// # Example
    ///
    /// ```rust
    /// let dev_table = bearingpro::deviation::DeviationTable::from_step(10); // Initialize with 10° step.
    /// let dev_table_cardinal = bearingpro::deviation::DeviationTable::from_step(45); // Initialize with cardinal directions.
    /// ```
    pub fn from_step(step: i32) -> Self {
        let mut table = HashMap::new();
        for cc in (0..=360).step_by(step as usize) {
            table.insert(cc % 360, 0.0); // Normalize to 0-360°
        }
        Self { table }
    }

    /// Creates a new deviation table using pre-defined cardinal and intercardinal directions.
    ///
    /// The directions are defined as follows:
    /// - N = 0°, NE = 45°, E = 90°, SE = 135°, S = 180°, SW = 225°, W = 270°, NW = 315°
    ///
    /// # Example
    ///
    /// ```rust
    /// let dev_table = bearingpro::deviation::DeviationTable::from_cardinal_directions();
    /// ```
    pub fn from_cardinal_directions() -> Self {
        let mut table = HashMap::new();
        let directions = vec![
            (0, "N"),    // North
            (45, "NE"),  // North-East
            (90, "E"),   // East
            (135, "SE"), // South-East
            (180, "S"),  // South
            (225, "SW"), // South-West
            (270, "W"),  // West
            (315, "NW"), // North-West
        ];

        for (angle, _) in directions {
            table.insert(angle, 0.0);
        }
        Self { table }
    }

    /// Sets the deviation for a specific cardinal direction.
    ///
    /// # Arguments
    ///
    /// * `direction` - String representing the direction (e.g., "N", "NE", "E", etc.).
    /// * `deviation` - The deviation value in degrees.
    ///
    /// # Returns
    ///
    /// `Ok(())` if successful, or `Err` with an error message if the direction is invalid.
    pub fn set_deviation_by_direction(
        &mut self,
        direction: &str,
        deviation: f64,
    ) -> Result<(), String> {
        let direction_map = Self::cardinal_direction_to_angle();
        if let Some(&angle) = direction_map.get(direction) {
            self.table.insert(angle, deviation);
            Ok(())
        } else {
            Err(format!("Invalid direction: {}", direction))
        }
    }

    /// Retrieves the deviation for a specific cardinal direction.
    ///
    /// # Arguments
    ///
    /// * `direction` - String representing the direction (e.g., "N", "NE", "E", etc.).
    ///
    /// # Returns
    ///
    /// `Some(f64)` with the deviation value if the direction is valid, or `None` if the direction is invalid.
    pub fn get_deviation_by_direction(&self, direction: &str) -> Option<f64> {
        let direction_map = Self::cardinal_direction_to_angle();
        if let Some(&angle) = direction_map.get(direction) {
            self.table.get(&angle).copied()
        } else {
            None
        }
    }

    /// Maps cardinal direction strings to their corresponding compass course angles.
    fn cardinal_direction_to_angle() -> HashMap<&'static str, i32> {
        HashMap::from([
            ("N", 0),
            ("NE", 45),
            ("E", 90),
            ("SE", 135),
            ("S", 180),
            ("SW", 225),
            ("W", 270),
            ("NW", 315),
        ])
    }

    /// Sets the deviation for a specific compass course.
    ///
    /// # Arguments
    ///
    /// * `cc` - Compass Course (must be valid in the current table, such as 0° to 360°).
    /// * `deviation` - The deviation value in degrees.
    ///
    /// # Returns
    ///
    /// `Ok(())` if successful, or `Err` with an error message if the compass course is invalid.
    pub fn set_deviation(&mut self, cc: i32, deviation: f64) -> Result<(), String> {
        let cc = cc % 360; // Normalize to 0-360°

        //if self.table.contains_key(&cc) {
        if let std::collections::hash_map::Entry::Occupied(_e) = self.table.entry(cc) {
            self.table.insert(cc, deviation);
            Ok(())
        } else {
            Err(format!(
                "Invalid compass course: {}°. The course is not defined in the table.",
                cc
            ))
        }
    }

    /// Initializes a deviation table from a vector of `(i32, f64)` tuples.
    ///
    /// This allows users to provide specific courses and their corresponding deviation values.
    ///
    /// # Example
    ///
    /// ```rust
    /// let deviations = vec![(0, -2.5), (90, -1.0)];
    /// let dev_table = bearingpro::deviation::DeviationTable::from_vec(deviations);
    /// ```
    pub fn from_vec(deviations: Vec<(i32, f64)>) -> Self {
        let mut table = HashMap::new();
        for (cc, deviation) in deviations {
            table.insert(cc % 360, deviation); // Normalize courses to 0-360°
        }
        Self { table }
    }

    /// Initializes the deviation table from a vector of deviations.
    ///
    /// The deviations should correspond to compass courses from 0° to 350°
    /// with a step of 10°. If the vector length is less than required, the remaining entries will be set to 0.
    ///
    /// # Example
    ///
    /// ```rust
    /// let deviations = vec![-2.5, -0.5, 0.0, 1.0, 2.0];
    /// let dev_table = bearingpro::deviation::DeviationTable::from_deviation_vec(deviations);
    /// ```
    pub fn from_deviation_vec(deviations: Vec<f64>) -> Self {
        let mut table = HashMap::new();
        let courses: Vec<i32> = (0..=350).step_by(10).collect();

        for (i, &cc) in courses.iter().enumerate() {
            let deviation = deviations.get(i).copied().unwrap_or(0.0);
            table.insert(cc, deviation);
        }

        Self { table }
    }

    /// Interpolates deviation values for non-standard compass angles using the specified interpolation method.
    ///
    /// This function is used when deviations are needed for angles not directly stored in the table.
    ///
    /// # Arguments
    ///
    /// * `new_angles` - A slice of compass angles (in degrees) for which to interpolate deviations.
    /// * `method` - The method of interpolation (`InterpolationMethod::Linear`, `InterpolationMethod::Cubic`, or `InterpolationMethod::Parametric`).
    /// * `coefficients` - Optional coefficients to use for parametric interpolation. Users can provide their own values or let the system calculate them.
    ///
    /// # Returns
    ///
    /// A `Result` containing a vector of interpolated deviation values corresponding to the given angles,
    /// or an error message if any angles are out of range.
    ///
    /// # Errors
    ///
    /// Returns an error if any angles are outside the valid range (0° to 360°).
    ///
    /// # Example
    ///
    pub fn interpolate_deviation(
        &self,
        new_angles: &[f64],
        method: InterpolationMethod,
        coefficients: Option<DeviationCoefficients>,
    ) -> Result<Vec<f64>, String> {
        if new_angles
            .iter()
            .any(|&angle| !(0.0..=360.0).contains(&angle))
        {
            return Err(
                "One or more angles are out of range. Angles must be between 0° and 360°."
                    .to_string(),
            );
        }

        // Extract compass courses and their corresponding deviation values, sorted by angle.
        let mut pairs: Vec<(f64, f64)> = self
            .table
            .iter()
            .map(|(&cc, &dev)| (cc as f64, dev))
            .collect();
        pairs.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap());

        let (courses_sorted, deviations_sorted): (Vec<f64>, Vec<f64>) = pairs.into_iter().unzip();

        // Create a default coefficients if none were provided
        let coeffs = coefficients.unwrap_or(DeviationCoefficients {
            a: None,
            b: None,
            c: None,
            d: None,
            e: None,
        });

        match method {
            InterpolationMethod::Linear => Ok(linear_interpolation(
                &courses_sorted,
                &deviations_sorted,
                new_angles,
            )),
            InterpolationMethod::Cubic => Ok(cubic_interpolation(
                &courses_sorted,
                &deviations_sorted,
                new_angles,
            )),
            InterpolationMethod::Parametric => Ok(parametric_interpolation(
                &courses_sorted,
                &deviations_sorted,
                new_angles,
                coeffs,
            )),
        }
    }
}

/// Helper function for cubic interpolation between deviation values.
///
/// This function provides smoother transitions between known deviation values for angles not stored in the table.
///
/// # Arguments
///
/// * `angles` - A slice of sorted compass course angles (in degrees).
/// * `deviations` - A slice of deviation values corresponding to the `angles`.
/// * `new_angles` - A slice of compass angles (in degrees) for which to interpolate deviations.
///
/// # Returns
///
/// A vector of interpolated deviation values corresponding to the `new_angles`.
///
fn cubic_interpolation(angles: &[f64], deviations: &[f64], new_angles: &[f64]) -> Vec<f64> {
    let n = angles.len();
    let mut result = Vec::new();

    let mut a = vec![0.0; n - 1];
    let mut b = vec![0.0; n - 1];
    let mut c_coeff = vec![0.0; n - 1];
    let mut d = vec![0.0; n - 1];

    for i in 0..n - 1 {
        let h = angles[i + 1] - angles[i];
        let delta = (deviations[i + 1] - deviations[i]) / h;

        if i > 0 {
            let prev_h = angles[i] - angles[i - 1];
            let prev_delta = (deviations[i] - deviations[i - 1]) / prev_h;

            a[i] = prev_delta; // Slope of the left interval
            b[i] = delta; // Slope of the right interval
        }
        c_coeff[i] = deviations[i];
        d[i] = (b[i] - a[i]) / (2.0 * h); // Coefficient of cubic interpolation
    }

    for &new_angle in new_angles {
        let mut i = 0;
        while i < n - 1 && new_angle > angles[i + 1] {
            i += 1;
        }
        if i < n - 1 {
            let h = angles[i + 1] - angles[i];
            let t = (new_angle - angles[i]) / h; // Normalized distance within the interval

            let interpolated_value = c_coeff[i] + t * (a[i] + t * (b[i] + t * d[i]));
            result.push(interpolated_value);
        } else {
            result.push(deviations[n - 1]);
        }
    }

    result
}

/// Helper function for linear interpolation between deviation values.
///
/// This function provides a simple linear interpolation between known deviation values for angles not stored in the table.
///
/// # Arguments
///
/// * `angles` - A slice of sorted compass course angles (in degrees).
/// * `deviations` - A slice of deviation values corresponding to the `angles`.
/// * `new_angles` - A slice of compass angles (in degrees) for which to interpolate deviations.
///
/// # Returns
///
/// A vector of interpolated deviation values corresponding to the `new_angles`.
///
fn linear_interpolation(angles: &[f64], deviations: &[f64], new_angles: &[f64]) -> Vec<f64> {
    let n = angles.len();
    let mut result = Vec::new();

    for &new_angle in new_angles {
        let mut i = 0;
        while i < n - 1 && new_angle > angles[i + 1] {
            i += 1;
        }
        if i < n - 1 {
            let x0 = angles[i];
            let y0 = deviations[i];
            let x1 = angles[i + 1];
            let y1 = deviations[i + 1];

            let interpolated_value = y0 + (new_angle - x0) * (y1 - y0) / (x1 - x0);
            result.push(interpolated_value);
        } else {
            result.push(deviations[n - 1]);
        }
    }

    result
}

/// Performs parametric interpolation using user-defined coefficients.
///
/// The formula used is:
///
///  δ = A + B * sin(y) + C * cos(y) + D * sin(2y) + E * cos(2y)
///
/// # Arguments
///
/// * `angles` - A slice of sorted compass course angles (in degrees).
/// * `deviations` - A slice of deviation values corresponding to the `angles`.
/// * `new_angles` - A slice of compass angles (in degrees) for which to calculate deviations.
/// * `coefficients` - Struct containing the coefficients for the parametric equation.
///
/// # Returns
///
/// A vector of calculated deviation values based on the parametric formula.
///
/// # Panics
///
/// Panics if the lengths of `angles` and `deviations` do not match.
///
/// # Example
///

fn parametric_interpolation(
    angles: &[f64],
    deviations: &[f64],
    new_angles: &[f64],
    coefficients: DeviationCoefficients,
) -> Vec<f64> {
    // Ensure that the input arrays have the same length
    assert_eq!(
        angles.len(),
        deviations.len(),
        "Angles and deviations must have the same length."
    );

    let n = angles.len() as f64;

    // Precompute sums
    let sum_a = deviations.iter().sum::<f64>();
    let sum_sin = angles.iter().map(|&x| x.to_radians().sin()).sum::<f64>();
    let sum_cos = angles.iter().map(|&x| x.to_radians().cos()).sum::<f64>();
    let sum_sin2 = angles
        .iter()
        .map(|&x| (2.0 * x.to_radians()).sin())
        .sum::<f64>();
    let sum_cos2 = angles
        .iter()
        .map(|&x| (2.0 * x.to_radians()).cos())
        .sum::<f64>();

    // Calculate coefficients if not provided
    let (a, b, c, d, e) = (
        coefficients.a.unwrap_or_else(|| sum_a / n),
        coefficients.b.unwrap_or_else(|| (n * sum_sin) / n),
        coefficients.c.unwrap_or_else(|| (n * sum_cos) / n),
        coefficients.d.unwrap_or_else(|| (n * sum_sin2) / n),
        coefficients.e.unwrap_or_else(|| (n * sum_cos2) / n),
    );

    // Compute the deviation for each angle in new_angles
    new_angles
        .iter()
        .map(|&cc| {
            let cc_rad = cc.to_radians(); // Convert compass course to radians for trigonometric functions
            a + b * cc_rad.sin()
                + c * cc_rad.cos()
                + d * (2.0 * cc_rad).sin()
                + e * (2.0 * cc_rad).cos()
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_default_deviation_table() {
        let dev_table = DeviationTable::default();
        assert_eq!(dev_table.table.get(&0), Some(&0.0));
        assert_eq!(dev_table.table.get(&90), Some(&0.0));
    }

    #[test]
    fn test_cardinal_directions_table() {
        let mut dev_table = DeviationTable::from_cardinal_directions();

        assert_eq!(dev_table.table.get(&0), Some(&0.0)); // N
        assert_eq!(dev_table.table.get(&45), Some(&0.0)); // NE

        dev_table.set_deviation_by_direction("N", -2.5).unwrap();
        dev_table.set_deviation_by_direction("E", 1.0).unwrap();

        assert_eq!(dev_table.get_deviation_by_direction("N"), Some(-2.5)); // N
        assert_eq!(dev_table.get_deviation_by_direction("E"), Some(1.0)); // E
        assert_eq!(dev_table.get_deviation_by_direction("SW"), Some(0.0)); // SW (default)

        assert_eq!(dev_table.get_deviation_by_direction("XYZ"), None); // Invalid direction
    }

    #[test]
    fn test_set_deviation() {
        let mut dev_table = DeviationTable::from_cardinal_directions();
        dev_table.set_deviation(90, -1.0).unwrap();
        assert_eq!(dev_table.table.get(&90), Some(&-1.0));
    }

    #[test]
    fn test_set_invalid_deviation() {
        let mut dev_table = DeviationTable::from_cardinal_directions();
        let result = dev_table.set_deviation(50, -1.0); // Invalid angle for cardinal directions
        assert!(result.is_err());
    }

    #[test]
    fn test_interpolate_deviation_linear() {
        let mut dev_table = DeviationTable::from_step(10);
        dev_table.set_deviation(0, -2.5).unwrap();
        dev_table.set_deviation(10, -1.5).unwrap();

        let interpolated_deviation = dev_table
            .interpolate_deviation(&[5.0], InterpolationMethod::Linear, None)
            .unwrap();
        assert_eq!(interpolated_deviation[0], (-2.0));
        assert!((interpolated_deviation[0] - (-2.0)).abs() < 1e-5);
    }

    #[test]
    fn test_interpolate_deviation_cubic() {
        let mut dev_table = DeviationTable::from_step(10);
        dev_table.set_deviation(0, -2.5).unwrap();
        dev_table.set_deviation(10, -1.5).unwrap();

        let interpolated_deviation = dev_table
            .interpolate_deviation(&[5.0], InterpolationMethod::Cubic, None)
            .unwrap();
        assert!((interpolated_deviation[0] - (-2.5)).abs() < 1e-5); // Example cubic interpolation
    }

    #[test]
    fn test_interpolate_invalid_angle() {
        let dev_table = DeviationTable::from_step(10);
        let result = dev_table.interpolate_deviation(&[400.0], InterpolationMethod::Linear, None); // Invalid angle
        assert!(result.is_err());
    }

    #[test]
    fn test_custom_step_table() {
        let dev_table = DeviationTable::from_step(45);
        assert_eq!(dev_table.table.get(&45), Some(&0.0)); // NE
        assert_eq!(dev_table.table.get(&135), Some(&0.0)); // SE
    }

    #[test]
    fn test_from_vec_initialization() {
        let deviations = vec![(0, -2.5), (90, -1.0)];
        let dev_table = DeviationTable::from_vec(deviations);
        assert_eq!(dev_table.table.get(&0), Some(&-2.5));
        assert_eq!(dev_table.table.get(&90), Some(&-1.0));
    }
}
