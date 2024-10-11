//! # Navigation Library
//!
//! A Rust library designed to assist in solving common maritime navigation problems, particularly in the context of compass corrections, bearing calculations, and course adjustments. This library allows for efficient handling of:
//!
//! - **True Course (TC)**: The actual geographical direction in which a vessel is traveling.
//! - **Magnetic Course (MC)**: The direction of a vessel relative to the Earth's magnetic field.
//! - **Compass Course (CC)**: The direction as indicated by a ship's compass, which is subject to both deviation (error due to the ship's magnetic environment) and variation (magnetic declination).
//! - **Relative Bearing (RB)**: The angular difference between the ship's heading and an object or waypoint, measured clockwise.
//! - **Course Over Ground (COG)**: The actual path of a vessel relative to the Earth's surface, typically measured using GPS.
//! - **Deviation Table**: A lookup table for correcting compass course errors using known deviation values, with support for linear and cubic interpolation methods.
//!
//! # Features
//!
//! This library provides utilities to handle both **direct** and **inverse** navigation tasks, as well as to calculate **true**, **magnetic**, and **compass** bearings. It offers solutions to:
//!
//! - Convert between compass and true courses by applying magnetic declination and deviation, with adjustable interpolation methods.
//! - Interpolate deviation values for compass courses using either **linear** or **cubic** interpolation.
//! - Calculate bearings (true, magnetic, compass) and resolve complex bearing-related problems.
//!
//! # Example Usage
//!
//! The example below demonstrates how to perform a compass deviation correction using a deviation table and how to convert between Compass Course (CC) and True Course (TC), with support for selecting interpolation methods.
//!
//! ```rust
//! use bearingpro::deviation::{DeviationTable, InterpolationMethod};
//! use bearingpro::navigation_solutions::{convert_compass_course_to_true_course, convert_true_course_to_compass_course};
//!
//! // Initialize a deviation table with known deviation values for compass headings.
//! let deviation_values = vec![
//!     -2.5, -0.5, 1.6, 4.4, -1.7, 0.0, 1.0, 0.3, -0.9, // 0° to 80°
//!     0.5, -1.2, 0.8, -0.3, 1.7, -2.1, 0.4, -0.6, 1.2, // 90° to 170°
//!     -1.3, 0.0, 0.9, -1.1, 1.5, -0.7, -13.2, -15.7, -17.9, // 180° to 260°
//!     -19.2, -18.1, 1.8, -0.4, 0.7, -0.2, 1.4, -4.4, -2.9, // 270° to 350°
//! ];
//! let dev_table = bearingpro::deviation::DeviationTable::from_deviation_vec(deviation_values);
//!
//! // Convert a Compass Course (CC) of 3° and a declination of -2.7° to a True Course (TC) using Parametric interpolation.
//! let cc = 3.0;
//! let tc = convert_compass_course_to_true_course(cc, -2.7, &dev_table, InterpolationMethod::Parametric).unwrap();
//! assert_eq!(format!("{:.2}", tc.course), "357.89");
//!
//! // Convert a Compass Course (CC) of 3° and a declination of -2.7° to a True Course (TC) using Cubic interpolation.
//! let cc = 3.0;
//! let tc = convert_compass_course_to_true_course(cc, -2.7, &dev_table, InterpolationMethod::Cubic).unwrap();
//! assert_eq!(format!("{:.2}", tc.course), "357.80");
//!
//! // Convert a Compass Course (CC) of 3° and a declination of -2.7° to a True Course (TC) using Linear interpolation.
//! let cc = 3.0;
//! let tc = convert_compass_course_to_true_course(cc, -2.7, &dev_table, InterpolationMethod::Linear).unwrap();
//! assert_eq!(format!("{:.2}", tc.course), "358.40");

//!
//! // Convert a True Course (TC) of 256.00° back to Compass Course (CC) using cubic interpolation.
//! let tc = 256.00;
//! let cc = convert_true_course_to_compass_course(tc, 0.7, &dev_table, InterpolationMethod::Cubic).unwrap();
//! assert_eq!(format!("{:.2}", cc.course), "271.19");
//! ```
//!
//! # Modules
//!
//! - `deviation`: Handles deviation table creation, modification, and interpolation. Supports both linear and cubic interpolation methods for handling deviation values.
//! - `error`: Custom error types for handling invalid inputs or missing data in navigation calculations.
//! - `navigation_solutions`: Functions for course conversions, bearing calculations, applying deviation corrections, and managing interpolation of deviation values.

pub mod deviation;
pub mod error;
pub mod navigation_solutions;
