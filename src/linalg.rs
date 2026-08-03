//! Small dense and banded linear solvers.
//!
//! These are the numeric kernels behind the periodic spline, the parametric
//! deviation fit, and the least-squares position fix. They are deliberately
//! tiny: the systems here are at most a few tens of unknowns, so a direct
//! factorisation is both simpler and faster than anything iterative.
//!
//! Every one of them returns `None` rather than panicking or dividing by zero
//! when the system turns out to be singular.

use alloc::vec;
use alloc::vec::Vec;

use crate::math;

/// Solves a tridiagonal system with two extra corner entries, by Sherman–Morrison.
///
/// `sub[i]` multiplies `x[i-1]`, `diag[i]` multiplies `x[i]`, `sup[i]` multiplies
/// `x[i+1]`; `corner_top_right` sits at `(0, n-1)` and `corner_bottom_left` at
/// `(n-1, 0)`. Returns `None` if the system is numerically singular.
pub(crate) fn solve_cyclic_tridiagonal(
    sub: &[f64],
    diag: &[f64],
    sup: &[f64],
    corner_top_right: f64,
    corner_bottom_left: f64,
    rhs: &[f64],
) -> Option<Vec<f64>> {
    let count = diag.len();
    if count < 3 || sub.len() != count || sup.len() != count || rhs.len() != count {
        return None;
    }

    // Rank-one correction: A = T + u·vᵀ, chosen so T stays strictly tridiagonal.
    let gamma = -diag.first()?;
    if math::abs(gamma) < f64::EPSILON {
        return None;
    }
    let ratio = corner_top_right / gamma;

    let mut modified_diag = diag.to_vec();
    *modified_diag.first_mut()? = diag.first()? - gamma;
    *modified_diag.last_mut()? = diag.last()? - corner_bottom_left * ratio;

    let mut correction = vec![0.0; count];
    *correction.first_mut()? = gamma;
    *correction.last_mut()? = corner_bottom_left;

    let solved_rhs = solve_tridiagonal(sub, &modified_diag, sup, rhs)?;
    let solved_correction = solve_tridiagonal(sub, &modified_diag, sup, &correction)?;

    let numerator = solved_rhs.first()? + ratio * solved_rhs.last()?;
    let denominator = 1.0 + solved_correction.first()? + ratio * solved_correction.last()?;
    if math::abs(denominator) < f64::EPSILON {
        return None;
    }
    let factor = numerator / denominator;

    Some(
        solved_rhs
            .iter()
            .zip(solved_correction.iter())
            .map(|(&value, &adjustment)| value - factor * adjustment)
            .collect(),
    )
}

/// Thomas algorithm for a strictly tridiagonal system. `None` if a pivot vanishes.
#[allow(clippy::indexing_slicing)]
pub(crate) fn solve_tridiagonal(
    sub: &[f64],
    diag: &[f64],
    sup: &[f64],
    rhs: &[f64],
) -> Option<Vec<f64>> {
    let count = diag.len();
    if count == 0 || sub.len() != count || sup.len() != count || rhs.len() != count {
        return None;
    }

    // Every index below is in `0..count`, checked once here.
    let mut sweep = vec![0.0; count];
    let mut solution = vec![0.0; count];

    if math::abs(diag[0]) < f64::EPSILON {
        return None;
    }
    sweep[0] = sup[0] / diag[0];
    solution[0] = rhs[0] / diag[0];

    for index in 1..count {
        let pivot = diag[index] - sub[index] * sweep[index - 1];
        if math::abs(pivot) < f64::EPSILON {
            return None;
        }
        sweep[index] = sup[index] / pivot;
        solution[index] = (rhs[index] - sub[index] * solution[index - 1]) / pivot;
    }

    for index in (0..count - 1).rev() {
        solution[index] -= sweep[index] * solution[index + 1];
    }

    Some(solution)
}

/// Gaussian elimination with partial pivoting on a row-major `size × size` system.
///
/// Consumes `matrix` and `rhs` as scratch space. `None` if the matrix is singular.
#[allow(clippy::indexing_slicing)]
pub(crate) fn solve_dense(matrix: &mut [f64], rhs: &mut [f64], size: usize) -> Option<Vec<f64>> {
    if size == 0 || matrix.len() != size * size || rhs.len() != size {
        return None;
    }

    // Every index below is bounded by `size`, checked once here.
    for column in 0..size {
        let mut pivot_row = column;
        let mut best = math::abs(matrix[column * size + column]);
        for row in (column + 1)..size {
            let candidate = math::abs(matrix[row * size + column]);
            if candidate > best {
                best = candidate;
                pivot_row = row;
            }
        }
        if best < 1e-12 {
            return None;
        }
        if pivot_row != column {
            for index in 0..size {
                matrix.swap(column * size + index, pivot_row * size + index);
            }
            rhs.swap(column, pivot_row);
        }

        let pivot = matrix[column * size + column];
        for row in (column + 1)..size {
            let factor = matrix[row * size + column] / pivot;
            if factor == 0.0 {
                continue;
            }
            for index in column..size {
                matrix[row * size + index] -= factor * matrix[column * size + index];
            }
            rhs[row] -= factor * rhs[column];
        }
    }

    let mut solution = vec![0.0; size];
    for row in (0..size).rev() {
        let mut accumulator = rhs[row];
        for column in (row + 1)..size {
            accumulator -= matrix[row * size + column] * solution[column];
        }
        solution[row] = accumulator / matrix[row * size + row];
    }
    Some(solution)
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::float_cmp, clippy::indexing_slicing)]
mod tests {
    use super::*;

    #[test]
    fn dense_solver_matches_a_hand_solution() {
        // 2x +  y = 5 ; x + 3y = 10  =>  x = 1, y = 3
        let mut matrix = vec![2.0, 1.0, 1.0, 3.0];
        let mut rhs = vec![5.0, 10.0];
        let solution = solve_dense(&mut matrix, &mut rhs, 2).unwrap();
        assert!((solution[0] - 1.0).abs() < 1e-12);
        assert!((solution[1] - 3.0).abs() < 1e-12);
    }

    #[test]
    fn dense_solver_pivots() {
        // A zero leading pivot must be swapped away, not divided by.
        let mut matrix = vec![0.0, 1.0, 1.0, 0.0];
        let mut rhs = vec![2.0, 3.0];
        let solution = solve_dense(&mut matrix, &mut rhs, 2).unwrap();
        assert!((solution[0] - 3.0).abs() < 1e-12);
        assert!((solution[1] - 2.0).abs() < 1e-12);
    }

    #[test]
    fn dense_solver_rejects_singular_systems() {
        let mut matrix = vec![1.0, 2.0, 2.0, 4.0];
        let mut rhs = vec![1.0, 2.0];
        assert!(solve_dense(&mut matrix, &mut rhs, 2).is_none());
        assert!(solve_dense(&mut [], &mut [], 0).is_none());
    }

    #[test]
    fn tridiagonal_solver_matches_a_hand_solution() {
        // 2x - y = 1 ; -x + 2y - z = 0 ; -y + 2z = 1  =>  x = y = z = 1
        let sub = [0.0, -1.0, -1.0];
        let diag = [2.0, 2.0, 2.0];
        let sup = [-1.0, -1.0, 0.0];
        let rhs = [1.0, 0.0, 1.0];
        let solution = solve_tridiagonal(&sub, &diag, &sup, &rhs).unwrap();
        for value in solution {
            assert!((value - 1.0).abs() < 1e-12);
        }
    }

    #[test]
    fn solvers_reject_mismatched_lengths() {
        assert!(solve_tridiagonal(&[0.0], &[1.0, 2.0], &[0.0], &[1.0]).is_none());
        assert!(solve_cyclic_tridiagonal(&[0.0], &[1.0], &[0.0], 1.0, 1.0, &[1.0]).is_none());
    }

    #[test]
    fn cyclic_solver_matches_a_dense_solution() {
        // A 4x4 cyclic tridiagonal system, solved both ways.
        let sub = [0.0, 1.0, 1.0, 1.0];
        let diag = [4.0, 4.0, 4.0, 4.0];
        let sup = [1.0, 1.0, 1.0, 0.0];
        let (corner_tr, corner_bl) = (1.0, 1.0);
        let rhs = [1.0, 2.0, 3.0, 4.0];

        let banded =
            solve_cyclic_tridiagonal(&sub, &diag, &sup, corner_tr, corner_bl, &rhs).unwrap();

        let mut dense = vec![0.0; 16];
        for row in 0..4 {
            dense[row * 4 + row] = diag[row];
            if row > 0 {
                dense[row * 4 + row - 1] = sub[row];
            }
            if row < 3 {
                dense[row * 4 + row + 1] = sup[row];
            }
        }
        dense[3] = corner_tr;
        dense[12] = corner_bl;
        let mut dense_rhs = rhs.to_vec();
        let reference = solve_dense(&mut dense, &mut dense_rhs, 4).unwrap();

        for (left, right) in banded.iter().zip(reference.iter()) {
            assert!((left - right).abs() < 1e-10, "{left} vs {right}");
        }
    }
}
