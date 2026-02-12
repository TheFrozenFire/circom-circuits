pragma circom 2.2.2;

include "linalg/fixedpoint.circom";
include "linalg/matrix.circom";

/// Verifies that Q is an orthogonal matrix: Q^T * Q ≈ I.
///
/// Key insight: Q entries are fixed-point values scaled by S = 2^scale_bits.
/// The raw dot product of two columns gives values at scale S^2:
///   - Diagonal (same column): sum_k Q[k][i]^2 ≈ S^2
///   - Off-diagonal (different columns): sum_k Q[k][i]*Q[k][j] ≈ 0
///
/// This avoids rescaling entirely for the orthogonality check.
/// Constraints: n^2 * n (dot products) + n^2 * (tolerance_bits + 1) (approx checks).
template OrthogonalCheck(n, scale_bits, tolerance_bits) {
    signal input Q[n][n];

    // Compute Q^T * Q (raw, no rescaling)
    // QtQ[i][j] = sum_k Q[k][i] * Q[k][j]
    signal products[n][n][n];
    signal qtq[n][n];

    for (var i = 0; i < n; i++) {
        for (var j = 0; j < n; j++) {
            var sum = 0;
            for (var k = 0; k < n; k++) {
                products[i][j][k] <== Q[k][i] * Q[k][j];
                sum += products[i][j][k];
            }
            qtq[i][j] <== sum;
        }
    }

    // Check diagonal ≈ S^2, off-diagonal ≈ 0
    var s_squared = 1 << (2 * scale_bits);

    component approx[n][n];
    for (var i = 0; i < n; i++) {
        for (var j = 0; j < n; j++) {
            approx[i][j] = ApproxEqual(tolerance_bits);
            approx[i][j].a <== qtq[i][j];
            if (i == j) {
                approx[i][j].b <== s_squared;
            } else {
                approx[i][j].b <== 0;
            }
        }
    }
}

/// Computes y = Q * x (fixed-point) and verifies Q is orthogonal.
///
/// Constraint breakdown:
///   - Matrix-vector mul: m * (n + scale_bits) for FixedPointMatrixVectorMul
///   - Orthogonality check: n^3 + n^2 * (tolerance_bits + 1)
template OrthogonalTransform(n, scale_bits, tolerance_bits) {
    signal input Q[n][n];
    signal input x[n];
    signal output y[n];

    // Compute y = Q * x with fixed-point rescaling
    component mul = FixedPointMatrixVectorMul(n, n, scale_bits);
    for (var i = 0; i < n; i++) {
        for (var j = 0; j < n; j++) {
            mul.M[i][j] <== Q[i][j];
        }
        mul.v[i] <== x[i];
    }
    for (var i = 0; i < n; i++) {
        y[i] <== mul.out[i];
    }

    // Verify orthogonality: Q^T * Q ≈ I
    component check = OrthogonalCheck(n, scale_bits, tolerance_bits);
    for (var i = 0; i < n; i++) {
        for (var j = 0; j < n; j++) {
            check.Q[i][j] <== Q[i][j];
        }
    }
}
