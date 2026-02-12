pragma circom 2.2.2;

include "circomlib/circuits/comparators.circom";

/// Element-wise matrix addition. Zero constraints.
template MatrixAdd(m, n) {
    signal input A[m][n];
    signal input B[m][n];
    signal output out[m][n];

    for (var i = 0; i < m; i++) {
        for (var j = 0; j < n; j++) {
            out[i][j] <== A[i][j] + B[i][j];
        }
    }
}

/// Element-wise matrix subtraction. Zero constraints.
template MatrixSub(m, n) {
    signal input A[m][n];
    signal input B[m][n];
    signal output out[m][n];

    for (var i = 0; i < m; i++) {
        for (var j = 0; j < n; j++) {
            out[i][j] <== A[i][j] - B[i][j];
        }
    }
}

/// Scalar-matrix multiplication. m*n constraints.
template ScalarMatrixMul(m, n) {
    signal input scalar;
    signal input M[m][n];
    signal output out[m][n];

    for (var i = 0; i < m; i++) {
        for (var j = 0; j < n; j++) {
            out[i][j] <== scalar * M[i][j];
        }
    }
}

/// Matrix-vector multiplication: out = M * v.
/// Each output element is a dot product of a matrix row with the vector.
/// m*n constraints (inlined dot products to avoid sub-component overhead).
template MatrixVectorMul(m, n) {
    signal input M[m][n];
    signal input v[n];
    signal output out[m];

    signal products[m][n];
    for (var i = 0; i < m; i++) {
        var sum = 0;
        for (var j = 0; j < n; j++) {
            products[i][j] <== M[i][j] * v[j];
            sum += products[i][j];
        }
        out[i] <== sum;
    }
}

/// Matrix multiplication: out = A * B where A is m x n and B is n x p.
/// Uses var accumulator per output element, one signal per output.
/// m*n*p constraints for multiplications.
template MatrixMul(m, n, p) {
    signal input A[m][n];
    signal input B[n][p];
    signal output out[m][p];

    // products[i][j][k] = A[i][k] * B[k][j]
    signal products[m][p][n];
    for (var i = 0; i < m; i++) {
        for (var j = 0; j < p; j++) {
            var sum = 0;
            for (var k = 0; k < n; k++) {
                products[i][j][k] <== A[i][k] * B[k][j];
                sum += products[i][j][k];
            }
            out[i][j] <== sum;
        }
    }
}

/// Matrix transpose. Zero constraints (pure signal rewiring).
template MatrixTranspose(m, n) {
    signal input M[m][n];
    signal output out[n][m];

    for (var i = 0; i < m; i++) {
        for (var j = 0; j < n; j++) {
            out[j][i] <== M[i][j];
        }
    }
}

/// Element-wise matrix equality check. Outputs 1 if equal, 0 otherwise.
/// 2*m*n constraints (from IsEqual per element) + (m*n - 1) for AND chain.
template MatrixIsEqual(m, n) {
    signal input A[m][n];
    signal input B[m][n];
    signal output out;

    var total = m * n;
    component eq[total];

    for (var i = 0; i < m; i++) {
        for (var j = 0; j < n; j++) {
            var idx = i * n + j;
            eq[idx] = IsEqual();
            eq[idx].in[0] <== A[i][j];
            eq[idx].in[1] <== B[i][j];
        }
    }

    // AND all equality results
    signal acc[total];
    acc[0] <== eq[0].out;
    for (var i = 1; i < total; i++) {
        acc[i] <== acc[i - 1] * eq[i].out;
    }
    out <== acc[total - 1];
}
