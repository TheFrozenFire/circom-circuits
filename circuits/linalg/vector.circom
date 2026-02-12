pragma circom 2.2.2;

include "circomlib/circuits/comparators.circom";

/// Element-wise vector addition. Zero constraints (addition is free in R1CS).
template VectorAdd(n) {
    signal input a[n];
    signal input b[n];
    signal output out[n];

    for (var i = 0; i < n; i++) {
        out[i] <== a[i] + b[i];
    }
}

/// Element-wise vector subtraction. Zero constraints.
template VectorSub(n) {
    signal input a[n];
    signal input b[n];
    signal output out[n];

    for (var i = 0; i < n; i++) {
        out[i] <== a[i] - b[i];
    }
}

/// Scalar-vector multiplication. n constraints (one per element).
template ScalarVectorMul(n) {
    signal input scalar;
    signal input v[n];
    signal output out[n];

    for (var i = 0; i < n; i++) {
        out[i] <== scalar * v[i];
    }
}

/// Dot product of two vectors. n constraints for multiplications + 1 output signal.
/// Uses var accumulator to avoid intermediate signal overhead.
template DotProduct(n) {
    signal input a[n];
    signal input b[n];
    signal output out;

    signal products[n];
    var sum = 0;
    for (var i = 0; i < n; i++) {
        products[i] <== a[i] * b[i];
        sum += products[i];
    }
    out <== sum;
}

/// Squared L2 norm of a vector: sum(v_i^2). n constraints.
template VectorNormSquared(n) {
    signal input v[n];
    signal output out;

    signal squares[n];
    var sum = 0;
    for (var i = 0; i < n; i++) {
        squares[i] <== v[i] * v[i];
        sum += squares[i];
    }
    out <== sum;
}

/// Checks element-wise equality of two vectors. Outputs 1 if equal, 0 otherwise.
/// Uses IsEqual from circomlib per element, then ANDs all results.
/// 2n constraints (IsEqual is 2 constraints each: IsZero internals).
template VectorIsEqual(n) {
    signal input a[n];
    signal input b[n];
    signal output out;

    component eq[n];
    for (var i = 0; i < n; i++) {
        eq[i] = IsEqual();
        eq[i].in[0] <== a[i];
        eq[i].in[1] <== b[i];
    }

    // AND all equality results via multiplication chain
    signal acc[n];
    acc[0] <== eq[0].out;
    for (var i = 1; i < n; i++) {
        acc[i] <== acc[i - 1] * eq[i].out;
    }
    out <== acc[n - 1];
}
