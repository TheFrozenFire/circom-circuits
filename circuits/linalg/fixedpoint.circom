pragma circom 2.2.2;

include "packing/bitify.circom";
include "core/comparators.circom";

/// Range check: constrains that `in` fits in `bits` bits (0 <= in < 2^bits).
/// bits constraints.
template InRange(bits) {
    signal input in;
    component n2b = Num2Bits(bits);
    n2b.in <== in;
}

/// Approximate equality: constrains |a - b| < 2^tolerance_bits.
/// Shifts the difference to make it non-negative, then range checks.
/// (tolerance_bits + 1) constraints.
template ApproxEqual(tolerance_bits) {
    signal input a;
    signal input b;

    // diff = a - b + 2^tolerance_bits
    // If |a - b| < 2^tolerance_bits, then 0 <= diff < 2^(tolerance_bits+1)
    signal diff;
    diff <== a - b + (1 << tolerance_bits);

    component rangeCheck = Num2Bits(tolerance_bits + 1);
    rangeCheck.in <== diff;
}

/// Fixed-point multiplication with rescaling.
/// Given a, b representing real values a/S, b/S where S = 2^scale_bits,
/// computes out = floor(a * b / S).
/// 1 constraint for the division check + scale_bits for remainder range check.
template FixedPointMul(scale_bits) {
    signal input a;
    signal input b;
    signal output out;

    // Prover provides quotient and remainder
    signal q;
    signal r;
    q <-- (a * b) >> scale_bits;
    r <-- (a * b) % (1 << scale_bits);

    // Verify: a * b === q * 2^scale_bits + r
    a * b === q * (1 << scale_bits) + r;

    // Range check remainder: 0 <= r < 2^scale_bits
    component rangeCheck = Num2Bits(scale_bits);
    rangeCheck.in <== r;

    out <== q;
}

/// Fixed-point dot product with a single rescaling at the end.
/// More efficient than n separate FixedPointMul calls.
/// n constraints for multiplications + 1 for division + scale_bits for range check.
template FixedPointDotProduct(n, scale_bits) {
    signal input a[n];
    signal input b[n];
    signal output out;

    // Compute raw dot product in the field
    signal products[n];
    var sum = 0;
    for (var i = 0; i < n; i++) {
        products[i] <== a[i] * b[i];
        sum += products[i];
    }
    signal rawDot;
    rawDot <== sum;

    // Single rescaling: rawDot = q * 2^scale_bits + r
    signal q;
    signal r;
    q <-- rawDot >> scale_bits;
    r <-- rawDot % (1 << scale_bits);

    rawDot === q * (1 << scale_bits) + r;

    component rangeCheck = Num2Bits(scale_bits);
    rangeCheck.in <== r;

    out <== q;
}

/// Fixed-point matrix-vector multiplication with per-row rescaling.
/// Each output element is a fixed-point dot product of a matrix row with the vector.
/// m * (n + scale_bits) constraints.
template FixedPointMatrixVectorMul(m, n, scale_bits) {
    signal input M[m][n];
    signal input v[n];
    signal output out[m];

    component dot[m];
    for (var i = 0; i < m; i++) {
        dot[i] = FixedPointDotProduct(n, scale_bits);
        for (var j = 0; j < n; j++) {
            dot[i].a[j] <== M[i][j];
            dot[i].b[j] <== v[j];
        }
        out[i] <== dot[i].out;
    }
}

/// Fixed-point division: computes floor(a * 2^scale_bits / b).
/// Precondition: b != 0.
template FixedPointDiv(scale_bits, max_bits) {
    signal input a;
    signal input b;
    signal output out;

    signal q;
    signal r;
    q <-- (a * (1 << scale_bits)) \ b;
    r <-- (a * (1 << scale_bits)) % b;

    signal qb;
    qb <== q * b;
    qb + r === a * (1 << scale_bits);

    component rcQ = Num2Bits(max_bits + scale_bits);
    rcQ.in <== q;

    component rcR = Num2Bits(max_bits);
    rcR.in <== r;

    component lt = LessThan(max_bits);
    lt.in[0] <== r;
    lt.in[1] <== b;
    lt.out === 1;

    out <== q;
}
