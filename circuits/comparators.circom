pragma circom 2.2.2;

include "packing/bitify.circom";

/// Outputs 1 if in == 0, else 0. Uses field inversion trick. 2 constraints.
template IsZero() {
    signal input in;
    signal output out;

    signal inv;
    inv <-- in != 0 ? 1/in : 0;

    out <== -in * inv + 1;
    in * out === 0;
}

/// Outputs 1 if in[0] == in[1], else 0.
template IsEqual() {
    signal input in[2];
    signal output out;

    out <== IsZero()(in[1] - in[0]);
}

/// n-bit less-than comparison. Assumes both inputs fit in n bits (n <= 252).
/// Outputs 1 if in[0] < in[1], else 0.
template LessThan(n) {
    assert(n <= 252);
    signal input in[2];
    signal output out;

    signal bits[n + 1] <== Num2Bits(n + 1)(in[0] + (1 << n) - in[1]);
    out <== 1 - bits[n];
}

/// Constrains in[0] == in[1] when enabled == 1. No-op when enabled == 0.
template ForceEqualIfEnabled() {
    signal input enabled;
    signal input in[2];

    signal isEq <== IsZero()(in[1] - in[0]);
    (1 - isEq) * enabled === 0;
}
