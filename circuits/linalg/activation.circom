pragma circom 2.2.2;

include "packing/bitify.circom";

/// ReLU activation: max(0, in) for signed fixed-point values
/// in [-2^(max_bits-1), 2^(max_bits-1)).
/// Uses bias trick: shift into non-negative range, decompose, check MSB.
template ReLU(max_bits) {
    signal input in;
    signal output out;

    // Bias into [0, 2^max_bits) range
    signal biased;
    biased <== in + (1 << (max_bits - 1));

    // Decompose — MSB (bit max_bits-1) is 1 iff original value >= 0
    component n2b = Num2Bits(max_bits);
    n2b.in <== biased;

    // If MSB is 1, value was non-negative → pass through; otherwise 0
    out <== n2b.out[max_bits - 1] * in;
}

/// Element-wise ReLU on an n-dimensional vector.
template ReLUVector(n, max_bits) {
    signal input in[n];
    signal output out[n];

    component relu[n];
    for (var i = 0; i < n; i++) {
        relu[i] = ReLU(max_bits);
        relu[i].in <== in[i];
        out[i] <== relu[i].out;
    }
}
