pragma circom 2.2.2;

include "core/comparators.circom";

/// Maximum value and its index from an array of n elements.
/// Prover witnesses the index; circuit verifies it via indicator mux and comparisons.
template Max(n, bits) {
    signal input in[n];
    signal output out;
    signal output index;

    // Compute the index of the maximum as a var
    var maxVal = in[0];
    var maxIdx = 0;
    for (var i = 1; i < n; i++) {
        if (in[i] > maxVal) {
            maxVal = in[i];
            maxIdx = i;
        }
    }
    index <-- maxIdx;

    // Build indicator: isIdx[i] = 1 iff i == index
    component isIdx[n];
    for (var i = 0; i < n; i++) {
        isIdx[i] = IsEqual();
        isIdx[i].in[0] <== index;
        isIdx[i].in[1] <== i;
    }

    // Extract in[index] via indicator mux
    signal terms[n];
    var sum = 0;
    for (var i = 0; i < n; i++) {
        terms[i] <== isIdx[i].out * in[i];
        sum += terms[i];
    }
    out <== sum;

    // Verify out >= in[i] for all i (i.e., in[i] <= out)
    component lt[n];
    for (var i = 0; i < n; i++) {
        lt[i] = LessThan(bits);
        lt[i].in[0] <== out;
        lt[i].in[1] <== in[i];
        lt[i].out === 0; // NOT (out < in[i])
    }
}

/// Index of the maximum value. Wraps Max, discards the value output.
template ArgMax(n, bits) {
    signal input in[n];
    signal output index;

    component m = Max(n, bits);
    for (var i = 0; i < n; i++) {
        m.in[i] <== in[i];
    }
    index <== m.index;
}
