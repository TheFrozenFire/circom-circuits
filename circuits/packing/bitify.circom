pragma circom 2.2.2;

/// Decomposes a field element into n bits, little-endian.
/// Constrains 0 <= in < 2^n. n constraints (binary) + 1 (sum).
template Num2BitsLE(n) {
    signal input in;
    signal output out[n];

    var sum = 0;
    for (var i = 0; i < n; i++) {
        out[i] <-- (in >> i) & 1;
        out[i] * (out[i] - 1) === 0;
        sum += out[i] * (1 << i);
    }
    in === sum;
}

/// Reconstructs a field element from n bits, little-endian.
/// Pure linear combination — zero constraints.
/// Does NOT constrain inputs to be binary; caller is responsible.
template Bits2NumLE(n) {
    signal input in[n];
    signal output out;

    var sum = 0;
    for (var i = 0; i < n; i++) {
        sum += in[i] * (1 << i);
    }
    out <== sum;
}

/// Alias for Num2BitsLE — circomlib-compatible name.
template Num2Bits(n) {
    signal input in;
    signal output out[n];

    var sum = 0;
    for (var i = 0; i < n; i++) {
        out[i] <-- (in >> i) & 1;
        out[i] * (out[i] - 1) === 0;
        sum += out[i] * (1 << i);
    }
    in === sum;
}

/// Alias for Bits2NumLE — circomlib-compatible name.
template Bits2Num(n) {
    signal input in[n];
    signal output out;

    var sum = 0;
    for (var i = 0; i < n; i++) {
        sum += in[i] * (1 << i);
    }
    out <== sum;
}

/// Decomposes to nIn bits (range check), outputs the lower nOut bits as a number.
/// Effectively computes in % 2^nOut with a proof that in < 2^nIn.
/// nIn constraints (binary) + 1 (sum).
template TruncNumLE(nIn, nOut) {
    assert(nOut <= nIn);

    signal input in;
    signal output out;

    signal bits[nIn];
    var sum = 0;
    for (var i = 0; i < nIn; i++) {
        bits[i] <-- (in >> i) & 1;
        bits[i] * (bits[i] - 1) === 0;
        sum += bits[i] * (1 << i);
    }
    in === sum;

    var truncSum = 0;
    for (var i = 0; i < nOut; i++) {
        truncSum += bits[i] * (1 << i);
    }
    out <== truncSum;
}
