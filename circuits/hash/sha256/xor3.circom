pragma circom 2.2.2;

/// Three-input XOR: out = a ^ b ^ c.
/// Uses algebraic identity: mid = b*c; out = a*(1 - 2b - 2c + 4*mid) + b + c - 2*mid.
template Xor3(n) {
    signal input a[n];
    signal input b[n];
    signal input c[n];
    signal output out[n];
    signal mid[n];

    for (var k = 0; k < n; k++) {
        mid[k] <== b[k] * c[k];
        out[k] <== a[k] * (1 - 2 * b[k] - 2 * c[k] + 4 * mid[k]) + b[k] + c[k] - 2 * mid[k];
    }
}
