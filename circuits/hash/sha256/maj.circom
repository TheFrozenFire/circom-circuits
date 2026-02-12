pragma circom 2.2.2;

/// Majority function: out = a&b ^ a&c ^ b&c.
/// Uses algebraic identity: mid = b*c; out = a*(b + c - 2*mid) + mid.
template Maj_t(n) {
    signal input a[n];
    signal input b[n];
    signal input c[n];
    signal output out[n];
    signal mid[n];

    for (var k = 0; k < n; k++) {
        mid[k] <== b[k] * c[k];
        out[k] <== a[k] * (b[k] + c[k] - 2 * mid[k]) + mid[k];
    }
}
