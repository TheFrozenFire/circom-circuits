pragma circom 2.2.2;

/// Choice function: out = a&b ^ (!a)&c = a*(b-c) + c.
template Ch_t(n) {
    signal input a[n];
    signal input b[n];
    signal input c[n];
    signal output out[n];

    for (var k = 0; k < n; k++) {
        out[k] <== a[k] * (b[k] - c[k]) + c[k];
    }
}
