pragma circom 2.2.2;

/// Right shift of an n-bit word by r positions. Vacated bits are zero.
template ShR(n, r) {
    signal input in[n];
    signal output out[n];

    for (var i = 0; i < n; i++) {
        if (i + r >= n) {
            out[i] <== 0;
        } else {
            out[i] <== in[i + r];
        }
    }
}
