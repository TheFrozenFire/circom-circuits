pragma circom 2.2.2;

include "curve/scalarmul.circom";
include "curve/constants.circom";

/// Test wrapper for EscalarMulFix with BASE8 hardcoded, n=8 bits.
template TestEscalarMulFixBase8() {
    signal input e[8];
    signal output out[2];

    component mul = EscalarMulFix(8, BABYJUB_BASE8());
    for (var i = 0; i < 8; i++) {
        mul.e[i] <== e[i];
    }
    out[0] <== mul.out[0];
    out[1] <== mul.out[1];
}
