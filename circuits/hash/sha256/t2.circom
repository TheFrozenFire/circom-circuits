pragma circom 2.2.2;

include "binsum.circom";
include "sigma.circom";
include "maj.circom";

/// T2 = BigSigma0(a) + Maj(a,b,c).
template T2() {
    signal input a[32];
    signal input b[32];
    signal input c[32];
    signal output out[32];

    component bigsigma0 = BigSigma(2, 13, 22);
    component maj = Maj_t(32);
    for (var k = 0; k < 32; k++) {
        bigsigma0.in[k] <== a[k];
        maj.a[k] <== a[k];
        maj.b[k] <== b[k];
        maj.c[k] <== c[k];
    }

    component sum = BinSum(32, 2);
    for (var k = 0; k < 32; k++) {
        sum.in[0][k] <== bigsigma0.out[k];
        sum.in[1][k] <== maj.out[k];
    }

    for (var k = 0; k < 32; k++) {
        out[k] <== sum.out[k];
    }
}
