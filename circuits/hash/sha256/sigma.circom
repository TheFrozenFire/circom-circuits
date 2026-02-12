pragma circom 2.2.2;

include "xor3.circom";
include "rotate.circom";
include "shift.circom";

/// Small sigma: XOR of two rotations and one right shift (message schedule).
template SmallSigma(ra, rb, rc) {
    signal input in[32];
    signal output out[32];

    component rota = RotR(32, ra);
    component rotb = RotR(32, rb);
    component shrc = ShR(32, rc);

    for (var k = 0; k < 32; k++) {
        rota.in[k] <== in[k];
        rotb.in[k] <== in[k];
        shrc.in[k] <== in[k];
    }

    component xor3 = Xor3(32);
    for (var k = 0; k < 32; k++) {
        xor3.a[k] <== rota.out[k];
        xor3.b[k] <== rotb.out[k];
        xor3.c[k] <== shrc.out[k];
    }

    for (var k = 0; k < 32; k++) {
        out[k] <== xor3.out[k];
    }
}

/// Big sigma: XOR of three rotations (working variable updates).
template BigSigma(ra, rb, rc) {
    signal input in[32];
    signal output out[32];

    component rota = RotR(32, ra);
    component rotb = RotR(32, rb);
    component rotc = RotR(32, rc);
    for (var k = 0; k < 32; k++) {
        rota.in[k] <== in[k];
        rotb.in[k] <== in[k];
        rotc.in[k] <== in[k];
    }

    component xor3 = Xor3(32);
    for (var k = 0; k < 32; k++) {
        xor3.a[k] <== rota.out[k];
        xor3.b[k] <== rotb.out[k];
        xor3.c[k] <== rotc.out[k];
    }

    for (var k = 0; k < 32; k++) {
        out[k] <== xor3.out[k];
    }
}
