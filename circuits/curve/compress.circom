pragma circom 2.2.2;

include "packing/bitify.circom";

/// Compresses a BabyJubjub point into 256 bits.
/// Output layout (little-endian): y[0..253], 0, sign(x).
/// Sign bit = LSB of x (parity determines which square root).
template BabyCompress() {
    signal input in[2]; // [x, y]
    signal output out[256];

    signal xBits[254] <== Num2BitsLE(254)(in[0]);
    signal yBits[254] <== Num2BitsLE(254)(in[1]);

    // y bits
    for (var i = 0; i < 254; i++) {
        out[i] <== yBits[i];
    }
    // Padding bit
    out[254] <== 0;
    // Sign bit = LSB of x
    out[255] <== xBits[0];
}

/// Compresses multiple BabyJubjub points into concatenated 256-bit outputs.
template BabyMultiCompress(nPoints) {
    signal input in[nPoints][2];
    signal output out[nPoints * 256];

    component comp[nPoints];
    for (var i = 0; i < nPoints; i++) {
        comp[i] = BabyCompress();
        comp[i].in[0] <== in[i][0];
        comp[i].in[1] <== in[i][1];
        for (var j = 0; j < 256; j++) {
            out[i * 256 + j] <== comp[i].out[j];
        }
    }
}
