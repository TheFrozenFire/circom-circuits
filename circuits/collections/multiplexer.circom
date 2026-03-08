pragma circom 2.2.2;

include "packing/bitify.circom";

// ═══════════════════════════════════════════════════
// Binary decoder and multiplexer for k-register selection.
// Used by PrivToPub for stride-8 windowed scalar multiplication.
// ═══════════════════════════════════════════════════

/// Decodes a w-bit input into a one-hot vector of 2^w outputs.
/// out[i] = 1 if inp == i, else 0.
/// Constraints: 2^w * (w - 1) for intermediate products + w for Num2Bits.
template Decoder(w) {
    signal input inp;
    signal output out[1 << w];

    // Decompose into w bits
    signal bits[w] <== Num2Bits(w)(inp);

    // For each value i in [0, 2^w), compute the product:
    //   out[i] = Π_{j=0}^{w-1} (bits[j] if bit j of i is 1, else (1 - bits[j]))
    signal tree[1 << w][w];
    for (var i = 0; i < (1 << w); i++) {
        for (var j = 0; j < w; j++) {
            if (j == 0) {
                if (((i >> j) & 1) == 1) {
                    tree[i][j] <== bits[j];
                } else {
                    tree[i][j] <== 1 - bits[j];
                }
            } else {
                if (((i >> j) & 1) == 1) {
                    tree[i][j] <== tree[i][j - 1] * bits[j];
                } else {
                    tree[i][j] <== tree[i][j - 1] * (1 - bits[j]);
                }
            }
        }
        out[i] <== tree[i][w - 1];
    }
}

/// Like Decoder(w) but accepts pre-decomposed bits instead of a scalar.
/// Saves Num2Bits(w) constraints when bits are already available.
/// Caller must ensure bits are binary and represent a valid w-bit value.
template DecoderFromBits(w) {
    signal input bits[w];
    signal output out[1 << w];

    signal tree[1 << w][w];
    for (var i = 0; i < (1 << w); i++) {
        for (var j = 0; j < w; j++) {
            if (j == 0) {
                if (((i >> j) & 1) == 1) {
                    tree[i][j] <== bits[j];
                } else {
                    tree[i][j] <== 1 - bits[j];
                }
            } else {
                if (((i >> j) & 1) == 1) {
                    tree[i][j] <== tree[i][j - 1] * bits[j];
                } else {
                    tree[i][j] <== tree[i][j - 1] * (1 - bits[j]);
                }
            }
        }
        out[i] <== tree[i][w - 1];
    }
}

/// Like DualMultiplexer but accepts pre-decomposed bits instead of a scalar selector.
/// Saves Bits2Num + Num2Bits round-trip when bits are already available.
template DualMultiplexerFromBits(nIn, nSel) {
    signal input inp0[nSel][nIn];
    signal input inp1[nSel][nIn];
    var w = 0;
    var temp = nSel;
    while (temp > 1) { w++; temp = temp >> 1; }
    signal input bits[w];
    signal output out0[nIn];
    signal output out1[nIn];

    signal decoded[nSel] <== DecoderFromBits(w)(bits);

    signal terms0[nSel][nIn];
    signal terms1[nSel][nIn];
    for (var j = 0; j < nSel; j++) {
        for (var i = 0; i < nIn; i++) {
            terms0[j][i] <== decoded[j] * inp0[j][i];
            terms1[j][i] <== decoded[j] * inp1[j][i];
        }
    }

    for (var i = 0; i < nIn; i++) {
        var sum0 = 0;
        var sum1 = 0;
        for (var j = 0; j < nSel; j++) {
            sum0 += terms0[j][i];
            sum1 += terms1[j][i];
        }
        out0[i] <== sum0;
        out1[i] <== sum1;
    }
}

/// Selects from TWO independent tables of nSel nIn-register values, sharing a single Decoder.
/// Saves one Decoder(log2(nSel)) worth of constraints vs two separate Multiplexer calls.
/// sel must be in [0, nSel). nSel must be a power of 2.
template DualMultiplexer(nIn, nSel) {
    signal input inp0[nSel][nIn];
    signal input inp1[nSel][nIn];
    signal input sel;
    signal output out0[nIn];
    signal output out1[nIn];

    var w = 0;
    var temp = nSel;
    while (temp > 1) { w++; temp = temp >> 1; }

    signal decoded[nSel] <== Decoder(w)(sel);

    signal terms0[nSel][nIn];
    signal terms1[nSel][nIn];
    for (var j = 0; j < nSel; j++) {
        for (var i = 0; i < nIn; i++) {
            terms0[j][i] <== decoded[j] * inp0[j][i];
            terms1[j][i] <== decoded[j] * inp1[j][i];
        }
    }

    for (var i = 0; i < nIn; i++) {
        var sum0 = 0;
        var sum1 = 0;
        for (var j = 0; j < nSel; j++) {
            sum0 += terms0[j][i];
            sum1 += terms1[j][i];
        }
        out0[i] <== sum0;
        out1[i] <== sum1;
    }
}

/// Selects one of nSel nIn-register values based on a selector.
/// sel must be in [0, nSel). nSel must be a power of 2.
/// inp[j][i] is register i of option j. out[i] is register i of the selected option.
template Multiplexer(nIn, nSel) {
    signal input inp[nSel][nIn];
    signal input sel;
    signal output out[nIn];

    var w = 0;
    var temp = nSel;
    while (temp > 1) { w++; temp = temp >> 1; }

    signal decoded[nSel] <== Decoder(w)(sel);

    // out[i] = Σ_j decoded[j] * inp[j][i]
    // Since decoded is one-hot, this selects exactly inp[sel][i].
    signal terms[nSel][nIn];
    for (var j = 0; j < nSel; j++) {
        for (var i = 0; i < nIn; i++) {
            terms[j][i] <== decoded[j] * inp[j][i];
        }
    }

    for (var i = 0; i < nIn; i++) {
        var sum = 0;
        for (var j = 0; j < nSel; j++) {
            sum += terms[j][i];
        }
        out[i] <== sum;
    }
}
