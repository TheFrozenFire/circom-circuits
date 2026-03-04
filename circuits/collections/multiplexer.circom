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
