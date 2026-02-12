pragma circom 2.2.2;

template ShiftRight(i) {
    signal input {binary} in[64];
    signal output {binary} out[64];

    for (var j = 0; j < 64; j++) {
        out[j] <== in[(j + i) % 64];
    }
}

function word_2_bits(in) {
    var out[64];

    for (var i = 0; i<64; i++) {
        out[i] = (in >> i) & 1;
    }

    return out;
}

function byte_2_bits(in) {
    var out[8];

    for (var i = 0; i<8; i++) {
        out[i] = (in >> i) & 1;
    }

    return out;
}