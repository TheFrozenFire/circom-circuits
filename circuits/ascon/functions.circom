pragma circom 2.2.2;

template ShiftRight(i) {
    signal input {binary} in[64];
    signal output {binary} out[64];

    for (var j = 0; j < 64; j++) {
        out[j] <== in[(j + i) % 64];
    }
}