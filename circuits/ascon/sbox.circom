pragma circom 2.2.2;

include "bitwise.circom";

// 𝑦0 = 𝑥4𝑥1 ⊕ 𝑥3 ⊕ 𝑥2𝑥1 ⊕ 𝑥2 ⊕ 𝑥1𝑥0 ⊕ 𝑥1 ⊕ 𝑥0
template Ascon_Sbox_y0() {
    signal input {binary} x[5];
    signal output {binary} y;

    signal {binary} y0_in[7];
    y0_in[0] <== AND () ([x[4], x[1]]);
    y0_in[1] <== x[3];
    y0_in[2] <== AND () ([x[2], x[1]]);
    y0_in[3] <== x[2];
    y0_in[4] <== AND () ([x[1], x[0]]);
    y0_in[5] <== x[1];
    y0_in[6] <== x[0];

    y <== MUXOR (7) (y0_in);
}

// 𝑦1 = 𝑥4 ⊕ 𝑥3𝑥2 ⊕ 𝑥3𝑥1 ⊕ 𝑥3 ⊕ 𝑥2𝑥1 ⊕ 𝑥2 ⊕ 𝑥1 ⊕ 𝑥0
template Ascon_Sbox_y1() {
    signal input {binary} x[5];
    signal output {binary} y;

    signal {binary} y1_in[8];
    y1_in[0] <== x[4];
    y1_in[1] <== AND () ([x[3], x[2]]);
    y1_in[2] <== AND () ([x[3], x[1]]);
    y1_in[3] <== x[3];
    y1_in[4] <== AND () ([x[2], x[1]]);
    y1_in[5] <== x[2];
    y1_in[6] <== x[1];
    y1_in[7] <== x[0];

    y <== MUXOR (8) (y1_in);
}

// 𝑦2 = 𝑥4𝑥3 ⊕ 𝑥4 ⊕ 𝑥2 ⊕ 𝑥1 ⊕ 1
template Ascon_Sbox_y2() {
    signal input {binary} x[5];
    signal output {binary} y;

    signal {binary} y2_in[5];

    y2_in[0] <== AND () ([x[4], x[3]]);
    y2_in[1] <== x[4];
    y2_in[2] <== x[2];
    y2_in[3] <== x[1];
    y2_in[4] <== 1;

    y <== MUXOR (5) (y2_in);
}

// 𝑦3 = 𝑥4𝑥0 ⊕ 𝑥4 ⊕ 𝑥3𝑥0 ⊕ 𝑥3 ⊕ 𝑥2 ⊕ 𝑥1 ⊕ 𝑥0
template Ascon_Sbox_y3() {
    signal input {binary} x[5];
    signal output {binary} y;

    signal {binary} y3_in[7];

    y3_in[0] <== AND () ([x[4], x[0]]);
    y3_in[1] <== x[4];
    y3_in[2] <== AND () ([x[3], x[0]]);
    y3_in[3] <== x[3];
    y3_in[4] <== AND () ([x[2], x[1]]);
    y3_in[5] <== x[2];
    y3_in[6] <== x[1];
}

// 𝑦4 = 𝑥4𝑥1 ⊕ 𝑥4 ⊕ 𝑥3 ⊕ 𝑥1𝑥0 ⊕ 𝑥1
template Ascon_Sbox_y4() {
    signal input {binary} x[5];
    signal output {binary} y;

    signal {binary} y4_in[5];

    y4_in[0] <== AND () ([x[4], x[1]]);
    y4_in[1] <== x[4];
    y4_in[2] <== x[3];
    y4_in[3] <== AND () ([x[1], x[0]]);
    y4_in[4] <== x[1];

    y <== MUXOR (5) (y4_in);
}