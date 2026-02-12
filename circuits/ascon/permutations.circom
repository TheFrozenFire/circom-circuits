pragma circom 2.2.2;

include "bitwise.circom";
include "ascon/constants.circom";
include "ascon/functions.circom";
include "ascon/types.circom";
include "ascon/sbox.circom";

template Ascon_Permutation(rnd) {
    input Ascon_State() in;
    output Ascon_State() out;

    Ascon_State() intermediate[rnd];
    intermediate[0] <== Ascon_LinearDiffusion() (
        Ascon_Sbox() (
            Ascon_ConstantAddition(rnd, 0) (in)
        )
    );
    for (var i = 1; i < rnd; i++) {
        intermediate[i] <== Ascon_LinearDiffusion() (
            Ascon_Sbox() (
                Ascon_ConstantAddition(rnd, i) (intermediate[i - 1])
            )
        );
    }
    out <== intermediate[rnd - 1];
}

template Ascon_ConstantAddition(rnd, i) {
    input Ascon_State() in;
    output Ascon_State() out;

    out.S0 <== in.S0;
    out.S1 <== in.S1;
    out.S3 <== in.S3;
    out.S4 <== in.S4;

    var constant[8] = ASCON_ROUND_CONSTANT(rnd, i);
    for (var i = 0; i < 56; i++) {
        out.S2[i] <== in.S2[i];
    }
    
    signal {binary} xor_in[8][2];
    for (var i = 0; i < 8; i++) {
        xor_in[i][0] <== in.S2[56 + i];
        xor_in[i][1] <== constant[i];
        out.S2[56 + i] <== XOR() (xor_in[i]);
    }
}

template Ascon_Sbox() {
    input Ascon_State() in;
    output Ascon_State() out;

    signal {binary} column_in[64][5];
    signal {binary} column_out[64][5];
    for (var i = 0; i < 64; i++) {
        column_in[i][0] <== in.S0[i];
        column_in[i][1] <== in.S1[i];
        column_in[i][2] <== in.S2[i];
        column_in[i][3] <== in.S3[i];
        column_in[i][4] <== in.S4[i];

        column_out[i] <== Ascon_Sbox_Circuit () (column_in[i]);

        out.S0[i] <== column_out[i][0];
        out.S1[i] <== column_out[i][1];
        out.S2[i] <== column_out[i][2];
        out.S3[i] <== column_out[i][3];
        out.S4[i] <== column_out[i][4];
    }
}

template Ascon_Sbox_Circuit() {
    signal input {binary} x[5];
    signal output {binary} y[5];

    y[0] <== Ascon_Sbox_y0 () (x);
    y[1] <== Ascon_Sbox_y1 () (x);
    y[2] <== Ascon_Sbox_y2 () (x);
    y[3] <== Ascon_Sbox_y3 () (x);
    y[4] <== Ascon_Sbox_y4 () (x);
}

template Ascon_LinearDiffusion() {
    input Ascon_State() in;
    output Ascon_State() out;

    out.S0 <== Ascon_LinearDiffusion_Layer(ASCON_LINEAR_DIFFUSION_DISTANCE(0)) (in.S0);
    out.S1 <== Ascon_LinearDiffusion_Layer(ASCON_LINEAR_DIFFUSION_DISTANCE(1)) (in.S1);
    out.S2 <== Ascon_LinearDiffusion_Layer(ASCON_LINEAR_DIFFUSION_DISTANCE(2)) (in.S2);
    out.S3 <== Ascon_LinearDiffusion_Layer(ASCON_LINEAR_DIFFUSION_DISTANCE(3)) (in.S3);
    out.S4 <== Ascon_LinearDiffusion_Layer(ASCON_LINEAR_DIFFUSION_DISTANCE(4)) (in.S4);
}

template Ascon_LinearDiffusion_Layer(shifts) {
    signal input {binary} in[64];
    signal output {binary} out[64];

    signal {binary} layer_i[64] <== ShiftRight (shifts[0]) (in);
    signal {binary} layer_j[64] <== ShiftRight (shifts[1]) (in);

    for (var k = 0; k < 64; k++) {
        out[k] <== MUXOR (3) ([in[k], layer_i[k], layer_j[k]]);
    }
}

template Ascon_Absorb() {
    input Ascon_State() in_state;
    signal input {binary} in[64];
    output Ascon_State() out_state;

    out_state.S0 <== MultiXOR (64) ([in_state.S0, in]);
    out_state.S1 <== in_state.S1;
    out_state.S2 <== in_state.S2;
    out_state.S3 <== in_state.S3;
    out_state.S4 <== in_state.S4;
}