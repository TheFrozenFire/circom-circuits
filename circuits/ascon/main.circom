pragma circom 2.2.2;

include "ascon/hash.circom";
include "ascon/permutations.circom";

template Main() {
    signal input in_state[5][64];
    signal input in[64];
    signal output out[5][64];

    Ascon_State() state;
    state.S0 <== in_state[0];
    state.S1 <== in_state[1];
    state.S2 <== in_state[2];
    state.S3 <== in_state[3];
    state.S4 <== in_state[4];

    signal {binary} in_bits[64];
    in_bits <== in;

    Ascon_State() out_state <== Ascon_Absorb() (state, in_bits);

    out[0] <== out_state.S0;
    out[1] <== out_state.S1;
    out[2] <== out_state.S2;
    out[3] <== out_state.S3;
    out[4] <== out_state.S4;
}

component main = Main();