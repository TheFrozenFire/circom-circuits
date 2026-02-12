pragma circom 2.2.2;

include "ascon/constants.circom";
include "ascon/types.circom";
include "ascon/permutations.circom";

template Ascon_Hash_256(nBlocks) {
    signal input in[nBlocks][64];
    signal output out[4][64];

    Ascon_State() absorb_state[nBlocks + 1];
    var initial_state_words[5][64] = ASCON_INITIAL_STATE_HASH_256();

    absorb_state[0].S0 <== initial_state_words[0];
    absorb_state[0].S1 <== initial_state_words[1];
    absorb_state[0].S2 <== initial_state_words[2];
    absorb_state[0].S3 <== initial_state_words[3];
    absorb_state[0].S4 <== initial_state_words[4];

    // Absorb the input blocks
    signal {binary} absorb_state_in[nBlocks][64];
    for (var i = 0; i < nBlocks; i++) {
        absorb_state_in[i] <== in[i];
        absorb_state[i + 1] <== Ascon_Permutation(12) (
            Ascon_Absorb() (
                absorb_state[i],
                absorb_state_in[i]
            )
        );
    }

    // Squeeze the output
    Ascon_State() squeeze_state[4];
    squeeze_state[0] <== absorb_state[nBlocks];
    out[0] <== squeeze_state[0].S0;
    for (var i = 1; i < 4; i++) {
        squeeze_state[i] <== Ascon_Permutation(12) (squeeze_state[i - 1]);
        out[i] <== squeeze_state[i].S0;
    }
}