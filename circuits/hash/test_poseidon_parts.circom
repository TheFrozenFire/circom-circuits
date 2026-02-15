pragma circom 2.2.2;

include "hash/poseidon.circom";
include "hash/poseidon_constants.circom";

/// Test wrapper for Ark with t=3 (Poseidon(2) state size).
template TestArk() {
    var t = 3;
    var C[t * 8 + 57] = POSEIDON_C(t);
    signal input in[t];
    signal output out[t];

    component ark = Ark(t, C, 0);
    ark.in <== in;
    out <== ark.out;
}

/// Test wrapper for Mix with t=3.
template TestMix() {
    var t = 3;
    var M[t][t] = POSEIDON_M(t);
    signal input in[t];
    signal output out[t];

    component mix = Mix(t, M);
    mix.in <== in;
    out <== mix.out;
}

/// Test wrapper for MixLast with t=3, s=0 (extract first element).
template TestMixLast() {
    var t = 3;
    var M[t][t] = POSEIDON_M(t);
    signal input in[t];
    signal output out;

    component ml = MixLast(t, M, 0);
    ml.in <== in;
    out <== ml.out;
}

/// Test wrapper for MixS with t=3, r=0 (first partial round).
template TestMixS() {
    var t = 3;
    var S[57 * (t * 2 - 1)] = POSEIDON_S(t);
    signal input in[t];
    signal output out[t];

    component ms = MixS(t, S, 0);
    ms.in <== in;
    out <== ms.out;
}
