pragma circom 2.2.2;

include "circomlib/circuits/poseidon.circom";

/// Hashes two field elements using Poseidon(2).
template HashLeftRight() {
    signal input left;
    signal input right;

    component hasher = Poseidon(2);
    hasher.inputs[0] <== left;
    hasher.inputs[1] <== right;
    signal output hash <== hasher.out;
}
