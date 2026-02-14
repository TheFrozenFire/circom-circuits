pragma circom 2.2.2;

include "core/comparators.circom";

/// Verifies strict ordering of inputs.
/// ascending=1: in[i] < in[i+1] for all i.
/// ascending=0: in[i] > in[i+1] for all i.
/// (nInputs - 1) * (nBits + 2) constraints.
template Ordered(nInputs, nBits, ascending) {
    assert(nBits <= 252);
    assert(nInputs >= 2);

    signal input in[nInputs];

    component lt[nInputs - 1];

    for (var i = 0; i < nInputs - 1; i++) {
        lt[i] = LessThan(nBits);
        if (ascending) {
            lt[i].in[0] <== in[i];
            lt[i].in[1] <== in[i + 1];
        } else {
            lt[i].in[0] <== in[i + 1];
            lt[i].in[1] <== in[i];
        }
        lt[i].out === 1;
    }
}
