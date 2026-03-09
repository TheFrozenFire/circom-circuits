pragma circom 2.2.2;

include "arithmetic/bigint_func.circom";
include "ecdsa/constants.circom";
include "ecdsa/functions.circom";

/// Diagnostic: exposes eisenstein_half_gcd raw output for debugging.
template EisensteinDiag(n, k) {
    assert(n == 32 && k == 8);
    signal input scalar[k];
    signal output x0[k];
    signal output x1[k];
    signal output z0[k];
    signal output z1[k];
    signal output s0;
    signal output s1;
    signal output s2;
    signal output s3;

    var eis[10][30] = eisenstein_half_gcd(n, k, scalar);
    for (var i = 0; i < k; i++) {
        x0[i] <-- eis[0][i];
        x1[i] <-- eis[1][i];
        z0[i] <-- eis[2][i];
        z1[i] <-- eis[3][i];
    }
    s0 <-- eis[4][0];
    s1 <-- eis[5][0];
    s2 <-- eis[6][0];
    s3 <-- eis[7][0];
}
