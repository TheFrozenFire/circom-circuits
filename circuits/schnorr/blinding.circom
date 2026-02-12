pragma circom 2.2.2;

include "curve/constants.circom";
include "curve/babyjub.circom";
include "circomlib/circuits/escalarmulany.circom";
include "circomlib/circuits/escalarmulfix.circom";
include "circomlib/circuits/bitify.circom";

/// Schnorr blinding: R' = signerR + a*G + b*signerX
/// https://eprint.iacr.org/2022/1676.pdf
template SchnorrBlinding() {
    signal input signerX[2];
    signal input signerR[2];
    signal input blindingA;
    signal input blindingB;

    signal a_G[2] <== EscalarMulFix(254, BABYJUB_BASE8())(Num2Bits(254)(blindingA));
    signal b_X[2] <== EscalarMulAny(254)(Num2Bits(254)(blindingB), signerX);

    signal R_plus_a_G[2] <== BabyPointAdd()([signerR, a_G]);

    signal output out[2] <== BabyPointAdd()([R_plus_a_G, b_X]);
}
