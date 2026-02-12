pragma circom 2.2.2;

include "curve/babyjub.circom";
include "schnorr/blinding.circom";
include "schnorr/message.circom";

/// Full Schnorr message blinding.
///   1. Blinds R: R' = signerR + a*G + b*signerX
///   2. Commits: c_blind = SHA256(R' || signerX || message) truncated to 248 bits
///   3. Adds blinding: out = c_blind + blindingB mod SUBORDER
/// https://eprint.iacr.org/2022/1676.pdf
template SchnorrMessageBlind(n) {
    signal input message[n];
    signal input signerX[2];
    signal input signerR[2];
    signal input blindingA;
    signal input blindingB;

    BabySuborderCheck()(blindingA);
    BabySuborderCheck()(blindingB);

    signal blinded_R[2] <== SchnorrBlinding()(signerX, signerR, blindingA, blindingB);

    signal c_blind <== SchnorrMessageCommit(n)(blinded_R, signerX, message);

    signal output out <== BabySuborderAdd()(c_blind, blindingB);
}
