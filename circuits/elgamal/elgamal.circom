pragma circom 2.2.2;

include "curve/constants.circom";
include "curve/scalarmul.circom";
include "curve/babyjub.circom";
include "packing/bitify.circom";

/// Computes ElGamal shared secret and ephemeral public key.
///   out = pubKey^y  (shared secret)
///   c1  = g^y       (ephemeral public key)
template ElGamalShare() {
    signal input pubKey[2];
    signal input y;

    component yBits = Num2Bits(254);
    yBits.in <== y;

    signal output out[2] <== EscalarMulAny(254)(yBits.out, pubKey);
    signal output c1[2] <== EscalarMulFix(254, BABYJUB_BASE8())(yBits.out);
}

/// ElGamal encryption on BabyJubjub.
///   c1 = g^y
///   c2 = message + pubKey^y
template ElGamalEncrypt() {
    signal input pubKey[2];
    signal input message[2];
    signal input y;

    signal output c1[2];
    signal output c2[2];

    component shared = ElGamalShare();
    shared.pubKey <== pubKey;
    shared.y <== y;

    // c2 = message + shared secret
    component m = BabyAdd();
    (m.x1, m.y1) <== (message[0], message[1]);
    (m.x2, m.y2) <== (shared.out[0], shared.out[1]);

    c1 <== shared.c1;
    c2 <== [m.xout, m.yout];
}

/// ElGamal decryption on BabyJubjub.
///   message = c2 - c1^privKey
template ElGamalDecrypt() {
    signal input c1[2];
    signal input c2[2];
    signal input privKey;
    signal output message[2];

    component privKeyBits = Num2Bits(254);
    privKeyBits.in <== privKey;

    // Shared secret: s = c1^privKey
    component c1x = EscalarMulAny(254);
    c1x.e <== privKeyBits.out;
    c1x.p <== c1;

    // Inverse: negate x-coordinate on twisted Edwards
    signal c1xInvX <== 0 - c1x.out[0];

    // message = c2 + (-s)
    component dec = BabyAdd();
    dec.x1 <== c1xInvX;
    dec.y1 <== c1x.out[1];
    (dec.x2, dec.y2) <== (c2[0], c2[1]);

    message <== [dec.xout, dec.yout];
}
