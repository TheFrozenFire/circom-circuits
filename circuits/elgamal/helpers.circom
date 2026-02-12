pragma circom 2.2.2;

include "curve/babyjub.circom";

/// Computes the blinding factor for ElGamal encryption.
/// out = -(message - point[0]) = point[0] - message
template ElGamalBlinding() {
    signal input message;
    signal input point[2];

    signal output out <== (message - point[0]) * -1;
}

/// Verifies that point[0] - blinding === message, and that the point
/// is on the BabyJubjub curve.
template ElGamalMessageCheck() {
    signal input point[2];
    signal input blinding;
    signal input message;

    BabyCheck()(point[0], point[1]);

    point[0] - blinding === message;
}
