pragma circom 2.2.2;

include "curve/constants.circom";
include "packing/bitify.circom";
include "circomlib/circuits/babyjub.circom";
include "circomlib/circuits/comparators.circom";

/// Point addition with array interface.
/// in[0] = [x, y], in[1] = [x, y] → out = [x, y].
template BabyPointAdd() {
    signal input in[2][2];
    signal output out[2];

    signal (x, y) <== BabyAdd()(in[0][0], in[0][1], in[1][0], in[1][1]);
    out[0] <== x;
    out[1] <== y;
}

/// Point doubling with array interface.
/// in = [x, y] → out = [x, y].
template BabyPointDouble() {
    signal input in[2];
    signal output out[2];

    signal (x, y) <== BabyAdd()(in[0], in[1], in[0], in[1]);
    out[0] <== x;
    out[1] <== y;
}

/// Constrains a scalar to be less than the BabyJubjub subgroup order.
/// Proves (suborder - 1 - in) is non-negative by decomposing into 253 bits.
template BabySuborderCheck() {
    signal input in;

    var l = BABYJUB_SUBORDER();
    signal diff <== l - 1 - in;
    signal _bits[253] <== Num2BitsLE(253)(diff);
}

/// Adds two scalars modulo the BabyJubjub subgroup order.
/// Assumes a, b < SUBORDER (callers should use BabySuborderCheck).
template BabySuborderAdd() {
    signal input a;
    signal input b;
    signal output out;

    var q = BABYJUB_SUBORDER();

    signal sum <== a + b;
    signal k;
    k <-- sum \ q;

    out <== sum - k * q;

    signal lt <== LessThan(252)([out, q]);
    lt === 1;
}
