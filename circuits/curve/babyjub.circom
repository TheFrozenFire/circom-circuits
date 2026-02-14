pragma circom 2.2.2;

include "curve/constants.circom";
include "packing/bitify.circom";
include "core/comparators.circom";

/// Twisted Edwards point addition on BabyJubjub.
/// Uses a*x^2 + y^2 = 1 + d*x^2*y^2 with a=168700, d=168696.
template BabyAdd() {
    signal input x1;
    signal input y1;
    signal input x2;
    signal input y2;
    signal output xout;
    signal output yout;

    signal beta;
    signal gamma;
    signal delta;
    signal tau;

    var a = BABYJUB_A();
    var d = BABYJUB_D();

    beta <== x1 * y2;
    gamma <== y1 * x2;
    delta <== (-a * x1 + y1) * (x2 + y2);
    tau <== beta * gamma;

    xout <-- (beta + gamma) / (1 + d * tau);
    (1 + d * tau) * xout === (beta + gamma);

    yout <-- (delta + a * beta - gamma) / (1 - d * tau);
    (1 - d * tau) * yout === (delta + a * beta - gamma);
}

/// Point doubling: delegates to BabyAdd(P, P).
template BabyDbl() {
    signal input x;
    signal input y;
    signal output xout;
    signal output yout;

    component adder = BabyAdd();
    adder.x1 <== x;
    adder.y1 <== y;
    adder.x2 <== x;
    adder.y2 <== y;

    adder.xout ==> xout;
    adder.yout ==> yout;
}

/// Constrains (x, y) to lie on the BabyJubjub curve: a*x^2 + y^2 = 1 + d*x^2*y^2.
template BabyCheck() {
    signal input x;
    signal input y;

    signal x2;
    signal y2;

    var a = BABYJUB_A();
    var d = BABYJUB_D();

    x2 <== x * x;
    y2 <== y * y;

    a * x2 + y2 === 1 + d * x2 * y2;
}

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
