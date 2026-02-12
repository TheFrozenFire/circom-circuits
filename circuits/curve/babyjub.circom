pragma circom 2.2.2;

include "curve/constants.circom";
include "packing/bitify.circom";

/// Verifies that a point (x, y) lies on the BabyJubjub curve.
/// Curve equation: a·x² + y² = 1 + d·x²·y²
/// 3 quadratic constraints + 1 linear constraint.
template BabyCheck() {
    signal input x, y;

    var a = BABYJUB_A();
    var d = BABYJUB_D();

    signal x2 <== x * x;
    signal y2 <== y * y;
    signal x2y2 <== x2 * y2;

    a * x2 + y2 === 1 + d * x2y2;
}

/// Twisted Edwards point addition on BabyJubjub.
/// Computes (xout, yout) = (x1, y1) + (x2, y2).
///   beta = x1·y2, gamma = y1·x2, tau = beta·gamma
///   delta = (-a·x1 + y1)·(x2 + y2)
///   xout = (beta + gamma) / (1 + d·tau)
///   yout = (delta + a·beta - gamma) / (1 - d·tau)
/// 6 constraints total.
template BabyAdd() {
    signal input x1, y1, x2, y2;
    signal output xout, yout;

    var a = BABYJUB_A();
    var d = BABYJUB_D();

    signal beta <== x1 * y2;
    signal gamma <== y1 * x2;
    signal delta <== (-a * x1 + y1) * (x2 + y2);
    signal tau <== beta * gamma;

    xout <-- (beta + gamma) / (1 + d * tau);
    (1 + d * tau) * xout === (beta + gamma);

    yout <-- (delta + a * beta - gamma) / (1 - d * tau);
    (1 - d * tau) * yout === (delta + a * beta - gamma);
}

/// Point doubling on BabyJubjub. Computes 2·(x, y).
/// Delegates to BabyAdd.
template BabyDbl() {
    signal input x, y;
    signal output xout, yout;

    component add = BabyAdd();
    add.x1 <== x;
    add.y1 <== y;
    add.x2 <== x;
    add.y2 <== y;
    xout <== add.xout;
    yout <== add.yout;
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
