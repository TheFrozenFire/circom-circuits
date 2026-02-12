pragma circom 2.2.2;

include "curve/constants.circom";

/// Convert Edwards point to Montgomery: [u, v] = [(1+y)/(1-y), (1+y)/((1-y)*x)].
template Edwards2Montgomery() {
    signal input in[2];
    signal output out[2];

    out[0] <-- (1 + in[1]) / (1 - in[1]);
    out[1] <-- out[0] / in[0];

    out[0] * (1 - in[1]) === (1 + in[1]);
    out[1] * in[0] === out[0];
}

/// Convert Montgomery point to Edwards: [x, y] = [u/v, (u-1)/(u+1)].
template Montgomery2Edwards() {
    signal input in[2];
    signal output out[2];

    out[0] <-- in[0] / in[1];
    out[1] <-- (in[0] - 1) / (in[0] + 1);

    out[0] * in[1] === in[0];
    out[1] * (in[0] + 1) === in[0] - 1;
}

/// Montgomery curve point addition.
/// lambda = (y2 - y1) / (x2 - x1)
/// x3 = B * lambda^2 - A - x1 - x2
/// y3 = lambda * (x1 - x3) - y1
template MontgomeryAdd() {
    signal input in1[2];
    signal input in2[2];
    signal output out[2];

    var a = BABYJUB_A();
    var d = BABYJUB_D();

    var A = (2 * (a + d)) / (a - d);
    var B = 4 / (a - d);

    signal lamda;

    lamda <-- (in2[1] - in1[1]) / (in2[0] - in1[0]);
    lamda * (in2[0] - in1[0]) === (in2[1] - in1[1]);

    out[0] <== B * lamda * lamda - A - in1[0] - in2[0];
    out[1] <== lamda * (in1[0] - out[0]) - in1[1];
}

/// Montgomery curve point doubling.
/// lambda = (3*x1^2 + 2*A*x1 + 1) / (2*B*y1)
/// x3 = B * lambda^2 - A - 2*x1
/// y3 = lambda * (x1 - x3) - y1
template MontgomeryDouble() {
    signal input in[2];
    signal output out[2];

    var a = BABYJUB_A();
    var d = BABYJUB_D();

    var A = (2 * (a + d)) / (a - d);
    var B = 4 / (a - d);

    signal lamda;
    signal x1_2;

    x1_2 <== in[0] * in[0];

    lamda <-- (3 * x1_2 + 2 * A * in[0] + 1) / (2 * B * in[1]);
    lamda * (2 * B * in[1]) === (3 * x1_2 + 2 * A * in[0] + 1);

    out[0] <== B * lamda * lamda - A - 2 * in[0];
    out[1] <== lamda * (in[0] - out[0]) - in[1];
}
