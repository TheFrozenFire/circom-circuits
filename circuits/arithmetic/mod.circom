pragma circom 2.2.2;

include "packing/bitify.circom";

/// (a + b) mod 2^n. Assumes a, b < 2^n.
/// (n + 1) binary constraints + 1 sum constraint.
template ModSum(n) {
    signal input a;
    signal input b;
    signal output out <== TruncNumLE(n + 1, n)(a + b);
}

/// (a - b) mod 2^n. Assumes a, b < 2^n.
/// Adds 2^n to ensure non-negative before decomposition.
template ModSub(n) {
    signal input a;
    signal input b;
    signal output out <== TruncNumLE(n + 1, n)(a - b + (1 << n));
}

/// (a + b + c) mod 2^n. Assumes a, b, c < 2^n.
template ModSumThree(n) {
    signal input a;
    signal input b;
    signal input c;
    signal output out <== TruncNumLE(n + 2, n)(a + b + c);
}

/// (a - b - c) mod 2^n. Assumes a, b, c < 2^n.
/// Adds 2^(n+1) to ensure non-negative before decomposition.
template ModSubThree(n) {
    signal input a;
    signal input b;
    signal input c;
    signal output out <== TruncNumLE(n + 2, n)(a - b - c + (1 << (n + 1)));
}

/// (a + b + c + d) mod 2^n. Assumes a, b, c, d < 2^n.
template ModSumFour(n) {
    signal input a;
    signal input b;
    signal input c;
    signal input d;
    signal output out <== TruncNumLE(n + 2, n)(a + b + c + d);
}

/// (a * b) mod 2^n. Assumes a, b < 2^n.
/// 2n binary constraints + 1 sum + 1 multiplication.
template ModProd(n) {
    signal input a;
    signal input b;
    signal output out;

    signal product <== a * b;
    out <== TruncNumLE(2 * n, n)(product);
}

/// Splits a value into a low part (n bits) and a high part (m bits).
/// Constrains: in = small + big * 2^n, small < 2^n, big < 2^m.
template Split(n, m) {
    signal input in;
    signal output small;
    signal output big;

    signal bits[n + m] <== Num2BitsLE(n + m)(in);

    var lowSum = 0;
    for (var i = 0; i < n; i++) {
        lowSum += bits[i] * (1 << i);
    }
    small <== lowSum;

    var highSum = 0;
    for (var i = 0; i < m; i++) {
        highSum += bits[n + i] * (1 << i);
    }
    big <== highSum;
}

/// Splits a value into three parts of n, m, and k bits.
/// Constrains: in = small + medium * 2^n + big * 2^(n+m).
template SplitThree(n, m, k) {
    signal input in;
    signal output small;
    signal output medium;
    signal output big;

    signal bits[n + m + k] <== Num2BitsLE(n + m + k)(in);

    var lowSum = 0;
    for (var i = 0; i < n; i++) {
        lowSum += bits[i] * (1 << i);
    }
    small <== lowSum;

    var midSum = 0;
    for (var i = 0; i < m; i++) {
        midSum += bits[n + i] * (1 << i);
    }
    medium <== midSum;

    var highSum = 0;
    for (var i = 0; i < k; i++) {
        highSum += bits[n + m + i] * (1 << i);
    }
    big <== highSum;
}
