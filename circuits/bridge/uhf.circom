pragma circom 2.2.2;

/// Polynomial Universal Hash Function via Horner evaluation.
///
/// UHF(r, x) = x[0] + x[1]*r + x[2]*r^2 + ... + x[n-1]*r^(n-1)
///
/// Evaluated right-to-left using Horner's method:
///   acc = x[n-1]
///   acc = acc * r + x[n-2]
///   ...
///   acc = acc * r + x[0]
///
/// Constraints: exactly n-1 (each Horner step is one quadratic R1CS constraint).
/// Requires n >= 2.
template PolyUHF(n) {
    signal input r;
    signal input x[n];
    signal output out;

    // For n == 2: single quadratic constraint directly into out.
    // For n >= 3: n-2 intermediate signals plus final step into out.
    // Using x[n-1] directly in the first step avoids a linear constraint,
    // and assigning the last step to out avoids another.
    if (n == 2) {
        out <== x[1] * r + x[0];
    } else {
        signal acc[n - 2];
        acc[0] <== x[n - 1] * r + x[n - 2];
        for (var k = 1; k < n - 2; k++) {
            acc[k] <== acc[k - 1] * r + x[n - 2 - k];
        }
        out <== acc[n - 3] * r + x[0];
    }
}
