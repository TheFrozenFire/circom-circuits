pragma circom 2.2.2;

include "core/comparators.circom";

/// Select in[sel] from an n-element array via one-hot IsEqual encoding.
/// n IsEqual + n quadratic constraints.
template Lookup(n) {
    signal input in[n];
    signal input sel;
    signal output out;

    component eq[n];
    signal products[n];
    var sum = 0;

    for (var i = 0; i < n; i++) {
        eq[i] = IsEqual();
        eq[i].in[0] <== sel;
        eq[i].in[1] <== i;

        products[i] <== in[i] * eq[i].out;
        sum += products[i];
    }

    out <== sum;
}

/// Select full row props[sel][*] from an n×nProps table via one-hot encoding.
/// n IsEqual + n×nProps quadratic constraints.
template LookupRow(n, nProps) {
    signal input props[n][nProps];
    signal input sel;
    signal output out[nProps];

    component eq[n];
    signal products[n][nProps];

    for (var i = 0; i < n; i++) {
        eq[i] = IsEqual();
        eq[i].in[0] <== sel;
        eq[i].in[1] <== i;

        for (var p = 0; p < nProps; p++) {
            products[i][p] <== props[i][p] * eq[i].out;
        }
    }

    for (var p = 0; p < nProps; p++) {
        var sum = 0;
        for (var i = 0; i < n; i++) {
            sum += products[i][p];
        }
        out[p] <== sum;
    }
}
