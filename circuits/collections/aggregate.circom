pragma circom 2.2.2;

/// Sums n inputs. Zero constraints (pure linear combination).
template CalculateTotal(n) {
    signal input in[n];
    signal output out;

    var sum = 0;
    for (var i = 0; i < n; i++) {
        sum += in[i];
    }
    out <== sum;
}

/// Multiplies n inputs. (n - 1) constraints.
template CalculateProduct(n) {
    assert(n > 0);

    signal input in[n];
    signal output out;

    signal intermediate[n];
    intermediate[0] <== in[0];
    for (var i = 1; i < n; i++) {
        intermediate[i] <== intermediate[i - 1] * in[i];
    }
    out <== intermediate[n - 1];
}
