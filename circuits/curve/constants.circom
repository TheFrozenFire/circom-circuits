pragma circom 2.2.2;

/// BabyJubjub twisted Edwards curve parameter a.
function BABYJUB_A() {
    return 168700;
}

/// BabyJubjub twisted Edwards curve parameter d.
function BABYJUB_D() {
    return 168696;
}

/// Subgroup order of the BabyJubjub curve.
function BABYJUB_SUBORDER() {
    return 2736030358979909402780800718157159386076813972158567259200215660948447373041;
}

/// Base point (generator) of the BabyJubjub subgroup of order l.
/// Returns [x, y].
function BABYJUB_BASE8() {
    return [
        5299619240641551281634865583518297030282874472190772894086521144482721001553,
        16950150798460657717958625567821834550301663161624707787222815936182638968203
    ];
}
