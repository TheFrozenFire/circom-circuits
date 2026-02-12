pragma circom 2.2.2;

include "arithmetic/bigint.circom";

/// Blinds a padded RSA message: out = padded_message * blinding mod public_modulus.
/// Expects pre-computed blinding factor (blinding^e mod N not implemented here).
template RSAMessageBlind(n, k, e) {
    signal input padded_message[k];
    signal input blinding[k];
    signal input public_modulus[k];

    signal output out[k] <== BigMultModP(n, k)(padded_message, blinding, public_modulus);
}
