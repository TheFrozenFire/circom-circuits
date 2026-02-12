pragma circom 2.2.2;

include "packing/bitify.circom";

/// PKCS v1.5 SHA-256 padding for RSA signatures.
/// Constructs the padded message from a SHA-256 hash for RSA signing/verification.
/// Hardcoded for 1024-bit keys with 32-bit windows (n=32, k=32).
///
/// Layout (big-endian byte order):
///   00 01 [FF padding] 00 [ASN.1 DigestInfo] [32-byte SHA-256 hash]
///
/// TODO: Adapt for different key sizes.
template RSAPKCSv15Pad(n, k) {
    signal input message_hash[256];
    signal padded_message_bwe[k];
    signal output padded_message[k];

    var nWindows = 256 \ n;

    // https://www.rfc-editor.org/rfc/rfc2313#section-8.1
    // 1024 bits = 128 bytes = 32 words (n=32)
    // Padding: 128 - 2 (prefix) - 1 (delimiter) - 19 (ASN.1) - 32 (digest) = 74 bytes
    // 74 / 4 = 18 full 0xFFFFFFFF words + 2 remaining FF bytes before delimiter
    padded_message_bwe[0] <== 0x0001FFFF;
    for (var i = 0; i < 18; i++) {
        padded_message_bwe[1 + i] <== 0xFFFFFFFF;
    }
    // 00 delimiter + ASN.1 DigestInfo for SHA-256
    padded_message_bwe[19] <== 0x00303130;
    padded_message_bwe[20] <== 0x0D060960;
    padded_message_bwe[21] <== 0x86480165;
    padded_message_bwe[22] <== 0x03040201;
    padded_message_bwe[23] <== 0x05000420;

    // Convert hash bits to 32-bit windows
    signal message_hash_bits[nWindows][n];
    for (var i = 0; i < nWindows; i++) {
        for (var j = 0; j < n; j++) {
            message_hash_bits[i][j] <== message_hash[i * n + j];
        }
        padded_message_bwe[24 + i] <== Bits2NumLE(n)(message_hash_bits[i]);
    }

    // Reverse to little-endian limb order
    for (var i = 0; i < k; i++) {
        padded_message[k - i - 1] <== padded_message_bwe[i];
    }
}
