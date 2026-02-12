pragma circom 2.2.2;

include "packing/bitify.circom";
include "curve/compress.circom";
include "circomlib/circuits/sha256/sha256.circom";

function N_COMMITMENT_BITS(n) { return (256 * 2) + n; }

/// Serializes a Schnorr commitment to bits for hashing.
/// Layout per point (256 bits): [0 pad][sign bit][y_bit_0..y_bit_253]
/// Followed by n message bits.
template SchnorrMessagePack(n) {
    signal input R[2];
    signal input signerX[2];
    signal input message[n];
    signal output out[N_COMMITMENT_BITS(n)];

    // Compress both points to extract sign bit and y-coordinate bits
    signal compR[256] <== BabyCompress()(R);
    signal compX[256] <== BabyCompress()(signerX);

    // Pack R: [0][sign][y0..y253]
    out[0] <== 0;
    out[1] <== compR[255]; // sign bit
    for (var j = 0; j < 254; j++) {
        out[2 + j] <== compR[j]; // y bits
    }

    // Pack signerX: [0][sign][y0..y253]
    out[256] <== 0;
    out[257] <== compX[255]; // sign bit
    for (var j = 0; j < 254; j++) {
        out[258 + j] <== compX[j]; // y bits
    }

    // Append message bits
    for (var i = 0; i < n; i++) {
        out[512 + i] <== message[i];
    }
}

/// Hashes a Schnorr commitment with SHA256, truncated to 248 bits.
/// Returns the hash as a field element (fits in BN128 field).
template SchnorrMessageCommit(n) {
    signal input R[2];
    signal input signerX[2];
    signal input message[n];

    signal commitment_bits[N_COMMITMENT_BITS(n)] <== SchnorrMessagePack(n)(R, signerX, message);

    signal commitment_hash[256] <== Sha256(N_COMMITMENT_BITS(n))(commitment_bits);

    // Truncate to 248 bits to fit safely in BN128 field
    signal truncated[248];
    for (var i = 0; i < 248; i++) {
        truncated[i] <== commitment_hash[i];
    }

    signal output out <== Bits2NumLE(248)(truncated);
}
