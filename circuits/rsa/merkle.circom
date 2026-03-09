pragma circom 2.2.2;

include "rsa/cube.circom";
include "arithmetic/bigint.circom";
include "core/mux.circom";

/// RSA Merkle compression function: H(L, R) = L³ + 2·R³ mod N.
///
/// The asymmetric constant 2 prevents swap attacks (H(L,R) ≠ H(R,L))
/// and is not a perfect cube, so 2^(1/3) mod N is the RSA problem itself.
/// Collision resistance reduces to factoring N.
///
/// Cost: 2 RSACube + 2 BigAdd + 2 BigMod
template RSAMerkleHash(n, k) {
    signal input L[k];
    signal input R[k];
    signal input N[k];
    signal output out[k];

    // L³ mod N (canonical)
    signal L3[k] <== RSACube(n, k)(L, N);

    // R³ mod N (canonical)
    signal R3[k] <== RSACube(n, k)(R, N);

    // 2·R³ = R³ + R³, then reduce mod N
    signal twoR3_wide[k + 1] <== BigAdd(n, k)(R3, R3);
    signal twoR3[k] <== BigMod(n, k)(twoR3_wide, N);

    // L³ + 2·R³ mod N
    signal sum[k + 1] <== BigAdd(n, k)(L3, twoR3);
    out <== BigMod(n, k)(sum, N);
}

/// RSA Merkle tree inclusion proof.
/// Verifies a path from leaf to root using RSAMerkleHash at each level.
///
/// At each level, pathIndices[i] selects whether the current hash is the
/// left child (0) or right child (1). The sibling is provided as a k-limb
/// big integer.
///
/// Parameters:
///   n — bits per limb
///   k — limbs per big integer (n*k = RSA modulus bit width)
///   nLevels — tree depth
template RSAMerkleTreeInclusionProof(n, k, nLevels) {
    signal input leaf[k];
    signal input pathIndices[nLevels];
    signal input siblings[nLevels][k];
    signal input N[k];
    signal output root[k];

    signal hashes[nLevels + 1][k];
    for (var j = 0; j < k; j++) {
        hashes[0][j] <== leaf[j];
    }

    // Muxed inputs and hash outputs, declared in initial scope
    signal muxL[nLevels][k];
    signal muxR[nLevels][k];
    signal levelHash[nLevels][k];

    for (var i = 0; i < nLevels; i++) {
        // pathIndices must be binary
        pathIndices[i] * (1 - pathIndices[i]) === 0;

        // Mux per limb: select (L, R) based on path direction.
        // pathIndex=0: L=current, R=sibling
        // pathIndex=1: L=sibling, R=current
        for (var j = 0; j < k; j++) {
            muxL[i][j] <== hashes[i][j] + pathIndices[i] * (siblings[i][j] - hashes[i][j]);
            muxR[i][j] <== siblings[i][j] + pathIndices[i] * (hashes[i][j] - siblings[i][j]);
        }

        levelHash[i] <== RSAMerkleHash(n, k)(muxL[i], muxR[i], N);

        for (var j = 0; j < k; j++) {
            hashes[i + 1][j] <== levelHash[i][j];
        }
    }

    for (var j = 0; j < k; j++) {
        root[j] <== hashes[nLevels][j];
    }
}
