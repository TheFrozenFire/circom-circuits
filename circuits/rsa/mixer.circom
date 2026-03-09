pragma circom 2.2.2;

include "rsa/cube.circom";
include "rsa/merkle.circom";
include "hash/poseidon.circom";
include "packing/bitify.circom";
include "arithmetic/bigint.circom";

/// RSA-based mixer withdrawal circuit.
///
/// Proves:
///   1. Knowledge of (nullifier, secret) encoding into a message m
///   2. m³ mod N equals the committed leaf
///   3. The leaf is in the Merkle tree with the given root
///   4. The nullifier hash is correctly derived
///
/// Parameters:
///   n — bits per limb
///   k — limbs per big integer (n*k = RSA modulus bit width)
///   nLevels — Merkle tree depth
///   nullifierLimbs — number of limbs for the nullifier portion of m
///   secretLimbs — number of limbs for the secret portion of m
///
/// Message encoding (little-endian limbs):
///   m[0..secretLimbs-1] = secret
///   m[secretLimbs..secretLimbs+nullifierLimbs-1] = nullifier
///   Remaining high limbs of m are zero-constrained.
///   Requires: secretLimbs + nullifierLimbs <= k
///   The encoding must produce m > N^(1/3) for hiding (enforced off-chain).
template RSAMixerWithdraw(n, k, nLevels, nullifierLimbs, secretLimbs) {
    // ─── Public inputs ──────────────────────────────────
    signal input root[k];           // Merkle root
    signal input nullifierHash;     // Poseidon(nullifier limbs) — prevents double-spend
    signal input N[k];              // RSA modulus
    signal input recipient;         // Withdrawal recipient (prevents front-running)

    // ─── Private inputs ─────────────────────────────────
    signal input nullifier[nullifierLimbs];
    signal input secret[secretLimbs];
    signal input pathIndices[nLevels];
    signal input siblings[nLevels][k];

    // ─── 1. Encode message ──────────────────────────────
    // m = secret ‖ nullifier, packed into k limbs (little-endian)
    signal m[k];
    for (var i = 0; i < k; i++) {
        if (i < secretLimbs) {
            m[i] <== secret[i];
        } else if (i < secretLimbs + nullifierLimbs) {
            m[i] <== nullifier[i - secretLimbs];
        } else {
            m[i] <== 0;
        }
    }

    // Range-check all message limbs to n bits
    signal secretBits[secretLimbs][n];
    for (var i = 0; i < secretLimbs; i++) {
        secretBits[i] <== Num2Bits(n)(secret[i]);
    }
    signal nullifierBits[nullifierLimbs][n];
    for (var i = 0; i < nullifierLimbs; i++) {
        nullifierBits[i] <== Num2Bits(n)(nullifier[i]);
    }

    // ─── 2. RSA commitment ──────────────────────────────
    // leaf = m³ mod N
    signal leaf[k] <== RSACube(n, k)(m, N);

    // ─── 3. Merkle inclusion proof ──────────────────────
    signal computedRoot[k] <== RSAMerkleTreeInclusionProof(n, k, nLevels)(
        leaf, pathIndices, siblings, N
    );

    // Verify computed root matches public root
    for (var j = 0; j < k; j++) {
        computedRoot[j] === root[j];
    }

    // ─── 4. Nullifier derivation ────────────────────────
    // Hash nullifier limbs with Poseidon.
    // Only computed in ZK — not shared with on-chain verifier.
    signal computedNullifierHash <== Poseidon(nullifierLimbs)(nullifier);
    computedNullifierHash === nullifierHash;

    // ─── 5. Constrain recipient (prevent front-running) ─
    // Square to create a constraint on recipient without
    // affecting any outputs. This prevents relay front-running.
    signal recipientSquare <== recipient * recipient;
}
