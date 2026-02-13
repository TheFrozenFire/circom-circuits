pragma circom 2.2.2;

include "search/commit.circom";
include "hash/merkle.circom";
include "linalg/vector.circom";
include "comparators.circom";

/// Private deduplication proof.
///
/// Proves that a private document embedding is sufficiently distant from
/// a candidate embedding in a committed database, without revealing
/// either document's content.
///
/// Public inputs: documentCommit (prover's document hash),
///                merkleRoot (database commitment),
///                minDistSq (minimum distance threshold).
/// Private inputs: document, candidate, Merkle proof path.
template PrivateDedup(n, chunkSize, dbDepth, bits) {
    signal input document[n];
    signal input candidate[n];
    signal input pathIndices[dbDepth];
    signal input siblings[dbDepth];
    signal input documentCommit;
    signal input merkleRoot;
    signal input minDistSq;

    // 1. Verify document matches published commitment
    component docCommit = VectorCommit(n, chunkSize);
    for (var i = 0; i < n; i++) {
        docCommit.v[i] <== document[i];
    }
    docCommit.out === documentCommit;

    // 2. Commit the candidate embedding
    component candCommit = VectorCommit(n, chunkSize);
    for (var i = 0; i < n; i++) {
        candCommit.v[i] <== candidate[i];
    }

    // 3. Verify candidate is in the database via Merkle inclusion
    component merkle = MerkleTreeInclusionProof(dbDepth);
    merkle.leaf <== candCommit.out;
    for (var i = 0; i < dbDepth; i++) {
        merkle.pathIndices[i] <== pathIndices[i];
        merkle.siblings[i] <== siblings[i];
    }
    merkle.out === merkleRoot;

    // 4. Compute distance between document and candidate
    component dist = EuclideanDistanceSquared(n);
    for (var i = 0; i < n; i++) {
        dist.a[i] <== document[i];
        dist.b[i] <== candidate[i];
    }

    // 5. Distance must exceed threshold: minDistSq < distSq
    component lt = LessThan(bits);
    lt.in[0] <== minDistSq;
    lt.in[1] <== dist.out;
    lt.out === 1;
}
