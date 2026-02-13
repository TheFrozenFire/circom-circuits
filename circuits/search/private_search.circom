pragma circom 2.2.2;

include "search/commit.circom";
include "hash/merkle.circom";
include "linalg/vector.circom";
include "comparators.circom";

/// Private semantic search proof.
///
/// Proves that a private query embedding is within distance threshold
/// of a document embedding that exists in a committed database,
/// without revealing the query or which document matched.
///
/// Public inputs: merkleRoot (database commitment), maxDistSq (distance threshold).
/// Private inputs: query, document, Merkle proof path.
template PrivateSearch(n, chunkSize, dbDepth, bits) {
    signal input query[n];
    signal input document[n];
    signal input pathIndices[dbDepth];
    signal input siblings[dbDepth];
    signal input merkleRoot;
    signal input maxDistSq;

    // 1. Commit the document embedding
    component commit = VectorCommit(n, chunkSize);
    for (var i = 0; i < n; i++) {
        commit.v[i] <== document[i];
    }

    // 2. Verify Merkle inclusion
    component merkle = MerkleTreeInclusionProof(dbDepth);
    merkle.leaf <== commit.out;
    for (var i = 0; i < dbDepth; i++) {
        merkle.pathIndices[i] <== pathIndices[i];
        merkle.siblings[i] <== siblings[i];
    }

    // 3. Computed root must match public root
    merkle.out === merkleRoot;

    // 4. Compute distance between query and document
    component dist = EuclideanDistanceSquared(n);
    for (var i = 0; i < n; i++) {
        dist.a[i] <== query[i];
        dist.b[i] <== document[i];
    }

    // 5. Distance must be less than threshold
    component lt = LessThan(bits);
    lt.in[0] <== dist.out;
    lt.in[1] <== maxDistSq;
    lt.out === 1;
}
