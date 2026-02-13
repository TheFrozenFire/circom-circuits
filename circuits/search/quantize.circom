pragma circom 2.2.2;

include "search/commit.circom";
include "linalg/fixedpoint.circom";

/// Quantization proof: proves that a quantized integer embedding is the
/// correct rounding of a high-precision fixed-point embedding.
///
/// Given commitments to both representations, verifies:
///   q[i] = round(embedding[i] * scale / 2^precision)
///
/// The rounding constraint is enforced by checking that the remainder
///   r[i] = embedding[i] * scale - quantized[i] * 2^precision + 2^(precision-1)
/// satisfies 0 <= r[i] < 2^precision (via InRange).
///
/// scale and precision are compile-time constants, so the linear
/// combination embedding[i] * scale costs zero constraints.
template QuantizationProof(n, chunkSize, scale, precision) {
    signal input embedding[n];
    signal input quantized[n];
    signal input embeddingCommit;
    signal input quantizedCommit;

    // 1. Verify embedding matches its commitment
    component embCommit = VectorCommit(n, chunkSize);
    for (var i = 0; i < n; i++) {
        embCommit.v[i] <== embedding[i];
    }
    embCommit.out === embeddingCommit;

    // 2. Verify quantized vector matches its commitment
    component qCommit = VectorCommit(n, chunkSize);
    for (var i = 0; i < n; i++) {
        qCommit.v[i] <== quantized[i];
    }
    qCommit.out === quantizedCommit;

    // 3. For each element, verify correct rounding via range check
    var halfRange = 1 << (precision - 1);
    var fullRange = 1 << precision;

    signal remainder[n];
    component rangeCheck[n];
    for (var i = 0; i < n; i++) {
        remainder[i] <== embedding[i] * scale - quantized[i] * fullRange + halfRange;
        rangeCheck[i] = InRange(precision);
        rangeCheck[i].in <== remainder[i];
    }
}
