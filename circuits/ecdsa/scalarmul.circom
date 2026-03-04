pragma circom 2.2.2;

include "arithmetic/bigint_func.circom";
include "collections/multiplexer.circom";
include "core/bitwise.circom";
include "core/comparators.circom";
include "packing/bitify.circom";
include "ecdsa/constants.circom";
include "ecdsa/g_table.circom";
include "ecdsa/point.circom";

// ═══════════════════════════════════════════════════
// Variable-base scalar multiplication on secp256k1.
// Double-and-add with OR-chain for leading zero handling.
// ═══════════════════════════════════════════════════

/// Computes scalar * point on secp256k1 via double-and-add.
/// The scalar is given as k limbs of n bits (little-endian).
/// Uses 255 Secp256k1Double + 255 Secp256k1AddUnequal internally.
///
/// NOTE: Does not handle scalar = 0 or point = identity.
/// The caller must ensure scalar ∈ [1, order-1] and point is a valid curve point.
template Secp256k1ScalarMult(n, k) {
    assert(n == 64 && k == 4);

    signal input scalar[k];
    signal input point[2][k];
    signal output out[2][k];

    // Decompose each scalar limb into n bits
    component n2b[k];
    for (var i = 0; i < k; i++) {
        n2b[i] = Num2Bits(n);
        n2b[i].in <== scalar[i];
    }

    // has_prev_non_zero[n*i + j] == 1 iff there is a nonzero bit
    // at position [i][j] or any higher-order position.
    // Scanned from MSB (i=k-1, j=n-1) to LSB (i=0, j=0).
    component has_prev_non_zero[k * n];
    for (var i = k - 1; i >= 0; i--) {
        for (var j = n - 1; j >= 0; j--) {
            has_prev_non_zero[n * i + j] = OR();
            if (i == k - 1 && j == n - 1) {
                has_prev_non_zero[n * i + j].in[0] <== 0;
                has_prev_non_zero[n * i + j].in[1] <== n2b[i].out[j];
            } else {
                has_prev_non_zero[n * i + j].in[0] <== has_prev_non_zero[n * i + j + 1].out;
                has_prev_non_zero[n * i + j].in[1] <== n2b[i].out[j];
            }
        }
    }

    // Double-and-add from MSB to LSB.
    // partial[idx] holds the running result after processing bit idx.
    signal partial[n * k][2][k];
    signal intermed[n * k - 1][2][k];
    component adders[n * k - 1];
    component doublers[n * k - 1];

    for (var i = k - 1; i >= 0; i--) {
        for (var j = n - 1; j >= 0; j--) {
            var idx = n * i + j;

            if (i == k - 1 && j == n - 1) {
                // MSB: initialize partial to the input point
                for (var l = 0; l < k; l++) {
                    partial[idx][0][l] <== point[0][l];
                    partial[idx][1][l] <== point[1][l];
                }
            } else {
                // Double the previous partial result
                doublers[idx] = Secp256k1Double(n, k);
                for (var l = 0; l < k; l++) {
                    doublers[idx].in[0][l] <== partial[idx + 1][0][l];
                    doublers[idx].in[1][l] <== partial[idx + 1][1][l];
                }

                // Add the input point to the doubled result
                adders[idx] = Secp256k1AddUnequal(n, k);
                for (var l = 0; l < k; l++) {
                    adders[idx].a[0][l] <== doublers[idx].out[0][l];
                    adders[idx].a[1][l] <== doublers[idx].out[1][l];
                    adders[idx].b[0][l] <== point[0][l];
                    adders[idx].b[1][l] <== point[1][l];
                }

                // Mux: select add vs double based on current bit
                // intermed = bit * (add - dbl) + dbl
                //          = bit ? add : dbl
                for (var l = 0; l < k; l++) {
                    intermed[idx][0][l] <== n2b[i].out[j] * (adders[idx].out[0][l] - doublers[idx].out[0][l]) + doublers[idx].out[0][l];
                    intermed[idx][1][l] <== n2b[i].out[j] * (adders[idx].out[1][l] - doublers[idx].out[1][l]) + doublers[idx].out[1][l];
                }

                // If no previous nonzero bit, use point directly (skip leading zeros).
                // partial = has_prev * (intermed - point) + point
                //         = has_prev ? intermed : point
                for (var l = 0; l < k; l++) {
                    partial[idx][0][l] <== has_prev_non_zero[idx + 1].out * (intermed[idx][0][l] - point[0][l]) + point[0][l];
                    partial[idx][1][l] <== has_prev_non_zero[idx + 1].out * (intermed[idx][1][l] - point[1][l]) + point[1][l];
                }
            }
        }
    }

    for (var l = 0; l < k; l++) {
        out[0][l] <== partial[0][0][l];
        out[1][l] <== partial[0][1][l];
    }
}

// ═══════════════════════════════════════════════════
// Fixed-base (generator G) scalar multiplication.
// Stride-8 windowed: only 31 additions, no doublings.
// ═══════════════════════════════════════════════════

/// Computes privkey * G on secp256k1 using a precomputed stride-8 table.
/// 32 strides × 256 precomputed points. Only 31 Secp256k1AddUnequal calls.
///
/// privkey must be in [1, order-1]. Does not handle privkey = 0.
template Secp256k1PrivToPub(n, k) {
    assert(n == 64 && k == 4);

    var stride = 8;
    signal input privkey[k];
    signal output pubkey[2][k];

    // Decompose privkey into bits
    component n2b[k];
    for (var i = 0; i < k; i++) {
        n2b[i] = Num2Bits(n);
        n2b[i].in <== privkey[i];
    }

    var num_strides = div_ceil(n * k, stride);

    // Precomputed table: powers[s][j] = j * 2^(8s) * G for j ∈ [0, 255]
    var powers[32][256][2][4] = SECP256K1_G_TABLE(n, k);

    // Dummy point: G * 2^255 — used when selector == 0 to avoid point-at-infinity.
    // AddUnequal requires distinct points, so we need a stand-in.
    var dummyVar[2][4] = SECP256K1_DUMMY(n, k);
    signal dummy[2][k];
    for (var i = 0; i < k; i++) {
        dummy[0][i] <== dummyVar[0][i];
        dummy[1][i] <== dummyVar[1][i];
    }

    // Extract 8-bit selector per stride from privkey bits
    component selectors[num_strides];
    for (var s = 0; s < num_strides; s++) {
        selectors[s] = Bits2Num(stride);
        for (var j = 0; j < stride; j++) {
            var bit_limb = (s * stride + j) \ n;
            var bit_pos = (s * stride + j) % n;
            if (bit_limb < k) {
                selectors[s].in[j] <== n2b[bit_limb].out[bit_pos];
            } else {
                selectors[s].in[j] <== 0;
            }
        }
    }

    // For each stride, select the precomputed point (or dummy if selector==0).
    // multiplexers[s][coord].out = selected k-register coordinate.
    component multiplexers[num_strides][2];
    for (var s = 0; s < num_strides; s++) {
        for (var c = 0; c < 2; c++) {
            multiplexers[s][c] = Multiplexer(k, (1 << stride));
            multiplexers[s][c].sel <== selectors[s].out;
            for (var l = 0; l < k; l++) {
                // selector==0 → dummy point
                multiplexers[s][c].inp[0][l] <== dummy[c][l];
                for (var j = 1; j < (1 << stride); j++) {
                    multiplexers[s][c].inp[j][l] <== powers[s][j][c][l];
                }
            }
        }
    }

    // Detect zero selectors (selector == 0 means this stride contributes nothing)
    component iszero[num_strides];
    for (var s = 0; s < num_strides; s++) {
        iszero[s] = IsZero();
        iszero[s].in <== selectors[s].out;
    }

    // Track whether any previous stride was non-zero
    component has_prev_nonzero[num_strides];
    has_prev_nonzero[0] = OR();
    has_prev_nonzero[0].in[0] <== 0;
    has_prev_nonzero[0].in[1] <== 1 - iszero[0].out;
    for (var s = 1; s < num_strides; s++) {
        has_prev_nonzero[s] = OR();
        has_prev_nonzero[s].in[0] <== has_prev_nonzero[s - 1].out;
        has_prev_nonzero[s].in[1] <== 1 - iszero[s].out;
    }

    // Accumulate: add each stride's contribution
    signal partial_result[num_strides][2][k];
    for (var c = 0; c < 2; c++) {
        for (var l = 0; l < k; l++) {
            partial_result[0][c][l] <== multiplexers[0][c].out[l];
        }
    }

    component adders[num_strides - 1];
    signal intermed1[num_strides - 1][2][k];
    signal intermed2[num_strides - 1][2][k];
    for (var s = 1; s < num_strides; s++) {
        adders[s - 1] = Secp256k1AddUnequal(n, k);
        for (var c = 0; c < 2; c++) {
            for (var l = 0; l < k; l++) {
                adders[s - 1].a[c][l] <== partial_result[s - 1][c][l];
                adders[s - 1].b[c][l] <== multiplexers[s][c].out[l];
            }
        }

        // Conditional accumulation:
        // If current stride is zero:  carry forward partial_result (skip add)
        // If current stride nonzero AND has prior: use adder output
        // If current stride nonzero AND no prior:  use multiplexer output directly
        for (var c = 0; c < 2; c++) {
            for (var l = 0; l < k; l++) {
                intermed1[s - 1][c][l] <== iszero[s].out * (partial_result[s - 1][c][l] - adders[s - 1].out[c][l]) + adders[s - 1].out[c][l];
                intermed2[s - 1][c][l] <== multiplexers[s][c].out[l] - iszero[s].out * multiplexers[s][c].out[l];
                partial_result[s][c][l] <== has_prev_nonzero[s - 1].out * (intermed1[s - 1][c][l] - intermed2[s - 1][c][l]) + intermed2[s - 1][c][l];
            }
        }
    }

    for (var c = 0; c < 2; c++) {
        for (var l = 0; l < k; l++) {
            pubkey[c][l] <== partial_result[num_strides - 1][c][l];
        }
    }
}
