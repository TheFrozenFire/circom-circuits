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
// Windowed (w=4) double-and-add: process 4 bits per step with 16-point table.
// ═══════════════════════════════════════════════════

/// Computes scalar * point on secp256k1 via windowed double-and-add (w=4).
/// The scalar is given as k limbs of n bits (little-endian).
/// Precomputes {P, 2P, ..., 15P}, then 64 windows of 4×Double + Mux + AddUnequal.
///
/// NOTE: Does not handle scalar = 0 or point = identity.
/// The caller must ensure scalar ∈ [1, order-1] and point is a valid curve point.
template Secp256k1ScalarMult(n, k) {
    assert(n == 32 && k == 8);

    var W = 4;
    var TABLE_SIZE = 1 << W;  // 16
    var NUM_WINDOWS = (n * k) \ W;  // 64

    signal input scalar[k];
    signal input point[2][k];
    signal output out[2][k];

    // Decompose each scalar limb into n bits
    component n2b[k];
    for (var i = 0; i < k; i++) {
        n2b[i] = Num2Bits(n);
        n2b[i].in <== scalar[i];
    }

    // ───────────────────────────────────────────────
    // Precompute 16-point table: table[j] = j * point for j ∈ [0, 15]
    // table[0] = DUMMY (placeholder for zero), table[1] = point
    // ───────────────────────────────────────────────

    var dummyVar[2][8] = SECP256K1_DUMMY(n, k);
    signal table[TABLE_SIZE][2][k];

    // table[0] = DUMMY
    for (var l = 0; l < k; l++) {
        table[0][0][l] <== dummyVar[0][l];
        table[0][1][l] <== dummyVar[1][l];
    }

    // table[1] = point
    for (var l = 0; l < k; l++) {
        table[1][0][l] <== point[0][l];
        table[1][1][l] <== point[1][l];
    }

    // table[2] = 2P (double)
    signal t2[2][k];
    t2 <== Secp256k1Double(n, k)(point);

    for (var l = 0; l < k; l++) {
        table[2][0][l] <== t2[0][l];
        table[2][1][l] <== t2[1][l];
    }

    // table[j] = table[j-1] + P for j = 3..15
    signal tN[TABLE_SIZE - 3][2][k];
    for (var j = 3; j < TABLE_SIZE; j++) {
        tN[j - 3] <== Secp256k1AddUnequal(n, k)(table[j - 1], point);
        for (var l = 0; l < k; l++) {
            table[j][0][l] <== tN[j - 3][0][l];
            table[j][1][l] <== tN[j - 3][1][l];
        }
    }

    // ───────────────────────────────────────────────
    // Main loop: 64 windows, MSB to LSB, 4 bits each
    // ───────────────────────────────────────────────

    signal partial[NUM_WINDOWS + 1][2][k];
    // W doublers per window: doublers[w*W + d] for d=0..W-1
    component doublers[NUM_WINDOWS * W];
    component adders[NUM_WINDOWS];
    component muxes[NUM_WINDOWS];
    component is_zero_sel[NUM_WINDOWS];
    signal has_prev_nz[NUM_WINDOWS + 1];
    // Intermediate doubling chain: dbl_chain[w][d] = result after d-th double in window w
    signal dbl_chain[NUM_WINDOWS][W + 1][2][k];
    // Conditional add result per window
    signal intermed[NUM_WINDOWS][2][k];
    has_prev_nz[NUM_WINDOWS] <== 0;

    // Dummy point for initial partial (before first non-zero window)
    for (var l = 0; l < k; l++) {
        partial[NUM_WINDOWS][0][l] <== point[0][l];
        partial[NUM_WINDOWS][1][l] <== point[1][l];
    }

    for (var w = NUM_WINDOWS - 1; w >= 0; w--) {
        // Build 4-bit window selector from scalar bits
        var first_bit = w * W;  // LSB of this window
        var sel_sum = 0;
        for (var b = 0; b < W; b++) {
            var bit_idx = first_bit + b;
            var limb_idx = bit_idx \ n;
            var bit_pos = bit_idx % n;
            sel_sum += n2b[limb_idx].out[bit_pos] * (1 << b);
        }

        // 16-way mux: select table entry for this window
        muxes[w] = DualMultiplexer(k, TABLE_SIZE);
        muxes[w].sel <== sel_sum;
        for (var j = 0; j < TABLE_SIZE; j++) {
            for (var l = 0; l < k; l++) {
                muxes[w].inp0[j][l] <== table[j][0][l];
                muxes[w].inp1[j][l] <== table[j][1][l];
            }
        }

        is_zero_sel[w] = IsZero();
        is_zero_sel[w].in <== sel_sum;

        // 4× Double the accumulator
        for (var l = 0; l < k; l++) {
            dbl_chain[w][0][0][l] <== partial[w + 1][0][l];
            dbl_chain[w][0][1][l] <== partial[w + 1][1][l];
        }
        for (var d = 0; d < W; d++) {
            var dbl_idx = w * W + d;
            doublers[dbl_idx] = Secp256k1Double(n, k);
            for (var l = 0; l < k; l++) {
                doublers[dbl_idx].in[0][l] <== dbl_chain[w][d][0][l];
                doublers[dbl_idx].in[1][l] <== dbl_chain[w][d][1][l];
            }
            for (var l = 0; l < k; l++) {
                dbl_chain[w][d + 1][0][l] <== doublers[dbl_idx].out[0][l];
                dbl_chain[w][d + 1][1][l] <== doublers[dbl_idx].out[1][l];
            }
        }

        // Add mux output to 4×-doubled accumulator
        adders[w] = Secp256k1AddUnequal(n, k);
        for (var l = 0; l < k; l++) {
            adders[w].a[0][l] <== dbl_chain[w][W][0][l];
            adders[w].a[1][l] <== dbl_chain[w][W][1][l];
            adders[w].b[0][l] <== muxes[w].out0[l];
            adders[w].b[1][l] <== muxes[w].out1[l];
        }

        // intermed = sel!=0 ? added : 4×-doubled
        for (var l = 0; l < k; l++) {
            intermed[w][0][l] <== (1 - is_zero_sel[w].out) * (adders[w].out[0][l] - dbl_chain[w][W][0][l]) + dbl_chain[w][W][0][l];
            intermed[w][1][l] <== (1 - is_zero_sel[w].out) * (adders[w].out[1][l] - dbl_chain[w][W][1][l]) + dbl_chain[w][W][1][l];
        }

        // has_prev_nz = prev OR (sel != 0)
        has_prev_nz[w] <== has_prev_nz[w + 1] + (1 - is_zero_sel[w].out)
                          - has_prev_nz[w + 1] * (1 - is_zero_sel[w].out);

        // partial = has_prev ? intermed : mux_output
        for (var l = 0; l < k; l++) {
            partial[w][0][l] <== has_prev_nz[w + 1] * (intermed[w][0][l] - muxes[w].out0[l]) + muxes[w].out0[l];
            partial[w][1][l] <== has_prev_nz[w + 1] * (intermed[w][1][l] - muxes[w].out1[l]) + muxes[w].out1[l];
        }
    }

    for (var l = 0; l < k; l++) {
        out[0][l] <== partial[0][0][l];
        out[1][l] <== partial[0][1][l];
    }
}

// ═══════════════════════════════════════════════════
// Fixed-base (generator G) scalar multiplication.
// Stride-6 windowed: only 42 additions, no doublings.
// ═══════════════════════════════════════════════════

/// Computes privkey * G on secp256k1 using a precomputed stride-6 table.
/// 43 strides × 64 precomputed points. Only 42 Secp256k1AddUnequal calls.
///
/// privkey must be in [1, order-1]. Does not handle privkey = 0.
template Secp256k1PrivToPub(n, k) {
    assert(n == 32 && k == 8);

    var stride = 6;
    signal input privkey[k];
    signal output pubkey[2][k];

    // Decompose privkey into bits
    component n2b[k];
    for (var i = 0; i < k; i++) {
        n2b[i] = Num2Bits(n);
        n2b[i].in <== privkey[i];
    }

    var num_strides = div_ceil(n * k, stride);

    // Precomputed table: powers[s][j] = j * 2^(6s) * G for j ∈ [0, 63]
    var powers[43][64][2][8] = SECP256K1_G_TABLE(n, k);

    // Dummy point: G * 2^255 — used when selector == 0 to avoid point-at-infinity.
    // AddUnequal requires distinct points, so we need a stand-in.
    var dummyVar[2][8] = SECP256K1_DUMMY(n, k);
    signal dummy[2][k];
    for (var i = 0; i < k; i++) {
        dummy[0][i] <== dummyVar[0][i];
        dummy[1][i] <== dummyVar[1][i];
    }

    // For each stride, extract bits and select from precomputed table.
    // Uses DualMultiplexerFromBits to avoid Bits2Num→Num2Bits round-trip.
    signal stride_bits[num_strides][stride];
    signal sel_val[num_strides];
    component muxes[num_strides];
    component iszero[num_strides];
    for (var s = 0; s < num_strides; s++) {
        // Wire stride bits directly from privkey decomposition
        var sel_sum = 0;
        for (var j = 0; j < stride; j++) {
            var bit_limb = (s * stride + j) \ n;
            var bit_pos = (s * stride + j) % n;
            if (bit_limb < k) {
                stride_bits[s][j] <== n2b[bit_limb].out[bit_pos];
            } else {
                stride_bits[s][j] <== 0;
            }
            sel_sum += stride_bits[s][j] * (1 << j);
        }
        sel_val[s] <== sel_sum;  // linear — 0 non-linear constraints

        muxes[s] = DualMultiplexerFromBits(k, (1 << stride));
        for (var j = 0; j < stride; j++) {
            muxes[s].bits[j] <== stride_bits[s][j];
        }
        for (var l = 0; l < k; l++) {
            // selector==0 → dummy point
            muxes[s].inp0[0][l] <== dummy[0][l];
            muxes[s].inp1[0][l] <== dummy[1][l];
            for (var j = 1; j < (1 << stride); j++) {
                muxes[s].inp0[j][l] <== powers[s][j][0][l];
                muxes[s].inp1[j][l] <== powers[s][j][1][l];
            }
        }

        iszero[s] = IsZero();
        iszero[s].in <== sel_val[s];
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
    for (var l = 0; l < k; l++) {
        partial_result[0][0][l] <== muxes[0].out0[l];
        partial_result[0][1][l] <== muxes[0].out1[l];
    }

    component adders[num_strides - 1];
    signal intermed1[num_strides - 1][2][k];
    signal intermed2[num_strides - 1][2][k];
    for (var s = 1; s < num_strides; s++) {
        adders[s - 1] = Secp256k1AddUnequal(n, k);
        for (var l = 0; l < k; l++) {
            adders[s - 1].a[0][l] <== partial_result[s - 1][0][l];
            adders[s - 1].a[1][l] <== partial_result[s - 1][1][l];
            adders[s - 1].b[0][l] <== muxes[s].out0[l];
            adders[s - 1].b[1][l] <== muxes[s].out1[l];
        }

        // Conditional accumulation:
        // If current stride is zero:  carry forward partial_result (skip add)
        // If current stride nonzero AND has prior: use adder output
        // If current stride nonzero AND no prior:  use multiplexer output directly
        for (var l = 0; l < k; l++) {
            intermed1[s - 1][0][l] <== iszero[s].out * (partial_result[s - 1][0][l] - adders[s - 1].out[0][l]) + adders[s - 1].out[0][l];
            intermed1[s - 1][1][l] <== iszero[s].out * (partial_result[s - 1][1][l] - adders[s - 1].out[1][l]) + adders[s - 1].out[1][l];
            intermed2[s - 1][0][l] <== muxes[s].out0[l] - iszero[s].out * muxes[s].out0[l];
            intermed2[s - 1][1][l] <== muxes[s].out1[l] - iszero[s].out * muxes[s].out1[l];
            partial_result[s][0][l] <== has_prev_nonzero[s - 1].out * (intermed1[s - 1][0][l] - intermed2[s - 1][0][l]) + intermed2[s - 1][0][l];
            partial_result[s][1][l] <== has_prev_nonzero[s - 1].out * (intermed1[s - 1][1][l] - intermed2[s - 1][1][l]) + intermed2[s - 1][1][l];
        }
    }

    for (var c = 0; c < 2; c++) {
        for (var l = 0; l < k; l++) {
            pubkey[c][l] <== partial_result[num_strides - 1][c][l];
        }
    }
}
