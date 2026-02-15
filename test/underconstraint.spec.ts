import { assert } from "chai";
import { compile_and_analyze, CircuitDef } from "./helpers.js";
import type { R1CSDetails } from "@frozenfire/circom-build";
import type { SymbolMap } from "@frozenfire/circom-witness";

// --- Analysis helpers ---

/**
 * Collect every variable index that appears in any R1CS constraint coefficient.
 * Uses indexed access rather than for...of to handle snarkjs BigArray proxies
 * (which don't support Symbol.iterator).
 */
function getReferencedVars(constraints: R1CSDetails["constraints"]): Set<number> {
    const refs = new Set<number>();
    const len = (constraints as any).length as number;
    for (let c = 0; c < len; c++) {
        const constraint = (constraints as any)[c];
        for (let j = 0; j < 3; j++) {
            const lc = constraint[j];
            for (const idx of Object.keys(lc)) refs.add(Number(idx));
        }
    }
    return refs;
}

/**
 * Find non-input signals that never appear in any constraint.
 * Variable layout: [constant_wire, outputs..., pubInputs..., prvInputs..., internal...]
 */
function findUnconstrainedSignals(
    details: R1CSDetails,
    symbols: SymbolMap
): string[] {
    const refs = getReferencedVars(details.constraints);

    // Inputs = outputs + public inputs + private inputs (all are "given" by prover/verifier)
    const inputEnd = 1 + details.nOutputs + details.nPubInputs + details.nPrvInputs;
    const unconstrained: string[] = [];

    // Build reverse map: varIndex -> signal name
    const indexToName = new Map<number, string>();
    for (const [name, sym] of Object.entries(symbols)) {
        indexToName.set(sym.varIndex, name);
    }

    // Check all non-input, non-constant variables
    for (let i = inputEnd; i < details.nVars; i++) {
        if (!refs.has(i)) {
            unconstrained.push(indexToName.get(i) ?? `var_${i}`);
        }
    }
    return unconstrained;
}

/** Compute degrees of freedom: nNonInputSignals - nConstraints. */
function computeDegreesOfFreedom(details: R1CSDetails): {
    nConstraints: number;
    nNonInput: number;
    dof: number;
} {
    const nNonInput = details.nVars - 1 - details.nPubInputs - details.nPrvInputs;
    return {
        nConstraints: details.nConstraints,
        nNonInput,
        dof: nNonInput - details.nConstraints,
    };
}

// --- Circuit table ---

const circuits: Array<{ label: string; def: CircuitDef }> = [
    // Core
    { label: "IsZero", def: { path: "core/comparators.circom", template: "IsZero" } },
    { label: "IsEqual", def: { path: "core/comparators.circom", template: "IsEqual" } },
    { label: "LessThan(4)", def: { path: "core/comparators.circom", template: "LessThan", params: [4] } },
    { label: "ForceEqualIfEnabled", def: { path: "core/comparators.circom", template: "ForceEqualIfEnabled" } },
    { label: "XOR", def: { path: "core/bitwise.circom", template: "XOR" } },
    { label: "AND", def: { path: "core/bitwise.circom", template: "AND" } },
    { label: "OR", def: { path: "core/bitwise.circom", template: "OR" } },
    { label: "MUXOR(4)", def: { path: "core/bitwise.circom", template: "MUXOR", params: [4] } },
    { label: "MultiXOR(4)", def: { path: "core/bitwise.circom", template: "MultiXOR", params: [4] } },
    { label: "BitwiseXOR(4)", def: { path: "core/bitwise.circom", template: "BitwiseXOR", params: [4] } },
    { label: "BitwiseAND(4)", def: { path: "core/bitwise.circom", template: "BitwiseAND", params: [4] } },
    { label: "BitwiseOR(4)", def: { path: "core/bitwise.circom", template: "BitwiseOR", params: [4] } },
    { label: "BitwiseNOT(4)", def: { path: "core/bitwise.circom", template: "BitwiseNOT", params: [4] } },
    { label: "MultiMux1(2)", def: { path: "core/mux.circom", template: "MultiMux1", params: [2] } },
    { label: "MultiMux3(2)", def: { path: "core/mux.circom", template: "MultiMux3", params: [2] } },

    // Packing
    { label: "Num2BitsLE(4)", def: { path: "packing/bitify.circom", template: "Num2BitsLE", params: [4] } },
    { label: "Bits2NumLE(4)", def: { path: "packing/bitify.circom", template: "Bits2NumLE", params: [4] } },
    { label: "Num2Bits(4)", def: { path: "packing/bitify.circom", template: "Num2Bits", params: [4] } },
    { label: "Bits2Num(4)", def: { path: "packing/bitify.circom", template: "Bits2Num", params: [4] } },
    { label: "TruncNumLE(8,4)", def: { path: "packing/bitify.circom", template: "TruncNumLE", params: [8, 4] } },
    { label: "Pack_Elements(1,4,4)", def: { path: "packing/pack.circom", template: "Pack_Elements", params: [1, 4, 4] } },
    { label: "Pack_Elements_FromBits(1,4,4)", def: { path: "packing/pack.circom", template: "Pack_Elements_FromBits", params: [1, 4, 4] } },
    { label: "Unpack_Elements(1,4,4)", def: { path: "packing/pack.circom", template: "Unpack_Elements", params: [1, 4, 4] } },

    // Arithmetic
    { label: "ModSum(4)", def: { path: "arithmetic/mod.circom", template: "ModSum", params: [4] } },
    { label: "ModSub(4)", def: { path: "arithmetic/mod.circom", template: "ModSub", params: [4] } },
    { label: "ModSumThree(4)", def: { path: "arithmetic/mod.circom", template: "ModSumThree", params: [4] } },
    { label: "ModSubThree(4)", def: { path: "arithmetic/mod.circom", template: "ModSubThree", params: [4] } },
    { label: "ModSumFour(4)", def: { path: "arithmetic/mod.circom", template: "ModSumFour", params: [4] } },
    { label: "ModProd(4)", def: { path: "arithmetic/mod.circom", template: "ModProd", params: [4] } },
    { label: "Split(4,4)", def: { path: "arithmetic/mod.circom", template: "Split", params: [4, 4] } },
    { label: "SplitThree(4,4,4)", def: { path: "arithmetic/mod.circom", template: "SplitThree", params: [4, 4, 4] } },
    { label: "CheckCarryToZero(4,4,3)", def: { path: "arithmetic/bigint.circom", template: "CheckCarryToZero", params: [4, 4, 3] } },
    { label: "LongToShortNoEndCarry(4,2)", def: { path: "arithmetic/bigint.circom", template: "LongToShortNoEndCarry", params: [4, 2] } },
    { label: "BigAdd(4,2)", def: { path: "arithmetic/bigint.circom", template: "BigAdd", params: [4, 2] } },
    { label: "BigSub(4,2)", def: { path: "arithmetic/bigint.circom", template: "BigSub", params: [4, 2] } },
    { label: "BigMult(4,2)", def: { path: "arithmetic/bigint.circom", template: "BigMult", params: [4, 2] } },
    { label: "BigLessThan(4,2)", def: { path: "arithmetic/bigint.circom", template: "BigLessThan", params: [4, 2] } },
    { label: "BigMod(4,2)", def: { path: "arithmetic/bigint.circom", template: "BigMod", params: [4, 2] } },
    { label: "BigSubModP(4,2)", def: { path: "arithmetic/bigint.circom", template: "BigSubModP", params: [4, 2] } },
    { label: "BigMultModP(4,2)", def: { path: "arithmetic/bigint.circom", template: "BigMultModP", params: [4, 2] } },
    { label: "BigModInv(4,2)", def: { path: "arithmetic/bigint.circom", template: "BigModInv", params: [4, 2] } },
    { label: "BigIsEqual(2)", def: { path: "arithmetic/bigint.circom", template: "BigIsEqual", params: [2] } },
    { label: "BigMultNoCarry(4,4,4,2,2)", def: { path: "arithmetic/bigint.circom", template: "BigMultNoCarry", params: [4, 4, 4, 2, 2] } },

    // Hash
    { label: "Ch_t(4)", def: { path: "hash/sha256/ch.circom", template: "Ch_t", params: [4] } },
    { label: "Maj_t(4)", def: { path: "hash/sha256/maj.circom", template: "Maj_t", params: [4] } },
    { label: "RotR(8,3)", def: { path: "hash/sha256/rotate.circom", template: "RotR", params: [8, 3] } },
    { label: "ShR(8,3)", def: { path: "hash/sha256/shift.circom", template: "ShR", params: [8, 3] } },
    { label: "Xor3(4)", def: { path: "hash/sha256/xor3.circom", template: "Xor3", params: [4] } },
    { label: "BinSum(4,2)", def: { path: "hash/sha256/binsum.circom", template: "BinSum", params: [4, 2] } },
    { label: "Sigma", def: { path: "hash/poseidon.circom", template: "Sigma" } },
    { label: "PoseidonEx(2,1)", def: { path: "hash/poseidon.circom", template: "PoseidonEx", params: [2, 1] } },
    { label: "Poseidon(2)", def: { path: "hash/poseidon.circom", template: "Poseidon", params: [2] } },
    { label: "HashLeftRight", def: { path: "hash/poseidon.circom", template: "HashLeftRight" } },
    { label: "MerkleTreeInclusionProof(2)", def: { path: "hash/merkle.circom", template: "MerkleTreeInclusionProof", params: [2] } },
    { label: "Ascon_Hash_256(1)", def: { path: "ascon/hash.circom", template: "Ascon_Hash_256", params: [1] } },

    // Curve
    { label: "BabyCheck", def: { path: "curve/babyjub.circom", template: "BabyCheck" } },
    { label: "BabyAdd", def: { path: "curve/babyjub.circom", template: "BabyAdd" } },
    { label: "BabyDbl", def: { path: "curve/babyjub.circom", template: "BabyDbl" } },
    { label: "BabyPointAdd", def: { path: "curve/babyjub.circom", template: "BabyPointAdd" } },
    { label: "BabyPointDouble", def: { path: "curve/babyjub.circom", template: "BabyPointDouble" } },
    { label: "BabySuborderCheck", def: { path: "curve/babyjub.circom", template: "BabySuborderCheck" } },
    { label: "BabySuborderAdd", def: { path: "curve/babyjub.circom", template: "BabySuborderAdd" } },
    { label: "Edwards2Montgomery", def: { path: "curve/montgomery.circom", template: "Edwards2Montgomery" } },
    { label: "Montgomery2Edwards", def: { path: "curve/montgomery.circom", template: "Montgomery2Edwards" } },
    { label: "MontgomeryAdd", def: { path: "curve/montgomery.circom", template: "MontgomeryAdd" } },
    { label: "MontgomeryDouble", def: { path: "curve/montgomery.circom", template: "MontgomeryDouble" } },
    { label: "BabyCompress", def: { path: "curve/compress.circom", template: "BabyCompress" } },
    { label: "BabyMultiCompress(2)", def: { path: "curve/compress.circom", template: "BabyMultiCompress", params: [2] } },
    { label: "EscalarMulAny(4)", def: { path: "curve/scalarmul.circom", template: "EscalarMulAny", params: [4] } },

    // Linalg
    { label: "VectorAdd(3)", def: { path: "linalg/vector.circom", template: "VectorAdd", params: [3] } },
    { label: "VectorSub(3)", def: { path: "linalg/vector.circom", template: "VectorSub", params: [3] } },
    { label: "ScalarVectorMul(3)", def: { path: "linalg/vector.circom", template: "ScalarVectorMul", params: [3] } },
    { label: "DotProduct(3)", def: { path: "linalg/vector.circom", template: "DotProduct", params: [3] } },
    { label: "VectorNormSquared(3)", def: { path: "linalg/vector.circom", template: "VectorNormSquared", params: [3] } },
    { label: "VectorIsEqual(3)", def: { path: "linalg/vector.circom", template: "VectorIsEqual", params: [3] } },
    { label: "HadamardProduct(3)", def: { path: "linalg/vector.circom", template: "HadamardProduct", params: [3] } },
    { label: "EuclideanDistanceSquared(3)", def: { path: "linalg/vector.circom", template: "EuclideanDistanceSquared", params: [3] } },
    { label: "WeightedSum(3,2)", def: { path: "linalg/vector.circom", template: "WeightedSum", params: [3, 2] } },
    { label: "VectorMean(2,2)", def: { path: "linalg/vector.circom", template: "VectorMean", params: [2, 2] } },
    { label: "MatrixAdd(2,2)", def: { path: "linalg/matrix.circom", template: "MatrixAdd", params: [2, 2] } },
    { label: "MatrixSub(2,2)", def: { path: "linalg/matrix.circom", template: "MatrixSub", params: [2, 2] } },
    { label: "ScalarMatrixMul(2,2)", def: { path: "linalg/matrix.circom", template: "ScalarMatrixMul", params: [2, 2] } },
    { label: "MatrixVectorMul(2,2)", def: { path: "linalg/matrix.circom", template: "MatrixVectorMul", params: [2, 2] } },
    { label: "MatrixMul(2,2,2)", def: { path: "linalg/matrix.circom", template: "MatrixMul", params: [2, 2, 2] } },
    { label: "MatrixTranspose(2,3)", def: { path: "linalg/matrix.circom", template: "MatrixTranspose", params: [2, 3] } },
    { label: "MatrixIsEqual(2,2)", def: { path: "linalg/matrix.circom", template: "MatrixIsEqual", params: [2, 2] } },
    { label: "CosineSimilarityCheck(3,8)", def: { path: "linalg/similarity.circom", template: "CosineSimilarityCheck", params: [3, 8] } },
    { label: "NearestNeighborCheck(2,3,8)", def: { path: "linalg/similarity.circom", template: "NearestNeighborCheck", params: [2, 3, 8] } },
    { label: "OrthogonalCheck(2,8,4)", def: { path: "linalg/orthogonal.circom", template: "OrthogonalCheck", params: [2, 8, 4] } },
    { label: "OrthogonalTransform(2,8,4)", def: { path: "linalg/orthogonal.circom", template: "OrthogonalTransform", params: [2, 8, 4] } },
    { label: "ReLU(4)", def: { path: "linalg/activation.circom", template: "ReLU", params: [4] } },
    { label: "ReLUVector(2,4)", def: { path: "linalg/activation.circom", template: "ReLUVector", params: [2, 4] } },
    { label: "Max(3,4)", def: { path: "linalg/selection.circom", template: "Max", params: [3, 4] } },
    { label: "ArgMax(3,4)", def: { path: "linalg/selection.circom", template: "ArgMax", params: [3, 4] } },
    { label: "InRange(4)", def: { path: "linalg/fixedpoint.circom", template: "InRange", params: [4] } },
    { label: "ApproxEqual(4)", def: { path: "linalg/fixedpoint.circom", template: "ApproxEqual", params: [4] } },
    { label: "FixedPointMul(4)", def: { path: "linalg/fixedpoint.circom", template: "FixedPointMul", params: [4] } },
    { label: "FixedPointDotProduct(3,4)", def: { path: "linalg/fixedpoint.circom", template: "FixedPointDotProduct", params: [3, 4] } },
    { label: "FixedPointMatrixVectorMul(2,2,4)", def: { path: "linalg/fixedpoint.circom", template: "FixedPointMatrixVectorMul", params: [2, 2, 4] } },
    { label: "FixedPointDiv(4,8)", def: { path: "linalg/fixedpoint.circom", template: "FixedPointDiv", params: [4, 8] } },

    // Collections
    { label: "CalculateTotal(4)", def: { path: "collections/aggregate.circom", template: "CalculateTotal", params: [4] } },
    { label: "CalculateProduct(4)", def: { path: "collections/aggregate.circom", template: "CalculateProduct", params: [4] } },
    { label: "IndexSelector(3,2,1)", def: { path: "collections/selector.circom", template: "IndexSelector", params: [3, 2, 1] } },
    { label: "Ordered(4,4,1)", def: { path: "collections/ordered.circom", template: "Ordered", params: [4, 4, 1] } },
    { label: "Contains(4,2)", def: { path: "collections/contains.circom", template: "Contains", params: [4, 2] } },
    { label: "Contains_Points(3,2)", def: { path: "collections/contains.circom", template: "Contains_Points", params: [3, 2] } },

    // Crypto protocols
    { label: "ElGamalBlinding", def: { path: "elgamal/helpers.circom", template: "ElGamalBlinding" } },
    { label: "ElGamalMessageCheck", def: { path: "elgamal/helpers.circom", template: "ElGamalMessageCheck" } },
    { label: "ElGamalShare", def: { path: "elgamal/elgamal.circom", template: "ElGamalShare" } },
    { label: "ElGamalEncrypt", def: { path: "elgamal/elgamal.circom", template: "ElGamalEncrypt" } },
    { label: "ElGamalDecrypt", def: { path: "elgamal/elgamal.circom", template: "ElGamalDecrypt" } },
    { label: "SchnorrBlinding", def: { path: "schnorr/blinding.circom", template: "SchnorrBlinding" } },
    // RSAPKCSv15Pad is hardcoded for 1024-bit RSA: n=32, k=32
    { label: "RSAPKCSv15Pad(32,32)", def: { path: "rsa/pad.circom", template: "RSAPKCSv15Pad", params: [32, 32] } },
    { label: "RSAMessageBlind(4,2,3)", def: { path: "rsa/blind.circom", template: "RSAMessageBlind", params: [4, 2, 3] } },

    // Search / Bridge
    { label: "VectorCommit(8,4)", def: { path: "search/commit.circom", template: "VectorCommit", params: [8, 4] } },
    { label: "PolyUHF(4)", def: { path: "bridge/uhf.circom", template: "PolyUHF", params: [4] } },
];

// --- Known over-allocations (not security bugs) ---
// These signals are allocated in arrays but never used due to off-by-one in array sizing.
// Pattern: carry/borrow arrays sized [k] or [2k] when only [k-1] or [2k-1] elements are needed.
// The unused final element has no prover input and doesn't affect soundness.
const KNOWN_OVER_ALLOCATIONS: Record<string, RegExp[]> = {
    // LongToShortNoEndCarry: signal carry[k] but only carry[0..k-2] used
    "LongToShortNoEndCarry(4,2)": [/\.carry\[1\]$/],
    // BigSub: signal borrow[k] but only borrow[0..k-2] used
    "BigSub(4,2)": [/\.borrow\[1\]$/],
    // BigMult: signal carry[2*k] but only carry[0..2k-2] used
    "BigMult(4,2)": [/\.carry\[3\]$/],
    // BigMultModP contains BigMult, inherits its over-allocation
    "BigMultModP(4,2)": [/BigMult.*\.carry\[3\]$/],
    // BigModInv contains BigMultModP which contains BigMult
    "BigModInv(4,2)": [/BigMult.*\.carry\[3\]$/],
    // RSAMessageBlind contains BigMultModP which contains BigMult
    "RSAMessageBlind(4,2,3)": [/BigMult.*\.carry\[3\]$/],
};

// --- Shared compilation cache ---

type AnalysisResult = { details: R1CSDetails; symbols: SymbolMap };
const cache = new Map<string, AnalysisResult>();

async function analyzeCircuit(entry: { label: string; def: CircuitDef }): Promise<AnalysisResult> {
    const cached = cache.get(entry.label);
    if (cached) return cached;
    const result = await compile_and_analyze(entry.def);
    cache.set(entry.label, result);
    return result;
}

// --- Tests ---

describe("@slow Under-constraint detection", function () {
    this.timeout(0);

    describe("Signal coverage", function () {
        for (const entry of circuits) {
            it(`${entry.label}: every non-input signal appears in >= 1 constraint`, async function () {
                const { details, symbols } = await analyzeCircuit(entry);
                let unconstrained = findUnconstrainedSignals(details, symbols);

                // Filter known over-allocations (not security bugs — see KNOWN_OVER_ALLOCATIONS)
                const patterns = KNOWN_OVER_ALLOCATIONS[entry.label];
                if (patterns) {
                    unconstrained = unconstrained.filter(
                        sig => !patterns.some(pat => pat.test(sig))
                    );
                }

                assert.deepEqual(
                    unconstrained,
                    [],
                    `Unconstrained signals found: ${unconstrained.join(", ")}`
                );
            });
        }
    });

    describe("Degree of freedom", function () {
        for (const entry of circuits) {
            it(`${entry.label}: nConstraints >= nNonInputSignals`, async function () {
                const { details } = await analyzeCircuit(entry);
                const { nConstraints, nNonInput, dof } = computeDegreesOfFreedom(details);
                assert(
                    dof <= 0,
                    `Under-determined: ${nNonInput} non-input signals but only ${nConstraints} constraints (DoF = ${dof})`
                );
            });
        }
    });
});
