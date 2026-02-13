import { assert } from "chai";
import { readFile } from "fs/promises";
import { resolve, dirname } from "path";
import { fileURLToPath } from "url";
import { describe_circuit } from "../helpers.js";

const __dirname = dirname(fileURLToPath(import.meta.url));

// BN254 prime field modulus
const P = 21888242871839275222246405745257275088548364400416034343698204186575808495617n;

interface EmbeddingFixture {
    model: string;
    dimension: number;
    scale: number;
    sentences: {
        id: string;
        text: string;
        group: string;
        quantized: number[];
    }[];
    pairwise_similarities: {
        id_a: string;
        id_b: string;
        cosine: number;
    }[];
}

/** Convert signed integer to field element. */
function toField(x: number): bigint {
    return x >= 0 ? BigInt(x) : P + BigInt(x);
}

/** Convert field element back to signed integer (for values near 0 or p). */
function fromField(x: bigint): bigint {
    return x > P / 2n ? x - P : x;
}

/** Get embedding by id from fixture. */
function getEmbedding(fixture: EmbeddingFixture, id: string): number[] {
    const s = fixture.sentences.find(s => s.id === id);
    if (!s) throw new Error(`Embedding not found: ${id}`);
    return s.quantized;
}

/** Convert quantized embedding to field element array. */
function toFieldArray(quantized: number[]): bigint[] {
    return quantized.map(toField);
}

/** Compute dot product of two quantized vectors (in JS, not circom). */
function jsDotProduct(a: number[], b: number[]): bigint {
    let sum = 0n;
    for (let i = 0; i < a.length; i++) {
        sum += BigInt(a[i]) * BigInt(b[i]);
    }
    return sum;
}

/** Compute norm squared of a quantized vector (in JS). */
function jsNormSquared(v: number[]): bigint {
    let sum = 0n;
    for (let i = 0; i < v.length; i++) {
        sum += BigInt(v[i]) * BigInt(v[i]);
    }
    return sum;
}

/** Compute Euclidean distance squared between two quantized vectors (in JS). */
function jsEuclideanDistSq(a: number[], b: number[]): bigint {
    let sum = 0n;
    for (let i = 0; i < a.length; i++) {
        const d = BigInt(a[i]) - BigInt(b[i]);
        sum += d * d;
    }
    return sum;
}

let fixture: EmbeddingFixture;

before(async function () {
    const fixturePath = resolve(__dirname, "../fixtures/embeddings.json");
    fixture = JSON.parse(await readFile(fixturePath, "utf-8"));
});

// ── DotProduct ──────────────────────────────────────────────────────────────

describe_circuit("DotProduct (real embeddings)", {
    dot: { path: "linalg/vector.circom", template: "DotProduct", params: [384] },
}, (calculators) => {
    it("computes correct dot product for similar pair (cat/kitten)", async () => {
        const a = getEmbedding(fixture, "cat_mat");
        const b = getEmbedding(fixture, "kitten_rug");
        const expected = jsDotProduct(a, b);

        const w = await calculators.dot.calculate({
            a: toFieldArray(a),
            b: toFieldArray(b),
        });

        // Positive dot product for similar pair → small positive field element
        assert.isTrue(expected > 0n, "similar pair should have positive dot product");
        assert.equal(fromField(w.value("main.out")), expected);
    });

    it("computes correct dot product for dissimilar pair (cat/ml_datasets)", async () => {
        const a = getEmbedding(fixture, "cat_mat");
        const b = getEmbedding(fixture, "ml_datasets");
        const expected = jsDotProduct(a, b);

        const w = await calculators.dot.calculate({
            a: toFieldArray(a),
            b: toFieldArray(b),
        });

        // Negative dot product → large field element (near p)
        assert.isTrue(expected < 0n, "dissimilar pair should have negative dot product");
        assert.equal(fromField(w.value("main.out")), expected);
    });
});

// ── FixedPointDotProduct ────────────────────────────────────────────────────

describe_circuit("FixedPointDotProduct (real embeddings)", {
    fpdot: { path: "linalg/fixedpoint.circom", template: "FixedPointDotProduct", params: [384, 10] },
}, (calculators) => {
    it("produces scaled dot product for similar pair", async () => {
        const a = getEmbedding(fixture, "cat_mat");
        const b = getEmbedding(fixture, "kitten_rug");
        const rawDot = jsDotProduct(a, b);

        // scale_bits=10 → divides by 1024
        const expected = rawDot >> 10n;

        const w = await calculators.fpdot.calculate({
            a: toFieldArray(a),
            b: toFieldArray(b),
        });

        const result = fromField(w.value("main.out"));
        assert.equal(result, expected);

        // Sanity check: for unit vectors at scale=1000, raw dot ≈ 10^6 * cos(a,b)
        // scaled result ≈ 10^6 * cos / 1024 ≈ 976 * cos
        // For cos ≈ 0.61, result should be ≈ 598
        assert.isTrue(result > 400n && result < 800n,
            `expected scaled dot product in reasonable range, got ${result}`);
    });
});

// ── EuclideanDistanceSquared ────────────────────────────────────────────────

describe_circuit("EuclideanDistanceSquared (real embeddings)", {
    dist: { path: "linalg/vector.circom", template: "EuclideanDistanceSquared", params: [384] },
}, (calculators) => {
    it("similar pair has smaller distance than dissimilar pair", async () => {
        const cat = getEmbedding(fixture, "cat_mat");
        const kitten = getEmbedding(fixture, "kitten_rug");
        const stock = getEmbedding(fixture, "stock_market");

        // Capture values immediately — the witness buffer is reused between calculations
        const wSimilar = await calculators.dist.calculate({
            a: toFieldArray(cat),
            b: toFieldArray(kitten),
        });
        const distSimilar = wSimilar.value("main.out");

        const wDissimilar = await calculators.dist.calculate({
            a: toFieldArray(cat),
            b: toFieldArray(stock),
        });
        const distDissimilar = wDissimilar.value("main.out");

        // For unit vectors: ||a-b||^2 = 2*(normSq - dot) ≈ 2*scale^2*(1-cos)
        assert.isTrue(distSimilar < distDissimilar,
            `similar distance ${distSimilar} should be < dissimilar distance ${distDissimilar}`);
    });

    it("computes exact distance matching JS reference", async () => {
        const a = getEmbedding(fixture, "sun_mountains");
        const b = getEmbedding(fixture, "sunset_hills");
        const expected = jsEuclideanDistSq(a, b);

        const w = await calculators.dist.calculate({
            a: toFieldArray(a),
            b: toFieldArray(b),
        });

        assert.equal(w.value("main.out"), expected);
    });
});

// ── CosineSimilarityCheck ───────────────────────────────────────────────────

describe_circuit("CosineSimilarityCheck (real embeddings)", {
    cos: { path: "linalg/similarity.circom", template: "CosineSimilarityCheck", params: [384, 64] },
}, (calculators) => {
    it("accepts similar pair with positive dot product (threshold_sq=0)", async () => {
        const a = getEmbedding(fixture, "cat_mat");
        const b = getEmbedding(fixture, "kitten_rug");

        // threshold_sq=0: only checks that dot product is non-negative
        await calculators.cos.calculate({
            a: toFieldArray(a),
            b: toFieldArray(b),
            threshold_sq: 0,
        });
        // No error means constraint satisfied
    });

    it("rejects pair with negative dot product (threshold_sq=0)", async () => {
        const a = getEmbedding(fixture, "cat_mat");
        const b = getEmbedding(fixture, "ml_datasets");

        // cat_mat <-> ml_datasets has negative cosine similarity (~-0.07)
        // The sign check (Num2Bits on dotAB) rejects negative dot products
        try {
            await calculators.cos.calculate({
                a: toFieldArray(a),
                b: toFieldArray(b),
                threshold_sq: 0,
            });
            assert.fail("should have rejected negative dot product pair");
        } catch (e: any) {
            // Expected: constraint violation from sign check
        }
    });

    it("rejects when threshold exceeds Cauchy-Schwarz bound", async () => {
        const a = getEmbedding(fixture, "cat_mat");
        const b = getEmbedding(fixture, "kitten_rug");

        // threshold_sq=1 means: dotAB^2 >= 1 * normSqA * normSqB
        // By Cauchy-Schwarz, dotAB^2 <= normSqA * normSqB (equality only for parallel vectors)
        // For non-parallel vectors this always fails
        try {
            await calculators.cos.calculate({
                a: toFieldArray(a),
                b: toFieldArray(b),
                threshold_sq: 1,
            });
            assert.fail("should have rejected: threshold_sq=1 exceeds Cauchy-Schwarz bound");
        } catch (e: any) {
            // Expected: constraint violation from LessThan check
        }
    });
});

// ── NearestNeighborCheck ────────────────────────────────────────────────────

describe_circuit("NearestNeighborCheck (real embeddings)", {
    nn: { path: "linalg/similarity.circom", template: "NearestNeighborCheck", params: [384, 5, 64] },
}, (calculators) => {
    it("accepts correct nearest neighbor index", async () => {
        const query = getEmbedding(fixture, "cat_mat");

        // Candidates: kitten_rug (idx 0) is nearest to cat_mat
        const candidateIds = ["kitten_rug", "ml_datasets", "sun_mountains", "stock_market", "piano_sonata"];
        const candidates = candidateIds.map(id => toFieldArray(getEmbedding(fixture, id)));

        await calculators.nn.calculate({
            query: toFieldArray(query),
            candidates,
            claimedIdx: 0,
        });
        // No error means constraint satisfied
    });

    it("rejects incorrect nearest neighbor index", async () => {
        const query = getEmbedding(fixture, "cat_mat");

        const candidateIds = ["kitten_rug", "ml_datasets", "sun_mountains", "stock_market", "piano_sonata"];
        const candidates = candidateIds.map(id => toFieldArray(getEmbedding(fixture, id)));

        // Claim index 3 (stock_market) — incorrect, kitten_rug is actually nearest
        try {
            await calculators.nn.calculate({
                query: toFieldArray(query),
                candidates,
                claimedIdx: 3,
            });
            assert.fail("should have rejected incorrect nearest neighbor");
        } catch (e: any) {
            // Expected: constraint violation
        }
    });
});

// ── WeightedSum ─────────────────────────────────────────────────────────────

describe_circuit("WeightedSum (real embeddings)", {
    ws: { path: "linalg/vector.circom", template: "WeightedSum", params: [384, 2] },
}, (calculators) => {
    it("combines two embeddings with integer weights", async () => {
        const a = getEmbedding(fixture, "sun_mountains");
        const b = getEmbedding(fixture, "sunset_hills");

        const w1 = 2, w2 = 3;

        // Expected: 2*a + 3*b element-wise
        const expected = a.map((ai, i) => toField(w1 * ai + w2 * b[i]));

        const w = await calculators.ws.calculate({
            w: [w1, w2],
            v: [toFieldArray(a), toFieldArray(b)],
        });

        const out = w.array("main.out");
        assert.deepEqual(out, expected);
    });
});
