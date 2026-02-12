import { assert } from "chai";
import { describe_circuit } from "../helpers.js";

// BN128 field modulus
const p = 21888242871839275222246405745257275088548364400416034343698204186575808495617n;

const BABYJUB_A = 168700n;
const BABYJUB_D = 168696n;
const SUBORDER = 2736030358979909402780800718157159386076813972158567259200215660948447373041n;
const BASE8_X = 5299619240641551281634865583518297030282874472190772894086521144482721001553n;
const BASE8_Y = 16950150798460657717958625567821834550301663161624707787222815936182638968203n;

function mod(a: bigint): bigint {
    return ((a % p) + p) % p;
}

function modPow(base: bigint, exp: bigint): bigint {
    let result = 1n;
    base = mod(base);
    while (exp > 0n) {
        if (exp & 1n) result = mod(result * base);
        exp >>= 1n;
        base = mod(base * base);
    }
    return result;
}

function modInv(a: bigint): bigint {
    return modPow(a, p - 2n);
}

function babyAdd(x1: bigint, y1: bigint, x2: bigint, y2: bigint): [bigint, bigint] {
    const x1x2 = mod(x1 * x2);
    const y1y2 = mod(y1 * y2);
    const x1y2 = mod(x1 * y2);
    const y1x2 = mod(y1 * x2);
    const dx1x2y1y2 = mod(BABYJUB_D * mod(x1x2 * y1y2));

    const xnum = mod(x1y2 + y1x2);
    const xden = mod(1n + dx1x2y1y2);
    const xout = mod(xnum * modInv(xden));

    const ynum = mod(y1y2 + p - mod(BABYJUB_A * x1x2));
    const yden = mod(1n + p - dx1x2y1y2);
    const yout = mod(ynum * modInv(yden));

    return [xout, yout];
}

// Precompute 2·BASE8
const [DBL_X, DBL_Y] = babyAdd(BASE8_X, BASE8_Y, BASE8_X, BASE8_Y);

describe_circuit("BabyCheck", {
    check: { path: "curve/babyjub.circom", template: "BabyCheck" },
}, (calculators) => {
    it("accepts a valid point (BASE8)", async () => {
        await calculators.check.calculate({ x: BASE8_X, y: BASE8_Y });
    });

    it("accepts the identity point", async () => {
        await calculators.check.calculate({ x: 0, y: 1 });
    });

    it("rejects an invalid point", async () => {
        try {
            await calculators.check.calculate({ x: 1, y: 2 });
            assert.fail("should have thrown");
        } catch (e: any) {
            assert.notEqual(e.message, "should have thrown");
        }
    });
});

describe_circuit("BabyAdd", {
    add: { path: "curve/babyjub.circom", template: "BabyAdd" },
}, (calculators) => {
    it("P + identity = P", async () => {
        const w = await calculators.add.calculate({
            x1: BASE8_X, y1: BASE8_Y, x2: 0, y2: 1,
        });
        assert.equal(w.value("main.xout"), BASE8_X);
        assert.equal(w.value("main.yout"), BASE8_Y);
    });

    it("identity + P = P", async () => {
        const w = await calculators.add.calculate({
            x1: 0, y1: 1, x2: BASE8_X, y2: BASE8_Y,
        });
        assert.equal(w.value("main.xout"), BASE8_X);
        assert.equal(w.value("main.yout"), BASE8_Y);
    });

    it("computes known doubling", async () => {
        const w = await calculators.add.calculate({
            x1: BASE8_X, y1: BASE8_Y, x2: BASE8_X, y2: BASE8_Y,
        });
        assert.equal(w.value("main.xout"), DBL_X);
        assert.equal(w.value("main.yout"), DBL_Y);
    });

    it("is commutative", async () => {
        const w1 = await calculators.add.calculate({
            x1: BASE8_X, y1: BASE8_Y, x2: DBL_X, y2: DBL_Y,
        });
        const w2 = await calculators.add.calculate({
            x1: DBL_X, y1: DBL_Y, x2: BASE8_X, y2: BASE8_Y,
        });
        assert.equal(w1.value("main.xout"), w2.value("main.xout"));
        assert.equal(w1.value("main.yout"), w2.value("main.yout"));
    });
});

describe_circuit("BabyDbl", {
    dbl: { path: "curve/babyjub.circom", template: "BabyDbl" },
}, (calculators) => {
    it("2P via doubling matches addition", async () => {
        const w = await calculators.dbl.calculate({ x: BASE8_X, y: BASE8_Y });
        assert.equal(w.value("main.xout"), DBL_X);
        assert.equal(w.value("main.yout"), DBL_Y);
    });

    it("doubles the identity to identity", async () => {
        const w = await calculators.dbl.calculate({ x: 0, y: 1 });
        assert.equal(w.value("main.xout"), 0n);
        assert.equal(w.value("main.yout"), 1n);
    });
});

describe_circuit("BabyPointAdd", {
    pointAdd: { path: "curve/babyjub.circom", template: "BabyPointAdd" },
}, (calculators) => {
    it("adds two points via array interface", async () => {
        const w = await calculators.pointAdd.calculate({
            in: [[BASE8_X, BASE8_Y], [0, 1]],
        });
        const out = w.array("main.out");
        assert.equal(out[0], BASE8_X);
        assert.equal(out[1], BASE8_Y);
    });
});

describe_circuit("BabyPointDouble", {
    pointDbl: { path: "curve/babyjub.circom", template: "BabyPointDouble" },
}, (calculators) => {
    it("doubles a point via array interface", async () => {
        const w = await calculators.pointDbl.calculate({
            in: [BASE8_X, BASE8_Y],
        });
        const out = w.array("main.out");
        assert.equal(out[0], DBL_X);
        assert.equal(out[1], DBL_Y);
    });
});

describe_circuit("BabySuborderCheck", {
    check: { path: "curve/babyjub.circom", template: "BabySuborderCheck" },
}, (calculators) => {
    it("accepts zero", async () => {
        await calculators.check.calculate({ in: 0 });
    });

    it("accepts suborder - 1", async () => {
        await calculators.check.calculate({ in: SUBORDER - 1n });
    });

    it("rejects suborder", async () => {
        try {
            await calculators.check.calculate({ in: SUBORDER });
            assert.fail("should have thrown");
        } catch (e: any) {
            assert.notEqual(e.message, "should have thrown");
        }
    });

    it("rejects suborder + 1", async () => {
        try {
            await calculators.check.calculate({ in: SUBORDER + 1n });
            assert.fail("should have thrown");
        } catch (e: any) {
            assert.notEqual(e.message, "should have thrown");
        }
    });
});

describe_circuit("BabySuborderAdd", {
    add: { path: "curve/babyjub.circom", template: "BabySuborderAdd" },
}, (calculators) => {
    it("adds two small values", async () => {
        const w = await calculators.add.calculate({ a: 3, b: 5 });
        assert.equal(w.value("main.out"), 8n);
    });

    it("adds with zero", async () => {
        const w = await calculators.add.calculate({ a: 42, b: 0 });
        assert.equal(w.value("main.out"), 42n);
    });

    it("wraps around suborder", async () => {
        const a = SUBORDER - 3n;
        const b = 10n;
        const w = await calculators.add.calculate({ a, b });
        assert.equal(w.value("main.out"), 7n);
    });

    it("adds (suborder - 1) + 1 = 0", async () => {
        const w = await calculators.add.calculate({ a: SUBORDER - 1n, b: 1n });
        assert.equal(w.value("main.out"), 0n);
    });

    it("adds (suborder - 1) + (suborder - 1) = suborder - 2", async () => {
        const a = SUBORDER - 1n;
        const w = await calculators.add.calculate({ a, b: a });
        assert.equal(w.value("main.out"), SUBORDER - 2n);
    });
});
