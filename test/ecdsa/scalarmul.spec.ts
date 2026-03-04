import { assert } from "chai";
import { describe_circuit } from "../helpers.js";
import { secp256k1 } from "@noble/curves/secp256k1.js";

const Point = secp256k1.Point;
const n = 32;
const k = 8;

function toLimbs32(val: bigint): bigint[] {
    const mask = (1n << 32n) - 1n;
    return Array.from({ length: 8 }, (_, i) => (val >> (BigInt(i) * 32n)) & mask);
}

function fromLimbs32(limbs: bigint[]): bigint {
    let result = 0n;
    for (let i = limbs.length - 1; i >= 0; i--) {
        result = (result << 32n) + limbs[i];
    }
    return result;
}

describe_circuit("Secp256k1GLVScalarMult", {
    glv: { path: "ecdsa/glv.circom", template: "Secp256k1GLVScalarMult", params: [n, k] },
}, (calculators) => {

    it("computes 5 * G (small scalar)", async () => {
        const G = Point.BASE.toAffine();
        const expected = Point.BASE.multiply(5n).toAffine();

        const w = await calculators.glv.calculate({
            scalar: toLimbs32(5n),
            point: [toLimbs32(G.x), toLimbs32(G.y)],
        });

        const outX = fromLimbs32(w.array("main.out[0]"));
        const outY = fromLimbs32(w.array("main.out[1]"));
        assert.equal(outX, expected.x);
        assert.equal(outY, expected.y);
    });

    it("computes 256-bit scalar * G", async () => {
        const scalar = 0xdeadbeefcafebabedeadbeefcafebabedeadbeefcafebabedeadbeefcafebaben;
        const G = Point.BASE.toAffine();
        const expected = Point.BASE.multiply(scalar).toAffine();

        const w = await calculators.glv.calculate({
            scalar: toLimbs32(scalar),
            point: [toLimbs32(G.x), toLimbs32(G.y)],
        });

        const outX = fromLimbs32(w.array("main.out[0]"));
        const outY = fromLimbs32(w.array("main.out[1]"));
        assert.equal(outX, expected.x);
        assert.equal(outY, expected.y);
    });

    it("computes scalar * non-generator point", async () => {
        const scalar = 42n;
        const P = Point.BASE.multiply(7n).toAffine();
        const expected = Point.BASE.multiply(7n * 42n).toAffine();

        const w = await calculators.glv.calculate({
            scalar: toLimbs32(scalar),
            point: [toLimbs32(P.x), toLimbs32(P.y)],
        });

        const outX = fromLimbs32(w.array("main.out[0]"));
        const outY = fromLimbs32(w.array("main.out[1]"));
        assert.equal(outX, expected.x);
        assert.equal(outY, expected.y);
    });

    it("computes scalar = 1 (edge case: 128 leading zeros)", async () => {
        const G = Point.BASE.toAffine();
        const expected = G; // 1 * G = G

        const w = await calculators.glv.calculate({
            scalar: toLimbs32(1n),
            point: [toLimbs32(G.x), toLimbs32(G.y)],
        });

        const outX = fromLimbs32(w.array("main.out[0]"));
        const outY = fromLimbs32(w.array("main.out[1]"));
        assert.equal(outX, expected.x);
        assert.equal(outY, expected.y);
    });

    it("handles scalar where k2 is negative", async () => {
        // Choose scalar that produces negative k2 in GLV decomposition
        // The scalar 0xadbeefcafebabe... from our verification test had k2_neg=1
        const scalar = 0xadbeefcafebabe1234567890abcdf01a2d7ea338546b83b84092ac9f3dd158a1n;
        const G = Point.BASE.toAffine();
        const expected = Point.BASE.multiply(scalar).toAffine();

        const w = await calculators.glv.calculate({
            scalar: toLimbs32(scalar),
            point: [toLimbs32(G.x), toLimbs32(G.y)],
        });

        const outX = fromLimbs32(w.array("main.out[0]"));
        const outY = fromLimbs32(w.array("main.out[1]"));
        assert.equal(outX, expected.x);
        assert.equal(outY, expected.y);
    });
});

describe_circuit("Secp256k1ScalarMult", {
    mul: { path: "ecdsa/scalarmul.circom", template: "Secp256k1ScalarMult", params: [n, k] },
}, (calculators) => {

    it("computes 5 * G", async () => {
        const G = Point.BASE.toAffine();
        const expected = Point.BASE.multiply(5n).toAffine();

        const w = await calculators.mul.calculate({
            scalar: toLimbs32(5n),
            point: [toLimbs32(G.x), toLimbs32(G.y)],
        });

        const outX = fromLimbs32(w.array("main.out[0]"));
        const outY = fromLimbs32(w.array("main.out[1]"));
        assert.equal(outX, expected.x);
        assert.equal(outY, expected.y);
    });

    it("computes 256-bit scalar * G", async () => {
        // A known private key
        const scalar = 0xdeadbeefcafebabedeadbeefcafebabedeadbeefcafebabedeadbeefcafebaben;
        const G = Point.BASE.toAffine();
        const expected = Point.BASE.multiply(scalar).toAffine();

        const w = await calculators.mul.calculate({
            scalar: toLimbs32(scalar),
            point: [toLimbs32(G.x), toLimbs32(G.y)],
        });

        const outX = fromLimbs32(w.array("main.out[0]"));
        const outY = fromLimbs32(w.array("main.out[1]"));
        assert.equal(outX, expected.x);
        assert.equal(outY, expected.y);
    });

    it("computes scalar * non-generator point", async () => {
        const scalar = 42n;
        const P = Point.BASE.multiply(7n).toAffine(); // 7G as base
        const expected = Point.BASE.multiply(7n * 42n).toAffine();

        const w = await calculators.mul.calculate({
            scalar: toLimbs32(scalar),
            point: [toLimbs32(P.x), toLimbs32(P.y)],
        });

        const outX = fromLimbs32(w.array("main.out[0]"));
        const outY = fromLimbs32(w.array("main.out[1]"));
        assert.equal(outX, expected.x);
        assert.equal(outY, expected.y);
    });
});
