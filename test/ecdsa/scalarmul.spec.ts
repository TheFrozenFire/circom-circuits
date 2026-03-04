import { assert } from "chai";
import { describe_circuit } from "../helpers.js";
import { secp256k1 } from "@noble/curves/secp256k1.js";

const Point = secp256k1.Point;
const n = 64;
const k = 4;

function toLimbs64(val: bigint): bigint[] {
    const mask = (1n << 64n) - 1n;
    return Array.from({ length: 4 }, (_, i) => (val >> (BigInt(i) * 64n)) & mask);
}

function fromLimbs64(limbs: bigint[]): bigint {
    let result = 0n;
    for (let i = limbs.length - 1; i >= 0; i--) {
        result = (result << 64n) + limbs[i];
    }
    return result;
}

describe_circuit("Secp256k1ScalarMult", {
    mul: { path: "ecdsa/scalarmul.circom", template: "Secp256k1ScalarMult", params: [n, k] },
}, (calculators) => {

    it("computes 5 * G", async () => {
        const G = Point.BASE.toAffine();
        const expected = Point.BASE.multiply(5n).toAffine();

        const w = await calculators.mul.calculate({
            scalar: toLimbs64(5n),
            point: [toLimbs64(G.x), toLimbs64(G.y)],
        });

        const outX = fromLimbs64(w.array("main.out[0]"));
        const outY = fromLimbs64(w.array("main.out[1]"));
        assert.equal(outX, expected.x);
        assert.equal(outY, expected.y);
    });

    it("computes 256-bit scalar * G", async () => {
        // A known private key
        const scalar = 0xdeadbeefcafebabedeadbeefcafebabedeadbeefcafebabedeadbeefcafebaben;
        const G = Point.BASE.toAffine();
        const expected = Point.BASE.multiply(scalar).toAffine();

        const w = await calculators.mul.calculate({
            scalar: toLimbs64(scalar),
            point: [toLimbs64(G.x), toLimbs64(G.y)],
        });

        const outX = fromLimbs64(w.array("main.out[0]"));
        const outY = fromLimbs64(w.array("main.out[1]"));
        assert.equal(outX, expected.x);
        assert.equal(outY, expected.y);
    });

    it("computes scalar * non-generator point", async () => {
        const scalar = 42n;
        const P = Point.BASE.multiply(7n).toAffine(); // 7G as base
        const expected = Point.BASE.multiply(7n * 42n).toAffine();

        const w = await calculators.mul.calculate({
            scalar: toLimbs64(scalar),
            point: [toLimbs64(P.x), toLimbs64(P.y)],
        });

        const outX = fromLimbs64(w.array("main.out[0]"));
        const outY = fromLimbs64(w.array("main.out[1]"));
        assert.equal(outX, expected.x);
        assert.equal(outY, expected.y);
    });
});
