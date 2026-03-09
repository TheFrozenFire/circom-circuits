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

function readLimbs(w: any, prefix: string): bigint {
    let val = 0n;
    for (let i = 0; i < 8; i++) {
        val += w.value(`${prefix}[${i}]`) << (BigInt(i) * 32n);
    }
    return val;
}

describe_circuit("Secp256k1EisensteinScalarMult", {
    eisenstein: {
        path: "ecdsa/eisenstein_glv.circom",
        template: "Secp256k1EisensteinScalarMult",
        params: [n, k],
    },
}, (calculators) => {

    it("computes [5]*G correctly", async function () {
        this.timeout(0);
        const scalar = 5n;
        const P = Point.BASE.toAffine();
        const Q = Point.BASE.multiply(scalar).toAffine();

        const w = await calculators.eisenstein.calculate({
            scalar: toLimbs32(scalar),
            point: [toLimbs32(P.x), toLimbs32(P.y)],
            hint: [toLimbs32(Q.x), toLimbs32(Q.y)],
        });

        assert.equal(readLimbs(w, "main.out[0]"), Q.x, "x mismatch");
        assert.equal(readLimbs(w, "main.out[1]"), Q.y, "y mismatch");
    });

    it("computes [large_scalar]*G correctly", async function () {
        this.timeout(0);
        const scalar = 0xdeadbeefcafebabedeadbeefcafebabedeadbeefcafebabedeadbeefcafebaben;
        const P = Point.BASE.toAffine();
        const Q = Point.BASE.multiply(scalar).toAffine();

        const w = await calculators.eisenstein.calculate({
            scalar: toLimbs32(scalar),
            point: [toLimbs32(P.x), toLimbs32(P.y)],
            hint: [toLimbs32(Q.x), toLimbs32(Q.y)],
        });

        assert.equal(readLimbs(w, "main.out[0]"), Q.x, "x mismatch");
    });

    it("computes scalar * non-generator point", async function () {
        this.timeout(0);
        const scalar = 42n;
        const basePoint = Point.BASE.multiply(7n);
        const P = basePoint.toAffine();
        const Q = basePoint.multiply(scalar).toAffine();

        const w = await calculators.eisenstein.calculate({
            scalar: toLimbs32(scalar),
            point: [toLimbs32(P.x), toLimbs32(P.y)],
            hint: [toLimbs32(Q.x), toLimbs32(Q.y)],
        });

        assert.equal(readLimbs(w, "main.out[0]"), Q.x, "x mismatch");
    });

    it("computes [42]*G correctly", async function () {
        this.timeout(0);
        const scalar = 42n;
        const P = Point.BASE.toAffine();
        const Q = Point.BASE.multiply(scalar).toAffine();

        const w = await calculators.eisenstein.calculate({
            scalar: toLimbs32(scalar),
            point: [toLimbs32(P.x), toLimbs32(P.y)],
            hint: [toLimbs32(Q.x), toLimbs32(Q.y)],
        });

        assert.equal(readLimbs(w, "main.out[0]"), Q.x, "x mismatch");
    });

    it("computes [5]*(7G) correctly", async function () {
        this.timeout(0);
        const scalar = 5n;
        const basePoint = Point.BASE.multiply(7n);
        const P = basePoint.toAffine();
        const Q = basePoint.multiply(scalar).toAffine();

        const w = await calculators.eisenstein.calculate({
            scalar: toLimbs32(scalar),
            point: [toLimbs32(P.x), toLimbs32(P.y)],
            hint: [toLimbs32(Q.x), toLimbs32(Q.y)],
        });

        assert.equal(readLimbs(w, "main.out[0]"), Q.x, "x mismatch");
    });

    it("computes [3]*G correctly", async function () {
        this.timeout(0);
        const scalar = 3n;
        const P = Point.BASE.toAffine();
        const Q = Point.BASE.multiply(scalar).toAffine();

        const w = await calculators.eisenstein.calculate({
            scalar: toLimbs32(scalar),
            point: [toLimbs32(P.x), toLimbs32(P.y)],
            hint: [toLimbs32(Q.x), toLimbs32(Q.y)],
        });

        assert.equal(readLimbs(w, "main.out[0]"), Q.x, "x mismatch");
    });
});
