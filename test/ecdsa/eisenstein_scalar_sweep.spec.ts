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

const order = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141n;

// Eisenstein half-GCD in JS to count iterations
function eisensteinIterCount(scalar: bigint): number {
    const w0 = 0x814141FDABB7BB0D1D58E9BFED34924En; // from constants
    const w1 = 0xE432AF0810EF7C89700E4AFDCAAB6423n;

    // Eisenstein norm
    function norm(a0: bigint, a1: bigint): bigint {
        return a0 * a0 - a0 * a1 + a1 * a1;
    }

    // Use absolute values for norm
    let rp0 = w0, rp1 = w1;
    let rc0 = scalar, rc1 = 0n;

    let count = 0;
    const threshold = 1n << 136n;

    while (norm(rc0 < 0n ? -rc0 : rc0, rc1 < 0n ? -rc1 : rc1) >= threshold) {
        // Simplified: just count iterations (we know the GCD converges)
        // Swap if needed
        const nPrev = norm(rp0 < 0n ? -rp0 : rp0, rp1 < 0n ? -rp1 : rp1);
        const nCurr = norm(rc0 < 0n ? -rc0 : rc0, rc1 < 0n ? -rc1 : rc1);

        if (nCurr === 0n) break;

        // Eisenstein division
        // c = rp * conj(rc), d = N(rc)
        // conj(rc0+rc1ω) = (rc0-rc1) + (-rc1)ω
        const conj0 = rc0 - rc1;
        const conj1 = -rc1;

        // c = rp * conj(rc)
        const c0 = rp0 * conj0 - rp1 * conj1;
        const c1 = rp0 * conj1 + rp1 * conj0 - rp1 * conj1;
        const d = rc0 * rc0 - rc0 * rc1 + rc1 * rc1;

        // Round division
        function roundDiv(a: bigint, b: bigint): bigint {
            if (b < 0n) { a = -a; b = -b; }
            if (a >= 0n) return (2n * a + b) / (2n * b);
            else return -((-2n * a + b) / (2n * b));
        }

        const q0 = roundDiv(c0, d);
        const q1 = roundDiv(c1, d);

        // r_next = r_prev - q * r_curr
        const qr0 = q0 * rc0 - q1 * rc1;
        const qr1 = q0 * rc1 + q1 * rc0 - q1 * rc1;
        const rn0 = rp0 - qr0;
        const rn1 = rp1 - qr1;

        rp0 = rc0; rp1 = rc1;
        rc0 = rn0; rc1 = rn1;

        count++;
        if (count > 100) break;
    }
    return count;
}

// Test scalars of different sizes
const testScalars: [string, bigint][] = [
    ["5", 5n],
    ["0xFF", 0xFFn],
    ["0xFFFF", 0xFFFFn],
    ["0xFFFFFFFF", 0xFFFFFFFFn],
    ["0xFFFFFFFFFF", 0xFFFFFFFFFFn],
    ["64-bit", 0xdeadbeefcafebaben],
    ["96-bit", 0xdeadbeefcafebabedeadbeen],
    ["128-bit", 0xdeadbeefcafebabedeadbeefcafebaben],
    ["160-bit", 0xdeadbeefcafebabedeadbeefcafebabedeadbeen],
    ["192-bit", 0xdeadbeefcafebabedeadbeefcafebabedeadbeefcafebaben],
    ["224-bit", 0xdeadbeefcafebabedeadbeefcafebabedeadbeefcafebabedeadbeen],
    ["full", 0xdeadbeefcafebabedeadbeefcafebabedeadbeefcafebabedeadbeefcafebaben],
];

describe_circuit("EisensteinScalarSweep", {
    eisenstein: {
        path: "ecdsa/eisenstein_glv.circom",
        template: "Secp256k1EisensteinScalarMult",
        params: [n, k],
    },
}, (calculators) => {

    // First print iteration counts
    it("print GCD iteration counts", function () {
        for (const [name, scalar] of testScalars) {
            const iters = eisensteinIterCount(scalar);
            console.log(`  ${name}: ${iters} iterations`);
        }
    });

    for (const [name, scalar] of testScalars) {
        it(`scalar ${name}`, async function () {
            this.timeout(0);
            const P = Point.BASE.toAffine();
            const Q = Point.BASE.multiply(scalar).toAffine();

            const w = await calculators.eisenstein.calculate({
                scalar: toLimbs32(scalar),
                point: [toLimbs32(P.x), toLimbs32(P.y)],
                hint: [toLimbs32(Q.x), toLimbs32(Q.y)],
            });

            assert.equal(readLimbs(w, "main.out[0]"), Q.x, `x mismatch for ${name}`);
        });
    }
});
