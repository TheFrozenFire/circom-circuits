import { assert } from "chai";
import { describe_circuit } from "../helpers.js";

function toLimbs(val: number | bigint, n: number, k: number): bigint[] {
    const v = BigInt(val);
    const mask = (1n << BigInt(n)) - 1n;
    const limbs: bigint[] = [];
    let remaining = v;
    for (let i = 0; i < k; i++) {
        limbs.push(remaining & mask);
        remaining >>= BigInt(n);
    }
    return limbs;
}

function fromLimbs(limbs: bigint[], n: number): bigint {
    let val = 0n;
    for (let i = limbs.length - 1; i >= 0; i--) {
        val = (val << BigInt(n)) + limbs[i];
    }
    return val;
}

function modPow(base: bigint, exp: bigint, mod: bigint): bigint {
    let result = 1n;
    let b = ((base % mod) + mod) % mod;
    let e = exp;
    while (e > 0n) {
        if (e & 1n) {
            result = (result * b) % mod;
        }
        b = (b * b) % mod;
        e >>= 1n;
    }
    return result;
}

function toBits(val: number | bigint, numBits: number): bigint[] {
    const v = BigInt(val);
    const bits: bigint[] = [];
    for (let i = 0; i < numBits; i++) {
        bits.push((v >> BigInt(i)) & 1n);
    }
    return bits;
}

// ═══════════════════════════════════════════════════
// BigMultModP_CRT — CRT-verified modular multiplication
// ═══════════════════════════════════════════════════

describe_circuit("BigMultModP_CRT", {
    mul: { path: "arithmetic/bigint_crt.circom", template: "BigMultModP_CRT", params: [4, 2] },
}, (calculators) => {
    const p = toLimbs(251, 4, 2);

    it("multiplies with reduction", async () => {
        // (20 * 13) mod 251 = 260 mod 251 = 9
        const a = toLimbs(20, 4, 2);
        const b = toLimbs(13, 4, 2);
        const w = await calculators.mul.calculate({ a, b, p });
        const out = w.array("main.out");
        assert.equal(fromLimbs(out, 4), 9n);
    });

    it("multiplies without reduction", async () => {
        // (10 * 5) mod 251 = 50
        const a = toLimbs(10, 4, 2);
        const b = toLimbs(5, 4, 2);
        const w = await calculators.mul.calculate({ a, b, p });
        const out = w.array("main.out");
        assert.equal(fromLimbs(out, 4), 50n);
    });

    it("multiply by one", async () => {
        const a = toLimbs(200, 4, 2);
        const b = toLimbs(1, 4, 2);
        const w = await calculators.mul.calculate({ a, b, p });
        const out = w.array("main.out");
        assert.equal(fromLimbs(out, 4), 200n);
    });

    it("multiply by zero", async () => {
        const a = toLimbs(123, 4, 2);
        const b = toLimbs(0, 4, 2);
        const w = await calculators.mul.calculate({ a, b, p });
        const out = w.array("main.out");
        assert.equal(fromLimbs(out, 4), 0n);
    });

    it("max values near modulus", async () => {
        // (250 * 250) mod 251 = 62500 mod 251 = 250*250 = 62500; 62500/251 = 249.00...; 249*251 = 62499; rem = 1
        const a = toLimbs(250, 4, 2);
        const b = toLimbs(250, 4, 2);
        const w = await calculators.mul.calculate({ a, b, p });
        const out = w.array("main.out");
        assert.equal(fromLimbs(out, 4), (250n * 250n) % 251n);
    });

    it("cross-validates against JS reference for multiple inputs", async () => {
        const cases: [number, number][] = [
            [20, 13], [10, 5], [200, 1], [250, 250], [1, 1], [100, 200],
        ];
        for (const [av, bv] of cases) {
            const a = toLimbs(av, 4, 2);
            const b = toLimbs(bv, 4, 2);
            const w = await calculators.mul.calculate({ a, b, p });
            const out = w.array("main.out");
            const expected = (BigInt(av) * BigInt(bv)) % 251n;
            assert.equal(fromLimbs(out, 4), expected, `${av} * ${bv} mod 251`);
        }
    });
});

// ═══════════════════════════════════════════════════
// BigModExp65537 — Fixed-exponent modexp (RSA verify)
// ═══════════════════════════════════════════════════

describe_circuit("BigModExp65537", {
    exp65537: { path: "arithmetic/bigint_crt.circom", template: "BigModExp65537", params: [4, 2] },
}, (calculators) => {
    it("computes 3^65537 mod 251", async () => {
        const base = toLimbs(3, 4, 2);
        const modulus = toLimbs(251, 4, 2);
        const w = await calculators.exp65537.calculate({ base, modulus });
        const out = w.array("main.out");
        const expected = modPow(3n, 65537n, 251n);
        assert.equal(fromLimbs(out, 4), expected);
    });

    it("computes 2^65537 mod 251", async () => {
        const base = toLimbs(2, 4, 2);
        const modulus = toLimbs(251, 4, 2);
        const w = await calculators.exp65537.calculate({ base, modulus });
        const out = w.array("main.out");
        const expected = modPow(2n, 65537n, 251n);
        assert.equal(fromLimbs(out, 4), expected);
    });

    it("computes 1^65537 mod 251 = 1", async () => {
        const base = toLimbs(1, 4, 2);
        const modulus = toLimbs(251, 4, 2);
        const w = await calculators.exp65537.calculate({ base, modulus });
        const out = w.array("main.out");
        assert.equal(fromLimbs(out, 4), 1n);
    });
});

// ═══════════════════════════════════════════════════
// BigModExp — Variable-exponent modexp
// ═══════════════════════════════════════════════════

describe_circuit("BigModExp", {
    modexp: { path: "arithmetic/bigint_crt.circom", template: "BigModExp", params: [4, 2, 8] },
}, (calculators) => {
    it("computes 3^7 mod 251", async () => {
        const base = toLimbs(3, 4, 2);
        const expBits = toBits(7, 8);
        const modulus = toLimbs(251, 4, 2);
        const w = await calculators.modexp.calculate({ base, exp: expBits, modulus });
        const out = w.array("main.out");
        assert.equal(fromLimbs(out, 4), modPow(3n, 7n, 251n));
    });

    it("computes 5^100 mod 251", async () => {
        const base = toLimbs(5, 4, 2);
        const expBits = toBits(100, 8);
        const modulus = toLimbs(251, 4, 2);
        const w = await calculators.modexp.calculate({ base, exp: expBits, modulus });
        const out = w.array("main.out");
        assert.equal(fromLimbs(out, 4), modPow(5n, 100n, 251n));
    });

    it("computes base^1 = base", async () => {
        const base = toLimbs(42, 4, 2);
        const expBits = toBits(1, 8);
        const modulus = toLimbs(251, 4, 2);
        const w = await calculators.modexp.calculate({ base, exp: expBits, modulus });
        const out = w.array("main.out");
        assert.equal(fromLimbs(out, 4), 42n);
    });

    it("computes base^0 = 1", async () => {
        const base = toLimbs(42, 4, 2);
        const expBits = toBits(0, 8);
        const modulus = toLimbs(251, 4, 2);
        const w = await calculators.modexp.calculate({ base, exp: expBits, modulus });
        const out = w.array("main.out");
        assert.equal(fromLimbs(out, 4), 1n);
    });

    it("computes 2^255 mod 251", async () => {
        const base = toLimbs(2, 4, 2);
        const expBits = toBits(255, 8);
        const modulus = toLimbs(251, 4, 2);
        const w = await calculators.modexp.calculate({ base, exp: expBits, modulus });
        const out = w.array("main.out");
        assert.equal(fromLimbs(out, 4), modPow(2n, 255n, 251n));
    });
});
