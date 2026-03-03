import { assert } from "chai";
import { describe_circuit, compile_and_count, type CircuitDef } from "../helpers.js";

function toLimbs(val: bigint, n: number, k: number): bigint[] {
    const mask = (1n << BigInt(n)) - 1n;
    const limbs: bigint[] = [];
    let remaining = val;
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
        if (e & 1n) result = (result * b) % mod;
        b = (b * b) % mod;
        e >>= 1n;
    }
    return result;
}

function modInverse(a: bigint, m: bigint): bigint {
    let [old_r, r] = [a, m];
    let [old_s, s] = [1n, 0n];
    while (r !== 0n) {
        const q = old_r / r;
        [old_r, r] = [r, old_r - q * r];
        [old_s, s] = [s, old_s - q * s];
    }
    return ((old_s % m) + m) % m;
}

// ═══════════════════════════════════════════════════
// BigMultModP_CRT with CRT primes active (n=32, k=4)
// ═══════════════════════════════════════════════════

describe_circuit("BigMultModP_CRT (128-bit, CRT active)", {
    mul: { path: "arithmetic/bigint_crt.circom", template: "BigMultModP_CRT", params: [32, 4] },
}, (calculators) => {
    // Mersenne prime M127
    const P = (1n << 127n) - 1n;
    const p = toLimbs(P, 32, 4);

    it("multiplies large values with CRT verification", async () => {
        const A = 123456789012345678901234567890123456789n % P;
        const B = 987654321098765432109876543210987654321n % P;
        const expected = (A * B) % P;
        const w = await calculators.mul.calculate({ a: toLimbs(A, 32, 4), b: toLimbs(B, 32, 4), p });
        assert.equal(fromLimbs(w.array("main.out"), 32), expected);
    });

    it("handles values near the modulus boundary", async () => {
        const A = P - 1n;
        const B = P - 1n;
        const expected = (A * B) % P;  // (P-1)^2 mod P = 1
        const w = await calculators.mul.calculate({ a: toLimbs(A, 32, 4), b: toLimbs(B, 32, 4), p });
        assert.equal(fromLimbs(w.array("main.out"), 32), expected);
    });

    it("handles zero multiplication at scale", async () => {
        const A = 99999999999999999999999999999999999999n % P;
        const w = await calculators.mul.calculate({ a: toLimbs(A, 32, 4), b: toLimbs(0n, 32, 4), p });
        assert.equal(fromLimbs(w.array("main.out"), 32), 0n);
    });
});

// ═══════════════════════════════════════════════════
// End-to-end RSA verification at 128-bit scale
// ═══════════════════════════════════════════════════

describe_circuit("BigModExp65537 (128-bit RSA end-to-end)", {
    exp65537: { path: "arithmetic/bigint_crt.circom", template: "BigModExp65537", params: [32, 4] },
}, (calculators) => {
    // RSA setup: N = p*q (128-bit composite)
    const pRsa = 18446744073709551557n;  // 64-bit prime
    const qRsa = 18446744073709551533n;  // 64-bit prime
    const N = pRsa * qRsa;

    it("verifies an RSA signature", async () => {
        const m = 42n;
        const e = 65537n;
        const phi = (pRsa - 1n) * (qRsa - 1n);
        const d = modInverse(e, phi);
        const sig = modPow(m, d, N);

        // Circuit verifies: sig^65537 mod N == m
        const w = await calculators.exp65537.calculate({
            base: toLimbs(sig, 32, 4),
            modulus: toLimbs(N, 32, 4),
        });
        assert.equal(fromLimbs(w.array("main.out"), 32), m);
    });

    it("verifies RSA with different message", async () => {
        const m = 12345678901234567890n;
        const e = 65537n;
        const phi = (pRsa - 1n) * (qRsa - 1n);
        const d = modInverse(e, phi);
        const sig = modPow(m, d, N);

        const w = await calculators.exp65537.calculate({
            base: toLimbs(sig, 32, 4),
            modulus: toLimbs(N, 32, 4),
        });
        assert.equal(fromLimbs(w.array("main.out"), 32), m);
    });
});

// ═══════════════════════════════════════════════════
// Constraint scaling from small params to RSA-2048
// ═══════════════════════════════════════════════════

describe("@slow BigMultModP_CRT constraint scaling", function () {
    this.timeout(0);

    const configs: Array<{ n: number; k: number; label: string }> = [
        { n: 4, k: 2, label: "8-bit" },
        { n: 8, k: 4, label: "32-bit" },
        { n: 32, k: 4, label: "128-bit" },
        { n: 32, k: 8, label: "256-bit" },
        { n: 32, k: 32, label: "1024-bit" },
        { n: 32, k: 64, label: "2048-bit (RSA)" },
    ];

    for (const { n, k, label } of configs) {
        it(`${label} (n=${n}, k=${k})`, async () => {
            const [sb, crt] = await Promise.all([
                compile_and_count({ path: "arithmetic/bigint.circom", template: "BigMultModP", params: [n, k] }),
                compile_and_count({ path: "arithmetic/bigint_crt.circom", template: "BigMultModP_CRT", params: [n, k] }),
            ]);
            const pct = ((1 - crt / sb) * 100).toFixed(1);
            console.log(`    ${label}: schoolbook=${sb}  CRT=${crt}  savings=${pct}%`);
            assert.isBelow(crt, sb);
        });
    }
});
