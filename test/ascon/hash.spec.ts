import { assert } from "chai";
import { describe_circuit } from "../helpers.js";

// Convert 64 LE bits to a 64-bit word.
function bitsToWordLE(bits: bigint[]): bigint {
    let w = 0n;
    for (let i = 0; i < 64; i++) {
        w |= bits[i] << BigInt(i);
    }
    return w;
}

// Convert a 64-bit word to 64 LE bits (matching circuit's word_2_bits).
function wordToBitsLE(w: bigint): number[] {
    const bits: number[] = [];
    for (let i = 0; i < 64; i++) {
        bits.push(Number((w >> BigInt(i)) & 1n));
    }
    return bits;
}

// Helper to extract all 4 output words from a witness.
function extractOutputWords(w: { value: (s: string) => bigint }): bigint[] {
    const words: bigint[] = [];
    for (let word = 0; word < 4; word++) {
        const bits: bigint[] = [];
        for (let bit = 0; bit < 64; bit++) {
            bits.push(w.value(`main.out[${word}][${bit}]`));
        }
        words.push(bitsToWordLE(bits));
    }
    return words;
}

// Regression test vectors captured from the circuit.
// The circuit's Ascon-Hash-256 uses round constants at the high byte of S2
// (bits 56..63 in LE representation), which differs from the standard Ascon spec
// (low byte). These vectors verify circuit consistency, not spec compliance.
const ZERO_BLOCK_EXPECTED = [
    0x5e6233521aecc29fn,
    0xc76c46e898ded600n,
    0xc252a89f154cde8en,
    0xf103dfad456d6124n,
];

const NONZERO_BLOCK_EXPECTED = [
    0xe0d6bd6bd55d0031n,
    0x3289e4eb8085fbb4n,
    0xb5c88d9c251fc635n,
    0x500b3f30ca805141n,
];

describe_circuit("Ascon_Hash_256", {
    hash: { path: "ascon/hash.circom", template: "Ascon_Hash_256", params: [1] },
}, (calculators) => {
    it("hashes a zero block to known output", async () => {
        const w = await calculators.hash.calculate({ in: [new Array(64).fill(0)] });
        const words = extractOutputWords(w);

        for (let i = 0; i < 4; i++) {
            assert.equal(words[i], ZERO_BLOCK_EXPECTED[i],
                `word ${i}: expected 0x${ZERO_BLOCK_EXPECTED[i].toString(16)}, got 0x${words[i].toString(16)}`);
        }
    });

    it("hashes a non-zero block to known output", async () => {
        const inputBits = wordToBitsLE(0x0123456789abcdefn);
        const w = await calculators.hash.calculate({ in: [inputBits] });
        const words = extractOutputWords(w);

        for (let i = 0; i < 4; i++) {
            assert.equal(words[i], NONZERO_BLOCK_EXPECTED[i],
                `word ${i}: expected 0x${NONZERO_BLOCK_EXPECTED[i].toString(16)}, got 0x${words[i].toString(16)}`);
        }
    });

    it("different inputs produce different outputs", async () => {
        const w1 = await calculators.hash.calculate({ in: [new Array(64).fill(0)] });
        // Extract w1 values BEFORE calling calculate again (WASM buffer sharing)
        const words1 = extractOutputWords(w1);

        const w2 = await calculators.hash.calculate({ in: [new Array(64).fill(1)] });
        const words2 = extractOutputWords(w2);

        assert.notDeepEqual(words1, words2);
    });

    it("output is 4 × 64 binary bits", async () => {
        const w = await calculators.hash.calculate({ in: [new Array(64).fill(0)] });
        for (let word = 0; word < 4; word++) {
            for (let bit = 0; bit < 64; bit++) {
                const v = w.value(`main.out[${word}][${bit}]`);
                assert.isTrue(v === 0n || v === 1n, `out[${word}][${bit}] is not binary`);
            }
        }
    });
});
