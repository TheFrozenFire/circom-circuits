import { assert } from "chai";
import { createHash } from "crypto";
import { describe_circuit } from "../helpers.js";

// Convert a byte to 8 bits in MSB-first order (SHA-256 convention).
function byteToBitsMSB(byte: number): number[] {
    const bits: number[] = [];
    for (let i = 7; i >= 0; i--) {
        bits.push((byte >> i) & 1);
    }
    return bits;
}

// Convert a SHA-256 digest (Buffer) to 256 bits in MSB-first order per word.
function digestToBits(digest: Buffer): bigint[] {
    const bits: bigint[] = [];
    for (const byte of digest) {
        for (let i = 7; i >= 0; i--) {
            bits.push(BigInt((byte >> i) & 1));
        }
    }
    return bits;
}

describe_circuit("Sha256", {
    sha: { path: "hash/sha256/sha256.circom", template: "Sha256", params: [8] },
}, (calculators) => {
    it("hashes 0x00 byte to known digest", async () => {
        const input = byteToBitsMSB(0x00);
        const expected = digestToBits(
            createHash("sha256").update(Buffer.from([0x00])).digest()
        );

        const w = await calculators.sha.calculate({ in: input });
        const out: bigint[] = [];
        for (let i = 0; i < 256; i++) {
            out.push(w.value(`main.out[${i}]`));
        }

        assert.deepEqual(out, expected);
    });

    it("hashes 0x61 ('a') to known digest", async () => {
        const input = byteToBitsMSB(0x61);
        const expected = digestToBits(
            createHash("sha256").update(Buffer.from([0x61])).digest()
        );

        const w = await calculators.sha.calculate({ in: input });
        const out: bigint[] = [];
        for (let i = 0; i < 256; i++) {
            out.push(w.value(`main.out[${i}]`));
        }

        assert.deepEqual(out, expected);
    });

    it("produces 256 output bits", async () => {
        const input = byteToBitsMSB(0xff);
        const w = await calculators.sha.calculate({ in: input });

        // All 256 bits should be binary (0 or 1)
        for (let i = 0; i < 256; i++) {
            const bit = w.value(`main.out[${i}]`);
            assert.isTrue(bit === 0n || bit === 1n, `bit ${i} is not binary`);
        }
    });
});
