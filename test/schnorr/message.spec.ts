import { assert } from "chai";
import { describe_circuit } from "../helpers.js";
import { scalarMul, BASE8_X, BASE8_Y } from "../babyjub_utils.js";

// Small message for fast compilation (8 bits = 520 total input bits to SHA256)
const nBits = 8;

// Known points
const nonce = 13n;
const [Rx, Ry] = scalarMul(nonce, BASE8_X, BASE8_Y);
const privKey = 7n;
const [signerXx, signerXy] = scalarMul(privKey, BASE8_X, BASE8_Y);

// 8-bit message (all ones)
const message = [1, 1, 1, 1, 1, 1, 1, 1];

describe_circuit("SchnorrMessagePack", {
    pack: { path: "schnorr/message.circom", template: "SchnorrMessagePack", params: [nBits] },
}, (calculators) => {
    it("produces deterministic output for same inputs", async () => {
        const w1 = await calculators.pack.calculate({
            R: [Rx, Ry],
            signerX: [signerXx, signerXy],
            message,
        });

        // Total output length: 256 * 2 + 8 = 520 bits
        const out1: bigint[] = [];
        for (let i = 0; i < 520; i++) {
            out1.push(w1.value(`main.out[${i}]`));
        }

        const w2 = await calculators.pack.calculate({
            R: [Rx, Ry],
            signerX: [signerXx, signerXy],
            message,
        });

        for (let i = 0; i < 520; i++) {
            assert.equal(w2.value(`main.out[${i}]`), out1[i]);
        }
    });

    it("first bit of each point block is zero (padding)", async () => {
        const w = await calculators.pack.calculate({
            R: [Rx, Ry],
            signerX: [signerXx, signerXy],
            message,
        });

        assert.equal(w.value("main.out[0]"), 0n);
        assert.equal(w.value("main.out[256]"), 0n);
    });

    it("message bits are appended at offset 512", async () => {
        const w = await calculators.pack.calculate({
            R: [Rx, Ry],
            signerX: [signerXx, signerXy],
            message,
        });

        for (let i = 0; i < nBits; i++) {
            assert.equal(w.value(`main.out[${512 + i}]`), BigInt(message[i]));
        }
    });
});

describe_circuit("SchnorrMessageCommit", {
    commit: { path: "schnorr/message.circom", template: "SchnorrMessageCommit", params: [nBits] },
}, (calculators) => {
    it("produces a non-zero hash", async () => {
        const w = await calculators.commit.calculate({
            R: [Rx, Ry],
            signerX: [signerXx, signerXy],
            message,
        });
        const hash = w.value("main.out");
        assert.isTrue(hash !== 0n);
    });

    it("different messages produce different hashes", async () => {
        const w1 = await calculators.commit.calculate({
            R: [Rx, Ry],
            signerX: [signerXx, signerXy],
            message: [1, 1, 1, 1, 1, 1, 1, 1],
        });
        const h1 = w1.value("main.out");

        const w2 = await calculators.commit.calculate({
            R: [Rx, Ry],
            signerX: [signerXx, signerXy],
            message: [0, 0, 0, 0, 0, 0, 0, 0],
        });
        const h2 = w2.value("main.out");

        assert.notEqual(h1, h2);
    });

    it("hash fits in 248 bits", async () => {
        const w = await calculators.commit.calculate({
            R: [Rx, Ry],
            signerX: [signerXx, signerXy],
            message,
        });
        const hash = w.value("main.out");
        assert.isTrue(hash < (1n << 248n));
    });
});
