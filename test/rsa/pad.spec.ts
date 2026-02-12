import { assert } from "chai";
import { describe_circuit } from "../helpers.js";

// 1024-bit RSA with 32-bit windows
const n = 32;
const k = 32;

describe_circuit("RSAPKCSv15Pad", {
    pad: { path: "rsa/pad.circom", template: "RSAPKCSv15Pad", params: [n, k] },
}, (calculators) => {
    it("produces correct PKCS v1.5 padding structure", async () => {
        // Create a dummy 256-bit hash (all zeros)
        const message_hash = new Array(256).fill(0);

        const w = await calculators.pad.calculate({ message_hash });

        const out: bigint[] = [];
        for (let i = 0; i < k; i++) {
            out.push(w.value(`main.padded_message[${i}]`));
        }

        // Output is in LE limb order, so last limb = first big-endian word
        // padded_message[31] should be 0x0001FFFF (the BEW[0] prefix)
        assert.equal(out[31], BigInt(0x0001FFFF));

        // padded_message[30..13] should be 0xFFFFFFFF (18 padding words)
        for (let i = 13; i <= 30; i++) {
            assert.equal(out[i], BigInt(0xFFFFFFFF));
        }

        // ASN.1 header words (reversed from BEW positions 19-23)
        assert.equal(out[12], BigInt(0x00303130)); // BEW[19]
        assert.equal(out[11], BigInt(0x0D060960)); // BEW[20]
        assert.equal(out[10], BigInt(0x86480165)); // BEW[21]
        assert.equal(out[9], BigInt(0x03040201));  // BEW[22]
        assert.equal(out[8], BigInt(0x05000420));  // BEW[23]
    });

    it("encodes hash bits into lower limbs", async () => {
        // Hash with known pattern: first 32 bits = 1 (LE bit 0 set)
        const message_hash = new Array(256).fill(0);
        message_hash[0] = 1; // first bit set

        const w = await calculators.pad.calculate({ message_hash });

        // First hash window (BEW[24]) maps to padded_message[7] (k-1-24 = 7)
        // Bits2NumLE([1,0,0,...,0]) = 1
        assert.equal(w.value("main.padded_message[7]"), 1n);
    });

    it("all-ones hash produces correct limbs", async () => {
        const message_hash = new Array(256).fill(1);

        const w = await calculators.pad.calculate({ message_hash });

        // Each 32-bit window of all-ones: Bits2NumLE gives 2^32 - 1 = 0xFFFFFFFF
        for (let i = 0; i < 8; i++) {
            assert.equal(w.value(`main.padded_message[${7 - i}]`), BigInt(0xFFFFFFFF));
        }
    });
});

describe_circuit("RSAMessageBlind", {
    blind: { path: "rsa/blind.circom", template: "RSAMessageBlind", params: [4, 2, 3] },
}, (calculators) => {
    it("multiplies message by blinding factor mod N", async () => {
        // Small example: n=4 bits, k=2 limbs
        // Message = [3, 2] = 3 + 2*16 = 35
        // Blinding = [5, 1] = 5 + 1*16 = 21
        // Modulus = [7, 3] = 7 + 3*16 = 55
        // Expected: (35 * 21) % 55 = 735 % 55 = 20
        // 20 = 4 + 1*16 → [4, 1]
        const w = await calculators.blind.calculate({
            padded_message: [3, 2],
            blinding: [5, 1],
            public_modulus: [7, 3],
        });

        const out = w.array("main.out");
        assert.equal(out[0], 4n);
        assert.equal(out[1], 1n);
    });

    it("blinding by one is identity", async () => {
        const w = await calculators.blind.calculate({
            padded_message: [3, 2],
            blinding: [1, 0],
            public_modulus: [7, 3],
        });

        const out = w.array("main.out");
        // (35 * 1) % 55 = 35 → [3, 2]
        assert.equal(out[0], 3n);
        assert.equal(out[1], 2n);
    });
});
