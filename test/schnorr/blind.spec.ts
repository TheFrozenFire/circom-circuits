import { assert } from "chai";
import { describe_circuit } from "../helpers.js";
import { scalarMul, BASE8_X, BASE8_Y, SUBORDER } from "../babyjub_utils.js";

const nBits = 8;

// Known points
const nonce = 13n;
const [Rx, Ry] = scalarMul(nonce, BASE8_X, BASE8_Y);
const privKey = 7n;
const [signerXx, signerXy] = scalarMul(privKey, BASE8_X, BASE8_Y);

const blindingA = 5n;
const blindingB = 11n;

const message = [1, 0, 1, 0, 1, 0, 1, 0];

describe_circuit("SchnorrMessageBlind", {
    blind: { path: "schnorr/blind.circom", template: "SchnorrMessageBlind", params: [nBits] },
}, (calculators) => {
    it("produces a non-zero blinded commitment", async () => {
        const w = await calculators.blind.calculate({
            message,
            signerX: [signerXx, signerXy],
            signerR: [Rx, Ry],
            blindingA,
            blindingB,
        });
        const out = w.value("main.out");
        assert.isTrue(out !== 0n);
    });

    it("output is less than suborder", async () => {
        const w = await calculators.blind.calculate({
            message,
            signerX: [signerXx, signerXy],
            signerR: [Rx, Ry],
            blindingA,
            blindingB,
        });
        const out = w.value("main.out");
        assert.isTrue(out < SUBORDER);
    });

    it("different blindings produce different outputs", async () => {
        const w1 = await calculators.blind.calculate({
            message,
            signerX: [signerXx, signerXy],
            signerR: [Rx, Ry],
            blindingA: 5n,
            blindingB: 11n,
        });
        const out1 = w1.value("main.out");

        const w2 = await calculators.blind.calculate({
            message,
            signerX: [signerXx, signerXy],
            signerR: [Rx, Ry],
            blindingA: 3n,
            blindingB: 17n,
        });
        const out2 = w2.value("main.out");

        assert.notEqual(out1, out2);
    });

    it("rejects blinding >= suborder", async () => {
        try {
            await calculators.blind.calculate({
                message,
                signerX: [signerXx, signerXy],
                signerR: [Rx, Ry],
                blindingA: SUBORDER, // invalid: not < suborder
                blindingB: 11n,
            });
            assert.fail("should have thrown");
        } catch (e: any) {
            assert.notEqual(e.message, "should have thrown");
        }
    });
});
