import { assert } from "chai";
import { describe_circuit } from "../helpers.js";
import { babyAdd, scalarMul, BASE8_X, BASE8_Y } from "../babyjub_utils.js";

// Known points and scalars
const blindingA = 5n;
const blindingB = 11n;

// signerX = privKey * G
const signerPriv = 7n;
const [signerXx, signerXy] = scalarMul(signerPriv, BASE8_X, BASE8_Y);

// signerR = nonce * G
const nonce = 13n;
const [signerRx, signerRy] = scalarMul(nonce, BASE8_X, BASE8_Y);

describe_circuit("SchnorrBlinding", {
    blind: { path: "schnorr/blinding.circom", template: "SchnorrBlinding" },
}, (calculators) => {
    it("computes R' = signerR + a*G + b*signerX", async () => {
        // Expected: a*G
        const [aGx, aGy] = scalarMul(blindingA, BASE8_X, BASE8_Y);
        // Expected: b*signerX
        const [bXx, bXy] = scalarMul(blindingB, signerXx, signerXy);
        // R + a*G
        const [rAGx, rAGy] = babyAdd(signerRx, signerRy, aGx, aGy);
        // R + a*G + b*X
        const [expX, expY] = babyAdd(rAGx, rAGy, bXx, bXy);

        const w = await calculators.blind.calculate({
            signerX: [signerXx, signerXy],
            signerR: [signerRx, signerRy],
            blindingA,
            blindingB,
        });

        const out = w.array("main.out");
        assert.equal(out[0], expX);
        assert.equal(out[1], expY);
    });

    it("with zero blindings returns signerR", async () => {
        const w = await calculators.blind.calculate({
            signerX: [signerXx, signerXy],
            signerR: [signerRx, signerRy],
            blindingA: 0n,
            blindingB: 0n,
        });

        const out = w.array("main.out");
        // 0*G = identity, 0*X = identity, R + id + id = R
        assert.equal(out[0], signerRx);
        assert.equal(out[1], signerRy);
    });
});
