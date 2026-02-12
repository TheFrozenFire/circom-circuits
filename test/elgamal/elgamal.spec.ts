import { assert } from "chai";
import { describe_circuit } from "../helpers.js";
import { mod, babyAdd, scalarMul, BASE8_X, BASE8_Y, SUBORDER, p } from "../babyjub_utils.js";

// Use small known scalars for testing
const privKey = 7n;
const [pubX, pubY] = scalarMul(privKey, BASE8_X, BASE8_Y);
const ephemeral_y = 13n;

// Message point = 2*G (a known point on curve)
const [msgX, msgY] = scalarMul(2n, BASE8_X, BASE8_Y);

describe_circuit("ElGamalShare", {
    share: { path: "elgamal/elgamal.circom", template: "ElGamalShare" },
}, (calculators) => {
    it("computes shared secret and c1", async () => {
        const [expSharedX, expSharedY] = scalarMul(ephemeral_y, pubX, pubY);
        const [expC1X, expC1Y] = scalarMul(ephemeral_y, BASE8_X, BASE8_Y);

        const w = await calculators.share.calculate({
            pubKey: [pubX, pubY],
            y: ephemeral_y,
        });

        const out = w.array("main.out");
        const c1 = w.array("main.c1");

        assert.equal(out[0], expSharedX);
        assert.equal(out[1], expSharedY);
        assert.equal(c1[0], expC1X);
        assert.equal(c1[1], expC1Y);
    });
});

describe_circuit("ElGamalEncrypt", {
    enc: { path: "elgamal/elgamal.circom", template: "ElGamalEncrypt" },
}, (calculators) => {
    it("encrypts a message point", async () => {
        const [sharedX, sharedY] = scalarMul(ephemeral_y, pubX, pubY);
        const [expC1X, expC1Y] = scalarMul(ephemeral_y, BASE8_X, BASE8_Y);
        const [expC2X, expC2Y] = babyAdd(msgX, msgY, sharedX, sharedY);

        const w = await calculators.enc.calculate({
            pubKey: [pubX, pubY],
            message: [msgX, msgY],
            y: ephemeral_y,
        });

        const c1 = w.array("main.c1");
        const c2 = w.array("main.c2");

        assert.equal(c1[0], expC1X);
        assert.equal(c1[1], expC1Y);
        assert.equal(c2[0], expC2X);
        assert.equal(c2[1], expC2Y);
    });
});

describe_circuit("ElGamalDecrypt", {
    dec: { path: "elgamal/elgamal.circom", template: "ElGamalDecrypt" },
}, (calculators) => {
    it("decrypts back to original message", async () => {
        // Encrypt in JS
        const [sharedX, sharedY] = scalarMul(ephemeral_y, pubX, pubY);
        const [c1X, c1Y] = scalarMul(ephemeral_y, BASE8_X, BASE8_Y);
        const [c2X, c2Y] = babyAdd(msgX, msgY, sharedX, sharedY);

        const w = await calculators.dec.calculate({
            c1: [c1X, c1Y],
            c2: [c2X, c2Y],
            privKey,
        });

        const message = w.array("main.message");
        assert.equal(message[0], msgX);
        assert.equal(message[1], msgY);
    });

    it("decrypts identity message correctly", async () => {
        // message = identity (0, 1)
        const [sharedX, sharedY] = scalarMul(ephemeral_y, pubX, pubY);
        const [c1X, c1Y] = scalarMul(ephemeral_y, BASE8_X, BASE8_Y);
        const [c2X, c2Y] = babyAdd(0n, 1n, sharedX, sharedY);

        const w = await calculators.dec.calculate({
            c1: [c1X, c1Y],
            c2: [c2X, c2Y],
            privKey,
        });

        const message = w.array("main.message");
        assert.equal(message[0], 0n);
        assert.equal(message[1], 1n);
    });
});
