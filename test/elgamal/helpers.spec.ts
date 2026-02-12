import { assert } from "chai";
import { describe_circuit } from "../helpers.js";
import { p, mod, BASE8_X, BASE8_Y } from "../babyjub_utils.js";

describe_circuit("ElGamalBlinding", {
    blind: { path: "elgamal/helpers.circom", template: "ElGamalBlinding" },
}, (calculators) => {
    it("computes blinding = point[0] - message", async () => {
        const message = 42n;
        const w = await calculators.blind.calculate({
            message,
            point: [BASE8_X, BASE8_Y],
        });
        // out = -(message - point[0]) = point[0] - message
        const expected = mod(BASE8_X - message);
        assert.equal(w.value("main.out"), expected);
    });

    it("blinding is zero when message equals point x-coord", async () => {
        const w = await calculators.blind.calculate({
            message: BASE8_X,
            point: [BASE8_X, BASE8_Y],
        });
        assert.equal(w.value("main.out"), 0n);
    });
});

describe_circuit("ElGamalMessageCheck", {
    check: { path: "elgamal/helpers.circom", template: "ElGamalMessageCheck" },
}, (calculators) => {
    it("accepts valid point/blinding/message relationship", async () => {
        const message = 42n;
        const blinding = mod(BASE8_X - message);
        await calculators.check.calculate({
            point: [BASE8_X, BASE8_Y],
            blinding,
            message,
        });
    });

    it("rejects invalid blinding", async () => {
        try {
            await calculators.check.calculate({
                point: [BASE8_X, BASE8_Y],
                blinding: 999n,
                message: 42n,
            });
            assert.fail("should have thrown");
        } catch (e: any) {
            assert.notEqual(e.message, "should have thrown");
        }
    });

    it("rejects point not on curve", async () => {
        try {
            await calculators.check.calculate({
                point: [1n, 2n], // not on curve
                blinding: 0n,
                message: 1n,
            });
            assert.fail("should have thrown");
        } catch (e: any) {
            assert.notEqual(e.message, "should have thrown");
        }
    });
});
