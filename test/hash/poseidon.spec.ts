import { assert } from "chai";
import { describe_circuit } from "../helpers.js";
import { Poseidon } from "@iden3/js-crypto";

describe_circuit("HashLeftRight", {
    hlr: { path: "hash/poseidon.circom", template: "HashLeftRight" },
}, (calculators) => {
    it("matches JS Poseidon for known inputs", async () => {
        const expected = Poseidon.hash([1n, 2n]);
        const w = await calculators.hlr.calculate({ left: 1, right: 2 });
        assert.equal(w.value("main.hash"), expected);
    });

    it("is not commutative", async () => {
        const w1 = await calculators.hlr.calculate({ left: 1, right: 2 });
        const h1 = w1.value("main.hash");
        const w2 = await calculators.hlr.calculate({ left: 2, right: 1 });
        const h2 = w2.value("main.hash");
        assert.notEqual(h1, h2);
    });

    it("hashes zero inputs", async () => {
        const expected = Poseidon.hash([0n, 0n]);
        const w = await calculators.hlr.calculate({ left: 0, right: 0 });
        assert.equal(w.value("main.hash"), expected);
        assert.isTrue(expected !== 0n);
    });
});
