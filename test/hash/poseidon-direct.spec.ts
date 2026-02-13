import { assert } from "chai";
import { describe_circuit } from "../helpers.js";
import { Poseidon } from "@iden3/js-crypto";

describe_circuit("Poseidon(2)", {
    p2: { path: "hash/poseidon.circom", template: "Poseidon", params: [2] },
}, (calculators) => {
    it("matches JS reference for known inputs", async () => {
        const expected = Poseidon.hash([3n, 7n]);
        const w = await calculators.p2.calculate({ inputs: [3, 7] });
        assert.equal(w.value("main.out"), expected);
    });

    it("matches JS reference for large inputs", async () => {
        const a = 123456789012345678901234567890n;
        const b = 987654321098765432109876543210n;
        const expected = Poseidon.hash([a, b]);
        const w = await calculators.p2.calculate({ inputs: [a, b] });
        assert.equal(w.value("main.out"), expected);
    });

    it("hashes zero inputs to non-trivial value", async () => {
        const expected = Poseidon.hash([0n, 0n]);
        const w = await calculators.p2.calculate({ inputs: [0, 0] });
        const result = w.value("main.out");
        assert.equal(result, expected);
        assert.notEqual(result, 0n);
    });
});

describe_circuit("Poseidon(4)", {
    p4: { path: "hash/poseidon.circom", template: "Poseidon", params: [4] },
}, (calculators) => {
    it("matches JS reference for 4 inputs", async () => {
        const inputs = [1n, 2n, 3n, 4n];
        const expected = Poseidon.hash(inputs);
        const w = await calculators.p4.calculate({ inputs });
        assert.equal(w.value("main.out"), expected);
    });

    it("differs from Poseidon(2) result", async () => {
        const expected2 = Poseidon.hash([1n, 2n]);
        const expected4 = Poseidon.hash([1n, 2n, 0n, 0n]);
        assert.notEqual(expected2, expected4);

        const w = await calculators.p4.calculate({ inputs: [1, 2, 0, 0] });
        assert.equal(w.value("main.out"), expected4);
    });
});
