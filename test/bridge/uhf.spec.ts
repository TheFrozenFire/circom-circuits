import { assert } from "chai";
import { describe_circuit, compile_and_count } from "../helpers.js";

const P = 21888242871839275222246405745257275088548364400416034343698204186575808495617n;

function polyUHF(r: bigint, x: bigint[]): bigint {
    let acc = x[x.length - 1];
    for (let i = x.length - 2; i >= 0; i--) {
        acc = ((acc * r % P) + x[i]) % P;
    }
    return ((acc % P) + P) % P;
}

describe_circuit("PolyUHF (n=4)", {
    uhf4: { path: "bridge/uhf.circom", template: "PolyUHF", params: [4] },
}, (calculators) => {
    it("matches JS reference for known values", async () => {
        const r = 7n;
        const x = [3n, 5n, 11n, 13n];
        const expected = polyUHF(r, x);

        const w = await calculators.uhf4.calculate({ r, x });
        assert.equal(w.value("main.out"), expected);
    });

    it("r=1 gives sum of elements", async () => {
        const x = [10n, 20n, 30n, 40n];
        const expected = x.reduce((a, b) => (a + b) % P, 0n);

        const w = await calculators.uhf4.calculate({ r: 1n, x });
        assert.equal(w.value("main.out"), expected);
    });

    it("different vectors produce different UHF values", async () => {
        const r = 42n;
        const x1 = [1n, 2n, 3n, 4n];
        const x2 = [4n, 3n, 2n, 1n];

        const w1 = await calculators.uhf4.calculate({ r, x: x1 });
        const v1 = w1.value("main.out");

        const w2 = await calculators.uhf4.calculate({ r, x: x2 });
        const v2 = w2.value("main.out");

        assert.notEqual(v1, v2);
        assert.equal(v1, polyUHF(r, x1));
        assert.equal(v2, polyUHF(r, x2));
    });

    it("handles field edge values", async () => {
        const r = P - 1n;
        const x = [P - 1n, P - 2n, 1n, 0n];
        const expected = polyUHF(r, x);

        const w = await calculators.uhf4.calculate({ r, x });
        assert.equal(w.value("main.out"), expected);
    });
});

describe_circuit("PolyUHF (n=8)", {
    uhf8: { path: "bridge/uhf.circom", template: "PolyUHF", params: [8] },
}, (calculators) => {
    it("matches JS reference for 8 elements", async () => {
        const r = 123456789n;
        const x = [1n, 2n, 3n, 4n, 5n, 6n, 7n, 8n];
        const expected = polyUHF(r, x);

        const w = await calculators.uhf8.calculate({ r, x });
        assert.equal(w.value("main.out"), expected);
    });
});

describe("PolyUHF constraint count", () => {
    it("uses exactly n-1 constraints", async function () {
        this.timeout(0);
        const count = await compile_and_count({
            path: "bridge/uhf.circom",
            template: "PolyUHF",
            params: [8],
        });
        assert.equal(count, 7);
    });
});
