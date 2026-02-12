import { assert } from "chai";
import { describe_circuit } from "./helpers.js";

describe_circuit("Bitwise", {
    xor: { path: "bitwise.circom", template: "XOR" },
    and: { path: "bitwise.circom", template: "AND" },
    or: { path: "bitwise.circom", template: "OR" },
    muxor: { path: "bitwise.circom", template: "MUXOR", params: [4] },
    multiXor: { path: "bitwise.circom", template: "MultiXOR", params: [8] },
    bitwiseXor: { path: "bitwise.circom", template: "BitwiseXOR", params: [8] },
    bitwiseAnd: { path: "bitwise.circom", template: "BitwiseAND", params: [8] },
    bitwiseOr: { path: "bitwise.circom", template: "BitwiseOR", params: [8] },
    bitwiseNot: { path: "bitwise.circom", template: "BitwiseNOT", params: [8] },
}, (calculators) => {

    describe("Bit-level gates", () => {
        it("XOR truth table", async () => {
            const cases: [number, number, bigint][] = [
                [0, 0, 0n], [0, 1, 1n], [1, 0, 1n], [1, 1, 0n],
            ];
            for (const [a, b, expected] of cases) {
                const w = await calculators.xor.calculate({ in: [a, b] });
                assert.equal(w.value("main.out"), expected);
            }
        });

        it("AND truth table", async () => {
            const cases: [number, number, bigint][] = [
                [0, 0, 0n], [0, 1, 0n], [1, 0, 0n], [1, 1, 1n],
            ];
            for (const [a, b, expected] of cases) {
                const w = await calculators.and.calculate({ in: [a, b] });
                assert.equal(w.value("main.out"), expected);
            }
        });

        it("OR truth table", async () => {
            const cases: [number, number, bigint][] = [
                [0, 0, 0n], [0, 1, 1n], [1, 0, 1n], [1, 1, 1n],
            ];
            for (const [a, b, expected] of cases) {
                const w = await calculators.or.calculate({ in: [a, b] });
                assert.equal(w.value("main.out"), expected);
            }
        });

        it("MUXOR computes multi-input XOR", async () => {
            // 1 ^ 0 ^ 1 ^ 0 = 0
            const w = await calculators.muxor.calculate({ in: [1, 0, 1, 0] });
            assert.equal(w.value("main.out"), 0n);

            // 1 ^ 1 ^ 1 ^ 1 = 0
            const w2 = await calculators.muxor.calculate({ in: [1, 1, 1, 1] });
            assert.equal(w2.value("main.out"), 0n);

            // 1 ^ 0 ^ 0 ^ 0 = 1
            const w3 = await calculators.muxor.calculate({ in: [1, 0, 0, 0] });
            assert.equal(w3.value("main.out"), 1n);
        });

        it("MultiXOR pairwise XORs two arrays", async () => {
            const a = [1, 0, 1, 0, 1, 1, 0, 0];
            const b = [0, 1, 1, 0, 0, 1, 1, 0];
            const expected = a.map((v, i) => BigInt(v ^ b[i]));

            const w = await calculators.multiXor.calculate({ in: [a, b] });
            const out = w.array("main.out");
            assert.deepEqual(out, expected);
        });
    });

    describe("Word-level operations (8-bit)", () => {
        it("BitwiseXOR on byte values", async () => {
            const cases: [number, number, bigint][] = [
                [0xFF, 0x00, 0xFFn],
                [0xAA, 0x55, 0xFFn],
                [0xFF, 0xFF, 0x00n],
                [0x0F, 0xF0, 0xFFn],
            ];
            for (const [a, b, expected] of cases) {
                const w = await calculators.bitwiseXor.calculate({ a, b });
                assert.equal(w.value("main.out"), expected);
            }
        });

        it("BitwiseAND on byte values", async () => {
            const cases: [number, number, bigint][] = [
                [0xFF, 0x00, 0x00n],
                [0xFF, 0xFF, 0xFFn],
                [0xAA, 0x55, 0x00n],
                [0x0F, 0xFF, 0x0Fn],
            ];
            for (const [a, b, expected] of cases) {
                const w = await calculators.bitwiseAnd.calculate({ a, b });
                assert.equal(w.value("main.out"), expected);
            }
        });

        it("BitwiseOR on byte values", async () => {
            const cases: [number, number, bigint][] = [
                [0x00, 0x00, 0x00n],
                [0xFF, 0x00, 0xFFn],
                [0xAA, 0x55, 0xFFn],
                [0x0F, 0xF0, 0xFFn],
            ];
            for (const [a, b, expected] of cases) {
                const w = await calculators.bitwiseOr.calculate({ a, b });
                assert.equal(w.value("main.out"), expected);
            }
        });

        it("BitwiseNOT inverts all bits", async () => {
            const cases: [number, bigint][] = [
                [0x00, 0xFFn],
                [0xFF, 0x00n],
                [0xAA, 0x55n],
                [0x0F, 0xF0n],
            ];
            for (const [a, expected] of cases) {
                const w = await calculators.bitwiseNot.calculate({ a });
                assert.equal(w.value("main.out"), expected);
            }
        });
    });
});
