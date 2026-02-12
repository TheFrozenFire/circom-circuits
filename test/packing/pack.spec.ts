import { assert } from "chai";
import { describe_circuit } from "../helpers.js";

describe_circuit("Pack_Elements", {
    pack: { path: "packing/pack.circom", template: "Pack_Elements", params: [1, 4, 4] },
    pack2: { path: "packing/pack.circom", template: "Pack_Elements", params: [2, 2, 4] },
}, (calculators) => {
    it("packs 4 items into 1 element", async () => {
        // [5, 10, 3, 12] with 4 bits each:
        // 5*2^0 + 10*2^4 + 3*2^8 + 12*2^12 = 5 + 160 + 768 + 49152 = 50085
        const w = await calculators.pack.calculate({ in: [5, 10, 3, 12] });
        assert.equal(w.value("main.out[0]"), 50085n);
    });

    it("packs zeros", async () => {
        const w = await calculators.pack.calculate({ in: [0, 0, 0, 0] });
        assert.equal(w.value("main.out[0]"), 0n);
    });

    it("packs into multiple elements", async () => {
        // Element 0: items [5, 10] → 5 + 10*16 = 165
        // Element 1: items [3, 12] → 3 + 12*16 = 195
        const w = await calculators.pack2.calculate({ in: [5, 10, 3, 12] });
        assert.equal(w.value("main.out[0]"), 165n);
        assert.equal(w.value("main.out[1]"), 195n);
    });

    it("rejects items exceeding bitsPerItem range", async () => {
        try {
            // 16 doesn't fit in 4 bits
            await calculators.pack.calculate({ in: [16, 0, 0, 0] });
            assert.fail("should have thrown");
        } catch (e: any) {
            assert.notEqual(e.message, "should have thrown");
        }
    });
});

describe_circuit("Pack_Elements_FromBits", {
    packBits: { path: "packing/pack.circom", template: "Pack_Elements_FromBits", params: [1, 4, 4] },
}, (calculators) => {
    it("packs pre-decomposed bits", async () => {
        // Same as Pack_Elements test: [5, 10, 3, 12] → 50085
        // 5  = [1,0,1,0], 10 = [0,1,0,1], 3 = [1,1,0,0], 12 = [0,0,1,1]
        const w = await calculators.packBits.calculate({
            in: [
                [1, 0, 1, 0],  // 5
                [0, 1, 0, 1],  // 10
                [1, 1, 0, 0],  // 3
                [0, 0, 1, 1],  // 12
            ],
        });
        assert.equal(w.value("main.out[0]"), 50085n);
    });

    it("packs zero bits", async () => {
        const w = await calculators.packBits.calculate({
            in: [
                [0, 0, 0, 0],
                [0, 0, 0, 0],
                [0, 0, 0, 0],
                [0, 0, 0, 0],
            ],
        });
        assert.equal(w.value("main.out[0]"), 0n);
    });
});

describe_circuit("Unpack_Elements", {
    unpack: { path: "packing/pack.circom", template: "Unpack_Elements", params: [1, 4, 4] },
}, (calculators) => {
    it("unpacks element to individual items", async () => {
        // 50085 → [5, 10, 3, 12]
        const w = await calculators.unpack.calculate({ in: [50085] });
        assert.equal(w.value("main.out[0]"), 5n);
        assert.equal(w.value("main.out[1]"), 10n);
        assert.equal(w.value("main.out[2]"), 3n);
        assert.equal(w.value("main.out[3]"), 12n);
    });

    it("unpacks zero", async () => {
        const w = await calculators.unpack.calculate({ in: [0] });
        assert.equal(w.value("main.out[0]"), 0n);
        assert.equal(w.value("main.out[1]"), 0n);
        assert.equal(w.value("main.out[2]"), 0n);
        assert.equal(w.value("main.out[3]"), 0n);
    });
});

describe_circuit("Pack/Unpack round-trip", {
    pack: { path: "packing/pack.circom", template: "Pack_Elements", params: [1, 4, 4] },
    unpack: { path: "packing/pack.circom", template: "Unpack_Elements", params: [1, 4, 4] },
}, (calculators) => {
    it("round-trip preserves values", async () => {
        const items = [5, 10, 3, 12];

        // Pack
        const packed = await calculators.pack.calculate({ in: items });
        const packedValue = packed.value("main.out[0]");

        // Unpack
        const unpacked = await calculators.unpack.calculate({ in: [Number(packedValue)] });
        assert.equal(unpacked.value("main.out[0]"), 5n);
        assert.equal(unpacked.value("main.out[1]"), 10n);
        assert.equal(unpacked.value("main.out[2]"), 3n);
        assert.equal(unpacked.value("main.out[3]"), 12n);
    });
});
