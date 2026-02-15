import { assert } from "chai";
import { describe_circuit } from "../helpers.js";

// ── Ch_t ───────────────────────────────────────────────────────────
// ch(a,b,c) = (a AND b) XOR (NOT a AND c) = a*(b-c) + c

describe_circuit("Ch_t", {
    ch: { path: "hash/sha256/ch.circom", template: "Ch_t", params: [4] },
}, (calculators) => {
    it("computes choose function on all-zero input", async () => {
        const w = await calculators.ch.calculate({
            a: [0, 0, 0, 0],
            b: [0, 0, 0, 0],
            c: [0, 0, 0, 0],
        });
        assert.deepEqual(w.array("main.out"), [0n, 0n, 0n, 0n]);
    });

    it("when a=1, selects b", async () => {
        const w = await calculators.ch.calculate({
            a: [1, 1, 1, 1],
            b: [1, 0, 1, 0],
            c: [0, 1, 0, 1],
        });
        assert.deepEqual(w.array("main.out"), [1n, 0n, 1n, 0n]);
    });

    it("when a=0, selects c", async () => {
        const w = await calculators.ch.calculate({
            a: [0, 0, 0, 0],
            b: [1, 1, 1, 1],
            c: [0, 1, 0, 1],
        });
        assert.deepEqual(w.array("main.out"), [0n, 1n, 0n, 1n]);
    });
});

// ── Maj_t ──────────────────────────────────────────────────────────
// maj(a,b,c) = (a AND b) XOR (a AND c) XOR (b AND c)

describe_circuit("Maj_t", {
    maj: { path: "hash/sha256/maj.circom", template: "Maj_t", params: [4] },
}, (calculators) => {
    it("all zeros → all zeros", async () => {
        const w = await calculators.maj.calculate({
            a: [0, 0, 0, 0],
            b: [0, 0, 0, 0],
            c: [0, 0, 0, 0],
        });
        assert.deepEqual(w.array("main.out"), [0n, 0n, 0n, 0n]);
    });

    it("majority of (1,1,0) is 1", async () => {
        const w = await calculators.maj.calculate({
            a: [1, 1, 0, 0],
            b: [1, 0, 1, 0],
            c: [0, 1, 1, 0],
        });
        // maj(1,1,0)=1, maj(1,0,1)=1, maj(0,1,1)=1, maj(0,0,0)=0
        assert.deepEqual(w.array("main.out"), [1n, 1n, 1n, 0n]);
    });

    it("all ones → all ones", async () => {
        const w = await calculators.maj.calculate({
            a: [1, 1, 1, 1],
            b: [1, 1, 1, 1],
            c: [1, 1, 1, 1],
        });
        assert.deepEqual(w.array("main.out"), [1n, 1n, 1n, 1n]);
    });
});

// ── RotR ───────────────────────────────────────────────────────────
// Right rotation by r positions

describe_circuit("RotR", {
    rot: { path: "hash/sha256/rotate.circom", template: "RotR", params: [8, 3] },
}, (calculators) => {
    it("rotates right by 3 positions", async () => {
        // Input: [1,0,0,0,0,0,0,0] (bit 0 set)
        // RotR(8,3): out[i] = in[(i+3) % 8]
        // out[0]=in[3]=0, out[1]=in[4]=0, ..., out[5]=in[0]=1, out[6]=in[1]=0, out[7]=in[2]=0
        const inp = [1, 0, 0, 0, 0, 0, 0, 0];
        const w = await calculators.rot.calculate({ in: inp });
        const out = w.array("main.out");
        const expected = inp.map((_, i) => BigInt(inp[(i + 3) % 8]));
        assert.deepEqual(out, expected);
    });

    it("identity when all same", async () => {
        const w = await calculators.rot.calculate({ in: [1, 1, 1, 1, 1, 1, 1, 1] });
        assert.deepEqual(w.array("main.out"), [1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n]);
    });
});

// ── ShR ────────────────────────────────────────────────────────────
// Right shift by r positions (vacated bits are zero)

describe_circuit("ShR", {
    shr: { path: "hash/sha256/shift.circom", template: "ShR", params: [8, 3] },
}, (calculators) => {
    it("shifts right by 3 positions", async () => {
        // ShR(8,3): out[i] = (i+3 >= 8) ? 0 : in[i+3]
        const inp = [1, 1, 0, 1, 0, 1, 0, 0];
        const expected = inp.map((_, i) => (i + 3 >= 8) ? 0n : BigInt(inp[i + 3]));
        const w = await calculators.shr.calculate({ in: inp });
        assert.deepEqual(w.array("main.out"), expected);
    });

    it("top bits become zero", async () => {
        const w = await calculators.shr.calculate({ in: [0, 0, 0, 0, 0, 1, 1, 1] });
        // in[5..7] = 1, shifted right 3 → out[2..4] = 1, out[5..7] = 0
        assert.deepEqual(w.array("main.out"), [0n, 0n, 1n, 1n, 1n, 0n, 0n, 0n]);
    });
});

// ── Xor3 ───────────────────────────────────────────────────────────
// Three-input XOR

describe_circuit("Xor3", {
    xor3: { path: "hash/sha256/xor3.circom", template: "Xor3", params: [4] },
}, (calculators) => {
    it("computes 3-way XOR", async () => {
        const w = await calculators.xor3.calculate({
            a: [0, 0, 1, 1],
            b: [0, 1, 0, 1],
            c: [1, 0, 0, 1],
        });
        // 0^0^1=1, 0^1^0=1, 1^0^0=1, 1^1^1=1
        assert.deepEqual(w.array("main.out"), [1n, 1n, 1n, 1n]);
    });

    it("all zeros → all zeros", async () => {
        const w = await calculators.xor3.calculate({
            a: [0, 0, 0, 0],
            b: [0, 0, 0, 0],
            c: [0, 0, 0, 0],
        });
        assert.deepEqual(w.array("main.out"), [0n, 0n, 0n, 0n]);
    });

    it("two equal inputs cancel", async () => {
        const w = await calculators.xor3.calculate({
            a: [1, 0, 1, 0],
            b: [1, 0, 1, 0],
            c: [0, 1, 0, 1],
        });
        // a^b = 0, 0^c = c
        assert.deepEqual(w.array("main.out"), [0n, 1n, 0n, 1n]);
    });
});

// ── BinSum ─────────────────────────────────────────────────────────
// Binary addition of ops operands, each n bits wide

describe_circuit("BinSum", {
    bs: { path: "hash/sha256/binsum.circom", template: "BinSum", params: [4, 2] },
}, (calculators) => {
    it("adds two 4-bit numbers", async () => {
        // 5 (0101) + 3 (1100 in LSB-first) → 8 (00010 in 5-bit LSB-first)
        // 5 = [1,0,1,0], 3 = [1,1,0,0]
        const w = await calculators.bs.calculate({
            in: [[1, 0, 1, 0], [1, 1, 0, 0]],
        });
        const out = w.array("main.out");
        // Sum = 5+3 = 8 = 01000 in LSB-first (5 bits for 2 ops of 4 bits: nbits(15*2)=5)
        const sum = out.reduce((acc, bit, i) => acc + bit * (1n << BigInt(i)), 0n);
        assert.equal(sum, 8n);
    });

    it("adds zero + zero = zero", async () => {
        const w = await calculators.bs.calculate({
            in: [[0, 0, 0, 0], [0, 0, 0, 0]],
        });
        const out = w.array("main.out");
        const sum = out.reduce((acc, bit, i) => acc + bit * (1n << BigInt(i)), 0n);
        assert.equal(sum, 0n);
    });

    it("max values: 15 + 15 = 30", async () => {
        const w = await calculators.bs.calculate({
            in: [[1, 1, 1, 1], [1, 1, 1, 1]],
        });
        const out = w.array("main.out");
        const sum = out.reduce((acc, bit, i) => acc + bit * (1n << BigInt(i)), 0n);
        assert.equal(sum, 30n);
    });
});
