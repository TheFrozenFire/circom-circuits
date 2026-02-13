import { assert } from "chai";
import { describe_circuit } from "./helpers.js";

describe_circuit("MultiMux1", {
    mux: { path: "mux.circom", template: "MultiMux1", params: [2] },
}, (calculators) => {
    it("selects channel 0 when s=0", async () => {
        // 2 channels, each with 2 options: c[0]=[10,20], c[1]=[30,40]
        // s=0 → out[0]=10, out[1]=30
        const w = await calculators.mux.calculate({
            c: [[10, 20], [30, 40]],
            s: 0,
        });
        assert.equal(w.value("main.out[0]"), 10n);
        assert.equal(w.value("main.out[1]"), 30n);
    });

    it("selects channel 1 when s=1", async () => {
        const w = await calculators.mux.calculate({
            c: [[10, 20], [30, 40]],
            s: 1,
        });
        assert.equal(w.value("main.out[0]"), 20n);
        assert.equal(w.value("main.out[1]"), 40n);
    });
});

describe_circuit("MultiMux3", {
    mux: { path: "mux.circom", template: "MultiMux3", params: [2] },
}, (calculators) => {
    // 2 channels, 8 options each. s[3] selects one of 8 slots.
    // c[channel][slot]
    const c0 = [100, 101, 102, 103, 104, 105, 106, 107];
    const c1 = [200, 201, 202, 203, 204, 205, 206, 207];

    for (let sel = 0; sel < 8; sel++) {
        const s0 = sel & 1;
        const s1 = (sel >> 1) & 1;
        const s2 = (sel >> 2) & 1;

        it(`selects slot ${sel} (s=[${s0},${s1},${s2}])`, async () => {
            const w = await calculators.mux.calculate({
                c: [c0, c1],
                s: [s0, s1, s2],
            });
            assert.equal(w.value("main.out[0]"), BigInt(c0[sel]));
            assert.equal(w.value("main.out[1]"), BigInt(c1[sel]));
        });
    }
});
