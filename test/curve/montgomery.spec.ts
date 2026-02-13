import { assert } from "chai";
import { describe_circuit } from "../helpers.js";
import { mod, modInv, babyAdd, BASE8_X, BASE8_Y, p } from "../babyjub_utils.js";

// Edwards → Montgomery conversion:
//   u = (1 + y) / (1 - y)
//   v = u / x
function edwardsToMontgomery(x: bigint, y: bigint): [bigint, bigint] {
    const u = mod((1n + y) * modInv(mod(1n + p - y)));
    const v = mod(u * modInv(x));
    return [u, v];
}

// Precompute Montgomery form of BASE8
const [mont_u, mont_v] = edwardsToMontgomery(BASE8_X, BASE8_Y);

// Precompute 2*BASE8 in Edwards
const [dbl_x, dbl_y] = babyAdd(BASE8_X, BASE8_Y, BASE8_X, BASE8_Y);
const [mont_dbl_u, mont_dbl_v] = edwardsToMontgomery(dbl_x, dbl_y);

// Precompute 3*BASE8 in Edwards
const [tri_x, tri_y] = babyAdd(dbl_x, dbl_y, BASE8_X, BASE8_Y);
const [mont_tri_u, mont_tri_v] = edwardsToMontgomery(tri_x, tri_y);

describe_circuit("Edwards2Montgomery", {
    e2m: { path: "curve/montgomery.circom", template: "Edwards2Montgomery" },
}, (calculators) => {
    it("converts BASE8 to Montgomery form", async () => {
        const w = await calculators.e2m.calculate({ in: [BASE8_X, BASE8_Y] });
        const out = w.array("main.out");
        assert.equal(out[0], mont_u);
        assert.equal(out[1], mont_v);
    });

    it("converts 2*BASE8 to Montgomery form", async () => {
        const w = await calculators.e2m.calculate({ in: [dbl_x, dbl_y] });
        const out = w.array("main.out");
        assert.equal(out[0], mont_dbl_u);
        assert.equal(out[1], mont_dbl_v);
    });
});

describe_circuit("Montgomery2Edwards", {
    m2e: { path: "curve/montgomery.circom", template: "Montgomery2Edwards" },
}, (calculators) => {
    it("converts Montgomery BASE8 back to Edwards", async () => {
        const w = await calculators.m2e.calculate({ in: [mont_u, mont_v] });
        const out = w.array("main.out");
        assert.equal(out[0], BASE8_X);
        assert.equal(out[1], BASE8_Y);
    });
});

describe_circuit("Edwards↔Montgomery round-trip", {
    e2m: { path: "curve/montgomery.circom", template: "Edwards2Montgomery" },
    m2e: { path: "curve/montgomery.circom", template: "Montgomery2Edwards" },
}, (calculators) => {
    it("round-trips BASE8 through both conversions", async () => {
        const w1 = await calculators.e2m.calculate({ in: [BASE8_X, BASE8_Y] });
        const mu = w1.value("main.out[0]");
        const mv = w1.value("main.out[1]");

        const w2 = await calculators.m2e.calculate({ in: [mu, mv] });
        assert.equal(w2.value("main.out[0]"), BASE8_X);
        assert.equal(w2.value("main.out[1]"), BASE8_Y);
    });

    it("round-trips 3*BASE8", async () => {
        const w1 = await calculators.e2m.calculate({ in: [tri_x, tri_y] });
        const mu = w1.value("main.out[0]");
        const mv = w1.value("main.out[1]");

        const w2 = await calculators.m2e.calculate({ in: [mu, mv] });
        assert.equal(w2.value("main.out[0]"), tri_x);
        assert.equal(w2.value("main.out[1]"), tri_y);
    });
});

describe_circuit("MontgomeryAdd", {
    add: { path: "curve/montgomery.circom", template: "MontgomeryAdd" },
}, (calculators) => {
    it("adds two Montgomery points (BASE8 + 2*BASE8 = 3*BASE8)", async () => {
        const w = await calculators.add.calculate({
            in1: [mont_u, mont_v],
            in2: [mont_dbl_u, mont_dbl_v],
        });
        const out = w.array("main.out");
        assert.equal(out[0], mont_tri_u);
        assert.equal(out[1], mont_tri_v);
    });
});

describe_circuit("MontgomeryDouble", {
    dbl: { path: "curve/montgomery.circom", template: "MontgomeryDouble" },
}, (calculators) => {
    it("doubles BASE8 in Montgomery form", async () => {
        const w = await calculators.dbl.calculate({ in: [mont_u, mont_v] });
        const out = w.array("main.out");
        assert.equal(out[0], mont_dbl_u);
        assert.equal(out[1], mont_dbl_v);
    });
});
