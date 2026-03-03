import { assert } from "chai";
import { compile_and_count, type CircuitDef } from "../helpers.js";

describe("@slow BigMultModP CRT constraint comparison", function () {
    this.timeout(0);

    it("CRT has fewer constraints than schoolbook (n=4, k=2)", async () => {
        const schoolbook: CircuitDef = {
            path: "arithmetic/bigint.circom",
            template: "BigMultModP",
            params: [4, 2],
        };
        const crt: CircuitDef = {
            path: "arithmetic/bigint_crt.circom",
            template: "BigMultModP_CRT",
            params: [4, 2],
        };

        const [sbCount, crtCount] = await Promise.all([
            compile_and_count(schoolbook),
            compile_and_count(crt),
        ]);

        console.log(`    BigMultModP(4,2):     ${sbCount} constraints`);
        console.log(`    BigMultModP_CRT(4,2): ${crtCount} constraints`);
        console.log(`    Savings: ${((1 - crtCount / sbCount) * 100).toFixed(1)}%`);

        assert.isBelow(crtCount, sbCount, "CRT should have fewer constraints");
    });

    it("CRT has fewer constraints than schoolbook (n=8, k=4)", async () => {
        const schoolbook: CircuitDef = {
            path: "arithmetic/bigint.circom",
            template: "BigMultModP",
            params: [8, 4],
        };
        const crt: CircuitDef = {
            path: "arithmetic/bigint_crt.circom",
            template: "BigMultModP_CRT",
            params: [8, 4],
        };

        const [sbCount, crtCount] = await Promise.all([
            compile_and_count(schoolbook),
            compile_and_count(crt),
        ]);

        console.log(`    BigMultModP(8,4):     ${sbCount} constraints`);
        console.log(`    BigMultModP_CRT(8,4): ${crtCount} constraints`);
        console.log(`    Savings: ${((1 - crtCount / sbCount) * 100).toFixed(1)}%`);

        assert.isBelow(crtCount, sbCount, "CRT should have fewer constraints");
    });

    it("nocanon has fewer constraints than canonical CRT (n=8, k=4)", async () => {
        const canonical: CircuitDef = {
            path: "arithmetic/bigint_crt.circom",
            template: "BigMultModP_CRT",
            params: [8, 4],
        };
        const nocanon: CircuitDef = {
            path: "arithmetic/bigint_crt.circom",
            template: "BigMultModP_CRT_nocanon",
            params: [8, 4],
        };

        const [canonCount, nocanonCount] = await Promise.all([
            compile_and_count(canonical),
            compile_and_count(nocanon),
        ]);

        console.log(`    BigMultModP_CRT(8,4):         ${canonCount} constraints`);
        console.log(`    BigMultModP_CRT_nocanon(8,4):  ${nocanonCount} constraints`);
        console.log(`    BigLessThan savings: ${canonCount - nocanonCount} constraints`);

        assert.isBelow(nocanonCount, canonCount, "nocanon should have fewer constraints");
    });
});
