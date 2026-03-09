import { Build, SnarkJSSetup } from "@frozenfire/circom-build";

const n = 32;
const k = 8;

interface Variant {
    name: string;
    path: string;
    template: string;
}

const variants: Variant[] = [
    {
        name: "ScalarMult (windowed w=4 double-and-add)",
        path: "bench/ecdsa_scalarmul.circom",
        template: "ECDSAVerifyScalarMult",
    },
    {
        name: "GLV (129-bit endomorphism loop)",
        path: "bench/ecdsa_glv.circom",
        template: "ECDSAVerifyGLV",
    },
    {
        name: "HintedGLV (128-bit Pippenger MSM)",
        path: "bench/ecdsa_hinted_glv.circom",
        template: "ECDSAVerifyHintedGLV",
    },
    {
        name: "Eisenstein (68-bit MSM(4,68))",
        path: "bench/ecdsa_eisenstein.circom",
        template: "ECDSAVerifyEisenstein",
    },
];

async function compileAndCount(v: Variant): Promise<number> {
    console.log(`  Compiling ${v.template}...`);
    const build = new Build(v.path, v.template, [n, k], "2.2.2", []);
    const { command } = await build.compile();
    console.log(`  Compiled. Reading R1CS...`);
    const setup = new SnarkJSSetup(command.paths.r1cs);
    const details = await setup.r1cs_details;
    return details.nConstraints;
}

describe("ECDSA Constraint Count Benchmark", function () {
    this.timeout(0);

    for (const v of variants) {
        it(`${v.name}`, async () => {
            const count = await compileAndCount(v);
            console.log(`\n  ┌─────────────────────────────────────────┐`);
            console.log(`  │ ${v.name}`);
            console.log(`  │ Constraints: ${count.toLocaleString()}`);
            console.log(`  └─────────────────────────────────────────┘\n`);
        });
    }
});
