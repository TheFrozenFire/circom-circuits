import { Build, SnarkJSSetup, type R1CSDetails } from "@frozenfire/circom-build";
import { Witness, SymbolReader, type SymbolMap } from "@frozenfire/circom-witness";
import { readFile } from "fs/promises";

export type CircuitDef = {
    path: string;
    template: string;
    params?: number[];
    publicInputs?: string[];
};

/**
 * Describe a test suite for one or more circuits. Compiles each circuit
 * in a `before()` hook and provides Witness calculators to the test body.
 *
 * Usage:
 *   describe_circuit("Name", {
 *       calc: { path: "module/file.circom", template: "Template", params: [4] },
 *   }, (calculators) => {
 *       it("works", async () => {
 *           const w = await calculators.calc.calculate({ in: [1, 2] });
 *           assert.equal(w.value("main.out"), 3n);
 *       });
 *   });
 */
/** Per-build timeout in milliseconds. Default: 60 seconds. */
export let COMPILE_TIMEOUT_MS = 60_000;

/**
 * Compile a circuit and return its R1CS constraint count.
 * Rejects if compilation exceeds COMPILE_TIMEOUT_MS.
 */
export async function compile_and_count(def: CircuitDef): Promise<number> {
    const build = new Build(
        def.path,
        def.template,
        def.params ?? [],
        "2.2.2",
        def.publicInputs ?? []
    );

    const timeout = new Promise<never>((_, reject) =>
        setTimeout(() => reject(new Error(
            `compile_and_count timed out after ${COMPILE_TIMEOUT_MS}ms: ${def.template}(${(def.params ?? []).join(",")})`
        )), COMPILE_TIMEOUT_MS)
    );

    const compile = (async () => {
        const { command } = await build.compile();
        const setup = new SnarkJSSetup(command.paths.r1cs);
        const details = await setup.r1cs_details;
        return details.nConstraints;
    })();

    return Promise.race([compile, timeout]);
}

/**
 * Compile a circuit and return its R1CS details + symbol map for analysis.
 * Rejects if compilation exceeds COMPILE_TIMEOUT_MS.
 */
export async function compile_and_analyze(def: CircuitDef): Promise<{
    details: R1CSDetails;
    symbols: SymbolMap;
}> {
    const build = new Build(
        def.path,
        def.template,
        def.params ?? [],
        "2.2.2",
        def.publicInputs ?? []
    );

    const timeout = new Promise<never>((_, reject) =>
        setTimeout(() => reject(new Error(
            `compile_and_analyze timed out after ${COMPILE_TIMEOUT_MS}ms: ${def.template}(${(def.params ?? []).join(",")})`
        )), COMPILE_TIMEOUT_MS)
    );

    const compile = (async () => {
        const { command } = await build.compile();
        const setup = new SnarkJSSetup(command.paths.r1cs);
        const details = await setup.r1cs_details;
        const symContent = await readFile(command.paths.sym, "utf-8");
        const symbols = new SymbolReader(symContent).readSymbolMap();
        return { details, symbols };
    })();

    return Promise.race([compile, timeout]);
}

export function describe_circuit(
    name: string,
    circuits: Record<string, CircuitDef>,
    fn: (calculators: Record<string, Witness>) => void
) {
    describe(name, function () {
        const calculators: Record<string, Witness> = {};

        before(async function () {
            this.timeout(0);

            for (const [key, def] of Object.entries(circuits)) {
                const build = new Build(
                    def.path,
                    def.template,
                    def.params ?? [],
                    "2.2.2",
                    def.publicInputs ?? []
                );

                const { command } = await build.compile();

                const wasmCode = await readFile(command.paths.wasm);
                const symContent = await readFile(command.paths.sym, "utf-8");
                const symbols = new SymbolReader(symContent).readSymbolMap();

                calculators[key] = new Witness(wasmCode, symbols);
            }
        });

        fn(calculators);
    });
}
