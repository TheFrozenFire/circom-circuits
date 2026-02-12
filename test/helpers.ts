import { Build } from "@frozenfire/circom-build";
import { Witness, SymbolReader } from "@frozenfire/circom-witness";
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
