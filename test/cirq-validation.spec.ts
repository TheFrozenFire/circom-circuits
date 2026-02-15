import { expect } from "chai";
import { basename, dirname, resolve } from "path";
import {
    discoverBarrelFiles,
    loadBarrel,
    extractAstTemplates,
    extractVernacNames,
    fileExists,
    barrelLabel,
    discoverCircomFiles,
    discoverProofFiles,
} from "./cirq-loader.js";

describe(".cirq barrel validation", function () {
    const barrelPaths = discoverBarrelFiles();
    const barrels = barrelPaths.map((p) => loadBarrel(p));

    // ── 3a. File references exist ──────────────────────────────────

    describe("file references exist", function () {
        for (const { barrel, dir, cirqPath } of barrels) {
            const label = barrelLabel(cirqPath);

            it(`${label} → circuit: ${barrel.circuit}`, function () {
                expect(
                    fileExists(resolve(dir, barrel.circuit)),
                    `${barrel.circuit} not found in ${dir}`
                ).to.be.true;
            });

            it(`${label} → ast: ${barrel.ast}`, function () {
                expect(
                    fileExists(resolve(dir, barrel.ast)),
                    `${barrel.ast} not found in ${dir}`
                ).to.be.true;
            });

            it(`${label} → proof: ${barrel.proof}`, function () {
                expect(
                    fileExists(resolve(dir, barrel.proof)),
                    `${barrel.proof} not found in ${dir}`
                ).to.be.true;
            });
        }
    });

    // ── 3b. Template names match AST ───────────────────────────────

    describe("template names match AST", function () {
        for (const { barrel, dir, cirqPath } of barrels) {
            const label = barrelLabel(cirqPath);
            const templates = barrel.templates;
            if (!templates) continue;

            const astPath = resolve(dir, barrel.ast);
            if (!fileExists(astPath)) continue;

            const astNames = extractAstTemplates(astPath);

            for (const templateName of Object.keys(templates)) {
                it(`${label}: ${templateName} exists in AST`, function () {
                    expect(
                        astNames,
                        `Template "${templateName}" not found in ${barrel.ast}. AST has: [${astNames.join(", ")}]`
                    ).to.include(templateName);
                });
            }
        }
    });

    // ── 3c. Property names match proof file ────────────────────────

    describe("property names match proof file", function () {
        for (const { barrel, dir, cirqPath } of barrels) {
            const label = barrelLabel(cirqPath);
            const vPath = resolve(dir, barrel.proof);
            if (!fileExists(vPath)) continue;

            const vernac = extractVernacNames(vPath);
            const vernacNames = vernac.map((v) => v.name);

            const templates = barrel.templates ?? {};
            for (const [tplName, tpl] of Object.entries(templates)) {
                const props = tpl.properties ?? {};
                for (const propName of Object.keys(props)) {
                    it(`${label}: ${tplName}.${propName} exists in ${barrel.proof}`, function () {
                        expect(
                            vernacNames,
                            `Property "${propName}" not found in ${barrel.proof}`
                        ).to.include(propName);
                    });
                }
            }
        }
    });

    // ── 3d. Definitions match proof file ───────────────────────────

    describe("definitions match proof file", function () {
        for (const { barrel, dir, cirqPath } of barrels) {
            const label = barrelLabel(cirqPath);
            const defs = barrel.definitions;
            if (!defs) continue;

            const vPath = resolve(dir, barrel.proof);
            if (!fileExists(vPath)) continue;

            const vernac = extractVernacNames(vPath);
            const vernacNames = vernac.map((v) => v.name);

            for (const defName of Object.keys(defs)) {
                it(`${label}: definition ${defName} exists in ${barrel.proof}`, function () {
                    expect(
                        vernacNames,
                        `Definition "${defName}" not found in ${barrel.proof}`
                    ).to.include(defName);
                });
            }
        }
    });

    // ── 3e. Proof drift detection (reverse check) ──────────────────

    describe("proof drift detection", function () {
        for (const { barrel, dir, cirqPath } of barrels) {
            const label = barrelLabel(cirqPath);
            const vPath = resolve(dir, barrel.proof);
            if (!fileExists(vPath)) continue;

            const vernac = extractVernacNames(vPath);

            // Collect all names referenced in the barrel
            const barrelNames = new Set<string>();
            for (const tpl of Object.values(barrel.templates ?? {})) {
                for (const propName of Object.keys(tpl.properties ?? {})) {
                    barrelNames.add(propName);
                }
            }
            for (const defName of Object.keys(barrel.definitions ?? {})) {
                barrelNames.add(defName);
            }

            for (const { name, kind } of vernac) {
                it(`${label}: ${kind} ${name} listed in barrel`, function () {
                    expect(
                        barrelNames.has(name),
                        `${kind} "${name}" in ${barrel.proof} is not listed in ${barrelLabel(cirqPath)}`
                    ).to.be.true;
                });
            }
        }
    });

    // ── 3f. Barrel coverage ────────────────────────────────────────

    describe("barrel coverage", function () {
        const circomFiles = discoverCircomFiles();
        const proofFiles = discoverProofFiles();

        // Build set of .circom stems that have companion .v files
        // A .circom "foo.circom" in dir D has a companion .v if there's
        // a .v file in D whose lowercase matches
        const circomWithProofs: Array<{
            circomPath: string;
            vPath: string;
        }> = [];

        for (const vPath of proofFiles) {
            const vDir = dirname(vPath);
            const vBase = basename(vPath, ".v").toLowerCase();

            // Find matching .circom (case-insensitive stem match)
            const match = circomFiles.find(
                (c) =>
                    dirname(c) === vDir &&
                    basename(c, ".circom").toLowerCase() === vBase
            );
            if (match) {
                circomWithProofs.push({ circomPath: match, vPath });
            }
        }

        // Build set of directories+circuits covered by existing barrels
        const barrelCoverage = new Set<string>();
        for (const { barrel, dir } of barrels) {
            barrelCoverage.add(resolve(dir, barrel.circuit));
        }

        for (const { circomPath, vPath } of circomWithProofs) {
            const label = barrelLabel(circomPath);
            it(`${label} has a .cirq barrel`, function () {
                expect(
                    barrelCoverage.has(circomPath),
                    `${label} has proof ${barrelLabel(vPath)} but no .cirq barrel`
                ).to.be.true;
            });
        }
    });
});
