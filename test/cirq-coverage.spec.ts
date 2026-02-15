import {
    discoverBarrelFiles,
    loadBarrel,
    discoverTestFiles,
    extractTestedTemplates,
    barrelLabel,
} from "./cirq-loader.js";

describe(".cirq test coverage report", function () {
    const barrelPaths = discoverBarrelFiles();
    const barrels = barrelPaths.map((p) => loadBarrel(p));
    const testFiles = discoverTestFiles();

    // Build a set of all template names exercised by describe_circuit calls
    const testedTemplates = new Set<string>();
    for (const tf of testFiles) {
        for (const name of extractTestedTemplates(tf)) {
            testedTemplates.add(name);
        }
    }

    // ── 5a. Circuits with barrels but no test files ────────────────

    it("barrel-level coverage report", function () {
        const missing: string[] = [];

        for (const { barrel, cirqPath } of barrels) {
            const templates = barrel.templates ?? {};
            const templateNames = Object.keys(templates);
            const hasTest = templateNames.some((t) =>
                testedTemplates.has(t)
            );
            if (!hasTest && templateNames.length > 0) {
                missing.push(barrelLabel(cirqPath));
            }
        }

        const total = barrels.filter(
            (b) =>
                Object.keys(b.barrel.templates ?? {}).length > 0
        ).length;
        const covered = total - missing.length;

        console.log(
            `\n  Barrel-level coverage: ${covered}/${total} barrels have at least one tested template`
        );
        if (missing.length > 0) {
            console.log("  Barrels with NO test coverage:");
            for (const m of missing) {
                console.log(`    - ${m}`);
            }
        }
    });

    // ── 5b. Template-level test coverage ───────────────────────────

    it("template-level coverage report", function () {
        const allTemplates: string[] = [];
        const untested: Array<{ barrel: string; template: string }> = [];

        for (const { barrel, cirqPath } of barrels) {
            const templates = barrel.templates ?? {};
            for (const tplName of Object.keys(templates)) {
                allTemplates.push(tplName);
                if (!testedTemplates.has(tplName)) {
                    untested.push({
                        barrel: barrelLabel(cirqPath),
                        template: tplName,
                    });
                }
            }
        }

        const tested = allTemplates.length - untested.length;
        console.log(
            `\n  Template-level coverage: ${tested}/${allTemplates.length} templates tested`
        );
        if (untested.length > 0) {
            console.log("  Untested templates:");
            for (const { barrel, template } of untested) {
                console.log(`    - ${barrel}: ${template}`);
            }
        }
    });
});
