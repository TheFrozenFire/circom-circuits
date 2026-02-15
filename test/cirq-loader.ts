import { readFileSync, existsSync, readdirSync } from "fs";
import { resolve, dirname, relative, extname } from "path";
import { parse as parseYAML } from "yaml";
import { fileURLToPath } from "url";

// ── Types ──────────────────────────────────────────────────────────

export interface CirqProperty {
    type: string;
    statement: string;
    assumes?: string[];
    technique?: string;
    depends_on?: string[];
    placeholder?: boolean;
    notes?: string;
}

export interface CirqDefinition {
    type: string;
    statement?: string;
    signature?: string;
    description?: string;
    notes?: string;
}

export interface CirqTemplate {
    source?: string;
    constraints?: string[];
    notes?: string;
    properties?: Record<string, CirqProperty>;
}

export interface CirqBarrel {
    circuit: string;
    ast: string;
    proof: string;
    imports?: string[];
    templates?: Record<string, CirqTemplate>;
    definitions?: Record<string, CirqDefinition>;
    notes?: string;
}

export interface LoadedBarrel {
    barrel: CirqBarrel;
    cirqPath: string;
    dir: string;
}

// ── Utility functions ──────────────────────────────────────────────

const THIS_DIR = dirname(fileURLToPath(import.meta.url));
const ROOT = resolve(THIS_DIR, "..");

function findFiles(dir: string, suffix: string): string[] {
    const results: string[] = [];
    for (const entry of readdirSync(dir, { withFileTypes: true })) {
        const full = resolve(dir, entry.name);
        if (entry.isDirectory()) {
            results.push(...findFiles(full, suffix));
        } else if (entry.name.endsWith(suffix)) {
            results.push(full);
        }
    }
    return results.sort();
}

export function discoverBarrelFiles(): string[] {
    return findFiles(resolve(ROOT, "circuits"), ".cirq");
}

/**
 * Preprocess .cirq YAML text to quote values containing characters that
 * the YAML 1.2 parser (yaml v2) misinterprets:
 *   - `: ` in values → "nested mapping" error
 *   - `[]` inside flow sequences → "missing separator" error
 *   - `<>` inside flow sequences → invalid flow syntax
 *
 * Strategy: for every `key: value` line where value is a plain scalar
 * (not already quoted, not a block scalar indicator, not a YAML list),
 * wrap the value in double quotes if it contains problematic patterns.
 * For `assumes: [...]` lines with nested brackets, quote the whole value.
 */
function preprocessCirqYaml(raw: string): string {
    return raw.replace(/^(\s+\w+): (.+)$/gm, (line, prefix, value) => {
        const trimmed = value.trim();

        // Already quoted or is a block scalar indicator
        if (/^["']/.test(trimmed) || /^[>|]/.test(trimmed)) {
            return line;
        }

        // Flow sequence with nested brackets or <> — quote the whole thing
        if (trimmed.startsWith("[") && (/\[\]|<>/.test(trimmed))) {
            return `${prefix}: "${trimmed.replace(/"/g, '\\"')}"`;
        }

        // Plain scalar containing `: ` (would be parsed as nested mapping)
        if (/: /.test(trimmed) && !trimmed.startsWith("[") && !trimmed.startsWith("{")) {
            return `${prefix}: "${trimmed.replace(/"/g, '\\"')}"`;
        }

        return line;
    });
}

export function loadBarrel(cirqPath: string): LoadedBarrel {
    const raw = readFileSync(cirqPath, "utf-8");
    const barrel = parseYAML(preprocessCirqYaml(raw)) as CirqBarrel;
    return { barrel, cirqPath, dir: dirname(cirqPath) };
}

export function extractAstTemplates(jsonPath: string): string[] {
    const raw = readFileSync(jsonPath, "utf-8");
    const ast = JSON.parse(raw);
    const names: string[] = [];
    for (const def of ast.definitions ?? []) {
        if (def.Template?.name) {
            names.push(def.Template.name);
        }
    }
    return names;
}

export function extractVernacNames(
    vPath: string
): Array<{ name: string; kind: string }> {
    const content = readFileSync(vPath, "utf-8");
    const pattern =
        /^(Theorem|Lemma|Definition|Fixpoint|Fact)\s+(\w+)/gm;
    const results: Array<{ name: string; kind: string }> = [];
    let match: RegExpExecArray | null;
    while ((match = pattern.exec(content)) !== null) {
        results.push({ kind: match[1], name: match[2] });
    }
    return results;
}

export function resolveBarrelPath(
    dir: string,
    relativePath: string
): string {
    return resolve(dir, relativePath);
}

export function fileExists(filePath: string): boolean {
    return existsSync(filePath);
}

export function discoverTestFiles(): string[] {
    return findFiles(resolve(ROOT, "test"), ".spec.ts");
}

export function extractTestedTemplates(testPath: string): string[] {
    const content = readFileSync(testPath, "utf-8");
    const pattern = /describe_circuit\(\s*["']([^"']+)["']/g;
    const names: string[] = [];
    let match: RegExpExecArray | null;
    while ((match = pattern.exec(content)) !== null) {
        names.push(match[1]);
    }
    return names;
}

export function discoverCircomFiles(): string[] {
    return findFiles(resolve(ROOT, "circuits"), ".circom");
}

export function discoverProofFiles(): string[] {
    return findFiles(resolve(ROOT, "circuits"), ".v");
}

export function barrelLabel(cirqPath: string): string {
    return relative(ROOT, cirqPath);
}
