import { pipeline } from "@huggingface/transformers";
import { writeFile } from "fs/promises";
import { resolve, dirname } from "path";
import { fileURLToPath } from "url";

const __dirname = dirname(fileURLToPath(import.meta.url));

const SCALE = 1000;
const MODEL = "Xenova/all-MiniLM-L6-v2";

interface Sentence {
    id: string;
    text: string;
    group: string;
}

const sentences: Sentence[] = [
    { id: "cat_mat", text: "The cat sat on the mat", group: "animals" },
    { id: "kitten_rug", text: "A kitten rested on the rug", group: "animals" },
    { id: "ml_datasets", text: "Machine learning models require large datasets", group: "tech" },
    { id: "neural_gradient", text: "Neural networks are trained with gradient descent", group: "tech" },
    { id: "sun_mountains", text: "The sun sets behind the mountains", group: "nature" },
    { id: "sunset_hills", text: "A beautiful sunset over the hills", group: "nature" },
    { id: "stock_market", text: "The stock market closed higher today", group: "unrelated" },
    { id: "piano_sonata", text: "She played a sonata on the piano", group: "unrelated" },
    { id: "baked_bread", text: "Freshly baked bread filled the kitchen with aroma", group: "unrelated" },
];

function cosineSimilarity(a: number[], b: number[]): number {
    let dot = 0, normA = 0, normB = 0;
    for (let i = 0; i < a.length; i++) {
        dot += a[i] * b[i];
        normA += a[i] * a[i];
        normB += b[i] * b[i];
    }
    return dot / (Math.sqrt(normA) * Math.sqrt(normB));
}

async function main() {
    console.log(`Loading model: ${MODEL}...`);
    const extractor = await pipeline("feature-extraction", MODEL);

    console.log("Generating embeddings...");
    const floatEmbeddings: number[][] = [];

    for (const s of sentences) {
        const output = await extractor(s.text, { pooling: "mean", normalize: true });
        const embedding = Array.from(output.data as Float32Array);
        floatEmbeddings.push(embedding);
        console.log(`  ${s.id}: ${embedding.length} dims, norm=${Math.sqrt(embedding.reduce((s, v) => s + v * v, 0)).toFixed(4)}`);
    }

    const dimension = floatEmbeddings[0].length;
    console.log(`\nDimension: ${dimension}`);

    // Quantize: multiply by SCALE and round
    const quantized = floatEmbeddings.map(emb =>
        emb.map(v => Math.round(v * SCALE))
    );

    // Verify quantized values are in expected range
    for (let i = 0; i < quantized.length; i++) {
        const min = Math.min(...quantized[i]);
        const max = Math.max(...quantized[i]);
        console.log(`  ${sentences[i].id}: quantized range [${min}, ${max}]`);
    }

    // Compute pairwise cosine similarities from float embeddings
    const pairwiseSimilarities: { id_a: string; id_b: string; cosine: number }[] = [];
    for (let i = 0; i < sentences.length; i++) {
        for (let j = i + 1; j < sentences.length; j++) {
            const cos = cosineSimilarity(floatEmbeddings[i], floatEmbeddings[j]);
            pairwiseSimilarities.push({
                id_a: sentences[i].id,
                id_b: sentences[j].id,
                cosine: cos,
            });
        }
    }

    console.log("\nPairwise cosine similarities:");
    for (const p of pairwiseSimilarities) {
        console.log(`  ${p.id_a} <-> ${p.id_b}: ${p.cosine.toFixed(4)}`);
    }

    const fixture = {
        model: MODEL,
        dimension,
        scale: SCALE,
        sentences: sentences.map((s, i) => ({
            id: s.id,
            text: s.text,
            group: s.group,
            quantized: quantized[i],
        })),
        pairwise_similarities: pairwiseSimilarities,
    };

    const outPath = resolve(__dirname, "../test/fixtures/embeddings.json");
    await writeFile(outPath, JSON.stringify(fixture, null, 2) + "\n");
    console.log(`\nFixture written to: ${outPath}`);
}

main().catch(err => {
    console.error(err);
    process.exit(1);
});
