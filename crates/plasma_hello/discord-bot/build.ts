
const result = await Bun.build({
    entrypoints: ["./index.ts"],
    target: "browser",
    format: "esm",
    minify: false,
});

if (!result.success) {
    console.error("Build failed:");
    for (const log of result.logs) {
        console.error(log);
    }
    process.exit(1);
}

const output = await result.outputs[0]!.text();
// Write to stdout for capture
console.log(output);

export {}