#!/usr/bin/env bun
/**
 * CLI wrapper for the shared transform module.
 *
 * Usage:
 *   bun viz/scripts/transform.ts              # text to stdout (default)
 *   bun viz/scripts/transform.ts text         # text to stdout
 *   bun viz/scripts/transform.ts json         # json to stdout
 */

import { readFileSync } from 'fs';
import { join, dirname } from 'path';
import { transformTrace, renderText } from '../src/lib/transform';

const ROOT = join(dirname(new URL(import.meta.url).pathname), '..');
const INPUT = join(ROOT, 'src/lib/trace.json');

const mode = process.argv[2] ?? 'text';
const raw = JSON.parse(readFileSync(INPUT, 'utf-8'));
const result = transformTrace(raw);

if (mode === 'text') {
	console.log(renderText(result));
} else if (mode === 'json') {
	console.log(JSON.stringify(result, null, 2));
} else {
	console.error(`unknown mode: ${mode} (use 'text' or 'json')`);
	process.exit(1);
}
