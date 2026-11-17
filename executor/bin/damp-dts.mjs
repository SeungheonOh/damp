#!/usr/bin/env node
// Usage: damp-dts.mjs <contract.json> [out.d.ts]
// Writes TypeScript declarations for a contract built by Damp.
import fs from 'node:fs';
import { generateDts } from '../src/dts.mjs';

const [input, output] = process.argv.slice(2);
if (!input) {
  console.error('usage: damp-dts.mjs <contract.json> [out.d.ts]');
  process.exit(2);
}
const text = generateDts(JSON.parse(fs.readFileSync(input, 'utf-8')));
if (output) fs.writeFileSync(output, text); else process.stdout.write(text);
