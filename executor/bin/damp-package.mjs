#!/usr/bin/env node
// Usage: damp-package.mjs <built contract dir> <output dir>
// Turns the output of `Damp.cli --keys` into a directory midnight-js can load.
import { packageContract } from '../src/package.mjs';

const [src, out] = process.argv.slice(2);
if (!src || !out) {
  console.error('usage: damp-package.mjs <built contract dir> <output dir>');
  process.exit(2);
}
try {
  const { spec } = packageContract(src, out);
  console.log(`${spec.name}: packaged to ${out}`);
} catch (e) {
  console.error(e instanceof Error ? e.message : String(e));
  process.exit(1);
}
