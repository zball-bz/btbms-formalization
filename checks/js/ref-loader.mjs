// The unlicensed reference is read only from the runner's ignored runtime copy.
// No upstream TypeScript is included in this tracked module.
import fs from 'node:fs';
import path from 'node:path';
import vm from 'node:vm';
import {stripTypeScriptTypes} from 'node:module';

export function loadReference(referenceDir) {
  const read = relative => fs.readFileSync(path.join(referenceDir, relative), 'utf8');
  const source = read('src/notations/BM-like/BTBM.ts');
  const utils = read('src/utils.ts');
  const variants = read('src/notations/notation_utils.ts');
  // Preserve the exact comparator and wrapper implementations. The remaining
  // utility classes are unrelated and include syntax unsupported in strip mode.
  const utilityEnd = utils.indexOf('/** 以 display');
  const variantStart = variants.indexOf('export function FS_default_LNZ_variant');
  if (utilityEnd < 0 || variantStart < 0) {
    throw new Error('Pinned reference extraction markers are missing');
  }
  const noImports = source.replace(/^import\s*\{[\s\S]*?\}\s*from\s*['"][^'"]+['"];\s*/gm, '');
  const merged = [utils.slice(0, utilityEnd), variants.slice(variantStart), noImports]
    .join('\n').replace(/\bexport\s+/g, '');
  const js = stripTypeScriptTypes(merged) + '\nglobalThis.reference = {BTBM, FS, infinity_FS, compare, to_height, height_compare, tail_layer, root_appending_start, is_special, display, from_display};';
  // This hides ordinary Node APIs from the evaluated source; vm is not claimed
  // to be a security boundary. The runner verifies the pinned source SHA256s.
  const context = vm.createContext({});
  vm.runInContext(js, context, {timeout: 5000});
  return context.reference;
}
