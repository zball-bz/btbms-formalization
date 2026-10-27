#!/usr/bin/env node
// Packaged Codex reference/graph checks. Passing bounded checks is not proof.
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import * as P from './ref-paper.mjs';
import {loadReference} from './ref-loader.mjs';
import {parseGraph, canon, mappedGraphs} from './occurrence-graph.mjs';
import {standardTargets, graphFixtures} from './fixtures.mjs';

const same = (a, b) => JSON.stringify(a) === JSON.stringify(b);
const digest = value => crypto.createHash('sha256').update(JSON.stringify(value)).digest('hex');
const maxFailures = 8;

function argumentsFrom(argv) {
  const name = argv[0];
  if (!['reference-diff', 'occurrence-graph'].includes(name)) throw new Error('Unknown JS check name');
  const options = {};
  for (let i = 1; i < argv.length; i += 2) {
    if (!['--config', '--output'].includes(argv[i]) || !argv[i + 1] || options[argv[i]]) {
      throw new Error('Usage: run_checks.mjs CHECK --config FILE --output FILE');
    }
    options[argv[i]] = argv[i + 1];
  }
  if (!options['--config'] || !options['--output']) throw new Error('Both --config and --output are required');
  return {name, configPath: options['--config'], outputPath: options['--output']};
}

function validateLimits(name, limits) {
  const keys = name === 'reference-diff'
    ? ['max_seed', 'seed_tests_max', 'max_parameter', 'max_size', 'max_states', 'max_processed', 'targeted_max_parameter']
    : ['max_parameter', 'max_states', 'fixture_max_parameter'];
  for (const key of keys) {
    if (!Number.isSafeInteger(limits[key]) || limits[key] < 0) throw new Error(`Invalid limit ${key}`);
  }
  if (!limits.max_states || (name === 'reference-diff' && (!limits.max_processed || !limits.max_size))) {
    throw new Error('State, processing and size limits must be positive');
  }
}

function reportFor(name) {
  return {check: name, status: 'pass', counts: {}, failures: [], observations: {}};
}
function inc(report, key, n = 1) {
  report.counts[key] = (report.counts[key] ?? 0) + n;
}
function fail(report, kind, details = {}) {
  inc(report, 'failures_total');
  report.status = 'fail';
  if (report.failures.length < maxFailures) report.failures.push({kind, ...details});
}
function runCase(report, name, action, details = {}) {
  try { return action(); }
  catch (error) {
    fail(report, 'exception', {case: name, ...details, message: String(error.message).slice(0, 1500)});
    return undefined;
  }
}
function referenceStep(R, E, n) {
  return P.fromRef(R.BTBM.FS(P.toRef(E), n));
}

function compareOperation(report, R, E, n, category, name, witness) {
  inc(report, `${category}_operation_comparisons`);
  const details = {case: name, n, input: E, ...(witness ? {witness} : {})};
  return runCase(report, name, () => {
    const actual = referenceStep(R, E, n), expected = P.fs(E, n);
    if (!same(actual, expected)) fail(report, 'operation-mismatch', {
      ...details, paper_output_sha256: digest(expected), reference_output_sha256: digest(actual),
    });
    if (!(P.cmp(expected, E) < 0) || !(P.cmp(actual, E) < 0)) {
      fail(report, 'nondecreasing-operation', details);
    } else inc(report, 'strict_decreases');
    return expected;
  }, details);
}

function standardTarget(report, R, target) {
  let E = P.seed(target.witness[0]);
  for (const n of target.witness.slice(1)) {
    const next = compareOperation(report, R, E, n, 'witness', target.name, target.witness);
    if (next === undefined) return undefined;
    E = next;
  }
  return E;
}

function scanProperties(E) {
  const s = P.stop(E);
  if (s.branch === 'special') {
    return {special_nonempty_prefix: s.route[s.l - 1].at(-1).length > 1};
  }
  if (s.branch !== 'ordinary') return {};
  const {route, r, t, Q} = s;
  let left = 0, j = 0;
  while (r >= left + route[j].length) { left += route[j].length; j++; }
  const F = route[j], i = r - left, column = F[i];
  let a = 0, b = 0;
  const signs = [];
  while (a < column.length && b < Q.length) {
    const sign = P.cmp(P.key(column[a][1], r), P.key(Q[b][1], t));
    signs.push(sign);
    if (sign <= 0) a++;
    if (sign >= 0) b++;
  }
  return {
    nonempty_query: Q.length > 0,
    owner_root: i === F.length - 1,
    equal_key: signs.includes(0),
    exhausted_nonowner: i !== F.length - 1 && column.length > 0 && a === column.length,
    source_only: signs.includes(-1), query_only: signs.includes(1),
  };
}

function checkExpectedDomains(report, R) {
  const cases = [
    {name: 'empty n=0', E: [], n: 0, error: 'empty has no operation', result: []},
    {name: 'empty n=2', E: [], n: 2, error: 'empty has no operation', result: []},
    {name: 'internal empty column n=0', E: [[], [[0, [[]]]]], n: 0, error: 'internal empty column', result: [[]]},
    {name: 'internal empty column n=1', E: [[], [[0, [[]]]]], n: 1, error: 'internal empty column', result: [[], []]},
  ];
  report.observations.expected_domain_differences = [];
  for (const item of cases) {
    inc(report, 'expected_domain_checks');
    runCase(report, item.name, () => {
      let error = null;
      try { P.fs(item.E, item.n); } catch (e) { error = e.message; }
      const result = referenceStep(R, item.E, item.n);
      const ok = error === item.error && same(result, item.result);
      if (!ok) fail(report, 'expected-domain-behavior-changed', {case: item.name, input: item.E, n: item.n, paper_error: error, reference_result: result});
      report.observations.expected_domain_differences.push({case: item.name, passed: ok});
    });
  }
}

function referenceDiff(config, R, report) {
  // Never let a failed regeneration leave a previous successful state's artifact.
  const statesPath = path.join(config.build_dir, 'ref-states.json');
  fs.rmSync(statesPath, {force: true});
  const limits = config.limits['reference-diff'];
  const seedResults = [];
  for (let m = 0; m <= limits.seed_tests_max; m++) {
    inc(report, 'seed_comparisons');
    runCase(report, `seed ${m}`, () => {
      const equal = same(P.seed(m), P.fromRef(R.infinity_FS(m)));
      if (!equal) fail(report, 'seed-mismatch', {m});
      seedResults.push({m, equal});
    });
  }
  report.observations.seeds = seedResults;
  checkExpectedDomains(report, R);
  const basics = [
    {name: 'one empty outer column', E: [[]], n: 0},
    {name: 'two empty outer columns', E: [[], []], n: 3},
    {name: 'depth zero ordinary n=0', E: P.seed(1), n: 0},
    {name: 'depth zero ordinary n=3', E: P.seed(1), n: 3},
    {name: 'special empty P n=0', E: P.seed(2), n: 0},
    {name: 'special empty P n=2', E: P.seed(2), n: 2},
    {name: 'special nonempty P outside H', E: [[], [[0, []], [0, [[[1, []]]]]]], n: 0},
  ];
  for (const item of basics) compareOperation(report, R, item.E, item.n, 'basic', item.name);
  report.observations.targeted_cases = [];
  for (const target of standardTargets) {
    const E = standardTarget(report, R, target);
    if (E === undefined) continue;
    const covered = Boolean(scanProperties(E)[target.property]);
    if (!covered) fail(report, 'targeted-case-lost-coverage', {case: target.name, witness: target.witness});
    for (let n = 0; n <= limits.targeted_max_parameter; n++) {
      compareOperation(report, R, E, n, 'targeted', target.name, target.witness);
    }
    report.observations.targeted_cases.push({name: target.name, witness: target.witness, property: target.property, covered});
  }

  const states = [], seen = new Set();
  function add(E, witness) {
    const key = JSON.stringify(E);
    if (P.size(E) <= limits.max_size && !seen.has(key) && states.length < limits.max_states) {
      seen.add(key); states.push({E, witness});
    }
  }
  for (let m = 0; m <= limits.max_seed; m++) add(P.seed(m), [m]);
  let processed = 0;
  for (let cursor = 0; cursor < states.length && cursor < limits.max_processed; cursor++) {
    const {E, witness} = states[cursor];
    processed++;
    if (!E.length) { inc(report, 'empty_states_skipped'); continue; }
    const {branch} = P.stop(E);
    inc(report, `generated_${branch}_inputs`);
    for (let n = 0; n <= limits.max_parameter; n++) {
      const next = compareOperation(report, R, E, n, 'generated', 'BFS', witness);
      if (next !== undefined) add(next, [...witness, n]);
    }
    if ((report.counts.failures_total ?? 0) >= maxFailures) break;
  }
  report.counts.stored_states = states.length;
  report.counts.processed_states = processed;
  report.counts.queued_states = Math.max(0, states.length - processed);
  for (let i = 0; i < states.length; i++) {
    const E = states[i].E, F = states[(i * 997 + 71) % states.length].E;
    runCase(report, 'order/key comparison', () => {
      const c = P.cmp(E, F), word = P.cmp(P.word(E), P.word(F));
      const reference = Math.sign(R.compare(P.toRef(E), P.toRef(F)));
      inc(report, 'syntax_order_comparisons'); inc(report, 'word_order_comparisons');
      if (c !== word || c !== reference) fail(report, 'order-mismatch', {i, E, F, syntax: c, word, reference});
      const host = i % 12;
      const key = P.cmp(P.key(E, host), P.key(F, host));
      const refKey = Math.sign(R.height_compare(R.to_height(P.toRef(E), host), R.to_height(P.toRef(F), host)));
      inc(report, 'relative_key_comparisons');
      if (key !== c || refKey !== c) fail(report, 'relative-key-mismatch', {i, E, F, host, syntax: c, key, reference: refKey});
    });
    if ((report.counts.failures_total ?? 0) >= maxFailures) break;
  }
  const artifact = {schema_version: 1, mode: config.mode, limits, status: report.status, states};
  fs.writeFileSync(statesPath, JSON.stringify(artifact) + '\n');
  report.observations.generated_states_sha256 = crypto.createHash('sha256').update(fs.readFileSync(statesPath)).digest('hex');
}

function graphCheck(config, R, report) {
  const limits = config.limits['occurrence-graph'];
  const statesPath = path.join(config.build_dir, 'ref-states.json');
  const stateBytes = fs.readFileSync(statesPath);
  const artifact = JSON.parse(stateBytes);
  if (artifact.schema_version !== 1 || artifact.mode !== config.mode || artifact.status !== 'pass'
      || !same(artifact.limits, config.limits['reference-diff']) || !Array.isArray(artifact.states)) {
    throw new Error('Missing, failed or stale reference-diff state artifact');
  }
  report.observations.generated_states_sha256 = crypto.createHash('sha256').update(stateBytes).digest('hex');
  report.counts.available_states = artifact.states.length;
  const coverage = {};
  function addCoverage(metadata, category) {
    const facts = {
      owner_root: metadata.ownerRoot,
      owner_root_with_entering_pair: metadata.ownerRoot && Boolean(metadata.enteringPair),
      empty_K: !metadata.K, empty_Q: !metadata.Q,
      consumed_root_blocks: Boolean(metadata.removed),
      entering_pair: Boolean(metadata.enteringPair),
      no_entering_pair: !metadata.enteringPair,
      copied_side_columns_above_stop: metadata.largePrintedSide.length > 0,
    };
    for (const [key, value] of Object.entries(facts)) if (value) {
      const name = `${category}_${key}`;
      coverage[name] = (coverage[name] ?? 0) + 1;
    }
  }
  function test(E, maxn, category, name, witness, requireLargeSide = false) {
    inc(report, `${category}_ordinary_inputs`);
    runCase(report, name, () => {
      const {results, persistentRoles, metadata} = mappedGraphs(E, maxn);
      addCoverage(metadata, category);
      if (requireLargeSide && !metadata.largePrintedSide.length) fail(report, 'fixture-lost-large-side-coverage', {case: name});
      for (let n = 0; n <= maxn; n++) {
        const output = referenceStep(R, E, n), parsed = parseGraph(output), actual = canon(parsed);
        inc(report, `${category}_graph_comparisons`);
        inc(report, `${category}_persistent_occurrence_comparisons`);
        if (n === 0) inc(report, 'zero_parameter_comparisons');
        const details = {case: name, input: E, n, ...(witness ? {witness} : {})};
        if (!same(parsed.roles.slice(0, metadata.T), persistentRoles)) fail(report, 'persistent-occurrence-mismatch', details);
        if (!same(actual, results[n])) fail(report, 'occurrence-graph-mismatch', {
          ...details, mapped_sha256: digest(results[n]), actual_sha256: digest(actual),
        });
      }
    }, {input: E, ...(witness ? {witness} : {})});
  }
  for (const item of artifact.states.slice(0, limits.max_states)) {
    inc(report, 'visited_states');
    if (P.stop(item.E).branch !== 'ordinary') { inc(report, 'nonordinary_states_skipped'); continue; }
    test(item.E, limits.max_parameter, 'generated', 'generated state', item.witness);
    if ((report.counts.failures_total ?? 0) >= maxFailures) break;
  }
  // Fixed targets survive even a tiny BFS limit and include equal-key/consumed
  // root blocks and both unilateral advances. Special targets are skipped here.
  for (const target of standardTargets) {
    let E = P.seed(target.witness[0]);
    for (const n of target.witness.slice(1)) E = P.fs(E, n);
    if (P.stop(E).branch === 'ordinary') test(E, limits.max_parameter, 'targeted', target.name, target.witness);
  }
  for (const fixture of graphFixtures()) {
    test(fixture.E, limits.fixture_max_parameter, 'fixture', fixture.name, undefined, true);
  }
  report.observations.coverage = coverage;
  report.observations.fixture_names = graphFixtures().map(item => item.name);
}

let outputPath;
let report;
try {
  const args = argumentsFrom(process.argv.slice(2));
  outputPath = args.outputPath;
  const config = JSON.parse(fs.readFileSync(args.configPath, 'utf8'));
  const limits = config.limits?.[args.name];
  if (!limits || !config.build_dir || !config.reference_dir) throw new Error('Incomplete runner config');
  validateLimits(args.name, limits);
  fs.mkdirSync(config.build_dir, {recursive: true});
  report = reportFor(args.name);
  const R = loadReference(config.reference_dir);
  if (args.name === 'reference-diff') referenceDiff(config, R, report);
  else graphCheck(config, R, report);
} catch (error) {
  report ??= reportFor(process.argv[2] ?? 'unknown');
  fail(report, 'worker-error', {message: String(error.message).slice(0, 1500)});
}
report.counts.failures_total ??= 0;
if (outputPath) {
  fs.mkdirSync(path.dirname(outputPath), {recursive: true});
  fs.writeFileSync(outputPath, JSON.stringify(report, null, 2) + '\n');
}
console.log(JSON.stringify({check: report.check, status: report.status, counts: report.counts}));
process.exitCode = report.status === 'pass' ? 0 : 1;
