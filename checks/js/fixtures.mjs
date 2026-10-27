// Small fixed witnesses ensure branch coverage independently of BFS limits.
export const standardTargets = [
  {name: 'nonempty-terminal-query-zero', witness: [2, 1], property: 'nonempty_query'},
  {name: 'owner-root-ordinary', witness: [3, 1], property: 'owner_root'},
  {name: 'equal-key-scan', witness: [2, 2, 2], property: 'equal_key'},
  {name: 'source-exhausted-nonowner-root', witness: [3, 1, 1, 2, 0, 1], property: 'exhausted_nonowner'},
  {name: 'standard-special-nonempty-P', witness: [3, 1, 1, 1, 1, 1], property: 'special_nonempty_prefix'},
  {name: 'source-only-scan-advance', witness: [3, 1, 1, 2, 1, 1, 1], property: 'source_only'},
  {name: 'query-only-scan-advance', witness: [3, 1], property: 'query_only'},
];

export function graphFixtures() {
  const tower = (first, last) => first > last ? [] : [[[first, tower(first + 1, last)]]];
  const large = tower(1, 2), deep = tower(1, 3);
  const tail = [[[1, []], [1, []]]];
  const twoColumnTail = [[[1, []]], [[1, []], [1, []]]];
  // These four inputs are admissible synthetic fixtures, not asserted standard.
  return [
    {name: 'empty query nonowner copies closed tower through column 4', E: [[], [[0, deep]], [[1, []]]]},
    {name: 'nonowner closed side column 3 exceeds stopping number 2', E: [[], [[0, large]], [[1, []], [1, []]]]},
    {name: 'owner root with unconsumed closed side above stopping number', E: [[], [[0, large], [0, tail]]]},
    {name: 'owner root with entering pair and closed side above stopping number', E: [[], [[0, deep], [0, twoColumnTail]]]},
  ];
}
