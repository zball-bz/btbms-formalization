import BTBMS.Expansion
import Lean.Data.Json

/-! Differential test: `BTBMS.expand` and `BTBMS.seed` against cases produced by the
reference `BTBM.ts` (`checks/lean/gen-cases.mjs`). Not part of the statement. -/

open Lean BTBMS

partial def forestOfJson (j : Json) : Except String Forest := do
  let cols ← j.getArr?
  let cs ← cols.toList.mapM fun c => do
    let es ← c.getArr?
    es.toList.mapM fun e => do
      let v ← e.getObjValAs? Nat "value"
      let h ← forestOfJson (← e.getObjVal? "height")
      pure (v, h)
  pure (.node cs)

partial def ser : Forest → String
  | .node cols => "[" ++ ",".intercalate (cols.map fun c =>
      "[" ++ ",".intercalate (c.map fun (p, h) => "(" ++ toString p ++ "," ++ ser h ++ ")") ++ "]") ++ "]"

def main (args : List String) : IO UInt32 := do
  let some path := args.head? | IO.eprintln "usage: difftest CASES.jsonl"; return 2
  let mut total := 0
  let mut bad := 0
  for line in (← IO.FS.lines path) do
    if line.isEmpty then continue
    let j ← IO.ofExcept (Json.parse line)
    if let .ok m := j.getObjValAs? Nat "seed" then
      total := total + 1
      let e ← IO.ofExcept (forestOfJson (← IO.ofExcept (j.getObjVal? "expr")))
      if ser (seed m) != ser e then
        bad := bad + 1; IO.println s!"SEED MISMATCH m={m}"
      continue
    if let .ok c := j.getObjValAs? Int "cmp" then
      total := total + 1
      let a ← IO.ofExcept (forestOfJson (← IO.ofExcept (j.getObjVal? "a")))
      let b ← IO.ofExcept (forestOfJson (← IO.ofExcept (j.getObjVal? "b")))
      let r ← IO.ofExcept (j.getObjValAs? Nat "r")
      let kc ← IO.ofExcept (j.getObjValAs? Int "keycmp")
      let sgn : Ordering → Int := fun | .lt => -1 | .eq => 0 | .gt => 1
      let ok := sgn (Tree.cmp compare a b) == c && decide (a < b) == (c == -1) &&
        sgn (keyCmp (relKey r a) (relKey r b)) == kc
      if !ok then
        bad := bad + 1
        if bad ≤ 5 then IO.println s!"ORDER MISMATCH a={ser a} b={ser b} r={r} cmp={c} keycmp={kc}"
      continue
    let e ← IO.ofExcept (forestOfJson (← IO.ofExcept (j.getObjVal? "in")))
    let n ← IO.ofExcept (j.getObjValAs? Nat "n")
    let expected : Option Forest ← match j.getObjVal? "out" with
      | .ok .null => pure none
      | .ok o => pure (some (← IO.ofExcept (forestOfJson o)))
      | .error err => throw (IO.userError err)
    total := total + 1
    let got := expand e n
    if got.map ser != expected.map ser then
      bad := bad + 1
      if bad ≤ 5 then
        IO.println s!"MISMATCH n={n} in={ser e}\n  expected={expected.map ser}\n  got     ={got.map ser}"
  -- seeds against the first cases' inputs are covered by the generator; check the order too
  IO.println s!"cases={total} mismatches={bad}"
  return if bad == 0 then 0 else 1
