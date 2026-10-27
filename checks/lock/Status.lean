import BTBMS

/-! Run by `scripts/lean-status.sh`. Prints one JSON array describing every declaration of the
`BTBMS` library: kind, module, whether its own statement or body contains `sorry`, and the axioms
it depends on transitively. The tracker derives Lean progress from this output only. -/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let mods := env.header.moduleNames
  let mut rows : Array Json := #[]
  for (n, ci) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := mods[idx.toNat]!
    unless (`BTBMS).isPrefixOf m do continue
    if n.isInternalDetail || isAuxRecursor env n || isNoConfusion env n ||
        Meta.isMatcherCore env n || isRecCore env n then continue
    let kind := match ci with
      | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .inductInfo _ => "inductive"
      | .ctorInfo _ => "ctor" | .axiomInfo _ => "axiom" | .opaqueInfo _ => "opaque"
      | _ => "other"
    if kind == "ctor" || kind == "other" then continue
    let value? := match ci with
      | .thmInfo t => some t.value | .defnInfo d => some d.value | _ => none
    let direct := ci.type.hasSorry || (value?.map Expr.hasSorry).getD false
    let axioms ← collectAxioms n
    rows := rows.push <| Json.mkObj [
      ("name", toJson n.toString), ("kind", toJson kind), ("module", toJson m.toString),
      ("direct_sorry", toJson direct),
      ("axioms", toJson ((axioms.map Name.toString).qsort (· < ·)))]
  IO.println (Json.arr (rows.qsort fun a b => a.compress < b.compress)).compress
