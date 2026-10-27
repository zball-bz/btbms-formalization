import BTBMS

/-! Run by `checks/lock/check.sh`. `lock.py` pins the locked inputs by hash; this file pins the
elaborated statements and the exported theorems (T-019 review):

* the Prop definitions are the types reviewed in T-014 and signed off at G2 (`rfl`);
* `mainTheorem` and `paperTheorem` are theorems whose stored type is *syntactically*
  `MainTheorem.{u}` / `PaperTheorem.{u}` for their single universe parameter `u`. The stored
  type is compared, never an elaborated term, so no coercion can be inserted;
* every module in the import closure has plain identifier components, so Lake reads each source
  from its standard path inside a tree that `lock.py` hashes (no `«..»`, `«.lake»`, separators);
* no declaration of the `BTBMS` library is an `axiom`, and the exported theorems use no axioms
  beyond `propext`, `Classical.choice`, `Quot.sound` and (until the proof is complete)
  `sorryAx`. With `BTBMS_FINAL=1`, `sorryAx` is rejected too. -/

namespace BTBMS

universe u

example : MainTheorem.{u} =
    ((∀ n : Nat, ∃ κ : Cardinal.{u}, IsWeaklyMahlo n κ) → IsWellOrder Std Std.lt) := rfl
example : PaperTheorem.{u} =
    ((∀ n : Nat, ∃ κ : Cardinal.{u}, IsMahlo n κ) → IsWellOrder Std Std.lt) := rfl

end BTBMS

/-- A module name whose every component is a plain identifier (no path manipulation). -/
def plainModuleName : Lean.Name → Bool
  | .anonymous => true
  | .str p s => plainModuleName p && !s.isEmpty && !s.front.isDigit &&
      s.all fun c => c.isAlphanum || c == '_' || c == '\''
  | .num _ _ => false

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let final := (← IO.getEnv "BTBMS_FINAL") == some "1"
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  let allowed := if final then standard else ``sorryAx :: standard
  let mods := env.header.moduleNames
  for m in mods do
    unless plainModuleName m do throwError "unsupported module name in the import closure: {m}"
  for (n, ci) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? n | continue
    if (`BTBMS).isPrefixOf mods[idx.toNat]! then
      if let .axiomInfo _ := ci then throwError "the BTBMS library declares an axiom: {n}"
  for (thm, stmt) in [(``BTBMS.mainTheorem, ``BTBMS.MainTheorem),
                      (``BTBMS.paperTheorem, ``BTBMS.PaperTheorem)] do
    let some ci := env.find? thm | throwError "{thm} is missing"
    let .thmInfo _ := ci | throwError "{thm} is not a theorem"
    let exact : Bool := match ci.levelParams with
      | [v] => ci.type == .const stmt [.param v]
      | _ => false
    unless exact do
      throwError "{thm} : {ci.type} (universe params {ci.levelParams}); expected exactly {stmt}.\{u}"
    let axioms ← collectAxioms thm
    let bad := axioms.filter (!allowed.contains ·)
    unless bad.isEmpty do throwError "{thm} depends on unapproved axioms {bad}"
    let status := if axioms.contains ``sorryAx then "incomplete (sorryAx)" else "complete"
    IO.println s!"{thm}: type exact; axioms {axioms.toList}; proof {status}"
