import Lean
import Eliashberg

/-! 全库公理审计：对 `Eliashberg.*` 模块里的每一条常量收集其依赖的公理，
凡依赖标准三条（`propext`、`Classical.choice`、`Quot.sound`）之外者一律打印。
`sorryAx`（sorry）、`Lean.ofReduceBool`（native_decide）与任何用户公理都会在此暴露。 -/

open Lean in
def stdAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut total := 0
  let mut thms := 0
  let mut bad : Array (Name × Array Name) := #[]
  let mut axiomsSeen : Std.HashSet Name := {}
  let mut mods : Std.HashSet Name := {}
  for (n, ci) in env.constants.map₁.toList do
    match env.getModuleIdxFor? n with
    | none => pure ()
    | some idx =>
      let modName := env.header.moduleNames[idx.toNat]!
      if modName.getRoot == `Eliashberg then
        mods := mods.insert modName
        total := total + 1
        if ci matches .thmInfo _ then thms := thms + 1
        let axs ← collectAxioms n
        for a in axs do axiomsSeen := axiomsSeen.insert a
        let extra := axs.filter (fun a => !(stdAxioms.contains a))
        if !extra.isEmpty then bad := bad.push (n, extra)
  logInfo m!"CHECKED modules={mods.size} constants={total} theorems={thms}"
  logInfo m!"AXIOMS_SEEN {axiomsSeen.toList}"
  logInfo m!"NONSTANDARD_COUNT {bad.size}"
  for (n, axs) in bad do
    logInfo m!"NONSTANDARD {n} : {axs}"
