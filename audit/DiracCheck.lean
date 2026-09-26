import Lean
import Eliashberg

/-! 闸门 5：Theorem B 等号情形的「论文原话版」必须住在库内。

原先这一条是库外审计脚本 `audit/DiracBridge.lean`，单独 `lake env lean` 编译，
因此不在 `lake build` 与全库公理审计的覆盖范围内。2026-09-26 入库为
`Eliashberg/DiracBridge.lean`。

本闸门钉三件事，任一不满足即非零退出：

1. 两条定理存在且签名可解析（`#check`）；
2. 它们**落在 `Eliashberg.DiracBridge` 模块里**——这才是「入库」本身的判据。
   只 `#check` 的话，把定理挪回库外、由别处重新声明同名也能显绿；
3. 打印该模块的全部常量，让声明数对账有一手依据（不靠推算）。
-/

#check @Eliashberg.ae_sq_const_iff_dirac
#check @Eliashberg.theorem_2_1_iff_dirac

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let target : Name := `Eliashberg.DiracBridge
  for n in [``Eliashberg.ae_sq_const_iff_dirac, ``Eliashberg.theorem_2_1_iff_dirac] do
    match env.getModuleIdxFor? n with
    | none => throwError "{n} 不在任何已导入模块中"
    | some idx =>
      let m := env.header.moduleNames[idx.toNat]!
      unless m == target do
        throwError "{n} 落在模块 {m}，不是 {target}（定理已被挪出库？）"
  let mut inMod : Array Name := #[]
  for (n, _) in env.constants.map₁.toList do
    match env.getModuleIdxFor? n with
    | none => pure ()
    | some idx =>
      if env.header.moduleNames[idx.toNat]! == target then inMod := inMod.push n
  logInfo m!"DIRAC_BRIDGE_MODULE_CONSTANTS {inMod.size}"
  for n in inMod.qsort (fun a b => a.toString < b.toString) do
    logInfo m!"  {n}"
  logInfo "DIRAC_BRIDGE_IN_LIBRARY ok"
