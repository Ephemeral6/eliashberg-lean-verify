/-
闸门：主定理的**传递依赖闭包**里不得出现 Conjecture 3.1。

读签名是不够的——`theorem_2_1` 的签名没有 `hcj`，但它若经由某条引理
间接用到 `theorem_2_1_of_conjecture`，签名上看不出来。这里让内核把
证明项的依赖闭包整个走一遍。
-/
import Eliashberg

open Lean Elab Command

/-- `n` 的传递依赖闭包（含自身）。 -/
partial def depsOf (env : Environment) (n : Name) : StateM NameSet Unit := do
  if (← get).contains n then return
  modify (·.insert n)
  match env.find? n with
  | none => return
  | some ci =>
    for c in ci.type.getUsedConstants do depsOf env c
    match ci.value? with
    | some v => for c in v.getUsedConstants do depsOf env c
    | none => return

#eval show CommandElabM Unit from do
  let env ← getEnv
  let conj : Name := ``Eliashberg.ConjectureThreeOne
  let bridge : Name := ``Eliashberg.theorem_2_1_of_conjecture

  -- 无条件主定理：不得依赖猜想
  let unconditional : List Name :=
    [``Eliashberg.theorem_2_1, ``Eliashberg.corollary_2_4_i,
     ``Eliashberg.lamM_sub_le, ``Eliashberg.Cinf_mem,
     ``Eliashberg.Tec_lt, ``Eliashberg.corollary_2_4_iii_Tc,
     ``Eliashberg.corollary_2_4_iii_Tec]
  for t in unconditional do
    let (_, deps) := (depsOf env t).run {}
    if deps.contains conj then
      throwError "{t} 的依赖闭包里出现 {conj}——主定理并非无条件！"
    if deps.contains bridge then
      throwError "{t} 依赖 {bridge}——主定理走了猜想桥！"
    logInfo m!"UNCOND ok {t}  依赖常数 {deps.size}"

  -- 对照：桥定理**应当**依赖猜想（否则这个闸门本身在空转）
  let (_, bdeps) := (depsOf env bridge).run {}
  unless bdeps.contains conj do
    throwError "{bridge} 竟不依赖 {conj}——闸门失效，反向检验没通过"
  logInfo m!"BRIDGE 依赖 {conj}，反向检验通过（依赖常数 {bdeps.size}）"

  logInfo "UNCONDITIONAL_MAIN_THEOREMS ok"
