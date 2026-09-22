import Eliashberg.Sandwich
import Eliashberg.PadBridge
import Eliashberg.ExpPad
import Eliashberg.ConeFinite

/-!
# Proposition 1.11 在 `ℓ²` 上：半群保锥

论文：

> **Proposition 1.11 (step 1: the semigroup preserves the cone).** Let `F` be admissible.
> Then `e^{tO[F]} C ⊂ C` for all `t ≥ 0`.

论文的证明用 (F5)（`e^{tO^{(N)}} → e^{tO[F]}` 的**强**收敛），mathlib 没有。
本文件改用**算子范数收敛**（`Sandwich.lean` 的 `sandwich_tendsto`：
`P_N O[F] P_N → O[F]`，界为 `2√τ_N`）与 `NormedSpace.exp` 在赋范环上的连续性，
完全绕开 (F5)。三段：

1. `S_N := P_N O[F] P_N → Op hF`（算子范数，`sandwich_tendsto`）；
2. 在 `ran P_N` 上 `S_N` 就是有限矩阵 `ON F`，故 `e^{tS_N}` 保 `C_N`（有限维 Prop 1.11）；
3. `C` 在 `ℓ²` 中闭（`InCone.of_tendsto`），故极限仍在锥内。

第 2 步的接口是 `ExpPad.lean` 的 `exp_padN`。
-/

namespace Eliashberg

open scoped BigOperators ENNReal Matrix
open Filter Topology

noncomputable section

/-- 逼近序列：`e^{t S_N}` 作用在 `x` 的截断上。 -/
private lemma tendsto_approx {f : ℕ → ℝ} (hf : L1 f) (t : ℝ) (x : H) :
    Tendsto (fun N => NormedSpace.exp (t • ((PNclm N).comp ((Op hf).comp (PNclm N))))
        (PN (extN (truncFn x N)) N)) atTop (𝓝 (NormedSpace.exp (t • Op hf) x)) := by
  letI : NormedAlgebra ℚ (H →L[ℝ] H) := NormedAlgebra.restrictScalars ℚ ℝ (H →L[ℝ] H)
  have hconv : Tendsto (fun N => (PNclm N).comp ((Op hf).comp (PNclm N))) atTop (𝓝 (Op hf)) :=
    sandwich_tendsto hf
  have hexpconv : Tendsto
      (fun N => NormedSpace.exp (t • ((PNclm N).comp ((Op hf).comp (PNclm N)))))
      atTop (𝓝 (NormedSpace.exp (t • Op hf))) :=
    (NormedSpace.exp_continuous.tendsto (t • Op hf)).comp (hconv.const_smul t)
  have hxN : Tendsto (fun N => PN (x : ℕ → ℝ) N) atTop (𝓝 x) := PN_tendsto x
  have hcont : Continuous (fun p : H × (H →L[ℝ] H) => p.2 p.1) :=
    ContinuousLinearMap.continuous₂ (ContinuousLinearMap.apply ℝ H)
  have h1 : Tendsto (fun N => NormedSpace.exp (t • ((PNclm N).comp ((Op hf).comp (PNclm N))))
      (PN (x : ℕ → ℝ) N)) atTop (𝓝 (NormedSpace.exp (t • Op hf) x)) := by
    have hpair : Tendsto (fun N => (PN (x : ℕ → ℝ) N,
        NormedSpace.exp (t • ((PNclm N).comp ((Op hf).comp (PNclm N))))))
        atTop (𝓝 (x, NormedSpace.exp (t • Op hf))) := by
      rw [Prod.tendsto_iff]
      exact ⟨hxN, hexpconv⟩
    exact (hcont.tendsto (x, NormedSpace.exp (t • Op hf))).comp hpair
  have hfun : (fun N => NormedSpace.exp (t • ((PNclm N).comp ((Op hf).comp (PNclm N))))
        (PN (extN (truncFn x N)) N))
      = (fun N => NormedSpace.exp (t • ((PNclm N).comp ((Op hf).comp (PNclm N))))
        (PN (x : ℕ → ℝ) N)) := by
    funext N
    rw [PN_extN_truncFn]
  rw [hfun]
  exact h1


/-- **Prop 1.11，`ℓ²` 版**：`F` admissible ⇒ `e^{tO[F]} C ⊂ C`（`t ≥ 0`）。

论文用 (F5) 的强收敛；本文件用算子范数收敛（`sandwich_tendsto`）加 `exp` 的连续性。
第 2 步（`e^{tS_N}` 在 `ran P_N` 上就是矩阵指数）由 `exp_padN` 提供，
其 `hpad` 前提正是 `sandwich_apply_pad`。 -/
theorem semigroup_preserves_cone {f : ℕ → ℝ} (hf : L1 f)
    (hanti : ∀ k, 1 ≤ k → f (k + 1) ≤ f k) (hpos : ∀ k, 1 ≤ k → 0 ≤ f k)
    (t : ℝ) (ht : 0 ≤ t) {x : H} (hx : InCone x) :
    InCone (NormedSpace.exp (t • Op hf) x) := by
  -- 每个 N：`e^{tS_N}` 保锥
  have hseq : ∀ N, InCone (NormedSpace.exp (t • ((PNclm N).comp ((Op hf).comp (PNclm N))))
      (PN (extN (truncFn x N)) N)) := by
    intro N
    rw [exp_padN hf N (sandwich_apply_pad hf N) (truncFn x N) t]
    exact padN_inCone_of_inConeN
      (exp_ON_preserves_cone' f hanti hpos (truncFn x N) (truncFn_inConeN hx N) t ht)
  exact InCone.of_tendsto hseq (tendsto_approx hf t x)

end

end Eliashberg
