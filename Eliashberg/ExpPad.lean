import Eliashberg.Compact
import Eliashberg.LemmaM
import Eliashberg.ConeFinite
import Eliashberg.PadBridge
set_option maxHeartbeats 4000000

/-!
# 指数与截断投影的交换：`e^{t•P_N O[f] P_N} (P_N x) = P_N (e^{t•O^{(N)}[f]} x)`（task-577）

设 `H := ℓ²(ℕ)`、`S := (P_Nclm N).comp ((Op hf).comp (PNclm N))`（`ℓ²` 上的截断压缩算子）、
`M := ON f`（`Fin N × Fin N` 实矩阵 `O^{(N)}[f]`），并设「零延拓 + 截断」

  `padCLM N : (Fin N → ℝ) →L[ℝ] H`,  `padCLM N w = P_N (extN w)`。

本文件的核心是一个**提升引理**：由假设

  `hpad : S (P_N (extN v)) = P_N (extN (M *ᵥ v))`   （一切 `v : Fin N → ℝ`）

推出算子指数与有限维矩阵指数相容：`e^{t•S} (P_N (extN v)) = P_N (extN (e^{t•M} *ᵥ v))`。

证明分四步（`exp_padN`）：

1. `pow_pad`：幂的提升 `(S^k) (P_N (extN v)) = P_N (extN ((M^k) *ᵥ v))`（对 `k` 归纳，用 `hpad`）；
2. `hasSum_left`：环 `H →L[ℝ] H` 上的指数级数经 `u ↦ u (padCLM N v)` 推到 `H`；
3. `hasSum_right`：矩阵环上的指数级数经 `A ↦ padCLM N (A *ᵥ v)` 推到 `H`；
4. 两边的第 `k` 项由 `pow_pad` + 幂的标量提取逐项相等，故由 `HasSum.unique` 得结论。

注意 `NormedAlgebra ℚ (H →L[ℝ] H)` 不能由类型类搜索合成（见 `L2Operator` 的注记），
但本文件走 `HasSum` 级数路线，**不需要**该实例。同样地，`H →L[ℝ] H` 上
`IsScalarTower ℝ _ _` 与 `SMulCommClass ℝ _ _` 也不可合成，故 `smul_pow` 在算子层
不可用，标量提取由 `op_smul_pow_apply` 手工给出。
-/

namespace Eliashberg

open scoped BigOperators ENNReal
open scoped Matrix.Norms.Operator Matrix
open Filter Topology NormedSpace

noncomputable section

variable {f : ℕ → ℝ}

/-! ### 一、`padCLM`：`w ↦ P_N (extN w)` 作为连续线性映射 -/

/-- `w ↦ ∑_{i : Fin N} e_i (w i)`，作为线性映射 `(Fin N → ℝ) →ₗ[ℝ] H`。 -/
def padL (N : ℕ) : (Fin N → ℝ) →ₗ[ℝ] H :=
  ∑ i : Fin N,
    (lp.singleContinuousLinearMap ℝ (fun _ : ℕ => ℝ) 2 (i : ℕ)).toLinearMap.comp
      (LinearMap.proj i)

/-- `padCLM N w := P_N (extN w) = ∑_{i : Fin N} e_i (w i)`，作为连续线性映射
（有限维空间上的线性映射自动连续）。 -/
def padCLM (N : ℕ) : (Fin N → ℝ) →L[ℝ] H :=
  LinearMap.toContinuousLinearMap (padL N)

lemma padCLM_apply (N : ℕ) (w : Fin N → ℝ) :
    padCLM N w = ∑ i : Fin N, lp.single 2 (i : ℕ) (w i) := by
  rw [padCLM, LinearMap.coe_toContinuousLinearMap', padL, LinearMap.sum_apply]
  apply Finset.sum_congr rfl; intro i _
  simp only [LinearMap.comp_apply, LinearMap.proj_apply, ContinuousLinearMap.coe_coe,
    lp.singleContinuousLinearMap_apply]

lemma padCLM_add (N : ℕ) (w w' : Fin N → ℝ) : padCLM N (w + w') = padCLM N w + padCLM N w' :=
  map_add _ _ _

lemma padCLM_smul (N : ℕ) (c : ℝ) (w : Fin N → ℝ) : padCLM N (c • w) = c • padCLM N w :=
  map_smul _ _ _

/-- `(padCLM N w)_n = 1_{n<N} w_n`。 -/
lemma padCLM_coord (N : ℕ) (w : Fin N → ℝ) (n : ℕ) :
    ((padCLM N w : H) : ℕ → ℝ) n = if h : n < N then w ⟨n, h⟩ else 0 := by
  rw [padCLM_apply, coeFn_sum_apply]
  simp only [lp.single_apply, Pi.single_apply]
  by_cases h : n < N
  · rw [dif_pos h, Finset.sum_eq_single ⟨n, h⟩]
    · rw [if_pos rfl]
    · intro i _ hi
      rw [if_neg]
      intro hc
      exact hi (Fin.ext hc.symm)
    · intro hnot
      exact absurd (Finset.mem_univ _) hnot
  · rw [dif_neg h, Finset.sum_eq_zero]
    intro i _
    rw [if_neg]
    intro hc
    exact absurd (hc ▸ i.isLt) h

/-- `padCLM N w = P_N (extN w)`（与 `PN` 的接口一致）。 -/
lemma padCLM_eq_PN (N : ℕ) (w : Fin N → ℝ) : padCLM N w = PN (extN w) N := by
  apply lp.ext
  funext n
  rw [padCLM_coord, PN_apply]
  split_ifs with h
  · unfold extN; rw [dite_eq_left h]
  · rfl

/-! ### 二、`A ↦ A *ᵥ v` 与 `A ↦ padCLM N (A *ᵥ v)` 作为连续线性映射 -/

/-- `A ↦ A *ᵥ v`，作为线性映射（对 `A` 线性）。 -/
def mulVecL (N : ℕ) (v : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ →ₗ[ℝ] (Fin N → ℝ) where
  toFun A := A *ᵥ v
  map_add' A B := Matrix.add_mulVec A B v
  map_smul' c A := Matrix.smul_mulVec c A v

/-- `A ↦ A *ᵥ v`，作为连续线性映射（有限维）。 -/
def mulVecCLM (N : ℕ) (v : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ →L[ℝ] (Fin N → ℝ) :=
  LinearMap.toContinuousLinearMap (mulVecL N v)

lemma mulVecCLM_apply (N : ℕ) (v : Fin N → ℝ) (A : Matrix (Fin N) (Fin N) ℝ) :
    mulVecCLM N v A = A *ᵥ v := rfl

/-- `A ↦ P_N (extN (A *ᵥ v))`，作为连续线性映射。 -/
def Phi (N : ℕ) (v : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ →L[ℝ] H :=
  (padCLM N).comp (mulVecCLM N v)

lemma Phi_apply (N : ℕ) (v : Fin N → ℝ) (A : Matrix (Fin N) (Fin N) ℝ) :
    Phi N v A = padCLM N (A *ᵥ v) := by
  rw [Phi, ContinuousLinearMap.comp_apply, mulVecCLM_apply]

lemma Phi_smulVec (N : ℕ) (v : Fin N → ℝ) (A : Matrix (Fin N) (Fin N) ℝ) (c : ℝ) :
    Phi N v (c • A) = c • Phi N v A := by
  rw [Phi_apply, Phi_apply, Matrix.smul_mulVec, padCLM_smul]

/-! ### 三、幂的提升 -/

/-- **幂的提升**：在 `hpad` 下，`ℓ²` 侧的幂作用在 `P_N x` 上等于有限维矩阵幂的零延拓。 -/
lemma pow_pad (hf : L1 f) (N : ℕ)
    (hpad : ∀ (v : Fin N → ℝ),
      (PNclm N).comp ((Op hf).comp (PNclm N)) (PN (extN v) N) = PN (extN ((ON f).mulVec v)) N)
    (v : Fin N → ℝ) (k : ℕ) :
    (((PNclm N).comp ((Op hf).comp (PNclm N)) : H →L[ℝ] H) ^ k) (PN (extN v) N)
      = PN (extN (((ON f) ^ k).mulVec v)) N := by
  induction k with
  | zero => rw [pow_zero, ContinuousLinearMap.one_apply, pow_zero, Matrix.one_mulVec]
  | succ k ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply, ih, hpad,
      Matrix.mulVec_mulVec v (ON f) (ON f ^ k), ← pow_succ']

/-- `pow_pad` 的 `padCLM` 形式。 -/
lemma pow_pad_pad (hf : L1 f) (N : ℕ)
    (hpad : ∀ (v : Fin N → ℝ),
      (PNclm N).comp ((Op hf).comp (PNclm N)) (PN (extN v) N) = PN (extN ((ON f).mulVec v)) N)
    (v : Fin N → ℝ) (k : ℕ) :
    (((PNclm N).comp ((Op hf).comp (PNclm N)) : H →L[ℝ] H) ^ k) (padCLM N v)
      = padCLM N (((ON f) ^ k).mulVec v) := by
  rw [padCLM_eq_PN, pow_pad hf N hpad v k, padCLM_eq_PN]

/-- **算子层的标量提取**：`((t • u)^k) x = t^k • ((u^k) x)`。

`H →L[ℝ] H` 上没有 `IsScalarTower ℝ _ _`（故 `smul_pow` 不适用），只能手工归纳。 -/
lemma op_smul_pow_apply (u : H →L[ℝ] H) (t : ℝ) (k : ℕ) (x : H) :
    ((t • u) ^ k) x = t ^ k • ((u ^ k) x) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    have h1 : ((t • u) ^ (k + 1)) x = (t ^ k * t) • ((u ^ k) (u x)) := by
      rw [pow_succ, ContinuousLinearMap.mul_apply, ih, ContinuousLinearMap.smul_apply,
        map_smul, ← smul_smul]
    have h2 : (t ^ (k + 1)) • ((u ^ (k + 1)) x) = (t ^ k * t) • ((u ^ k) (u x)) := by
      rw [pow_succ, pow_succ, ContinuousLinearMap.mul_apply]
    rw [h1, h2]

/-- `pow_pad` 在 `t • S` 上的形式（供 `term_eq` 使用）。 -/
lemma pow_pad_scaled (hf : L1 f) (N : ℕ)
    (hpad : ∀ (v : Fin N → ℝ),
      (PNclm N).comp ((Op hf).comp (PNclm N)) (PN (extN v) N) = PN (extN ((ON f).mulVec v)) N)
    (v : Fin N → ℝ) (t : ℝ) (k : ℕ) :
    ((t • ((PNclm N).comp ((Op hf).comp (PNclm N)) : H →L[ℝ] H)) ^ k) (padCLM N v)
      = t ^ k • padCLM N (((ON f) ^ k).mulVec v) := by
  rw [op_smul_pow_apply, pow_pad_pad hf N hpad v k]

/-! ### 四、两侧的 `HasSum` -/

/-- **左侧**：算子指数级数经 `u ↦ u (padCLM N v)` 推到 `H`。 -/
lemma hasSum_left (hf : L1 f) (N : ℕ) (v : Fin N → ℝ) (t : ℝ) :
    HasSum (fun k : ℕ => (((k.factorial : ℝ)⁻¹) • (t • ((PNclm N).comp ((Op hf).comp (PNclm N))
        : H →L[ℝ] H)) ^ k) (padCLM N v))
      (NormedSpace.exp (t • ((PNclm N).comp ((Op hf).comp (PNclm N)) : H →L[ℝ] H))
        (padCLM N v)) :=
  (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (𝔸 := H →L[ℝ] H)
      (t • ((PNclm N).comp ((Op hf).comp (PNclm N)) : H →L[ℝ] H))).mapL
    ((ContinuousLinearMap.apply ℝ H) (padCLM N v))

/-- **右侧**：矩阵指数级数经 `A ↦ P_N (extN (A *ᵥ v))` 推到 `H`。 -/
lemma hasSum_right (N : ℕ) (v : Fin N → ℝ) (t : ℝ) :
    HasSum (fun k : ℕ => Phi N v (((k.factorial : ℝ)⁻¹) • (t • (ON f)) ^ k))
      (Phi N v (NormedSpace.exp (t • (ON f : Matrix (Fin N) (Fin N) ℝ)))) :=
  (NormedSpace.exp_series_hasSum_exp'
      (t • (ON f : Matrix (Fin N) (Fin N) ℝ))).mapL (Phi N v)

/-- 两侧级数的第 `k` 项逐项相等。 -/
lemma term_eq (hf : L1 f) (N : ℕ)
    (hpad : ∀ (v : Fin N → ℝ),
      (PNclm N).comp ((Op hf).comp (PNclm N)) (PN (extN v) N) = PN (extN ((ON f).mulVec v)) N)
    (v : Fin N → ℝ) (t : ℝ) (k : ℕ) :
    (((k.factorial : ℝ)⁻¹) • (t • ((PNclm N).comp ((Op hf).comp (PNclm N))
        : H →L[ℝ] H)) ^ k) (padCLM N v)
      = Phi N v (((k.factorial : ℝ)⁻¹) • (t • (ON f)) ^ k) := by
  rw [ContinuousLinearMap.smul_apply, pow_pad_scaled hf N hpad v t k,
    smul_pow, Phi_smulVec, Phi_smulVec, Phi_apply]

/-- **主定理 `exp_padN`**：在 `hpad` 下，算子指数与有限维矩阵指数相容。 -/
theorem exp_padN (hf : L1 f) (N : ℕ)
    (hpad : ∀ (v : Fin N → ℝ),
      (PNclm N).comp ((Op hf).comp (PNclm N)) (PN (extN v) N) = PN (extN ((ON f).mulVec v)) N)
    (v : Fin N → ℝ) (t : ℝ) :
    NormedSpace.exp (t • ((PNclm N).comp ((Op hf).comp (PNclm N)))) (PN (extN v) N)
      = PN (extN (NormedSpace.exp (t • (ON f : Matrix (Fin N) (Fin N) ℝ)) *ᵥ v)) N := by
  have h1 := hasSum_left hf N v t
  have hfun : (fun k : ℕ => Phi N v (((k.factorial : ℝ)⁻¹) • (t • (ON f)) ^ k))
      = (fun k : ℕ => (((k.factorial : ℝ)⁻¹) • (t • ((PNclm N).comp ((Op hf).comp (PNclm N))
          : H →L[ℝ] H)) ^ k) (padCLM N v)) := by
    funext k
    exact (term_eq hf N hpad v t k).symm
  have h2 := hasSum_right (f := f) N v t
  rw [hfun] at h2
  rw [← padCLM_eq_PN, ← padCLM_eq_PN]
  exact h1.unique h2

end

end Eliashberg
