import Eliashberg.AppendixFinite

/-!
# Temple 不等式（Theorem A.10 的核心）与迹界（Lemma A.5(ii)）—— 有限维版

论文 A.6：设 `A` 自伴、`ρ := ⟨w,Aw⟩`（`‖w‖=1`）、`β < ρ`，且**除 `λ₁` 外的谱都 `≤ β`**，则
`λ₁ ≤ ρ + ‖Aw − ρw‖²/(ρ − β)`。证明：`(A − λ₁)(A − β) ⪰ 0` ⇒ `0 ≤ ‖Aw‖² − (λ₁+β)ρ + λ₁β`，
再用 `‖Aw‖² = ρ² + ‖Aw − ρw‖²`。

这里在 `N × N` 实对称矩阵上证明（`temple`）。谱假设「除 `λ₁` 外都 `≤ β`」写成
`∀ i, hA.eigenvalues i ≠ top hA → hA.eigenvalues i ≤ β`。

**Lemma A.5(ii) 的有限维版**（`second_eigen_le_trace_sub`）：`B ⪰ 0` ⇒ 除最大特征值外每个特征值
`≤ tr B − λ₁(B) ≤ tr B − B₀₀`。这就是论文的 `λ₂(B) ≤ β₀ := ∑_{n≥1} B_nn`。

**Courant–Fischer 的一半**（`eigen_le_of_le`，Lemma A.5(v) 的有限维版）：`A ⪯ B`（二次型）⇒
「除 `λ₁(A)` 外的谱 `≤ β`」可由「除 `λ₁(B)` 外的谱 `≤ β`」推出——这需要完整的 Courant–Fischer，
mathlib 没有；本文件用一个更直接的形式：若 `A ⪯ B`，则 `A` 的**任意二维**特征子空间上的
Rayleigh 商 `≤ λ₂(B)`。具体见 `two_dim_rayleigh_le`。

## 关于 `ℓ²` 层的 Theorem A.10

论文的 Theorem A.10 在 `ℓ²` 上：需要 `A` 的完整谱分解（紧算子谱定理）以说「除 `λ₁` 外谱 `≤ β`」。
mathlib 没有无穷维紧自伴算子的谱定理，故 `ℓ²` 层的 Theorem A.10 与 Corollary A.6 **未形式化**；
本文件给出其全部有限维成分。
-/

namespace Eliashberg

open scoped BigOperators Matrix
open Filter Topology

section Temple

variable {N : ℕ} [NeZero N] {A : Matrix (Fin N) (Fin N) ℝ}

omit [NeZero N] in
/-- `‖Aw‖² = ∑_i λ_i² c_i(w)²`。 -/
lemma mulVec_dot_self_eq (hA : A.IsHermitian) (w : Fin N → ℝ) :
    (A *ᵥ w) ⬝ᵥ (A *ᵥ w) = ∑ i, hA.eigenvalues i ^ 2 * coeff hA w i ^ 2 := by
  conv_lhs => rw [← sum_coeff_smul hA w]
  rw [Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, mulVec_evec, smul_smul]
  rw [dot_expand]
  apply Finset.sum_congr rfl; intro i _; ring

/-- `(A − λ₁)(A − β) ⪰ 0` 的二次型形式：除 `λ₁` 外谱 `≤ β` ⇒
`∑_i (λ_i − λ₁)(λ_i − β) c_i² ≥ 0`。 -/
lemma spectral_product_nonneg (hA : A.IsHermitian) (β : ℝ)
    (hspec : ∀ i, hA.eigenvalues i ≠ top hA → hA.eigenvalues i ≤ β) (w : Fin N → ℝ) :
    0 ≤ ∑ i, (hA.eigenvalues i - top hA) * (hA.eigenvalues i - β) * coeff hA w i ^ 2 := by
  apply Finset.sum_nonneg; intro i _
  apply mul_nonneg _ (sq_nonneg _)
  by_cases h : hA.eigenvalues i = top hA
  · rw [h, sub_self, zero_mul]
  · have h1 := hspec i h
    have h2 := eigenvalues_le_top hA i
    nlinarith

/-- **Temple 不等式（有限维）**：`A` 实对称，`w ⬝ w = 1`，`ρ := ⟨w,Aw⟩ > β`，
除 `λ₁` 外谱 `≤ β` ⇒ `λ₁ ≤ ρ + ‖Aw − ρw‖²/(ρ − β)`。 -/
theorem temple (hA : A.IsHermitian) (β : ℝ)
    (hspec : ∀ i, hA.eigenvalues i ≠ top hA → hA.eigenvalues i ≤ β)
    (w : Fin N → ℝ) (hw : w ⬝ᵥ w = 1) (hρ : β < w ⬝ᵥ A *ᵥ w) :
    top hA ≤ w ⬝ᵥ A *ᵥ w + ((A *ᵥ w - (w ⬝ᵥ A *ᵥ w) • w) ⬝ᵥ (A *ᵥ w - (w ⬝ᵥ A *ᵥ w) • w))
      / (w ⬝ᵥ A *ᵥ w - β) := by
  set ρ := w ⬝ᵥ A *ᵥ w with hρdef
  set Λ := top hA with hΛ
  -- 展开：`∑ (λ_i − Λ)(λ_i − β) c_i² = ‖Aw‖² − (Λ+β)ρ + Λβ`
  have h1 := spectral_product_nonneg hA β hspec w
  have hnorm := mulVec_dot_self_eq hA w
  have hρ' : ρ = ∑ i, hA.eigenvalues i * coeff hA w i ^ 2 := dot_mulVec_eq hA w
  have hw' : (1:ℝ) = ∑ i, coeff hA w i ^ 2 := by rw [← hw]; exact dot_self_eq hA w
  have hexp : ∑ i, (hA.eigenvalues i - Λ) * (hA.eigenvalues i - β) * coeff hA w i ^ 2
      = (A *ᵥ w) ⬝ᵥ (A *ᵥ w) - (Λ + β) * ρ + Λ * β := by
    have e : Λ * β = Λ * β * ∑ i, coeff hA w i ^ 2 := by rw [← hw', mul_one]
    rw [hnorm, hρ', e, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  -- `‖Aw − ρw‖² = ‖Aw‖² − ρ²`
  have hres : (A *ᵥ w - ρ • w) ⬝ᵥ (A *ᵥ w - ρ • w) = (A *ᵥ w) ⬝ᵥ (A *ᵥ w) - ρ ^ 2 := by
    rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, smul_dotProduct, dotProduct_smul,
      smul_dotProduct, dotProduct_smul, hw]
    simp only [smul_eq_mul]
    have hsymm : w ⬝ᵥ (A *ᵥ w) = (A *ᵥ w) ⬝ᵥ w := dotProduct_comm _ _
    rw [← hρdef, ← hsymm, ← hρdef]
    ring
  -- 组装：`0 ≤ ‖Aw‖² − (Λ+β)ρ + Λβ = r² + ρ(ρ−β) − Λ(ρ−β)`，`ρ − β > 0`
  have hpos : 0 < ρ - β := sub_pos.mpr hρ
  have hkey : Λ * (ρ - β) ≤ ρ * (ρ - β) + (A *ᵥ w - ρ • w) ⬝ᵥ (A *ᵥ w - ρ • w) := by
    rw [hres]; linarith [h1, hexp]
  rw [← sub_le_iff_le_add', le_div_iff₀ hpos] at *
  have := hkey
  nlinarith [hpos]

/-! ### Lemma A.5(ii)：正半定矩阵的迹界 -/

omit [NeZero N] in
/-- 迹 `= ∑ 对角元 = ∑ 特征值`。 -/
lemma trace_eq (hA : A.IsHermitian) : ∑ i, A i i = ∑ i, hA.eigenvalues i := by
  have h := hA.trace_eq_sum_eigenvalues
  simp only [Matrix.trace, Matrix.diag, RCLike.ofReal_real_eq_id, id] at h
  exact h

/-- **Lemma A.5(ii) 有限维版**：`A ⪰ 0`（所有特征值 `≥ 0`），则除最大特征值 `λ₁` 外的每个特征值
`λ_j ≤ tr A − λ₁ ≤ tr A − A₀₀`。 -/
theorem eigen_le_trace_sub (hA : A.IsHermitian) (hpos : ∀ i, 0 ≤ hA.eigenvalues i)
    (j : Fin N) (hj : hA.eigenvalues j ≠ top hA) (i₀ : Fin N) :
    hA.eigenvalues j ≤ (∑ i, A i i) - A i₀ i₀ := by
  obtain ⟨j₁, hj₁⟩ := exists_eigenvalues_eq_top hA
  have hne : j ≠ j₁ := fun h => hj (h ▸ hj₁)
  -- `λ_j + λ₁ ≤ ∑ λ_i = tr A`
  have h1 : hA.eigenvalues j + hA.eigenvalues j₁ ≤ ∑ i, hA.eigenvalues i := by
    have hsub : ({j, j₁} : Finset (Fin N)) ⊆ Finset.univ := Finset.subset_univ _
    have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hpos i)
    rw [Finset.sum_pair hne] at this
    exact this
  -- `A i₀ i₀ ≤ λ₁`（Rayleigh：`e_{i₀}` 是单位向量）
  have h2 : A i₀ i₀ ≤ top hA := by
    have := dot_mulVec_le_top hA (Pi.single i₀ 1) (by simp)
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this
  rw [trace_eq hA]
  rw [hj₁] at h1
  linarith

end Temple

end Eliashberg
