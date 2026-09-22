import Eliashberg.Temple
import Eliashberg.MainB
import Eliashberg.L2Operator

/-!
# Theorem A.10（Theorem (∗)）在 `ℓ²` 上的完整形式化——经有限截断

论文 Theorem A.10：`M ≥ 1`、`N₁ ≥ M`、`p₀,…,p_{M−1} > 0`，定义 (A.4)–(A.5) 的
`‖v‖²、Q、g_n、W、ρ = Q/‖v‖²、R、r² = R/‖v‖²`；若 `ρ > 13/25`，则 `ρ ≤ g(2) ≤ ρ + r²/(ρ − 13/25)`。

论文的证明在 `ℓ²` 上用紧算子的谱分解（Lemma A.5、Cor A.6）。mathlib 没有无穷维紧自伴算子的谱定理，
本文件改走**有限截断**路线，全程只用 mathlib 的有限维谱定理：

1. **Temple 不等式（齐次形式）**`temple'`：`A` 实对称，`x ≠ 0`，`ρ := ⟨x,Ax⟩/⟨x,x⟩ > β`，
   除 `λ₁` 外谱 `≤ β` ⇒ `λ₁ ≤ ρ + (‖Ax − ρx‖²/‖x‖²)/(ρ − β)`。
2. **谱分离的有限维形式**`eigen_le_of_dominated`（Lemma A.5(v) + Cor A.6）：`A ⪯ B`（二次型），
   `B` 除某一个特征值外都 `≤ β` ⇒ `A` 除 `λ₁` 外都 `≤ β`。证明用二维子空间：若 `A` 有两个
   特征值 `> β`，在其张成的平面里取与 `B` 的顶特征向量正交的 `x`，则
   `β⟨x,x⟩ < ⟨x,Ax⟩ ≤ ⟨x,Bx⟩ ≤ β⟨x,x⟩`，矛盾。这替代了论文引用的 Courant–Fischer。
3. **`B_N` 的迹界**`BN_trace_sub_le`（Lemma A.5(i)–(iv)）：`B_N ⪰ 0`，
   `tr B_N − (B_N)₀₀ = ∑_{1≤n<N} B_nn ≤ ∑_{n≥1}[(2n+1)⁻³ + 2(2n+1)⁻²] = (7/8)ζ(3) + (3/2)ζ(2) − 3 < 13/25`。
   奇数项级数用 `tsum_even_add_odd` 化到 `ζ`。
4. **`A_N ⪯ B_N`**（Cor A.3 的有限版 `quadForm_le_B`）⇒ `A_N` 除 `λ₁^{(N)}` 外谱 `≤ 13/25`。
5. **试探向量代数**：`v_n = p_n/u_n`（`n < M`），`(A_N v)_n = u_n g_n`，
   `‖A_N v − ρv‖² = ∑_{n<N}(g_n − ρ(2n+1)p_n)²/(2n+1) ≤ R`（尾部用 Lemma A.7 + A.9）。
6. 对每个 `N ≥ M`：`λ₁^{(N)} ≤ ρ + r²/(ρ−β)`；再由 `g(2) = sup_N λ₁^{(N)}`（`lam1_eq_iSup_lamN`）得
   **`theorem_A10`**。下界 `ρ ≤ g(2)` 是 Rayleigh 商（`quadForm_le_lam1_mul`）。

于是 Theorem A.10 的结论对 `g2 := lam1 (k ↦ k⁻²)` 成立，且 `lam1 = max spec`（`L2Operator.lean`）。
-/

namespace Eliashberg

open scoped BigOperators Matrix
open Filter Topology

/-! ### 1. Temple 不等式的齐次形式 -/

section TempleHom

variable {N : ℕ} [NeZero N] {A : Matrix (Fin N) (Fin N) ℝ}

/-- **Temple 不等式（齐次）**：`x ≠ 0`，`ρ := ⟨x,Ax⟩/⟨x,x⟩`，`β⟨x,x⟩ < ⟨x,Ax⟩`，除 `λ₁` 外谱 `≤ β` ⇒
`λ₁ ≤ ρ + (‖Ax − ρx‖²/⟨x,x⟩)/(ρ − β)`。 -/
theorem temple' (hA : A.IsHermitian) (β : ℝ)
    (hspec : ∀ i, hA.eigenvalues i ≠ top hA → hA.eigenvalues i ≤ β)
    (x : Fin N → ℝ) (hx : 0 < x ⬝ᵥ x) (hρ : β * (x ⬝ᵥ x) < x ⬝ᵥ A *ᵥ x) :
    top hA ≤ (x ⬝ᵥ A *ᵥ x) / (x ⬝ᵥ x)
      + ((A *ᵥ x - ((x ⬝ᵥ A *ᵥ x) / (x ⬝ᵥ x)) • x) ⬝ᵥ (A *ᵥ x - ((x ⬝ᵥ A *ᵥ x) / (x ⬝ᵥ x)) • x))
        / (x ⬝ᵥ x) / ((x ⬝ᵥ A *ᵥ x) / (x ⬝ᵥ x) - β) := by
  have h1 := spectral_product_nonneg hA β hspec x
  have hnorm := mulVec_dot_self_eq hA x
  have hP : x ⬝ᵥ A *ᵥ x = ∑ i, hA.eigenvalues i * coeff hA x i ^ 2 := dot_mulVec_eq hA x
  have hS : x ⬝ᵥ x = ∑ i, coeff hA x i ^ 2 := dot_self_eq hA x
  have hsymm : (A *ᵥ x) ⬝ᵥ x = x ⬝ᵥ A *ᵥ x := dotProduct_comm _ _
  set S := x ⬝ᵥ x with hSdef
  set P := x ⬝ᵥ A *ᵥ x with hPdef
  set ρ := P / S with hρdef
  set Λ := top hA with hΛ
  clear_value S P ρ Λ
  have hexp : ∑ i, (hA.eigenvalues i - Λ) * (hA.eigenvalues i - β) * coeff hA x i ^ 2
      = (A *ᵥ x) ⬝ᵥ (A *ᵥ x) - (Λ + β) * P + Λ * β * S := by
    rw [hnorm, hP, hS, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  have hres : (A *ᵥ x - ρ • x) ⬝ᵥ (A *ᵥ x - ρ • x)
      = (A *ᵥ x) ⬝ᵥ (A *ᵥ x) - 2 * ρ * P + ρ ^ 2 * S := by
    rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, smul_dotProduct, dotProduct_smul,
      smul_dotProduct, dotProduct_smul, hsymm, ← hPdef, ← hSdef]
    simp only [smul_eq_mul]; ring
  have hSpos : 0 < S := hx
  have hρS : ρ * S = P := by rw [hρdef]; exact div_mul_cancel₀ P hSpos.ne'
  have hρβ : 0 < ρ - β := by
    rw [sub_pos, hρdef, lt_div_iff₀ hSpos]; linarith
  set r := (A *ᵥ x - ρ • x) ⬝ᵥ (A *ᵥ x - ρ • x) with hr
  have hr' : r = (A *ᵥ x) ⬝ᵥ (A *ᵥ x) - ρ * P := by
    rw [hres]; linear_combination ρ * hρS
  have hkey : 0 ≤ r + ρ * P - Λ * P - β * P + Λ * β * S := by
    rw [hr']; linarith [h1, hexp]
  rw [← sub_le_iff_le_add', le_div_iff₀ hρβ, le_div_iff₀ hSpos]
  have e : (Λ - ρ) * (ρ - β) * S = Λ * P - Λ * β * S - ρ * P + β * P := by
    linear_combination (Λ - ρ + β) * hρS
  rw [e]; linarith [hkey]

end TempleHom

/-! ### 2. 谱分离的有限维形式（Lemma A.5(v) + Cor A.6） -/

section Dominated

variable {N : ℕ} [NeZero N]

/-- 顶特征值以外的特征值被迹控制（按下标排除）：`B ⪰ 0` ⇒ 存在 `k₀`，
`∀ k ≠ k₀, μ_k ≤ tr B − B_{i₀i₀}`。 -/
theorem nontop_le_trace_sub {B : Matrix (Fin N) (Fin N) ℝ} (hB : B.IsHermitian)
    (hpos : ∀ k, 0 ≤ hB.eigenvalues k) (i₀ : Fin N) :
    ∃ k₀, ∀ k, k ≠ k₀ → hB.eigenvalues k ≤ (∑ i, B i i) - B i₀ i₀ := by
  obtain ⟨k₀, hk₀⟩ := exists_eigenvalues_eq_top hB
  refine ⟨k₀, fun k hk => ?_⟩
  have h1 : hB.eigenvalues k + hB.eigenvalues k₀ ≤ ∑ i, hB.eigenvalues i := by
    have hsub : ({k, k₀} : Finset (Fin N)) ⊆ Finset.univ := Finset.subset_univ _
    have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hpos i)
    rw [Finset.sum_pair hk] at this
    exact this
  have h2 : B i₀ i₀ ≤ top hB := by
    have := dot_mulVec_le_top hB (Pi.single i₀ 1) (by simp)
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this
  rw [trace_eq hB]
  rw [hk₀] at h1
  linarith

/-- **谱分离（有限维）**：`A ⪯ B`（二次型），`B` 除下标 `k₀` 外的特征值都 `≤ β` ⇒
`A` 除 `λ₁(A)` 外的特征值都 `≤ β`。 -/
theorem eigen_le_of_dominated {A B : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hAB : ∀ x : Fin N → ℝ, x ⬝ᵥ A *ᵥ x ≤ x ⬝ᵥ B *ᵥ x) (β : ℝ)
    (hBspec : ∃ k₀, ∀ k, k ≠ k₀ → hB.eigenvalues k ≤ β) :
    ∀ i, hA.eigenvalues i ≠ top hA → hA.eigenvalues i ≤ β := by
  intro i hi
  by_cases hle : hA.eigenvalues i ≤ β
  · exact hle
  exfalso
  have hlt : β < hA.eigenvalues i := not_le.mp hle
  obtain ⟨j₀, hj₀⟩ := exists_eigenvalues_eq_top hA
  obtain ⟨k₀, hk₀⟩ := hBspec
  have hij : i ≠ j₀ := fun h => hi (h ▸ hj₀)
  have hj₀β : β < hA.eigenvalues j₀ := by
    rw [hj₀]; exact lt_of_lt_of_le hlt (eigenvalues_le_top hA i)
  -- 平面 `span(e_i, e_{j₀})` 上的二次型
  have hquad : ∀ a b : ℝ, (a • evec hA i + b • evec hA j₀) ⬝ᵥ A *ᵥ (a • evec hA i + b • evec hA j₀)
      = a ^ 2 * hA.eigenvalues i + b ^ 2 * hA.eigenvalues j₀ := by
    intro a b
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, mulVec_evec, mulVec_evec]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, evec_dot,
      smul_eq_mul, hij, hij.symm, ite_true, ite_false]
    ring
  have hnorm : ∀ a b : ℝ, (a • evec hA i + b • evec hA j₀) ⬝ᵥ (a • evec hA i + b • evec hA j₀)
      = a ^ 2 + b ^ 2 := by
    intro a b
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, evec_dot,
      smul_eq_mul, hij, hij.symm, ite_true, ite_false]
    ring
  -- `B` 侧：与 `B` 的顶特征向量正交 ⇒ `⟨x,Bx⟩ ≤ β⟨x,x⟩`
  have hBle : ∀ x : Fin N → ℝ, evec hB k₀ ⬝ᵥ x = 0 → x ⬝ᵥ B *ᵥ x ≤ β * (x ⬝ᵥ x) := by
    intro x hfx
    rw [dot_mulVec_eq hB, dot_self_eq hB, Finset.mul_sum]
    apply Finset.sum_le_sum; intro k _
    by_cases hk : k = k₀
    · subst hk
      have : coeff hB x k = 0 := hfx
      rw [this]; simp
    · exact mul_le_mul_of_nonneg_right (hk₀ k hk) (sq_nonneg _)
  set α := evec hB k₀ ⬝ᵥ evec hA i with hα
  set γ := evec hB k₀ ⬝ᵥ evec hA j₀ with hγ
  by_cases h0 : α = 0 ∧ γ = 0
  · -- `x = e_i`
    have h1 := hAB (evec hA i)
    have h2 := hBle (evec hA i) h0.1
    have h3 : evec hA i ⬝ᵥ A *ᵥ evec hA i = hA.eigenvalues i := by
      have := hquad 1 0; simpa using this
    have h4 : evec hA i ⬝ᵥ evec hA i = 1 := by
      have := hnorm 1 0; simpa using this
    rw [h3] at h1; rw [h4, mul_one] at h2
    linarith
  · -- `x = γ e_i − α e_{j₀}`
    have hfx : evec hB k₀ ⬝ᵥ (γ • evec hA i + (-α) • evec hA j₀) = 0 := by
      simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, ← hα, ← hγ]; ring
    have h1 := hAB (γ • evec hA i + (-α) • evec hA j₀)
    have h2 := hBle _ hfx
    rw [hquad] at h1; rw [hnorm] at h2
    rcases not_and_or.mp h0 with h | h
    · have hα2 : 0 < α ^ 2 := by positivity
      nlinarith [mul_pos hα2 (sub_pos.mpr hj₀β), mul_nonneg (sq_nonneg γ) (sub_pos.mpr hlt).le]
    · have hγ2 : 0 < γ ^ 2 := by positivity
      nlinarith [mul_pos hγ2 (sub_pos.mpr hlt), mul_nonneg (sq_nonneg α) (sub_pos.mpr hj₀β).le]

end Dominated

/-! ### 3. 奇数项级数：`∑_{k≥0} (2k+1)^{-s} = (1 − 2^{-s}) ζ(s)` -/

lemma summable_odd_pow (s : ℕ) (hsum : Summable (fun k : ℕ => 1 / ((k:ℝ) + 1) ^ s)) :
    Summable (fun k : ℕ => 1 / (2 * (k:ℝ) + 1) ^ s) := by
  apply Summable.of_nonneg_of_le (fun k => by positivity) _ hsum
  intro k
  apply one_div_le_one_div_of_le (by positivity)
  apply pow_le_pow_left₀ (by positivity)
  linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]

/-- `∑'_{k≥0} 1/(2k+1)^s = (1 − 2^{−s}) ∑'_{k≥0} 1/(k+1)^s`。 -/
theorem tsum_odd_pow (s : ℕ) (hsum : Summable (fun k : ℕ => 1 / ((k:ℝ) + 1) ^ s)) :
    ∑' k : ℕ, 1 / (2 * (k:ℝ) + 1) ^ s = (1 - 1 / 2 ^ s) * ∑' k : ℕ, 1 / ((k:ℝ) + 1) ^ s := by
  have hodd := summable_odd_pow s hsum
  have heven : Summable (fun k : ℕ => (1 / (2:ℝ) ^ s) * (1 / ((k:ℝ) + 1) ^ s)) :=
    hsum.mul_left _
  have h := tsum_even_add_odd (f := fun k : ℕ => 1 / ((k:ℝ) + 1) ^ s) ?_ ?_
  · have e1 : (fun k : ℕ => 1 / (((2 * k : ℕ) : ℝ) + 1) ^ s)
        = fun k : ℕ => 1 / (2 * (k:ℝ) + 1) ^ s := by
      funext k; push_cast; ring
    have e2 : (fun k : ℕ => 1 / (((2 * k + 1 : ℕ) : ℝ) + 1) ^ s)
        = fun k : ℕ => (1 / (2:ℝ) ^ s) * (1 / ((k:ℝ) + 1) ^ s) := by
      funext k; push_cast
      rw [show (2 * (k:ℝ) + 1 + 1) = 2 * ((k:ℝ) + 1) by ring, mul_pow]
      field_simp
    rw [e1, e2, tsum_mul_left] at h
    linarith
  · simpa using (show Summable (fun k : ℕ => 1 / (((2 * k : ℕ) : ℝ) + 1) ^ s) by
      convert hodd using 2 with k; push_cast; ring)
  · simpa using (show Summable (fun k : ℕ => 1 / (((2 * k + 1 : ℕ) : ℝ) + 1) ^ s) by
      convert heven using 2 with k; push_cast
      rw [show (2 * (k:ℝ) + 1 + 1) = 2 * ((k:ℝ) + 1) by ring, mul_pow]
      field_simp)

/-- `∑'_{k≥0} 1/(2k+3)^s = (1 − 2^{−s}) ζ(s) − 1`。 -/
theorem tsum_odd_pow_shift (s : ℕ) (hsum : Summable (fun k : ℕ => 1 / ((k:ℝ) + 1) ^ s)) :
    ∑' k : ℕ, 1 / (2 * (k:ℝ) + 3) ^ s = (1 - 1 / 2 ^ s) * (∑' k : ℕ, 1 / ((k:ℝ) + 1) ^ s) - 1 := by
  have hodd := summable_odd_pow s hsum
  have h := hodd.tsum_eq_zero_add
  rw [tsum_odd_pow s hsum] at h
  have e : (fun k : ℕ => 1 / (2 * ((k + 1 : ℕ) : ℝ) + 1) ^ s)
      = fun k : ℕ => 1 / (2 * (k:ℝ) + 3) ^ s := by
    funext k; push_cast; ring_nf
  simp only [Nat.cast_zero, mul_zero, zero_add, one_pow, div_one] at h
  rw [e] at h
  linarith

lemma summable_odd_pow_shift (s : ℕ) (hsum : Summable (fun k : ℕ => 1 / ((k:ℝ) + 1) ^ s)) :
    Summable (fun k : ℕ => 1 / (2 * (k:ℝ) + 3) ^ s) := by
  have := (summable_nat_add_iff 1).mpr (summable_odd_pow s hsum)
  convert this using 2 with k; push_cast; ring_nf

/-- `∑_{k<K} 1/(2k+3)^s ≤ (1 − 2^{−s}) ζ(s) − 1`。 -/
theorem sum_odd_pow_shift_le (s : ℕ) (hsum : Summable (fun k : ℕ => 1 / ((k:ℝ) + 1) ^ s)) (K : ℕ) :
    ∑ k ∈ Finset.range K, 1 / (2 * (k:ℝ) + 3) ^ s
      ≤ (1 - 1 / 2 ^ s) * (∑' k : ℕ, 1 / ((k:ℝ) + 1) ^ s) - 1 := by
  rw [← tsum_odd_pow_shift s hsum]
  exact (summable_odd_pow_shift s hsum).sum_le_tsum _ (fun k _ => by positivity)

end Eliashberg

namespace Eliashberg

open scoped BigOperators Matrix
open Filter Topology

/-! ### 4. 矩阵 `B_N`：正定、二次型、迹界（Lemma A.5(i)–(iv)） -/

/-- Lemma A.1 的 `B`：`B_{nm} = u_n u_m/(n+m+1)² + δ_{nm} u_n² ψ'(n+1)`。 -/
noncomputable def Bf (n m : ℕ) : ℝ :=
  u n * u m * (1 / (((n:ℝ) + m + 1) ^ 2)) + (if n = m then u n ^ 2 * psi' n else 0)

lemma Bf_symm (n m : ℕ) : Bf n m = Bf m n := by
  unfold Bf
  by_cases h : n = m
  · subst h; rfl
  · have h' : m ≠ n := Ne.symm h
    simp only [h, h', ite_false, add_zero]
    rw [show ((n:ℝ) + m + 1) = ((m:ℝ) + n + 1) by ring, mul_comm (u n) (u m)]

/-- `B_N := P_N B P_N`。 -/
noncomputable def BN (N : ℕ) : Matrix (Fin N) (Fin N) ℝ := Matrix.of fun n m => Bf n.val m.val

lemma BN_isHermitian (N : ℕ) : (BN N).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  apply Matrix.IsSymm.ext
  intro i j
  simp only [BN, Matrix.of_apply]
  exact Bf_symm j.val i.val

/-- `⟨x, B_N x⟩ = quadFormB (extN x) N`。 -/
lemma dot_BN {N : ℕ} (x : Fin N → ℝ) : x ⬝ᵥ (BN N) *ᵥ x = quadFormB (extN x) N := by
  unfold quadFormB pOf
  simp only [dotProduct, Matrix.mulVec, BN, Matrix.of_apply, Bf, add_mul, Finset.sum_add_distrib,
    ite_mul, zero_mul, Fin.val_inj, Finset.sum_ite_eq, Finset.mem_univ, ite_true, mul_add]
  congr 1
  · rw [← Fin.sum_univ_eq_sum_range (fun n => ∑ m ∈ Finset.range N,
      u n * extN x n * (u m * extN x m) * (1 / (((n:ℝ) + m + 1) ^ 2))) N]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum, ← Fin.sum_univ_eq_sum_range (fun m =>
      u i.val * extN x i.val * (u m * extN x m) * (1 / (((i.val:ℝ) + m + 1) ^ 2))) N]
    apply Finset.sum_congr rfl; intro j _
    rw [extN_fin, extN_fin]; ring
  · rw [← Fin.sum_univ_eq_sum_range (fun n => psi' n * (u n * extN x n) ^ 2) N]
    apply Finset.sum_congr rfl; intro i _
    rw [extN_fin]; ring

/-- Lemma A.4：`B_N ⪰ 0`（所有特征值非负）。 -/
lemma BN_eigen_nonneg (N : ℕ) : ∀ k, 0 ≤ (BN_isHermitian N).eigenvalues k := by
  intro k
  have h1 : evec (BN_isHermitian N) k ⬝ᵥ (BN N) *ᵥ evec (BN_isHermitian N) k
      = (BN_isHermitian N).eigenvalues k := by
    rw [mulVec_evec, dotProduct_smul, evec_dot, smul_eq_mul]; simp
  rw [← h1, dot_BN]
  exact quadFormB_nonneg _ _

/-- `B_nn = (2n+1)⁻³ + ψ'(n+1)/(2n+1)`。 -/
lemma Bf_diag (n : ℕ) : Bf n n = 1 / (2 * (n:ℝ) + 1) ^ 3 + psi' n / (2 * (n:ℝ) + 1) := by
  unfold Bf
  rw [if_pos rfl, show ((n:ℝ) + n + 1) = 2 * (n:ℝ) + 1 by ring,
    show u n * u n = u n ^ 2 by ring, u_sq]
  have hpos : (0:ℝ) < 2 * (n:ℝ) + 1 := two_mul_add_one_pos n
  field_simp

/-- Lemma A.5(iii)：`B_{n+1,n+1} ≤ (2n+3)⁻³ + 2(2n+3)⁻²`。 -/
lemma Bf_diag_succ_le (n : ℕ) :
    Bf (n+1) (n+1) ≤ 1 / (2 * (n:ℝ) + 3) ^ 3 + 2 * (1 / (2 * (n:ℝ) + 3) ^ 2) := by
  rw [Bf_diag]
  have h := psi'_le (n+1)
  have hpos : (0:ℝ) < 2 * (n:ℝ) + 3 := by positivity
  have e1 : (2 * ((n+1 : ℕ):ℝ) + 1) = 2 * (n:ℝ) + 3 := by push_cast; ring
  rw [e1] at h ⊢
  have h2 : psi' (n+1) / (2 * (n:ℝ) + 3) ≤ 2 / (2 * (n:ℝ) + 3) / (2 * (n:ℝ) + 3) :=
    div_le_div_of_nonneg_right h hpos.le
  have e2 : (2:ℝ) / (2 * (n:ℝ) + 3) / (2 * (n:ℝ) + 3) = 2 * (1 / (2 * (n:ℝ) + 3) ^ 2) := by
    field_simp
  linarith

/-- Lemma A.5(iii)：`∑_{1≤n≤K} B_nn ≤ (7/8)ζ(3) + (3/2)ζ(2) − 3`。 -/
theorem sum_Bf_diag_le (K : ℕ) :
    ∑ n ∈ Finset.range K, Bf (n+1) (n+1) ≤ 7/8 * zeta3 + 3/2 * zeta2 - 3 := by
  have h3 : ∑ n ∈ Finset.range K, 1 / (2 * (n:ℝ) + 3) ^ 3 ≤ (1 - 1 / 2 ^ 3) * zeta3 - 1 :=
    sum_odd_pow_shift_le 3 zeta3_summable K
  have h2 : ∑ n ∈ Finset.range K, 1 / (2 * (n:ℝ) + 3) ^ 2 ≤ (1 - 1 / 2 ^ 2) * zeta2 - 1 :=
    sum_odd_pow_shift_le 2 hasSum_zeta_two_shift.summable K
  calc ∑ n ∈ Finset.range K, Bf (n+1) (n+1)
      ≤ ∑ n ∈ Finset.range K, (1 / (2 * (n:ℝ) + 3) ^ 3 + 2 * (1 / (2 * (n:ℝ) + 3) ^ 2)) :=
        Finset.sum_le_sum (fun n _ => Bf_diag_succ_le n)
    _ = ∑ n ∈ Finset.range K, 1 / (2 * (n:ℝ) + 3) ^ 3
          + 2 * ∑ n ∈ Finset.range K, 1 / (2 * (n:ℝ) + 3) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ ((1 - 1 / 2 ^ 3) * zeta3 - 1) + 2 * ((1 - 1 / 2 ^ 2) * zeta2 - 1) := by linarith
    _ = 7/8 * zeta3 + 3/2 * zeta2 - 3 := by ring

/-- **Lemma A.5(i)–(iv)**：`tr B_N − (B_N)₀₀ ≤ 13/25`。 -/
theorem BN_trace_sub_le (K : ℕ) :
    (∑ i : Fin (K+1), BN (K+1) i i) - BN (K+1) 0 0 ≤ 13/25 := by
  simp only [BN, Matrix.of_apply]
  rw [Fin.sum_univ_eq_sum_range (fun n => Bf n n) (K+1), Finset.sum_range_succ']
  simp only [Fin.val_zero, add_sub_cancel_right]
  have h := sum_Bf_diag_le K
  have hz2 := zeta2_le_R2
  have hz3 := zeta3_le_R3
  have hA3 := A3_rational
  linarith

/-- **Lemma A.5 + Cor A.6（有限截断）**：`A_N = P_N O[k⁻²] P_N` 除 `λ₁^{(N)}` 外的谱 `≤ 13/25`。 -/
theorem AN_spec_le (K : ℕ) :
    ∀ i, (ON_isHermitian (N := K+1) (fun k => 1 / (k:ℝ) ^ 2)).eigenvalues i
        ≠ top (ON_isHermitian (N := K+1) (fun k => 1 / (k:ℝ) ^ 2)) →
      (ON_isHermitian (N := K+1) (fun k => 1 / (k:ℝ) ^ 2)).eigenvalues i ≤ 13/25 := by
  apply eigen_le_of_dominated _ (BN_isHermitian (K+1))
  · intro x
    rw [quadForm_eq_dot, dot_BN]
    exact quadForm_le_B _ _
  · obtain ⟨k₀, hk₀⟩ := nontop_le_trace_sub (BN_isHermitian (K+1)) (BN_eigen_nonneg (K+1)) 0
    exact ⟨k₀, fun k hk => (hk₀ k hk).trans (BN_trace_sub_le K)⟩

/-! ### 5. 试探向量：(A.4)–(A.5) 的实数版，`(A_N v)_n = u_n g_n`，`‖A_N v − ρv‖² ≤ R` -/

/-- (A.4)：`‖v‖² = ∑_{n<M} (2n+1) p_n²`。 -/
noncomputable def nv2R (p : ℕ → ℝ) (M : ℕ) : ℝ := ∑ n ∈ Finset.range M, (2 * (n:ℝ) + 1) * p n ^ 2

/-- (A.4)：`Q = ∑_{n,m<M} p_n p_m K(n,m) − 2∑_{n<M} H_n^{(2)} p_n²`。 -/
noncomputable def QR (p : ℕ → ℝ) (M : ℕ) : ℝ :=
  (∑ n ∈ Finset.range M, ∑ m ∈ Finset.range M, p n * p m * KA n m)
    - 2 * ∑ n ∈ Finset.range M, H2 n * p n ^ 2

/-- (A.4)：`g_n = ∑_{m<M} p_m K(n,m) − 2H_n^{(2)} p_n [n<M]`。 -/
noncomputable def gR (p : ℕ → ℝ) (M n : ℕ) : ℝ :=
  (∑ m ∈ Finset.range M, p m * KA n m) - (if n < M then 2 * H2 n * p n else 0)

/-- (A.4)：`W = ∑_{m<M} p_m ((N₁+1)²/(N₁−m)² + 1)`。 -/
noncomputable def WR (p : ℕ → ℝ) (M N₁ : ℕ) : ℝ :=
  ∑ m ∈ Finset.range M, p m * (((N₁:ℝ) + 1) ^ 2 / ((N₁:ℝ) - m) ^ 2 + 1)

/-- `ρ := Q/‖v‖²`。 -/
noncomputable def rhoR (p : ℕ → ℝ) (M : ℕ) : ℝ := QR p M / nv2R p M

/-- 残差项 `T_n := (g_n − ρ(2n+1)p_n)²/(2n+1)`。 -/
noncomputable def resT (p : ℕ → ℝ) (M n : ℕ) : ℝ :=
  (gR p M n - rhoR p M * (2 * (n:ℝ) + 1) * p n) ^ 2 / (2 * (n:ℝ) + 1)

/-- (A.5)：`R = ∑_{n<M} T_n + ∑_{M≤n<N₁} g_n²/(2n+1) + W²/(N₁(2N₁+1)³)`。 -/
noncomputable def RR (p : ℕ → ℝ) (M N₁ : ℕ) : ℝ :=
  (∑ n ∈ Finset.range M, resT p M n)
    + (∑ n ∈ Finset.Ico M N₁, gR p M n ^ 2 / (2 * (n:ℝ) + 1))
    + WR p M N₁ ^ 2 / ((N₁:ℝ) * (2 * (N₁:ℝ) + 1) ^ 3)

/-- `r² := R/‖v‖²`。 -/
noncomputable def r2R (p : ℕ → ℝ) (M N₁ : ℕ) : ℝ := RR p M N₁ / nv2R p M

/-- 试探向量 `v_n := p_n/u_n = √(2n+1) p_n`。 -/
noncomputable def vOf (p : ℕ → ℝ) (n : ℕ) : ℝ := p n / u n

/-- 截断到 `Fin N`。 -/
noncomputable def xOf (p : ℕ → ℝ) (N : ℕ) : Fin N → ℝ := fun i => vOf p i.val

lemma pOf_vOf (p : ℕ → ℝ) (n : ℕ) : pOf (vOf p) n = p n := by
  unfold pOf vOf
  rw [mul_div_cancel₀ _ (u_pos n).ne']

lemma vOf_sq (p : ℕ → ℝ) (n : ℕ) : vOf p n ^ 2 = (2 * (n:ℝ) + 1) * p n ^ 2 := by
  unfold vOf
  rw [div_pow, u_sq, div_div_eq_mul_div, div_one, mul_comm]

/-- 支撑在 `[0,M)` 的求和可以从 `range N` 缩到 `range M`。 -/
lemma sum_range_of_supp {p : ℕ → ℝ} {M : ℕ} (hs : ∀ n, M ≤ n → p n = 0) (φ : ℕ → ℝ)
    (hφ : ∀ n, p n = 0 → φ n = 0) {N : ℕ} (hN : M ≤ N) :
    ∑ n ∈ Finset.range N, φ n = ∑ n ∈ Finset.range M, φ n := by
  symm
  apply Finset.sum_subset
  · intro x hx; exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hN)
  · intro n hn hnM
    rw [Finset.mem_range] at hn hnM
    exact hφ n (hs n (not_lt.mp hnM))

lemma sum_vOf_sq {p : ℕ → ℝ} {M : ℕ} (hs : ∀ n, M ≤ n → p n = 0) {N : ℕ} (hN : M ≤ N) :
    ∑ n ∈ Finset.range N, vOf p n ^ 2 = nv2R p M := by
  unfold nv2R
  simp_rw [vOf_sq]
  exact sum_range_of_supp hs _ (fun n h => by rw [h]; ring) hN

/-- `⟨v, A v⟩ = Q`（`N ≥ M`）。 -/
lemma quadForm_vOf {p : ℕ → ℝ} {M : ℕ} (hs : ∀ n, M ≤ n → p n = 0) {N : ℕ} (hN : M ≤ N) :
    quadForm (fun k => 1 / (k:ℝ) ^ 2) (vOf p) N = QR p M := by
  rw [quadForm_invSq_eq]
  simp only [pOf_vOf]
  unfold QR
  congr 1
  · rw [sum_range_of_supp hs (fun n => ∑ m ∈ Finset.range N, p n * p m * KA n m)
      (fun n h => by simp [h]) hN]
    apply Finset.sum_congr rfl; intro n _
    exact sum_range_of_supp hs (fun m => p n * p m * KA n m) (fun m h => by simp [h]) hN
  · congr 1
    exact sum_range_of_supp hs (fun n => H2 n * p n ^ 2) (fun n h => by simp [h]) hN

lemma gR_eq {p : ℕ → ℝ} {M : ℕ} (hs : ∀ n, M ≤ n → p n = 0) {N : ℕ} (hN : M ≤ N) (n : ℕ) :
    gR p M n = (∑ m ∈ Finset.range N, p m * KA n m) - 2 * H2 n * p n := by
  unfold gR
  rw [sum_range_of_supp hs (fun m => p m * KA n m) (fun m h => by rw [h, zero_mul]) hN]
  congr 1
  split_ifs with h
  · rfl
  · rw [hs n (not_lt.mp h)]; ring

/-- (A.1)：`(A_N v)_n = u_n g_n`。 -/
lemma mulVec_xOf {p : ℕ → ℝ} {M : ℕ} (hs : ∀ n, M ≤ n → p n = 0) {N : ℕ} (hN : M ≤ N) (i : Fin N) :
    ((ON (fun k => 1 / (k:ℝ) ^ 2) : Matrix (Fin N) (Fin N) ℝ) *ᵥ xOf p N) i
      = u i.val * gR p M i.val := by
  simp only [Matrix.mulVec, dotProduct, ON, Matrix.of_apply, xOf]
  rw [Fin.sum_univ_eq_sum_range (fun m => Of (fun k => 1 / (k:ℝ) ^ 2) i.val m * vOf p m) N]
  simp only [Of_invSq, vOf, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_range, i.isLt, ite_true]
  rw [gR_eq hs hN i.val, mul_sub, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl; intro m _
    have hum : u m ≠ 0 := (u_pos m).ne'
    rw [show u i.val * u m * KA i.val m * (p m / u m)
        = u i.val * (p m * KA i.val m) * (u m / u m) by ring, div_self hum, mul_one]
  · have hui : u i.val ≠ 0 := (u_pos _).ne'
    rw [show 2 * u i.val ^ 2 * H2 i.val * (p i.val / u i.val)
        = u i.val * (2 * H2 i.val * p i.val) * (u i.val / u i.val) by ring, div_self hui, mul_one]

/-- `(A_N v − ρ v)_n² = (g_n − ρ(2n+1)p_n)²/(2n+1)`。 -/
lemma resid_sq {p : ℕ → ℝ} {M : ℕ} (hs : ∀ n, M ≤ n → p n = 0) {N : ℕ} (hN : M ≤ N) (ρ : ℝ)
    (i : Fin N) :
    (((ON (fun k => 1 / (k:ℝ) ^ 2) : Matrix (Fin N) (Fin N) ℝ) *ᵥ xOf p N - ρ • xOf p N) i) ^ 2
      = (gR p M i.val - ρ * (2 * (i.val:ℝ) + 1) * p i.val) ^ 2 / (2 * (i.val:ℝ) + 1) := by
  rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mulVec_xOf hs hN]
  show (u i.val * gR p M i.val - ρ * vOf p i.val) ^ 2 = _
  unfold vOf
  have hinv : u i.val * (2 * (i.val:ℝ) + 1) = (u i.val)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [show u i.val * (2 * (i.val:ℝ) + 1) * u i.val = u i.val ^ 2 * (2 * (i.val:ℝ) + 1) by ring,
      u_sq]
    have h2 : (0:ℝ) < 2 * (i.val:ℝ) + 1 := two_mul_add_one_pos _
    field_simp
  have e : u i.val * gR p M i.val - ρ * (p i.val / u i.val)
      = u i.val * (gR p M i.val - ρ * (2 * (i.val:ℝ) + 1) * p i.val) := by
    rw [div_eq_mul_inv, ← hinv]; ring
  rw [e, mul_pow, u_sq]; ring

/-- `‖A_N v − ρ v‖² = ∑_{n<N} T_n`（`ρ = rhoR`）。 -/
lemma resid_norm {p : ℕ → ℝ} {M : ℕ} (hs : ∀ n, M ≤ n → p n = 0) {N : ℕ} (hN : M ≤ N) :
    ((ON (fun k => 1 / (k:ℝ) ^ 2) : Matrix (Fin N) (Fin N) ℝ) *ᵥ xOf p N - rhoR p M • xOf p N)
      ⬝ᵥ ((ON (fun k => 1 / (k:ℝ) ^ 2) : Matrix (Fin N) (Fin N) ℝ) *ᵥ xOf p N - rhoR p M • xOf p N)
      = ∑ n ∈ Finset.range N, resT p M n := by
  rw [← Fin.sum_univ_eq_sum_range (fun n => resT p M n) N]
  simp only [dotProduct]
  apply Finset.sum_congr rfl; intro i _
  rw [← sq, resid_sq hs hN (rhoR p M) i]
  rfl

lemma nv2R_pos {p : ℕ → ℝ} {M : ℕ} (hp : ∀ n, n < M → 0 < p n) (hM : 1 ≤ M) : 0 < nv2R p M := by
  unfold nv2R
  apply Finset.sum_pos
  · intro n hn
    have := hp n (Finset.mem_range.mp hn)
    exact mul_pos (two_mul_add_one_pos n) (pow_pos this 2)
  · exact ⟨0, Finset.mem_range.mpr hM⟩

/-- Theorem A.10 证明中的尾部估计：`n ≥ N₁` ⇒ `0 ≤ g_n ≤ W/(n+1)²`（用到 `p > 0`，Remark A.12）。 -/
lemma gR_tail_bounds {p : ℕ → ℝ} {M N₁ : ℕ} (hp : ∀ n, n < M → 0 < p n) (hMN : M ≤ N₁)
    (n : ℕ) (hn : N₁ ≤ n) :
    0 ≤ gR p M n ∧ gR p M n ≤ WR p M N₁ / ((n:ℝ) + 1) ^ 2 := by
  have hnM : ¬ n < M := by omega
  unfold gR
  rw [if_neg hnM, sub_zero]
  constructor
  · exact Finset.sum_nonneg (fun m hm => mul_nonneg (hp m (Finset.mem_range.mp hm)).le (KA_nonneg n m))
  · unfold WR
    rw [Finset.sum_div]
    apply Finset.sum_le_sum; intro m hm
    rw [Finset.mem_range] at hm
    have hmN : m < N₁ := lt_of_lt_of_le hm hMN
    have hpm := (hp m hm).le
    have hK : KA n m ≤ (((N₁:ℝ) + 1) ^ 2 / ((N₁:ℝ) - m) ^ 2 + 1) / ((n:ℝ) + 1) ^ 2 := by
      unfold KA
      have hne : n ≠ m := by omega
      rw [if_pos hne]
      have h1 := kernel_comparison m N₁ n hmN hn
      rw [mul_comm (((n:ℝ) + 1) ^ 2) (((N₁:ℝ) - m) ^ 2)] at h1
      have h2 : (1:ℝ) / ((n:ℝ) + m + 1) ^ 2 ≤ 1 / ((n:ℝ) + 1) ^ 2 := by
        apply one_div_le_one_div_of_le (by positivity)
        apply pow_le_pow_left₀ (by positivity)
        linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
      rw [add_div, div_div]
      linarith
    calc p m * KA n m ≤ p m * ((((N₁:ℝ) + 1) ^ 2 / ((N₁:ℝ) - m) ^ 2 + 1) / ((n:ℝ) + 1) ^ 2) :=
          mul_le_mul_of_nonneg_left hK hpm
      _ = p m * (((N₁:ℝ) + 1) ^ 2 / ((N₁:ℝ) - m) ^ 2 + 1) / ((n:ℝ) + 1) ^ 2 := by ring

/-- **`‖A_N v − ρ v‖² ≤ R`**（Theorem A.10 证明的核心估计，`N₁ ≤ N`）。 -/
theorem resid_le_RR {p : ℕ → ℝ} {M N₁ : ℕ} (hs : ∀ n, M ≤ n → p n = 0) (hp : ∀ n, n < M → 0 < p n)
    (hM : 1 ≤ M) (hMN : M ≤ N₁) {N : ℕ} (hN : N₁ ≤ N) :
    ∑ n ∈ Finset.range N, resT p M n ≤ RR p M N₁ := by
  have hMN' : M ≤ N := hMN.trans hN
  rw [← Finset.sum_range_add_sum_Ico (resT p M) hMN', ← Finset.sum_Ico_consecutive (resT p M) hMN hN]
  unfold RR
  -- 中段：`p_n = 0` ⇒ `T_n = g_n²/(2n+1)`
  have hmid : ∑ n ∈ Finset.Ico M N₁, resT p M n
      = ∑ n ∈ Finset.Ico M N₁, gR p M n ^ 2 / (2 * (n:ℝ) + 1) := by
    apply Finset.sum_congr rfl; intro n hn
    rw [Finset.mem_Ico] at hn
    unfold resT
    rw [hs n hn.1, mul_zero, sub_zero]
  -- 尾段：`T_n ≤ W²/((n+1)⁴(2n+1))`
  have htail1 : ∀ n, N₁ ≤ n →
      resT p M n ≤ WR p M N₁ ^ 2 * (1 / ((((N₁:ℝ) + (n - N₁ : ℕ)) + 1) ^ 4 * (2 * ((N₁:ℝ) + (n - N₁ : ℕ)) + 1))) := by
    intro n hn
    obtain ⟨h0, h1⟩ := gR_tail_bounds hp hMN n hn
    have hpn : p n = 0 := hs n (hMN.trans hn)
    unfold resT
    rw [hpn, mul_zero, sub_zero]
    have e : ((N₁:ℝ) + (n - N₁ : ℕ)) = n := by
      rw [Nat.cast_sub hn]; ring
    rw [e]
    have h2 : gR p M n ^ 2 ≤ (WR p M N₁ / ((n:ℝ) + 1) ^ 2) ^ 2 := pow_le_pow_left₀ h0 h1 2
    have hpos : (0:ℝ) < 2 * (n:ℝ) + 1 := two_mul_add_one_pos n
    rw [div_le_iff₀ hpos]
    refine h2.trans (le_of_eq ?_)
    have hn1 : ((n:ℝ) + 1) ≠ 0 := by positivity
    field_simp
  have htail : ∑ n ∈ Finset.Ico N₁ N, resT p M n
      ≤ WR p M N₁ ^ 2 / ((N₁:ℝ) * (2 * (N₁:ℝ) + 1) ^ 3) := by
    calc ∑ n ∈ Finset.Ico N₁ N, resT p M n
        ≤ ∑ n ∈ Finset.Ico N₁ N, WR p M N₁ ^ 2 *
            (1 / ((((N₁:ℝ) + (n - N₁ : ℕ)) + 1) ^ 4 * (2 * ((N₁:ℝ) + (n - N₁ : ℕ)) + 1))) :=
          Finset.sum_le_sum (fun n hn => htail1 n (Finset.mem_Ico.mp hn).1)
      _ = WR p M N₁ ^ 2 * ∑ i ∈ Finset.range (N - N₁),
            1 / ((((N₁:ℝ) + i) + 1) ^ 4 * (2 * ((N₁:ℝ) + i) + 1)) := by
          rw [← Finset.mul_sum, Finset.sum_Ico_eq_sum_range]
          congr 1
          apply Finset.sum_congr rfl; intro i _
          rw [Nat.add_sub_cancel_left]
      _ ≤ WR p M N₁ ^ 2 * TA9 N₁ := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          exact (TA9_summable N₁).sum_le_tsum _ (fun i _ => by positivity)
      _ ≤ WR p M N₁ ^ 2 * (1 / ((N₁:ℝ) * (2 * (N₁:ℝ) + 1) ^ 3)) :=
          mul_le_mul_of_nonneg_left (tail_T_le N₁ (hM.trans hMN)) (sq_nonneg _)
      _ = WR p M N₁ ^ 2 / ((N₁:ℝ) * (2 * (N₁:ℝ) + 1) ^ 3) := by ring
  linarith [hmid, htail]

/-! ### 6. Theorem A.10 -/

/-- 对每个截断 `N = K+1 ≥ N₁`：`λ₁^{(N)}(k⁻²) ≤ ρ + r²/(ρ − 13/25)`。 -/
theorem lamN_le_temple {p : ℕ → ℝ} {M N₁ : ℕ} (hs : ∀ n, M ≤ n → p n = 0)
    (hp : ∀ n, n < M → 0 < p n) (hM : 1 ≤ M) (hMN : M ≤ N₁) (hρ : 13/25 < rhoR p M)
    (K : ℕ) (hK : N₁ ≤ K + 1) :
    lamN (fun k => 1 / (k:ℝ) ^ 2) K ≤ rhoR p M + r2R p M N₁ / (rhoR p M - 13/25) := by
  have hMK : M ≤ K + 1 := hMN.trans hK
  have hext : ∀ n < K + 1, extN (xOf p (K+1)) n = vOf p n := by
    intro n hn; unfold extN xOf; rw [dif_pos hn]
  have hS : xOf p (K+1) ⬝ᵥ xOf p (K+1) = nv2R p M := by
    rw [← sum_extN_sq, ← sum_vOf_sq hs hMK]
    apply Finset.sum_congr rfl; intro n hn; rw [hext n (Finset.mem_range.mp hn)]
  have hP : xOf p (K+1) ⬝ᵥ (ON (fun k => 1 / (k:ℝ) ^ 2) : Matrix (Fin (K+1)) (Fin (K+1)) ℝ)
      *ᵥ xOf p (K+1) = QR p M := by
    rw [quadForm_eq_dot, ← quadForm_vOf hs hMK]
    exact quadForm_congr _ (K+1) hext
  have hSpos : 0 < nv2R p M := nv2R_pos hp hM
  have hρβ : 0 < rhoR p M - 13/25 := by linarith
  have hβS : (13/25 : ℝ) * (xOf p (K+1) ⬝ᵥ xOf p (K+1))
      < xOf p (K+1) ⬝ᵥ (ON (fun k => 1 / (k:ℝ) ^ 2) : Matrix (Fin (K+1)) (Fin (K+1)) ℝ) *ᵥ xOf p (K+1) := by
    rw [hS, hP]
    unfold rhoR at hρ
    rw [lt_div_iff₀ hSpos] at hρ
    exact hρ
  have hT := temple' (ON_isHermitian (N := K+1) (fun k => 1 / (k:ℝ) ^ 2)) (13/25) (AN_spec_le K)
    (xOf p (K+1)) (hS ▸ hSpos) hβS
  rw [hS, hP, show QR p M / nv2R p M = rhoR p M from rfl, resid_norm hs hMK] at hT
  have hRR := resid_le_RR hs hp hM hMN hK
  have h1 := div_le_div_of_nonneg_right hRR hSpos.le
  have h2 := div_le_div_of_nonneg_right h1 hρβ.le
  unfold lamN r2R
  linarith

/-- **Theorem A.10（Theorem (∗)）**：`M ≥ 1`、`N₁ ≥ M`、`p` 支撑在 `[0,M)` 且在其上严格正，
`ρ > 13/25` ⇒ `ρ ≤ g(2) ≤ ρ + r²/(ρ − 13/25)`。 -/
theorem theorem_A10 {p : ℕ → ℝ} {M N₁ : ℕ} (hs : ∀ n, M ≤ n → p n = 0)
    (hp : ∀ n, n < M → 0 < p n) (hM : 1 ≤ M) (hMN : M ≤ N₁) (hρ : 13/25 < rhoR p M) :
    rhoR p M ≤ g2 ∧ g2 ≤ rhoR p M + r2R p M N₁ / (rhoR p M - 13/25) := by
  constructor
  · have h := quadForm_le_lam1_mul invSq_L1 (vOf p) M
    rw [quadForm_vOf hs le_rfl, sum_vOf_sq hs le_rfl] at h
    unfold rhoR g2
    rw [div_le_iff₀ (nv2R_pos hp hM)]
    exact h
  · unfold g2
    rw [lam1_eq_iSup_lamN invSq_L1]
    apply ciSup_le
    intro K
    have hmono := lamN_mono (fun k => 1 / (k:ℝ) ^ 2) (le_max_left K N₁)
    exact hmono.trans (lamN_le_temple hs hp hM hMN hρ (max K N₁)
      ((le_max_right K N₁).trans (Nat.le_succ _)))

end Eliashberg
