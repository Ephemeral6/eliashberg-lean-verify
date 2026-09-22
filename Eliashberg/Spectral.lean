import Eliashberg.ConeFinite

/-!
# 有限维谱论：Rayleigh 刻画、(F3) 的有限维形式、锥中的顶特征向量

论文 §1.3 的 (F1)、(F3) 与 Proposition 1.12 在 `N × N` 实对称矩阵上的版本。
mathlib 只有**有限维**谱定理（`Matrix.IsHermitian.eigenvectorBasis`），这里正是用它。

* `top hA`：最大特征值 `λ₁(A)`
* `dot_mulVec_le`、**`top_isGreatest`**：(F1) 的 Rayleigh 刻画
  `λ₁(A) = max {⟨x, Ax⟩ : ⟨x,x⟩ = 1}`
* `exp_smul_mulVec_eigen`：`A w = μ w ⇒ e^{tA} w = e^{tμ} w`
* `topProj`、**`tendsto_exp_smul_topProj`**：(F3) 的有限维形式
  `e^{-tλ₁} e^{tA} v → Π v`（`Π` 是到顶特征空间的正交投影），`t → ∞`
* `topProj_ne_zero`：`Π ≠ 0`
* **`exists_cone_eigenvector`**：Proposition 1.12(3) 的有限维形式——若 `e^{tA}`（`t ≥ 0`）保持 `C_N`，
  则存在 `v ∈ C_N`、`v ≠ 0`，`A v = λ₁ v`

## 与论文的对应

论文的 (F3) 用谱测度与控制收敛；有限维下谱测度是有限和，控制收敛退化为
`e^{t(μ-λ₁)} → 0`（`μ < λ₁`），即 `Real.tendsto_exp_atBot`。
论文 Proposition 1.12(3) 的「`Π` 在 `C − C` 上为零则 `Π = 0`」用到 `C − C` 稠密（Lemma 0.3.3）；
有限维下 `C_N − C_N = ℝ^N`（`x = E(Dx)⁺ − E(Dx)⁻`），不需要闭包。
-/

namespace Eliashberg

open scoped Matrix
open NormedSpace Filter Topology

section Spectral

variable {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}

/-- 特征向量（作为 `Fin N → ℝ`）。 -/
noncomputable def evec (hA : A.IsHermitian) (j : Fin N) : Fin N → ℝ := (hA.eigenvectorBasis j).ofLp

lemma mulVec_evec (hA : A.IsHermitian) (j : Fin N) :
    A *ᵥ evec hA j = hA.eigenvalues j • evec hA j := hA.mulVec_eigenvectorBasis j

/-- 正交归一：`⟨b_i, b_j⟩ = δ_{ij}`。 -/
lemma evec_dot (hA : A.IsHermitian) (i j : Fin N) :
    evec hA i ⬝ᵥ evec hA j = if i = j then 1 else 0 := by
  have h := (orthonormal_iff_ite.mp hA.eigenvectorBasis.orthonormal) i j
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at h
  unfold evec
  rw [dotProduct_comm]
  exact h

/-- 展开系数 `c_j(v) := ⟨b_j, v⟩`。 -/
noncomputable def coeff (hA : A.IsHermitian) (v : Fin N → ℝ) (j : Fin N) : ℝ := evec hA j ⬝ᵥ v

/-- `v = ∑_j c_j(v) b_j`。 -/
lemma sum_coeff_smul (hA : A.IsHermitian) (v : Fin N → ℝ) :
    ∑ j, coeff hA v j • evec hA j = v := by
  have h := hA.eigenvectorBasis.sum_repr' (WithLp.toLp 2 v)
  have h' := congrArg WithLp.ofLp h
  rw [WithLp.ofLp_sum] at h'
  simp only [WithLp.ofLp_smul] at h'
  convert h' using 2 with j
  unfold coeff evec
  congr 1
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, WithLp.ofLp_toLp, dotProduct_comm]

/-- `(∑_i c_i b_i) ⬝ (∑_j d_j b_j) = ∑_i c_i d_i`。 -/
lemma dot_expand (hA : A.IsHermitian) (c d : Fin N → ℝ) :
    (∑ i, c i • evec hA i) ⬝ᵥ (∑ j, d j • evec hA j) = ∑ i, c i * d i := by
  rw [sum_dotProduct]
  apply Finset.sum_congr rfl; intro i _
  rw [dotProduct_sum]
  simp only [smul_dotProduct, dotProduct_smul, evec_dot, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp [mul_comm]

lemma dot_self_eq (hA : A.IsHermitian) (v : Fin N → ℝ) : v ⬝ᵥ v = ∑ i, coeff hA v i ^ 2 := by
  conv_lhs => rw [← sum_coeff_smul hA v]
  rw [dot_expand]
  apply Finset.sum_congr rfl; intro i _; ring

lemma dot_mulVec_eq (hA : A.IsHermitian) (v : Fin N → ℝ) :
    v ⬝ᵥ A *ᵥ v = ∑ i, hA.eigenvalues i * coeff hA v i ^ 2 := by
  conv_lhs => rw [← sum_coeff_smul hA v]
  rw [Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, mulVec_evec, smul_smul]
  rw [dot_expand]
  apply Finset.sum_congr rfl; intro i _; ring

variable [NeZero N]

/-- 最大特征值 `λ₁(A)`。 -/
noncomputable def top (hA : A.IsHermitian) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty hA.eigenvalues

lemma eigenvalues_le_top (hA : A.IsHermitian) (j : Fin N) : hA.eigenvalues j ≤ top hA :=
  Finset.le_sup' hA.eigenvalues (Finset.mem_univ j)

lemma exists_eigenvalues_eq_top (hA : A.IsHermitian) : ∃ j, hA.eigenvalues j = top hA := by
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty hA.eigenvalues
  exact ⟨j, hj.symm⟩

/-- (F1) 的上界：`⟨x, Ax⟩ ≤ λ₁ ⟨x, x⟩`。 -/
theorem dot_mulVec_le (hA : A.IsHermitian) (x : Fin N → ℝ) :
    x ⬝ᵥ A *ᵥ x ≤ top hA * (x ⬝ᵥ x) := by
  rw [dot_mulVec_eq, dot_self_eq hA, Finset.mul_sum]
  apply Finset.sum_le_sum; intro i _
  exact mul_le_mul_of_nonneg_right (eigenvalues_le_top hA i) (sq_nonneg _)

/-- **(F1)**：`λ₁(A)` 是单位球面上 Rayleigh 商的最大值。 -/
theorem top_isGreatest (hA : A.IsHermitian) :
    IsGreatest {q : ℝ | ∃ x : Fin N → ℝ, x ⬝ᵥ x = 1 ∧ q = x ⬝ᵥ A *ᵥ x} (top hA) := by
  constructor
  · obtain ⟨j, hj⟩ := exists_eigenvalues_eq_top hA
    refine ⟨evec hA j, by rw [evec_dot]; simp, ?_⟩
    rw [mulVec_evec, dotProduct_smul, evec_dot, smul_eq_mul]
    simp [hj]
  · rintro q ⟨x, hx, rfl⟩
    have := dot_mulVec_le hA x
    rwa [hx, mul_one] at this

/-- 若 `x ⬝ x = 1` 则 `⟨x, Ax⟩ ≤ λ₁`。 -/
lemma dot_mulVec_le_top (hA : A.IsHermitian) (x : Fin N → ℝ) (hx : x ⬝ᵥ x = 1) :
    x ⬝ᵥ A *ᵥ x ≤ top hA := top_isGreatest hA |>.2 ⟨x, hx, rfl⟩

/-! ### 矩阵指数作用在特征向量上 -/

omit [NeZero N] in
open scoped Matrix.Norms.Operator in
/-- `A w = μ w ⇒ e^{tA} w = e^{tμ} w`。 -/
lemma exp_smul_mulVec_eigen {w : Fin N → ℝ} {μ : ℝ} (hw : A *ᵥ w = μ • w) (t : ℝ) :
    exp (t • A) *ᵥ w = Real.exp (t * μ) • w := by
  have hpow : ∀ n : ℕ, (t • A) ^ n *ᵥ w = (t * μ) ^ n • w := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, hw, Matrix.mulVec_smul,
        Matrix.mulVec_smul, ih, smul_smul, smul_smul, pow_succ]
      ring_nf
  have hs : HasSum (fun n : ℕ => ((n.factorial : ℝ)⁻¹) • (t • A) ^ n) (exp (t • A)) :=
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) _
  have h1 : Tendsto (fun n => (∑ k ∈ Finset.range n, ((k.factorial : ℝ)⁻¹) • (t • A) ^ k) *ᵥ w)
      atTop (𝓝 (exp (t • A) *ᵥ w)) :=
    ((Continuous.matrix_mulVec continuous_id continuous_const).tendsto _).comp hs.tendsto_sum_nat
  have hr : HasSum (fun n : ℕ => ((n.factorial : ℝ)⁻¹) • (t * μ) ^ n) (Real.exp (t * μ)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) _
  have h2 : Tendsto (fun n => ∑ k ∈ Finset.range n, (((k.factorial : ℝ)⁻¹) • (t * μ) ^ k) • w)
      atTop (𝓝 (Real.exp (t * μ) • w)) :=
    (hr.smul_const w).tendsto_sum_nat
  have heq : ∀ n, (∑ k ∈ Finset.range n, ((k.factorial : ℝ)⁻¹) • (t • A) ^ k) *ᵥ w
      = ∑ k ∈ Finset.range n, (((k.factorial : ℝ)⁻¹) • (t * μ) ^ k) • w := by
    intro n
    rw [Matrix.sum_mulVec]
    apply Finset.sum_congr rfl; intro k _
    rw [Matrix.smul_mulVec, hpow, smul_smul, smul_eq_mul]
  exact tendsto_nhds_unique (h1.congr heq) h2

omit [NeZero N] in
/-- `e^{tA} v = ∑_j c_j(v) e^{tλ_j} b_j`。 -/
lemma exp_smul_mulVec_expand (hA : A.IsHermitian) (v : Fin N → ℝ) (t : ℝ) :
    exp (t • A) *ᵥ v = ∑ j, (coeff hA v j * Real.exp (t * hA.eigenvalues j)) • evec hA j := by
  conv_lhs => rw [← sum_coeff_smul hA v]
  rw [Matrix.mulVec_sum]
  apply Finset.sum_congr rfl; intro j _
  rw [Matrix.mulVec_smul, exp_smul_mulVec_eigen (mulVec_evec hA j), smul_smul]

/-! ### (F3) 的有限维形式 -/

/-- 到顶特征空间的正交投影 `Π v := ∑_{λ_j = λ₁} c_j(v) b_j`。 -/
noncomputable def topProj (hA : A.IsHermitian) (v : Fin N → ℝ) : Fin N → ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => hA.eigenvalues j = top hA), coeff hA v j • evec hA j

/-- `Π v` 是 `λ₁` 的特征向量（可能为零）。 -/
lemma mulVec_topProj (hA : A.IsHermitian) (v : Fin N → ℝ) :
    A *ᵥ topProj hA v = top hA • topProj hA v := by
  unfold topProj
  rw [Matrix.mulVec_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl; intro j hj
  rw [Finset.mem_filter] at hj
  rw [Matrix.mulVec_smul, mulVec_evec, hj.2, smul_comm]

lemma topProj_sub (hA : A.IsHermitian) (x y : Fin N → ℝ) :
    topProj hA (x - y) = topProj hA x - topProj hA y := by
  unfold topProj coeff
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro j _
  rw [dotProduct_sub, sub_smul]

/-- `Π b_{j₀} = b_{j₀}`（`λ_{j₀} = λ₁`）。 -/
lemma topProj_evec (hA : A.IsHermitian) (j₀ : Fin N) (hj₀ : hA.eigenvalues j₀ = top hA) :
    topProj hA (evec hA j₀) = evec hA j₀ := by
  unfold topProj coeff
  simp only [evec_dot]
  rw [Finset.sum_filter]
  have : ∀ j, (if hA.eigenvalues j = top hA then (if j = j₀ then (1:ℝ) else 0) • evec hA j else 0)
      = if j = j₀ then evec hA j₀ else 0 := by
    intro j
    by_cases h : j = j₀
    · subst h; simp [hj₀]
    · simp [h]
  simp only [this]
  rw [Finset.sum_ite_eq']
  simp

omit [NeZero N] in
lemma evec_ne_zero (hA : A.IsHermitian) (j : Fin N) : evec hA j ≠ 0 := by
  intro h
  have := evec_dot hA j j
  rw [h] at this
  simp at this

/-- `Π ≠ 0`。 -/
lemma topProj_ne_zero (hA : A.IsHermitian) : ∃ v, topProj hA v ≠ 0 := by
  obtain ⟨j₀, hj₀⟩ := exists_eigenvalues_eq_top hA
  exact ⟨evec hA j₀, by rw [topProj_evec hA j₀ hj₀]; exact evec_ne_zero hA j₀⟩

/-- **(F3) 的有限维形式**：`e^{-tλ₁} e^{tA} v → Π v`（`t → ∞`）。 -/
theorem tendsto_exp_smul_topProj (hA : A.IsHermitian) (v : Fin N → ℝ) :
    Tendsto (fun t : ℝ => Real.exp (-(t * top hA)) • (exp (t • A) *ᵥ v)) atTop
      (𝓝 (topProj hA v)) := by
  have heq : ∀ t : ℝ, Real.exp (-(t * top hA)) • (exp (t • A) *ᵥ v)
      = ∑ j, (coeff hA v j * Real.exp (t * (hA.eigenvalues j - top hA))) • evec hA j := by
    intro t
    rw [exp_smul_mulVec_expand hA v t, Finset.smul_sum]
    apply Finset.sum_congr rfl; intro j _
    rw [smul_smul]
    congr 1
    rw [mul_sub, Real.exp_sub, Real.exp_neg]
    field_simp
  simp only [heq]
  unfold topProj
  rw [Finset.sum_filter]
  apply tendsto_finsetSum
  intro j _
  by_cases hj : hA.eigenvalues j = top hA
  · simp only [hj, sub_self, mul_zero, Real.exp_zero, mul_one, ite_true]
    exact tendsto_const_nhds
  · simp only [hj, ite_false]
    have hlt : hA.eigenvalues j - top hA < 0 :=
      sub_neg.mpr (lt_of_le_of_ne (eigenvalues_le_top hA j) hj)
    have h1 : Tendsto (fun t : ℝ => t * (hA.eigenvalues j - top hA)) atTop atBot :=
      Tendsto.atTop_mul_const_of_neg hlt tendsto_id
    have h2 : Tendsto (fun t : ℝ => Real.exp (t * (hA.eigenvalues j - top hA))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp h1
    have h3 : Tendsto (fun t : ℝ => coeff hA v j * Real.exp (t * (hA.eigenvalues j - top hA)))
        atTop (𝓝 (coeff hA v j * 0)) := tendsto_const_nhds.mul h2
    rw [mul_zero] at h3
    have h4 := h3.smul_const (evec hA j)
    rwa [zero_smul] at h4

/-! ### 锥的闭性与 `C_N − C_N = ℝ^N` -/

omit [NeZero N] in
/-- `C_N` 对逐坐标极限封闭。 -/
lemma inConeN_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] {f : ι → Fin N → ℝ} {L : Fin N → ℝ}
    (hf : Tendsto f l (𝓝 L)) (hc : ∀ᶠ i in l, InConeN (f i)) : InConeN L := by
  rw [tendsto_pi_nhds] at hf
  constructor
  · intro i j hij
    exact le_of_tendsto_of_tendsto (hf j) (hf i) (hc.mono (fun k hk => hk.1 i j hij))
  · intro i
    exact ge_of_tendsto (hf i) (hc.mono (fun k hk => hk.2 i))

omit [NeZero N] in
/-- `C_N` 对非负数乘封闭。 -/
lemma inConeN_smul {v : Fin N → ℝ} (hv : InConeN v) {c : ℝ} (hc : 0 ≤ c) : InConeN (c • v) := by
  constructor
  · intro i j hij
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (hv.1 i j hij) hc
  · intro i
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg hc (hv.2 i)

omit [NeZero N] in
/-- `y ≥ 0 ⇒ E y ∈ C_N`（阶梯基的非负组合落在锥内）。 -/
lemma inConeN_E_mulVec {y : Fin N → ℝ} (hy : ∀ i, 0 ≤ y i) : InConeN ((E : Matrix (Fin N) (Fin N) ℝ) *ᵥ y) := by
  rw [inConeN_iff, Matrix.mulVec_mulVec, D_mul_E, Matrix.one_mulVec]
  exact hy

omit [NeZero N] in
/-- **`C_N − C_N = ℝ^N`**（Lemma 0.3.3 的有限维形式）：`x = E (Dx)⁺ − E (Dx)⁻`。 -/
lemma exists_cone_sub (x : Fin N → ℝ) :
    ∃ a b : Fin N → ℝ, InConeN a ∧ InConeN b ∧ x = a - b := by
  refine ⟨E *ᵥ (D *ᵥ x)⁺, E *ᵥ (D *ᵥ x)⁻, inConeN_E_mulVec (fun i => ?_), inConeN_E_mulVec (fun i => ?_), ?_⟩
  · rw [Pi.posPart_apply]; exact posPart_nonneg _
  · rw [Pi.negPart_apply]; exact negPart_nonneg _
  · rw [← Matrix.mulVec_sub, posPart_sub_negPart, Matrix.mulVec_mulVec, E_mul_D, Matrix.one_mulVec]

/-- 若 `e^{tA}`（`t ≥ 0`）保持 `C_N`，则 `Π` 保持 `C_N`。 -/
lemma inConeN_topProj (hA : A.IsHermitian)
    (hpres : ∀ t : ℝ, 0 ≤ t → ∀ v, InConeN v → InConeN (exp (t • A) *ᵥ v))
    {v : Fin N → ℝ} (hv : InConeN v) : InConeN (topProj hA v) := by
  apply inConeN_of_tendsto (tendsto_exp_smul_topProj hA v)
  rw [eventually_atTop]
  refine ⟨0, fun t ht => ?_⟩
  exact inConeN_smul (hpres t ht v hv) (le_of_lt (Real.exp_pos _))

/-- **Proposition 1.12(3) 的有限维形式**：若 `e^{tA}`（`t ≥ 0`）保持 `C_N`，
则顶特征空间与 `C_N` 有非零交：存在 `v ∈ C_N`、`v ≠ 0`、`A v = λ₁ v`。 -/
theorem exists_cone_eigenvector (hA : A.IsHermitian)
    (hpres : ∀ t : ℝ, 0 ≤ t → ∀ v, InConeN v → InConeN (exp (t • A) *ᵥ v)) :
    ∃ v : Fin N → ℝ, InConeN v ∧ v ≠ 0 ∧ A *ᵥ v = top hA • v := by
  -- 若 `Π` 在 `C_N` 上恒零，则由 `C_N − C_N = ℝ^N` 得 `Π = 0`，与 `Π ≠ 0` 矛盾
  by_contra hcon
  push Not at hcon
  have hzero : ∀ w, InConeN w → topProj hA w = 0 := by
    intro w hw
    by_contra hne
    exact hcon (topProj hA w) (inConeN_topProj hA hpres hw) hne (mulVec_topProj hA w)
  obtain ⟨x, hx⟩ := topProj_ne_zero hA
  obtain ⟨a, b, ha, hb, hab⟩ := exists_cone_sub x
  apply hx
  rw [hab, topProj_sub, hzero a ha, hzero b hb, sub_zero]

end Spectral

end Eliashberg
