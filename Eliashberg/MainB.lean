import Eliashberg.MainA

/-!
# 主定理 II：Theorem 2.1（Theorem B）、Lemma 2.2、Theorem 2.3（Theorem A(c)）、Corollary 2.4

记 `h(ϖ) := λ₁(O[[[·]](ϖ)])`（`hh ϖ`）、`g(2) := λ₁(O[k ↦ k⁻²])`（`g2`）、`r(ϖ) := h(ϖ)/ϖ²`（`rr ϖ`）。

* **`theorem_2_1`（Theorem B）**：`k(P,T) ≤ h(ϖ_rms)`；`theorem_2_1_strict`：`ω` 非几乎处处常数时严格；
  `theorem_2_1_eq_of_ae_const`：`ω` 几乎处处等于 `ω_E` 时取等（点质量）
* **`lemma_2_2_h_eq`**：`h(ϖ) = ϖ² r(ϖ)`；**`lemma_2_2_r_strictAnti`**：`r` 严格递减；
  **`lemma_2_2_r_lt_g2`**：`r(ϖ) < g(2)`，即 `h(ϖ) < g(2) ϖ²`；**`lemma_2_2_r_tendsto`**：`r(0⁺) = g(2)`
* **`theorem_2_3`（Theorem A(c)）**：`k(P,T) < g(2)⟨ω²⟩/(2πT)²`；**`theorem_2_3_Tc`**：
  `T_c < T̃_c := √(g(2)⟨ω²⟩λ)/(2π)`
* **`corollary_2_4_i`**：`ϖ ↦ h(ϖ)` 严格递增；(ii) 即 Lemma 2.2；(iv) 即 `lamN_tendsto`；(v) 即 `lamM_sub_le`
* Corollary 2.4(iii) 的数值区间 `C_∞ ∈ [0.182726247746, 0.182726247790]` 来自 Appendix A 的
  计算机辅助区间算术，**未形式化**；`theorem_2_3_Tc` 以 `g(2)` 为参数陈述，任何 `g(2)` 的上界都可直接代入。
-/

namespace Eliashberg

open scoped BigOperators
open Filter Topology MeasureTheory

/-! ### 几个核函数的 `ℓ¹` 性质 -/

lemma kern_L1 (ϖ : ℝ) : L1 (fun k => kern k ϖ) :=
  L1_of_summable_nonneg (kern_summable ϖ) (fun k => kern_nonneg _ _)

lemma invSqAdd_summable (ϖ : ℝ) : Summable (fun k : ℕ => 1 / (((k+1:ℕ):ℝ) ^ 2 + ϖ ^ 2)) := by
  apply Summable.of_nonneg_of_le (fun k => by positivity) _ hasSum_zeta_two_shift.summable
  intro k
  push_cast
  apply one_div_le_one_div_of_le (by positivity)
  linarith [sq_nonneg ϖ]

lemma invSqAdd_L1 (ϖ : ℝ) : L1 (fun k => 1 / ((k:ℝ) ^ 2 + ϖ ^ 2)) :=
  L1_of_summable_nonneg (invSqAdd_summable ϖ) (fun k => by positivity)

lemma invSq_L1 : L1 (fun k => 1 / (k:ℝ) ^ 2) := by
  have := invSqAdd_L1 0
  simpa using this

/-! ### `h`、`g(2)`、`r` -/

/-- `h(ϖ) := λ₁(O[[[·]](ϖ)])`。 -/
noncomputable def hh (ϖ : ℝ) : ℝ := lam1 (fun k => kern k ϖ)

/-- `g(2) := λ₁(O[k ↦ k⁻²])`。 -/
noncomputable def g2 : ℝ := lam1 (fun k => 1 / (k:ℝ) ^ 2)

/-- `r(ϖ) := λ₁(O[k ↦ (k²+ϖ²)⁻¹])`（论文：`= h(ϖ)/ϖ²`）。 -/
noncomputable def rr (ϖ : ℝ) : ℝ := lam1 (fun k => 1 / ((k:ℝ) ^ 2 + ϖ ^ 2))

lemma one_le_g2 : 1 ≤ g2 := by
  have h := f1_le_lam1 invSq_L1
  have e : (1:ℝ) = 1 / ((1:ℕ):ℝ) ^ 2 := by norm_num
  unfold g2
  exact e.le.trans h

/-- **Lemma 2.2，第一句**：`h(ϖ) = ϖ² r(ϖ)`（`ϖ ≠ 0`）。 -/
theorem lemma_2_2_h_eq (ϖ : ℝ) (hϖ : ϖ ≠ 0) : hh ϖ = ϖ ^ 2 * rr ϖ := by
  unfold hh rr
  have e : (fun k : ℕ => kern k ϖ) = fun k : ℕ => ϖ ^ 2 * (1 / ((k:ℝ) ^ 2 + ϖ ^ 2)) := by
    funext k; unfold kern; ring
  rw [e]
  exact lam1_smul (invSqAdd_L1 ϖ) (ϖ ^ 2) (by positivity)

/-- **Lemma 2.2，单调性**：`0 < ϖ < ϖ'` ⇒ `r(ϖ') < r(ϖ)`。 -/
theorem lemma_2_2_r_strictAnti (ϖ ϖ' : ℝ) (hϖ : 0 < ϖ) (hϖϖ : ϖ < ϖ') : rr ϖ' < rr ϖ := by
  unfold rr
  have hsq : ϖ ^ 2 < ϖ' ^ 2 := by nlinarith
  have hF1 : (0:ℝ) < 1 / (((1:ℕ):ℝ) ^ 2 + ϖ' ^ 2) := by positivity
  refine lam1_lt (invSqAdd_L1 ϖ') (inv_sq_add_anti ϖ') (inv_sq_add_pos ϖ') hF1 (invSqAdd_L1 ϖ) ?_ ?_
  · intro k hk
    have hk' : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  · apply one_div_lt_one_div_of_lt (by positivity)
    push_cast; linarith

/-- **Lemma 2.2，上界**：`ϖ > 0` ⇒ `r(ϖ) < g(2)`。 -/
theorem lemma_2_2_r_lt_g2 (ϖ : ℝ) (hϖ : 0 < ϖ) : rr ϖ < g2 := by
  unfold rr g2
  have hsq : 0 < ϖ ^ 2 := by positivity
  have hF1 : (0:ℝ) < 1 / (((1:ℕ):ℝ) ^ 2 + ϖ ^ 2) := by positivity
  refine lam1_lt (invSqAdd_L1 ϖ) (inv_sq_add_anti ϖ) (inv_sq_add_pos ϖ) hF1 invSq_L1 ?_ ?_
  · intro k hk
    have hk' : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  · apply one_div_lt_one_div_of_lt (by positivity)
    push_cast; linarith

/-- **Lemma 2.2**：`h(ϖ) < g(2) ϖ²`。 -/
theorem lemma_2_2_h_lt (ϖ : ℝ) (hϖ : 0 < ϖ) : hh ϖ < g2 * ϖ ^ 2 := by
  rw [lemma_2_2_h_eq ϖ (ne_of_gt hϖ), mul_comm]
  exact mul_lt_mul_of_pos_right (lemma_2_2_r_lt_g2 ϖ hϖ) (by positivity)

/-- `ζ(4)` 的移位和 `∑_{k≥0} 1/(k+1)⁴` 可和。 -/
lemma summable_inv_pow_four : Summable (fun k : ℕ => 1 / ((k:ℝ) + 1) ^ 4) := by
  have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 4))
  simpa using this

/-- 逐项：`|(k+1)²+ϖ²)⁻¹ − (k+1)⁻²| ≤ ϖ²/(k+1)⁴`。 -/
lemma invSqAdd_sub_term_le (ϖ : ℝ) (k : ℕ) :
    |(1:ℝ) / (((k+1:ℕ):ℝ) ^ 2 + ϖ ^ 2) - 1 / ((k+1:ℕ):ℝ) ^ 2| ≤ ϖ ^ 2 * (1 / ((k:ℝ) + 1) ^ 4) := by
  push_cast
  have hk2 : (0:ℝ) < ((k:ℝ) + 1) ^ 2 := by positivity
  have hden : (0:ℝ) < ((k:ℝ) + 1) ^ 2 + ϖ ^ 2 := by positivity
  have e : 1 / (((k:ℝ) + 1) ^ 2 + ϖ ^ 2) - 1 / ((k:ℝ) + 1) ^ 2
      = -(ϖ ^ 2 / (((k:ℝ) + 1) ^ 2 * (((k:ℝ) + 1) ^ 2 + ϖ ^ 2))) := by
    rw [div_sub_div _ _ (ne_of_gt hden) (ne_of_gt hk2)]
    ring
  rw [e, abs_neg, abs_of_nonneg (by positivity), div_eq_mul_one_div]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg ϖ)
  apply one_div_le_one_div_of_le (by positivity)
  have : ((k:ℝ) + 1) ^ 4 = ((k:ℝ) + 1) ^ 2 * ((k:ℝ) + 1) ^ 2 := by ring
  rw [this]
  apply mul_le_mul_of_nonneg_left _ (le_of_lt hk2)
  linarith [sq_nonneg ϖ]

/-- `‖(k²+ϖ²)⁻¹ − k⁻²‖_ℓ¹ ≤ ϖ² ζ(4)`。 -/
lemma l1_invSqAdd_sub_le (ϖ : ℝ) :
    l1 (fun k => 1 / ((k:ℝ) ^ 2 + ϖ ^ 2) - 1 / (k:ℝ) ^ 2)
      ≤ ϖ ^ 2 * ∑' k : ℕ, 1 / ((k:ℝ) + 1) ^ 4 := by
  unfold l1
  rw [← tsum_mul_left]
  have hs2 : Summable (fun k : ℕ => ϖ ^ 2 * (1 / ((k:ℝ) + 1) ^ 4)) :=
    summable_inv_pow_four.mul_left _
  have hs1 : Summable (fun k : ℕ => |(1:ℝ) / (((k+1:ℕ):ℝ) ^ 2 + ϖ ^ 2) - 1 / ((k+1:ℕ):ℝ) ^ 2|) :=
    Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => invSqAdd_sub_term_le ϖ k) hs2
  exact Summable.tsum_le_tsum (fun k => invSqAdd_sub_term_le ϖ k) hs1 hs2

/-- **Lemma 2.2，极限**：`r(ϖ) → g(2)`（`ϖ ↓ 0`）。
证：`|r(ϖ) − g(2)| ≤ 5‖k⁻² − (k²+ϖ²)⁻¹‖_ℓ¹ = 5 ∑_k ϖ²/(k²(k²+ϖ²)) ≤ 5ϖ² ζ(4)`（(S2) 与 Lemma 0.2.1）。 -/
theorem lemma_2_2_r_tendsto : Tendsto rr (𝓝[>] 0) (𝓝 g2) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  set ζ4 : ℝ := ∑' k : ℕ, 1 / ((k:ℝ) + 1) ^ 4 with hζ4
  have hlim : Tendsto (fun ϖ : ℝ => 5 * ζ4 * ϖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun ϖ : ℝ => 5 * ζ4 * ϖ ^ 2) (𝓝 0) (𝓝 (5 * ζ4 * 0 ^ 2)) :=
      ((continuous_const.mul (continuous_id.pow 2)).tendsto 0)
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  apply squeeze_zero' (Eventually.of_forall (fun ϖ => norm_nonneg _)) _ hlim
  filter_upwards [self_mem_nhdsWithin] with ϖ _
  rw [Real.norm_eq_abs]
  have hL : |rr ϖ - g2| ≤ 5 * l1 (fun k => 1 / ((k:ℝ) ^ 2 + ϖ ^ 2) - 1 / (k:ℝ) ^ 2) :=
    abs_lam1_sub_le (invSqAdd_L1 ϖ) invSq_L1
  have hsum := l1_invSqAdd_sub_le ϖ
  rw [← hζ4] at hsum
  linarith

/-! ### Theorem B -/

section

variable (P : Measure ℝ) [IsProbabilityMeasure P]

/-- **Theorem 2.1（Theorem B），不等式**：`k(P,T) ≤ h(ϖ_rms)`。 -/
theorem theorem_2_1 (hP : ∀ᵐ ω ∂P, 0 < ω) (hm : Integrable (fun ω => ω ^ 2) P) (T : ℝ) (hT : 0 < T) :
    kk P T ≤ hh (varpiRms P T) := by
  unfold kk hh
  apply lam1_mono (FT_anti_k P hP T hT) (FT_nonneg' P T) _ (kern_L1 _)
  intro k hk
  exact FT_le_kern_rms P hm k hk T hT

/-- **Theorem 2.1，严格情形**：`ω²` 非几乎处处常数（`P` 非点质量）⇒ `k(P,T) < h(ϖ_rms)`。 -/
theorem theorem_2_1_strict (hP : ∀ᵐ ω ∂P, 0 < ω) (hm : Integrable (fun ω => ω ^ 2) P)
    (hnc : ¬ ((fun ω : ℝ => ω ^ 2) =ᵐ[P] (fun _ => moment2 P))) (T : ℝ) (hT : 0 < T) :
    kk P T < hh (varpiRms P T) := by
  rcases FT_ae_const_or_lt_kern_rms P hm 1 le_rfl T hT with h | h
  · exact absurd h hnc
  · unfold kk hh
    apply lam1_lt (L1_FT P hm T hT) (FT_anti_k P hP T hT) (FT_nonneg' P T)
      (FT_pos P hP 1 le_rfl T hT) (kern_L1 _)
    · intro k hk; exact FT_le_kern_rms P hm k hk T hT
    · exact h

/-- **Theorem 2.1，等号情形**：`ω` 几乎处处等于 `ω_E > 0`（`P` 是点质量）⇒ `k(P,T) = h(ϖ_rms)`。 -/
theorem theorem_2_1_eq_of_ae_const (ωE : ℝ) (hωE : 0 ≤ ωE) (hae : ∀ᵐ ω ∂P, ω = ωE) (T : ℝ) :
    kk P T = hh (varpiRms P T) := by
  have hFT : FT P T = fun k => kern k (ωE / (2 * Real.pi * T)) := by
    funext k
    unfold FT
    have h1 : (fun ω : ℝ => kern k (ω / (2 * Real.pi * T)))
        =ᵐ[P] (fun _ => kern k (ωE / (2 * Real.pi * T))) :=
      hae.mono (fun ω hω => by simp only [hω])
    rw [integral_congr_ae h1, integral_const, probReal_univ, one_smul]
  have hm2 : moment2 P = ωE ^ 2 := by
    unfold moment2
    have h1 : (fun ω : ℝ => ω ^ 2) =ᵐ[P] (fun _ => ωE ^ 2) :=
      hae.mono (fun ω hω => by simp only [hω])
    rw [integral_congr_ae h1, integral_const, probReal_univ, one_smul]
  have hrms : varpiRms P T = ωE / (2 * Real.pi * T) := by
    unfold varpiRms; rw [hm2, Real.sqrt_sq hωE]
  unfold kk hh
  rw [hFT, hrms]

/-- **Theorem 2.1，完整的「当且仅当」**：`k(P,T) = h(ϖ_rms) ⟺ ω² 几乎处处为常数`
（对概率测度即 `P` 是点质量）。 -/
theorem theorem_2_1_iff (hP : ∀ᵐ ω ∂P, 0 < ω) (hm : Integrable (fun ω => ω ^ 2) P) (T : ℝ) (hT : 0 < T) :
    kk P T = hh (varpiRms P T) ↔ ((fun ω : ℝ => ω ^ 2) =ᵐ[P] (fun _ => moment2 P)) := by
  constructor
  · intro heq
    by_contra hnc
    exact absurd heq (ne_of_lt (theorem_2_1_strict P hP hm hnc T hT))
  · intro hae
    -- `ω² = ⟨ω²⟩` 且 `ω > 0` 几乎处处 ⇒ `ω = √⟨ω²⟩` 几乎处处
    have hae' : ∀ᵐ ω ∂P, ω = Real.sqrt (moment2 P) := by
      filter_upwards [hae, hP] with ω hω hpos
      have hω' : ω ^ 2 = moment2 P := hω
      rw [← hω', Real.sqrt_sq (le_of_lt hpos)]
    exact theorem_2_1_eq_of_ae_const P (Real.sqrt (moment2 P)) (Real.sqrt_nonneg _) hae' T

/-- 二阶矩严格正（`P((0,∞)) = 1`）。 -/
lemma moment2_pos (hP : ∀ᵐ ω ∂P, 0 < ω) (hm : Integrable (fun ω => ω ^ 2) P) : 0 < moment2 P := by
  unfold moment2
  rw [integral_pos_iff_support_of_nonneg (fun ω => sq_nonneg ω) hm]
  have hsub : Set.Ioi (0:ℝ) ⊆ Function.support (fun ω : ℝ => ω ^ 2) := by
    intro ω hω
    simp only [Set.mem_Ioi] at hω
    simp only [Function.mem_support]
    positivity
  calc (0:ENNReal) < 1 := by norm_num
    _ = P (Set.Ioi 0) := (prob_Ioi_eq_one P hP).symm
    _ ≤ _ := measure_mono hsub

/-! ### Theorem 2.3 -/

/-- **Theorem 2.3（Theorem A(c)）**：`k(P,T) < g(2)⟨ω²⟩/(2πT)²`。 -/
theorem theorem_2_3 (hP : ∀ᵐ ω ∂P, 0 < ω) (hm : Integrable (fun ω => ω ^ 2) P) (T : ℝ) (hT : 0 < T) :
    kk P T < g2 * varpiSq P T := by
  have hm0 := moment2_pos P hP hm
  have hrms : 0 < varpiRms P T := by
    unfold varpiRms
    exact div_pos (Real.sqrt_pos.mpr hm0) (two_pi_T_pos T hT)
  have h1 := theorem_2_1 P hP hm T hT
  have h2 := lemma_2_2_h_lt (varpiRms P T) hrms
  have e : varpiRms P T ^ 2 = varpiSq P T := by
    unfold varpiRms varpiSq
    rw [div_pow, Real.sq_sqrt (le_of_lt hm0)]
  rw [e] at h2
  linarith

/-- **Theorem 2.3，第二句**：`λ k(P,T_c) = 1` ⇒ `T_c < T̃_c := √(g(2)⟨ω²⟩λ)/(2π)`。 -/
theorem theorem_2_3_Tc (hP : ∀ᵐ ω ∂P, 0 < ω) (hm : Integrable (fun ω => ω ^ 2) P)
    (lam Tc : ℝ) (hlam : 0 < lam) (hTc : 0 < Tc) (hcrit : lam * kk P Tc = 1) :
    Tc < Real.sqrt (g2 * moment2 P * lam) / (2 * Real.pi) := by
  have h := theorem_2_3 P hP hm Tc hTc
  unfold varpiSq at h
  have hpi := two_pi_T_pos Tc hTc
  have hpi0 : (0:ℝ) < 2 * Real.pi := by have := Real.pi_pos; positivity
  -- `1 = λ k < λ g(2) ⟨ω²⟩/(2πT_c)²`
  have h1 : 1 < lam * (g2 * (moment2 P / (2 * Real.pi * Tc) ^ 2)) := by
    rw [← hcrit]; exact mul_lt_mul_of_pos_left h hlam
  have h2 : (2 * Real.pi * Tc) ^ 2 < g2 * moment2 P * lam := by
    have e : lam * (g2 * (moment2 P / (2 * Real.pi * Tc) ^ 2))
        = (g2 * moment2 P * lam) / (2 * Real.pi * Tc) ^ 2 := by ring
    rw [e, lt_div_iff₀ (by positivity)] at h1
    linarith
  rw [lt_div_iff₀ hpi0]
  have h3 : 2 * Real.pi * Tc = Tc * (2 * Real.pi) := by ring
  rw [← h3]
  exact (Real.lt_sqrt (le_of_lt hpi)).mpr h2

/-! ### Corollary 2.4(i) -/

/-- **Corollary 2.4(i)**（= Remark 1.15(b)）：`ϖ ↦ h(ϖ)` 在 `(0,∞)` 严格递增。 -/
theorem corollary_2_4_i (ϖ ϖ' : ℝ) (hϖ : 0 < ϖ) (hϖϖ : ϖ < ϖ') : hh ϖ < hh ϖ' := by
  unfold hh
  have hϖ' : 0 < ϖ' := lt_trans hϖ hϖϖ
  apply lam1_lt (kern_L1 ϖ) _ (fun k _ => kern_nonneg k ϖ) (kern_pos 1 ϖ (ne_of_gt hϖ)) (kern_L1 ϖ')
  · intro k hk
    exact le_of_lt (kern_strictMonoOn_ϖ k hk (le_of_lt hϖ) (le_of_lt hϖ') hϖϖ)
  · exact kern_strictMonoOn_ϖ 1 le_rfl (le_of_lt hϖ) (le_of_lt hϖ') hϖϖ
  · intro k hk
    exact le_of_lt (kern_strictAnti_k ϖ (ne_of_gt hϖ) (Nat.lt_succ_self k))

end

end Eliashberg
