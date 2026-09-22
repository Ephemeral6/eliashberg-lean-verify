import Eliashberg.Kernel

/-!
# Lemma 0.1：平均核 `F_{P,T}(k) := ∫ [[k]](ω/2πT) P(dω)` 的性质；Theorem B 的 Jensen 步 (2.1)

论文 §0.2、Lemma 0.1、Theorem 2.1 的第一段。

## 约定

`P : Measure ℝ` 是概率测度（`[IsProbabilityMeasure P]`）。论文的标准约定 `P((0,∞)) = 1` 写成
`hP : ∀ᵐ ω ∂P, 0 < ω`；二阶矩 `⟨ω²⟩ < ∞` 写成 `hm : Integrable (fun ω => ω ^ 2) P`。
只在真正需要的地方带这两个假设（对应论文 Remark 1.2(b)、1.15(a) 的分析）。

## 结论（照 Lemma 0.1 的四条）

* (1) `FT_pos`、`FT_le_one`：`0 < F_T(k) ≤ 1`；`FT_strictAnti_k`：`k ↦ F_T(k)` 严格递减；
  `FT_tendsto_zero_k`：`F_T(k) → 0`
* (2) `FT_le_moment`：`F_T(k) ≤ ⟨ϖ²⟩/k²`；`FT_summable`、`FT_tsum_le`：`‖F_T‖_{ℓ¹} ≤ (π²/6)⟨ϖ²⟩`
* (3) `FT_continuousAt`：`T ↦ F_T(k)` 在 `(0,∞)` 连续；`FT_strictAnti_T`：严格递减
* (4) `FT_tendsto_one`：`F_T(k) → 1`（`T ↓ 0`）

以及 Theorem B 的核心不等式 (2.1)：
* `FT_le_kern_rms`：`F_{P,T}(k) ≤ [[k]](ϖ_rms)`，`ϖ_rms := √⟨ω²⟩/(2πT)`（Jensen）
* `FT_ae_const_or_lt_kern_rms`：等号成立则 `ω²` 几乎处处为常数（严格 Jensen）
* `FT_dirac`：`P = δ_{ω_E}` 时 `F_T = [[·]](ω_E/2πT)`，(2.1) 取等
-/

namespace Eliashberg

open MeasureTheory Filter Topology

/-- `F_{P,T}(k) := ∫ [[k]](ω/(2πT)) P(dω)`。 -/
noncomputable def FT (P : Measure ℝ) (T : ℝ) (k : ℕ) : ℝ :=
  ∫ ω, kern k (ω / (2 * Real.pi * T)) ∂P

/-- 二阶矩 `⟨ω²⟩ := ∫ ω² P(dω)`。 -/
noncomputable def moment2 (P : Measure ℝ) : ℝ := ∫ ω, ω ^ 2 ∂P

/-- `⟨ϖ²⟩ := ⟨ω²⟩/(2πT)²`。 -/
noncomputable def varpiSq (P : Measure ℝ) (T : ℝ) : ℝ := moment2 P / (2 * Real.pi * T) ^ 2

/-- `ϖ_rms := √⟨ω²⟩/(2πT)`。 -/
noncomputable def varpiRms (P : Measure ℝ) (T : ℝ) : ℝ := Real.sqrt (moment2 P) / (2 * Real.pi * T)

section

variable (P : Measure ℝ) [IsProbabilityMeasure P]

lemma two_pi_T_pos (T : ℝ) (hT : 0 < T) : 0 < 2 * Real.pi * T := by
  have := Real.pi_pos; positivity

lemma kern_comp_continuous (k : ℕ) (hk : 1 ≤ k) (T : ℝ) :
    Continuous (fun ω : ℝ => kern k (ω / (2 * Real.pi * T))) :=
  (kern_continuous k hk).comp (continuous_id.div_const _)

omit [IsProbabilityMeasure P] in
lemma kern_comp_aesm (k : ℕ) (hk : 1 ≤ k) (T : ℝ) :
    AEStronglyMeasurable (fun ω : ℝ => kern k (ω / (2 * Real.pi * T))) P :=
  (kern_comp_continuous k hk T).aestronglyMeasurable

lemma kern_norm_le_one (k : ℕ) (ϖ : ℝ) : ‖kern k ϖ‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (kern_nonneg _ _)]
  exact kern_le_one _ _

lemma kern_comp_integrable (k : ℕ) (hk : 1 ≤ k) (T : ℝ) :
    Integrable (fun ω : ℝ => kern k (ω / (2 * Real.pi * T))) P :=
  Integrable.of_bound (kern_comp_aesm P k hk T) 1 (ae_of_all _ (fun ω => kern_norm_le_one _ _))

/-- 由 `∀ᵐ ω, 0 < ω` 得 `P((0,∞)) = 1`。 -/
lemma prob_Ioi_eq_one (hP : ∀ᵐ ω ∂P, 0 < ω) : P (Set.Ioi 0) = 1 := by
  rw [← prob_compl_eq_zero_iff measurableSet_Ioi, Set.compl_Ioi]
  rw [ae_iff] at hP
  convert hP using 2
  ext ω; simp [not_lt]

/-! ### Lemma 0.1(1) -/

omit [IsProbabilityMeasure P] in
lemma FT_nonneg (T : ℝ) (k : ℕ) : 0 ≤ FT P T k :=
  integral_nonneg (fun ω => kern_nonneg _ _)

lemma FT_le_one (k : ℕ) (hk : 1 ≤ k) (T : ℝ) : FT P T k ≤ 1 := by
  unfold FT
  have := integral_mono (kern_comp_integrable P k hk T) (integrable_const (1:ℝ))
    (fun ω => kern_le_one k _)
  rwa [integral_const, probReal_univ, one_smul] at this

/-- 严格正性只用到 `P((0,∞)) > 0`（论文 Remark 1.15(a)）；这里用标准约定 `P((0,∞)) = 1`。 -/
lemma FT_pos (hP : ∀ᵐ ω ∂P, 0 < ω) (k : ℕ) (hk : 1 ≤ k) (T : ℝ) (hT : 0 < T) : 0 < FT P T k := by
  unfold FT
  rw [integral_pos_iff_support_of_nonneg (fun ω => kern_nonneg _ _) (kern_comp_integrable P k hk T)]
  have hsub : Set.Ioi (0:ℝ) ⊆ Function.support (fun ω : ℝ => kern k (ω / (2 * Real.pi * T))) := by
    intro ω hω
    simp only [Set.mem_Ioi] at hω
    simp only [Function.mem_support]
    apply ne_of_gt
    apply kern_pos
    have := two_pi_T_pos T hT
    positivity
  calc (0:ENNReal) < 1 := by norm_num
    _ = P (Set.Ioi 0) := (prob_Ioi_eq_one P hP).symm
    _ ≤ _ := measure_mono hsub

/-- `k ↦ [[k]](ϖ)` 非严格递减（含 `ϖ = 0`）。 -/
lemma kern_anti_k (ϖ : ℝ) : Antitone (fun k : ℕ => kern k ϖ) := by
  rcases eq_or_ne ϖ 0 with h | h
  · subst h; intro a b _; simp [kern]
  · exact (kern_strictAnti_k ϖ h).antitone

/-- Lemma 0.1(1)：`k ↦ F_T(k)` 严格递减。 -/
lemma FT_strictAnti_k (hP : ∀ᵐ ω ∂P, 0 < ω) (T : ℝ) (hT : 0 < T) (k k' : ℕ) (hk : 1 ≤ k)
    (hkk : k < k') : FT P T k' < FT P T k := by
  unfold FT
  have hint : Integrable (fun ω : ℝ => kern k (ω / (2 * Real.pi * T)) - kern k' (ω / (2 * Real.pi * T))) P :=
    (kern_comp_integrable P k hk T).sub (kern_comp_integrable P k' (by omega) T)
  have hpos : 0 < ∫ ω, (kern k (ω / (2 * Real.pi * T)) - kern k' (ω / (2 * Real.pi * T))) ∂P := by
    rw [integral_pos_iff_support_of_nonneg _ hint]
    · have hsub : Set.Ioi (0:ℝ) ⊆ Function.support
          (fun ω : ℝ => kern k (ω / (2 * Real.pi * T)) - kern k' (ω / (2 * Real.pi * T))) := by
        intro ω hω
        simp only [Set.mem_Ioi] at hω
        simp only [Function.mem_support]
        apply ne_of_gt
        apply sub_pos.mpr
        have hϖ : ω / (2 * Real.pi * T) ≠ 0 := by
          have := two_pi_T_pos T hT; positivity
        exact kern_strictAnti_k _ hϖ hkk
      calc (0:ENNReal) < 1 := by norm_num
        _ = P (Set.Ioi 0) := (prob_Ioi_eq_one P hP).symm
        _ ≤ _ := measure_mono hsub
    · intro ω
      exact sub_nonneg.mpr (kern_anti_k _ (le_of_lt hkk))
  rw [integral_sub (kern_comp_integrable P k hk T) (kern_comp_integrable P k' (by omega) T)] at hpos
  linarith

/-- Lemma 0.1(1)：`F_T(k) → 0`（`k → ∞`），控制收敛（控制函数 `1`）。 -/
lemma FT_tendsto_zero_k (T : ℝ) : Tendsto (fun k => FT P T k) atTop (𝓝 0) := by
  unfold FT
  have h := tendsto_integral_filter_of_dominated_convergence (μ := P) (l := atTop)
    (F := fun k ω => kern k (ω / (2 * Real.pi * T))) (f := fun _ => (0:ℝ)) (fun _ => (1:ℝ))
    (eventually_atTop.mpr ⟨1, fun k hk => kern_comp_aesm P k hk T⟩)
    (Eventually.of_forall (fun k => ae_of_all _ (fun ω => kern_norm_le_one _ _)))
    (integrable_const 1)
    (ae_of_all _ (fun ω => kern_tendsto_zero_k _))
  simpa using h

/-! ### Lemma 0.1(2) -/

omit [IsProbabilityMeasure P] in
lemma moment2_nonneg : 0 ≤ moment2 P := integral_nonneg (fun ω => sq_nonneg ω)

/-- Lemma 0.1(2)：`F_T(k) ≤ ⟨ϖ²⟩/k²`。 -/
lemma FT_le_moment (hm : Integrable (fun ω => ω ^ 2) P) (k : ℕ) (hk : 1 ≤ k) (T : ℝ) (hT : 0 < T) :
    FT P T k ≤ varpiSq P T / (k:ℝ) ^ 2 := by
  unfold FT varpiSq moment2
  have hc : (0:ℝ) < (2 * Real.pi * T) ^ 2 := by have := two_pi_T_pos T hT; positivity
  have h : ∀ ω : ℝ, kern k (ω / (2 * Real.pi * T)) ≤ ω ^ 2 / ((2 * Real.pi * T) ^ 2 * (k:ℝ) ^ 2) := by
    intro ω
    have := kern_le_div k hk (ω / (2 * Real.pi * T))
    rwa [div_pow, div_div] at this
  calc ∫ ω, kern k (ω / (2 * Real.pi * T)) ∂P
      ≤ ∫ ω, ω ^ 2 / ((2 * Real.pi * T) ^ 2 * (k:ℝ) ^ 2) ∂P :=
        integral_mono (kern_comp_integrable P k hk T) (hm.div_const _) h
    _ = (∫ ω, ω ^ 2 ∂P) / ((2 * Real.pi * T) ^ 2 * (k:ℝ) ^ 2) := integral_div _ _
    _ = (∫ ω, ω ^ 2 ∂P) / (2 * Real.pi * T) ^ 2 / (k:ℝ) ^ 2 := by rw [div_div]

lemma FT_summable (hm : Integrable (fun ω => ω ^ 2) P) (T : ℝ) (hT : 0 < T) :
    Summable (fun k : ℕ => FT P T (k+1)) := by
  have hs : Summable (fun k : ℕ => varpiSq P T * (1 / ((k:ℝ) + 1) ^ 2)) := by
    apply Summable.mul_left
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    simpa using this
  apply Summable.of_nonneg_of_le (fun k => FT_nonneg P T _) _ hs
  intro k
  have := FT_le_moment P hm (k+1) (Nat.succ_pos k) T hT
  push_cast at this
  rw [mul_one_div]
  exact this

/-- Lemma 0.1(2)：`‖F_T‖_{ℓ¹} = ∑_{k≥1} F_T(k) ≤ (π²/6) ⟨ϖ²⟩`。 -/
lemma FT_tsum_le (hm : Integrable (fun ω => ω ^ 2) P) (T : ℝ) (hT : 0 < T) :
    ∑' k : ℕ, FT P T (k+1) ≤ Real.pi ^ 2 / 6 * varpiSq P T := by
  have hz : HasSum (fun k : ℕ => 1 / ((k:ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    have h := hasSum_zeta_two
    have h' := (hasSum_nat_add_iff' 1).mpr h
    simp only [Finset.sum_range_one, Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, div_zero, sub_zero] at h'
    convert h' using 2
    push_cast; ring
  have hz' : HasSum (fun k : ℕ => varpiSq P T * (1 / ((k:ℝ) + 1) ^ 2))
      (varpiSq P T * (Real.pi ^ 2 / 6)) := hz.mul_left _
  have hle : ∑' k : ℕ, FT P T (k+1) ≤ ∑' k : ℕ, varpiSq P T * (1 / ((k:ℝ) + 1) ^ 2) := by
    apply (FT_summable P hm T hT).tsum_le_tsum _ hz'.summable
    intro k
    have := FT_le_moment P hm (k+1) (Nat.succ_pos k) T hT
    push_cast at this
    rw [mul_one_div]
    exact this
  rw [hz'.tsum_eq] at hle
  linarith

/-! ### Lemma 0.1(3) -/

/-- Lemma 0.1(3)：`T ↦ F_T(k)` 在每个 `T₀ > 0` 连续（控制收敛，控制函数 `1`）。 -/
lemma FT_continuousAt (k : ℕ) (hk : 1 ≤ k) (T₀ : ℝ) (hT₀ : 0 < T₀) :
    ContinuousAt (fun T => FT P T k) T₀ := by
  unfold FT
  apply continuousAt_of_dominated (bound := fun _ => (1:ℝ))
  · exact Eventually.of_forall (fun T => kern_comp_aesm P k hk T)
  · exact Eventually.of_forall (fun T => ae_of_all _ (fun ω => kern_norm_le_one _ _))
  · exact integrable_const 1
  · apply ae_of_all
    intro ω
    apply (kern_continuous k hk).continuousAt.comp
    apply ContinuousAt.div continuousAt_const (continuousAt_const.mul continuousAt_id)
    exact ne_of_gt (two_pi_T_pos T₀ hT₀)

lemma FT_continuousOn (k : ℕ) (hk : 1 ≤ k) : ContinuousOn (fun T => FT P T k) (Set.Ioi 0) :=
  fun T hT => (FT_continuousAt P k hk T hT).continuousWithinAt

/-- `|ϖ| ≤ |ϖ'|` ⇒ `[[k]](ϖ) ≤ [[k]](ϖ')`（`kern` 只依赖 `ϖ²`）。 -/
lemma kern_le_of_abs_le (k : ℕ) (hk : 1 ≤ k) (a b : ℝ) (h : |a| ≤ |b|) : kern k a ≤ kern k b := by
  have e1 : kern k a = kern k |a| := by unfold kern; rw [sq_abs]
  have e2 : kern k b = kern k |b| := by unfold kern; rw [sq_abs]
  rw [e1, e2]
  exact (kern_strictMonoOn_ϖ k hk).monotoneOn (abs_nonneg a) (abs_nonneg b) h

/-- Lemma 0.1(3)：`T ↦ F_T(k)` 在 `(0,∞)` 严格递减。 -/
lemma FT_strictAnti_T (hP : ∀ᵐ ω ∂P, 0 < ω) (k : ℕ) (hk : 1 ≤ k) (T T' : ℝ) (hT : 0 < T)
    (hTT : T < T') : FT P T' k < FT P T k := by
  unfold FT
  have hT' : 0 < T' := lt_trans hT hTT
  have hint : Integrable (fun ω : ℝ => kern k (ω / (2 * Real.pi * T)) - kern k (ω / (2 * Real.pi * T'))) P :=
    (kern_comp_integrable P k hk T).sub (kern_comp_integrable P k hk T')
  have hpos : 0 < ∫ ω, (kern k (ω / (2 * Real.pi * T)) - kern k (ω / (2 * Real.pi * T'))) ∂P := by
    rw [integral_pos_iff_support_of_nonneg _ hint]
    · have hsub : Set.Ioi (0:ℝ) ⊆ Function.support
          (fun ω : ℝ => kern k (ω / (2 * Real.pi * T)) - kern k (ω / (2 * Real.pi * T'))) := by
        intro ω hω
        simp only [Set.mem_Ioi] at hω
        simp only [Function.mem_support]
        apply ne_of_gt
        apply sub_pos.mpr
        have hlt : ω / (2 * Real.pi * T') < ω / (2 * Real.pi * T) :=
          varpi_strictAntiOn ω hω hT hT' hTT
        have h0 : 0 ≤ ω / (2 * Real.pi * T') := by
          have := two_pi_T_pos T' hT'; positivity
        exact kern_strictMonoOn_ϖ k hk h0 (le_trans h0 (le_of_lt hlt)) hlt
      calc (0:ENNReal) < 1 := by norm_num
        _ = P (Set.Ioi 0) := (prob_Ioi_eq_one P hP).symm
        _ ≤ _ := measure_mono hsub
    · intro ω
      apply sub_nonneg.mpr
      apply kern_le_of_abs_le k hk
      rw [abs_div, abs_div, abs_of_pos (two_pi_T_pos T hT), abs_of_pos (two_pi_T_pos T' hT')]
      apply div_le_div_of_nonneg_left (abs_nonneg ω) (two_pi_T_pos T hT)
      have := Real.pi_pos
      nlinarith
  rw [integral_sub (kern_comp_integrable P k hk T) (kern_comp_integrable P k hk T')] at hpos
  linarith

/-! ### Lemma 0.1(4) -/

/-- Lemma 0.1(4)：`F_T(k) → 1`（`T ↓ 0`）。这是四条中唯一用到完整归一化 `P((0,∞)) = 1` 的地方
（论文 Remark 1.15(a)：若只有 `P((0,∞)) = p`，极限是 `p`）。 -/
lemma FT_tendsto_one (hP : ∀ᵐ ω ∂P, 0 < ω) (k : ℕ) (hk : 1 ≤ k) :
    Tendsto (fun T => FT P T k) (𝓝[>] 0) (𝓝 1) := by
  unfold FT
  have h := tendsto_integral_filter_of_dominated_convergence (μ := P) (l := 𝓝[>] (0:ℝ))
    (F := fun T ω => kern k (ω / (2 * Real.pi * T))) (f := fun _ => (1:ℝ)) (fun _ => (1:ℝ))
    (Eventually.of_forall (fun T => kern_comp_aesm P k hk T))
    (Eventually.of_forall (fun T => ae_of_all _ (fun ω => kern_norm_le_one _ _)))
    (integrable_const 1)
    (hP.mono (fun ω hω => kern_varpi_tendsto_one k ω hω))
  rwa [integral_const, probReal_univ, one_smul] at h

/-! ### Theorem B 的 Jensen 步 (2.1) -/

lemma kern_comp_eq_chi (k : ℕ) (hk : 1 ≤ k) (T : ℝ) (hT : 0 < T) :
    (fun ω : ℝ => kern k (ω / (2 * Real.pi * T)))
      = (chi ((2 * Real.pi * T * k) ^ 2) ∘ fun ω => ω ^ 2) := by
  funext ω
  exact kern_eq_chi k hk T ω hT

lemma y_pos (k : ℕ) (hk : 1 ≤ k) (T : ℝ) (hT : 0 < T) : 0 < (2 * Real.pi * T * k) ^ 2 := by
  have : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have := two_pi_T_pos T hT
  positivity

omit [IsProbabilityMeasure P] in
/-- `χ_{(2πTk)²}(⟨ω²⟩) = [[k]](ϖ_rms)`。 -/
lemma chi_moment_eq_kern_rms (k : ℕ) (hk : 1 ≤ k) (T : ℝ) (hT : 0 < T) :
    chi ((2 * Real.pi * T * k) ^ 2) (moment2 P) = kern k (varpiRms P T) := by
  rw [chi_eq _ _ (y_pos k hk T hT) (moment2_nonneg P)]
  unfold kern varpiRms
  rw [div_pow, Real.sq_sqrt (moment2_nonneg P)]
  have hc : (2 * Real.pi * T) ≠ 0 := ne_of_gt (two_pi_T_pos T hT)
  have hk' : (k:ℝ) ≠ 0 := by
    have : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    positivity
  field_simp

/-- **(2.1)，Jensen**：`F_{P,T}(k) ≤ [[k]](ϖ_rms)`。 -/
theorem FT_le_kern_rms (hm : Integrable (fun ω => ω ^ 2) P) (k : ℕ) (hk : 1 ≤ k) (T : ℝ)
    (hT : 0 < T) : FT P T k ≤ kern k (varpiRms P T) := by
  unfold FT
  have hy := y_pos k hk T hT
  have hgi : Integrable (chi ((2 * Real.pi * T * k) ^ 2) ∘ fun ω : ℝ => ω ^ 2) P := by
    rw [← kern_comp_eq_chi k hk T hT]; exact kern_comp_integrable P k hk T
  have hJ := (chi_strictConcaveOn _ hy).concaveOn.le_map_integral (chi_continuousOn _ hy)
    isClosed_Ici (ae_of_all _ (fun ω : ℝ => (sq_nonneg ω : (fun ω : ℝ => ω ^ 2) ω ∈ Set.Ici 0)))
    hm hgi
  have e : (fun ω : ℝ => kern k (ω / (2 * Real.pi * T)))
      = fun ω => chi ((2 * Real.pi * T * k) ^ 2) (ω ^ 2) := kern_comp_eq_chi k hk T hT
  calc ∫ ω, kern k (ω / (2 * Real.pi * T)) ∂P
      = ∫ ω, chi ((2 * Real.pi * T * k) ^ 2) (ω ^ 2) ∂P := by rw [e]
    _ ≤ chi ((2 * Real.pi * T * k) ^ 2) (∫ ω, ω ^ 2 ∂P) := hJ
    _ = kern k (varpiRms P T) := chi_moment_eq_kern_rms P k hk T hT

/-- **(2.1) 的严格版本**：或者 `ω²` 几乎处处等于 `⟨ω²⟩`（`P` 是点质量），或者不等式严格。 -/
theorem FT_ae_const_or_lt_kern_rms (hm : Integrable (fun ω => ω ^ 2) P) (k : ℕ) (hk : 1 ≤ k)
    (T : ℝ) (hT : 0 < T) :
    (fun ω : ℝ => ω ^ 2) =ᵐ[P] (fun _ => moment2 P) ∨ FT P T k < kern k (varpiRms P T) := by
  unfold FT
  have hy := y_pos k hk T hT
  have hgi : Integrable (chi ((2 * Real.pi * T * k) ^ 2) ∘ fun ω : ℝ => ω ^ 2) P := by
    rw [← kern_comp_eq_chi k hk T hT]; exact kern_comp_integrable P k hk T
  have hJ := (chi_strictConcaveOn _ hy).ae_eq_const_or_lt_map_average (chi_continuousOn _ hy)
    isClosed_Ici (ae_of_all _ (fun ω : ℝ => (sq_nonneg ω : (fun ω : ℝ => ω ^ 2) ω ∈ Set.Ici 0)))
    hm hgi
  rw [average_eq_integral, average_eq_integral] at hJ
  have e : (fun ω : ℝ => kern k (ω / (2 * Real.pi * T)))
      = fun ω => chi ((2 * Real.pi * T * k) ^ 2) (ω ^ 2) := kern_comp_eq_chi k hk T hT
  rcases hJ with h | h
  · left; exact h
  · right
    rw [e, ← chi_moment_eq_kern_rms P k hk T hT]
    exact h

end

/-! ### 点质量 `P = δ_{ω_E}` -/

/-- `P = δ_{ω_E}` 时 `F_T(k) = [[k]](ω_E/2πT)`。 -/
lemma FT_dirac (ωE T : ℝ) (k : ℕ) :
    FT (Measure.dirac ωE) T k = kern k (ωE / (2 * Real.pi * T)) := by
  unfold FT
  exact integral_dirac _ ωE

lemma moment2_dirac (ωE : ℝ) : moment2 (Measure.dirac ωE) = ωE ^ 2 := by
  unfold moment2
  exact integral_dirac _ ωE

/-- `P = δ_{ω_E}`（`ω_E ≥ 0`）时 `ϖ_rms = ω_E/(2πT)`，故 (2.1) 取等。 -/
lemma varpiRms_dirac (ωE T : ℝ) (hω : 0 ≤ ωE) :
    varpiRms (Measure.dirac ωE) T = ωE / (2 * Real.pi * T) := by
  unfold varpiRms
  rw [moment2_dirac, Real.sqrt_sq hω]

theorem FT_dirac_eq_kern_rms (ωE T : ℝ) (hω : 0 ≤ ωE) (k : ℕ) :
    FT (Measure.dirac ωE) T k = kern k (varpiRms (Measure.dirac ωE) T) := by
  rw [FT_dirac, varpiRms_dirac ωE T hω]

end Eliashberg
