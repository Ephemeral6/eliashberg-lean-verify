import Eliashberg.SectionThree

/-!
# Remark 1.16(a) 的 (1.8)：`k(P,T) ≤ ∫ h(ω/2πT) P(dω)`

论文 Remark 1.16(a) 由 `f ↦ λ₁(O[f])` 的凸性（(1.7)）＋ `ω ↦ [[·]](ω/2πT)` 的 `ℓ¹` 值 Bochner
可积性得出 (1.8)。**本文件完全不用 Bochner 积分**：本库的 `λ₁` 按论文 Remark 1.2(b) 定义为
**有限支撑单位向量上 Rayleigh 商的上确界**，而每个 Rayleigh 商 `⟨v, O[f]v⟩` 是 `f` 的值的
**有限**线性组合，所以「积分与二次型交换」只用到实值积分的线性性：

`⟨v, O[F_{P,T}]v⟩ = ∫ ⟨v, O[[[·]](ω/2πT)]v⟩ P(dω) ≤ ∫ h(ω/2πT) P(dω)`，

再对 `v` 取上确界即得 (1.8)。这正是论文说的「the functional commutes with the integral」，
但因为定义已是有限和的上确界，无穷维向量值积分的构造可以整条绕开。

| 定理 | 内容 |
|---|---|
| `hh_nonneg`、`hh_zero` | `h ≥ 0`，`h(0) = 0` |
| `hext`、`hext_monotone`、`hext_measurable` | `h` 补零延拓后**全局单调**（`ϖ ≤ 0` 取 0），故可测 |
| `hh_comp_integrable` | `ω ↦ h(ω/2πT)` 可积（`0 ≤ h(ϖ) ≤ g(2)ϖ²` + `⟨ω²⟩ < ∞`） |
| `Of_integral`、`quadForm_integral` | 矩阵元与二次型都与积分交换（有限线性组合） |
| **`theorem_1_8`** | **(1.8)**：`k(P,T) ≤ ∫ h(ω/2πT) P(dω)` |
| **`integral_hh_le_of_concave`** | **猜想 ⇒ (1.8) 比 Theorem B 更紧**：`∫h dP ≤ h(ϖ_rms)` |
| **`theorem_2_1_of_theorem_1_8`** | 于是 Conjecture 3.1 ⇒ Theorem B 是 (1.8) 的推论 |

**与论文一处不符（见文件末注）**：论文 Remark 1.16(a) 说 (1.8)「is superseded by Theorem B,
which is strictly stronger」。但在论文自己的 Conjecture 3.1（`H` 凹）下，Jensen 给出
`∫ h dP ≤ h(ϖ_rms)`，即 **(1.8) 才是更紧的那个**。两者不能同时成立。
-/

namespace Eliashberg

open scoped BigOperators
open Filter Topology MeasureTheory

noncomputable section

/-! ### 一、`h` 的符号与延拓可测性 -/

/-- `h(ϖ) ≥ 0`：`λ₁ ≥ f(1) = [[1]](ϖ) ≥ 0`。 -/
lemma hh_nonneg (ϖ : ℝ) : 0 ≤ hh ϖ := by
  unfold hh
  exact le_trans (kern_nonneg 1 ϖ) (f1_le_lam1 (kern_L1 ϖ))

/-- `h(0) = 0`（`[[k]](0) = 0`）。 -/
lemma hh_zero : hh 0 = 0 := by
  have hk : (fun k : ℕ => kern k 0) = fun _ : ℕ => (0:ℝ) := by
    funext k; unfold kern; simp
  refine le_antisymm ?_ (hh_nonneg 0)
  unfold hh
  rw [hk]
  apply lam1_le
  intro v N hv
  unfold quadForm
  apply le_of_eq
  apply Finset.sum_eq_zero; intro n _
  apply Finset.sum_eq_zero; intro m _
  have hz : Of (fun _ : ℕ => (0:ℝ)) n m = 0 := by
    unfold Of; simp
  rw [hz]; ring

/-- `h` 的补零延拓：`ϖ ≤ 0` 时取 `0`。 -/
def hext (ϖ : ℝ) : ℝ := if 0 < ϖ then hh ϖ else 0

lemma hext_eq (ϖ : ℝ) (hϖ : 0 < ϖ) : hext ϖ = hh ϖ := by
  unfold hext; rw [if_pos hϖ]

/-- **延拓后全局单调**：`ϖ ≤ 0` 段恒为 `0`，`ϖ > 0` 段由 Cor 2.4(i) 严格递增，
而 `h > 0` 于 `(0,∞)`，两段在 `0` 处相接不降。 -/
lemma hext_monotone : Monotone hext := by
  intro a b hab
  unfold hext
  by_cases ha : 0 < a
  · rw [if_pos ha, if_pos (lt_of_lt_of_le ha hab)]
    rcases eq_or_lt_of_le hab with h | h
    · rw [h]
    · exact le_of_lt (corollary_2_4_i a b ha h)
  · rw [if_neg ha]
    by_cases hb : 0 < b
    · rw [if_pos hb]; exact hh_nonneg b
    · rw [if_neg hb]

lemma hext_measurable : Measurable hext := hext_monotone.measurable

/-! ### 二、`ω ↦ h(ω/2πT)` 可积 -/

variable (P : Measure ℝ) [IsProbabilityMeasure P]

lemma hh_comp_aesm (hP : ∀ᵐ ω ∂P, 0 < ω) (T : ℝ) (hT : 0 < T) :
    AEStronglyMeasurable (fun ω : ℝ => hh (ω / (2 * Real.pi * T))) P := by
  have hm : Measurable (fun ω : ℝ => hext (ω / (2 * Real.pi * T))) :=
    hext_measurable.comp (measurable_id.div_const _)
  apply hm.aestronglyMeasurable.congr
  filter_upwards [hP] with ω hω
  have hpos : 0 < ω / (2 * Real.pi * T) := by
    apply div_pos hω
    have := Real.pi_pos
    positivity
  exact hext_eq _ hpos

/-- `ω ↦ h(ω/2πT)` 可积：`0 ≤ h(ϖ) ≤ g(2)ϖ²` 且 `⟨ω²⟩ < ∞`。 -/
lemma hh_comp_integrable (hP : ∀ᵐ ω ∂P, 0 < ω) (hm : Integrable (fun ω => ω ^ 2) P)
    (T : ℝ) (hT : 0 < T) : Integrable (fun ω : ℝ => hh (ω / (2 * Real.pi * T))) P := by
  have hc : (0:ℝ) < 2 * Real.pi * T := by have := Real.pi_pos; positivity
  have hbd : Integrable (fun ω : ℝ => g2 / (2 * Real.pi * T) ^ 2 * ω ^ 2) P := hm.const_mul _
  apply Integrable.mono' hbd (hh_comp_aesm P hP T hT)
  filter_upwards [hP] with ω hω
  have hpos : 0 < ω / (2 * Real.pi * T) := div_pos hω hc
  rw [Real.norm_eq_abs, abs_of_nonneg (hh_nonneg _)]
  have h := le_of_lt (lemma_2_2_h_lt _ hpos)
  calc hh (ω / (2 * Real.pi * T)) ≤ g2 * (ω / (2 * Real.pi * T)) ^ 2 := h
    _ = g2 / (2 * Real.pi * T) ^ 2 * ω ^ 2 := by rw [div_pow]; ring

/-! ### 三、矩阵元与二次型和积分交换（有限线性组合） -/

/-- `O[·]_{nm}` 与积分交换：`Of` 只用到 `f` 在有限多个下标上的值。 -/
lemma Of_integral (φ : ℕ → ℝ → ℝ) (hint : ∀ k, Integrable (φ k) P) (n m : ℕ) :
    Of (fun k => ∫ ω, φ k ω ∂P) n m = ∫ ω, Of (fun k => φ k ω) n m ∂P := by
  unfold Of
  have hdiag : Integrable (fun ω => -(2 * u n ^ 2 * ∑ k ∈ Finset.Icc 1 n, φ k ω)) P := by
    apply Integrable.neg
    exact Integrable.const_mul (integrable_finset_sum _ (fun k _ => hint k)) _
  have hoff : Integrable (fun ω => if n ≠ m then φ (Nat.dist n m) ω * (u n * u m) else 0) P := by
    by_cases h : n ≠ m
    · simp only [if_pos h]
      exact (hint _).mul_const _
    · simp only [if_neg h]
      exact integrable_zero _ _ _
  have hlast : Integrable (fun ω => φ (n + m + 1) ω * (u n * u m)) P := (hint _).mul_const _
  rw [integral_add (by
        by_cases h : n = m
        · simp only [if_pos h]; exact hdiag.add hoff
        · simp only [if_neg h]; exact (integrable_zero _ _ _).add hoff) hlast,
      integral_add (by
        by_cases h : n = m
        · simp only [if_pos h]; exact hdiag
        · simp only [if_neg h]; exact integrable_zero _ _ _) hoff]
  congr 1
  · congr 1
    · by_cases h : n = m
      · simp only [if_pos h]
        rw [integral_neg, integral_const_mul,
          integral_finsetSum _ (fun k _ => hint k)]
      · simp only [if_neg h, integral_zero]
    · by_cases h : n ≠ m
      · simp only [if_pos h, integral_mul_const]
      · simp only [if_neg h, integral_zero]
  · rw [integral_mul_const]

/-- `ω ↦ O[φ(·,ω)]_{nm}` 可积。 -/
lemma Of_integrable (φ : ℕ → ℝ → ℝ) (hint : ∀ k, Integrable (φ k) P) (n m : ℕ) :
    Integrable (fun ω => Of (fun k => φ k ω) n m) P := by
  unfold Of
  apply Integrable.add
  · apply Integrable.add
    · by_cases h : n = m
      · simp only [if_pos h]
        exact Integrable.neg (Integrable.const_mul
          (integrable_finset_sum _ (fun k _ => hint k)) _)
      · simp only [if_neg h]; exact integrable_zero _ _ _
    · by_cases h : n ≠ m
      · simp only [if_pos h]; exact (hint _).mul_const _
      · simp only [if_neg h]; exact integrable_zero _ _ _
  · exact (hint _).mul_const _

/-- `ω ↦ ⟨v, O[φ(·,ω)]v⟩` 可积（有限和）。 -/
lemma quadForm_integrable (φ : ℕ → ℝ → ℝ) (hint : ∀ k, Integrable (φ k) P)
    (v : ℕ → ℝ) (N : ℕ) : Integrable (fun ω => quadForm (fun k => φ k ω) v N) P := by
  unfold quadForm
  apply integrable_finset_sum _ (fun n _ => integrable_finset_sum _ (fun m _ => ?_))
  exact ((Of_integrable P φ hint n m).const_mul (v n)).mul_const (v m)

/-- 二次型与积分交换。 -/
lemma quadForm_integral (φ : ℕ → ℝ → ℝ) (hint : ∀ k, Integrable (φ k) P)
    (v : ℕ → ℝ) (N : ℕ) :
    quadForm (fun k => ∫ ω, φ k ω ∂P) v N = ∫ ω, quadForm (fun k => φ k ω) v N ∂P := by
  have hOf : ∀ n m, Integrable (fun ω => v n * Of (fun k => φ k ω) n m * v m) P :=
    fun n m => ((Of_integrable P φ hint n m).const_mul (v n)).mul_const (v m)
  unfold quadForm
  rw [integral_finsetSum _ (fun n _ => integrable_finset_sum _ (fun m _ => hOf n m))]
  apply Finset.sum_congr rfl; intro n _
  rw [integral_finsetSum _ (fun m _ => hOf n m)]
  apply Finset.sum_congr rfl; intro m _
  rw [Of_integral P φ hint n m, ← integral_const_mul, ← integral_mul_const]

/-! ### 四、(1.8) -/

/-- **(1.8)（Remark 1.16(a)）**：`k(P,T) ≤ ∫ h(ω/2πT) P(dω)`。

证明只有三步：二次型与积分交换（`quadForm_integral`，有限线性组合）、
被积函数逐点被 `h(ω/2πT)` 控制（`quadForm_le_lam1`）、对 `v` 取上确界（`lam1_le`）。 -/
theorem theorem_1_8 (hP : ∀ᵐ ω ∂P, 0 < ω) (hm : Integrable (fun ω => ω ^ 2) P)
    (T : ℝ) (hT : 0 < T) :
    kk P T ≤ ∫ ω, hh (ω / (2 * Real.pi * T)) ∂P := by
  have hc : (0:ℝ) < 2 * Real.pi * T := by have := Real.pi_pos; positivity
  set φ : ℕ → ℝ → ℝ := fun k ω => kern k (ω / (2 * Real.pi * T)) with hφ
  have hint : ∀ k, Integrable (φ k) P := by
    intro k
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      have hmeas : Measurable (φ 0) := by
        simp only [hφ]
        unfold kern
        exact ((measurable_id.div_const _).pow_const 2).div
          (measurable_const.add ((measurable_id.div_const _).pow_const 2))
      exact Integrable.of_bound hmeas.aestronglyMeasurable 1
        (ae_of_all _ (fun ω => kern_norm_le_one _ _))
    · exact kern_comp_integrable P k hk T
  have hFT : FT P T = fun k => ∫ ω, φ k ω ∂P := rfl
  have hInt := hh_comp_integrable P hP hm T hT
  unfold kk
  rw [hFT]
  apply lam1_le
  intro v N hv
  rw [quadForm_integral P φ hint v N]
  apply integral_mono_ae (quadForm_integrable P φ hint v N) hInt
  filter_upwards with ω
  exact quadForm_le_lam1 (kern_L1 _) v N hv

/-! ### 五、(1.8) 与 Theorem B 的强弱关系

论文 Remark 1.16(a) 末句说 (1.8)「is superseded by Theorem B, which is strictly stronger」。
本节指出：在论文自己的 **Conjecture 3.1**（`H` 凹）下，Jensen 不等式给出相反的方向——
`∫ h(ω/2πT) P(dω) ≤ h(ϖ_rms)`，也就是 **(1.8) 的右端更小、(1.8) 更紧**，
于是 Theorem B 反而成为 (1.8) 的推论。「strictly stronger」与 Conjecture 3.1 不能同时为真。

这不影响任何已证结果：Theorem B（`theorem_2_1`）在本库中是无条件定理，
(1.8)（`theorem_1_8`）也是；受影响的只是论文那句关于两者强弱的**断言**。
-/

/-- `√(⟨ϖ²⟩) = ϖ_rms`。 -/
lemma sqrt_varpiSq (hm : Integrable (fun ω => ω ^ 2) P) (T : ℝ) (hT : 0 < T) :
    Real.sqrt (varpiSq P T) = varpiRms P T := by
  have hc : (0:ℝ) < 2 * Real.pi * T := by have := Real.pi_pos; positivity
  have hmn : 0 ≤ moment2 P := by
    unfold moment2
    exact integral_nonneg (fun ω => sq_nonneg ω)
  unfold varpiSq varpiRms
  rw [Real.sqrt_div hmn, Real.sqrt_sq (le_of_lt hc)]

/-- **猜想 ⇒ (1.8) 不弱于 Theorem B**：若 `H` 在 `[0,∞)` 凹且连续，则
`∫ h(ω/2πT) P(dω) ≤ h(ϖ_rms)`。

`h(ϖ) = H(ϖ²)`，所以这正是 Jensen 用在 `X := (ω/2πT)²` 上，`⟨X⟩ = ⟨ϖ²⟩`。 -/
theorem integral_hh_le_of_concave (hP : ∀ᵐ ω ∂P, 0 < ω) (hm : Integrable (fun ω => ω ^ 2) P)
    (T : ℝ) (hT : 0 < T) (hcon : ConcaveOn ℝ (Set.Ici 0) HH)
    (hcont : ContinuousOn HH (Set.Ici 0)) :
    ∫ ω, hh (ω / (2 * Real.pi * T)) ∂P ≤ hh (varpiRms P T) := by
  have hc : (0:ℝ) < 2 * Real.pi * T := by have := Real.pi_pos; positivity
  set c : ℝ := 2 * Real.pi * T with hcdef
  have hfi : Integrable (fun ω : ℝ => (ω / c) ^ 2) P := by
    have : (fun ω : ℝ => (ω / c) ^ 2) = fun ω : ℝ => (1 / c ^ 2) * ω ^ 2 := by
      funext ω; rw [div_pow]; ring
    rw [this]; exact hm.const_mul _
  have hgi : Integrable (HH ∘ fun ω : ℝ => (ω / c) ^ 2) P := by
    apply (hh_comp_integrable P hP hm T hT).congr
    filter_upwards [hP] with ω hω
    have hpos : 0 < ω / c := div_pos hω hc
    simp only [Function.comp_apply, HH]
    rw [Real.sqrt_sq (le_of_lt hpos)]
  have hmem : ∀ᵐ ω ∂P, (fun ω : ℝ => (ω / c) ^ 2) ω ∈ Set.Ici (0:ℝ) :=
    Filter.Eventually.of_forall (fun ω => Set.mem_Ici.mpr (sq_nonneg _))
  have hJ := hcon.le_map_integral hcont isClosed_Ici hmem hfi hgi
  have hlhs : ∫ ω, hh (ω / c) ∂P = ∫ ω, HH ((ω / c) ^ 2) ∂P := by
    apply integral_congr_ae
    filter_upwards [hP] with ω hω
    have hpos : 0 < ω / c := div_pos hω hc
    simp only [HH]
    rw [Real.sqrt_sq (le_of_lt hpos)]
  have hint : ∫ ω, (ω / c) ^ 2 ∂P = varpiSq P T := by
    unfold varpiSq moment2
    rw [show (fun ω : ℝ => (ω / c) ^ 2) = fun ω : ℝ => (1 / c ^ 2) * ω ^ 2 from by
      funext ω; rw [div_pow]; ring, integral_const_mul]
    rw [hcdef]; ring
  rw [hlhs]
  calc ∫ ω, HH ((ω / c) ^ 2) ∂P ≤ HH (∫ ω, (ω / c) ^ 2 ∂P) := hJ
    _ = HH (varpiSq P T) := by rw [hint]
    _ = hh (varpiRms P T) := by
        simp only [HH]; rw [sqrt_varpiSq P hm T hT]

/-- **于是 Conjecture 3.1 下 Theorem B 是 (1.8) 的推论**，而非「strictly stronger」。 -/
theorem theorem_2_1_of_theorem_1_8 (hP : ∀ᵐ ω ∂P, 0 < ω) (hm : Integrable (fun ω => ω ^ 2) P)
    (T : ℝ) (hT : 0 < T) (hcon : ConcaveOn ℝ (Set.Ici 0) HH)
    (hcont : ContinuousOn HH (Set.Ici 0)) :
    kk P T ≤ hh (varpiRms P T) :=
  le_trans (theorem_1_8 P hP hm T hT) (integral_hh_le_of_concave P hP hm T hT hcon hcont)

end

end Eliashberg
