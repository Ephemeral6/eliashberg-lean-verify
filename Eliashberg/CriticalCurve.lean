import Eliashberg.SpectralSep

/-!
# Remark 1.18：`λ ↦ T_c(λ,P)` 严格递增且连续；Remark 0.4 的反例

论文 Remark 1.18 的最后一句是一条**实质断言**，而且论文明说它「比猜想所断言的更强」：
不仅每个 `(λ,P)` 有唯一交点，而且 `T ↦ k(P,T)` 整体严格递减，**于是 `λ ↦ T_c(λ,P)`
本身严格递增且连续**。`Corollary 1.17` 只给了「对每个 `λ` 有唯一 `T_c`」，
把 `T_c` 作为 `λ` 的**函数**及其单调性、连续性没有陈述。本文件补上。

`T_c(λ)` 由 `Corollary 1.17` 的唯一性经选择公理定义。严格递增是一行：
`λ < λ'` 时 `λ' k(P,T_c(λ)) > λ k(P,T_c(λ)) = 1`，故 `T_c(λ)` 落在 `λ'` 的「`> 1`」一侧，
即 `T_c(λ) < T_c(λ')`。连续性用**严格单调 + 中间值**：
严格单调函数的像若是区间则连续，而 `T_c` 的像由 `theorem_1_1_b` 对每个 `λ` 都有解而铺满。
这里给出的是更直接的 `ε–δ` 形式：由 `k` 在 `T_c(λ)` 处连续且严格递减，
`λ'` 充分接近 `λ` 时 `T_c(λ')` 被夹在 `(T_c(λ)−ε, T_c(λ)+ε)` 内。

| 定理 | 内容 |
|---|---|
| `Tc`、`Tc_pos`、`Tc_eq` | `T_c(λ)` 的定义与定义性质 `λ k(P,T_c λ) = 1` |
| `Tc_unique` | `λ k(P,T) = 1`、`T > 0` ⇒ `T = T_c λ` |
| **`Tc_strictMonoOn`** | **Remark 1.18**：`λ ↦ T_c(λ)` 在 `(0,∞)` 严格递增 |
| **`Tc_continuousAt`** | **Remark 1.18**：`λ ↦ T_c(λ)` 连续 |
| `naive_split_fails` | **Remark 0.4** 的反例：`x = (1,0,1,0)`、`M = 10`，`M·1 − x` 不是非增的 |
-/

namespace Eliashberg

open Filter Topology MeasureTheory

noncomputable section

variable (P : Measure ℝ) [IsProbabilityMeasure P]

/-! ### 一、`T_c` 作为 `λ` 的函数 -/

/-- `T_c(λ)`：`Corollary 1.17` 的唯一解。 -/
def Tc (hP : ∀ᵐ ω ∂P, 0 < ω) (hm : Integrable (fun ω => ω ^ 2) P) (lam : ℝ) : ℝ :=
  if h : 0 < lam then (theorem_1_1_b P hP hm lam h).choose else 0

variable {P}
variable (hP : ∀ᵐ ω ∂P, 0 < ω) (hm : Integrable (fun ω => ω ^ 2) P)

lemma Tc_pos {lam : ℝ} (hlam : 0 < lam) : 0 < Tc P hP hm lam := by
  rw [Tc, dif_pos hlam]
  exact (theorem_1_1_b P hP hm lam hlam).choose_spec.1

lemma Tc_eq {lam : ℝ} (hlam : 0 < lam) : lam * kk P (Tc P hP hm lam) = 1 := by
  rw [Tc, dif_pos hlam]
  exact (theorem_1_1_b P hP hm lam hlam).choose_spec.2

/-- `T_c(λ)` 是唯一的正解。 -/
lemma Tc_unique {lam T : ℝ} (hlam : 0 < lam) (hT : 0 < T) (heq : lam * kk P T = 1) :
    T = Tc P hP hm lam := by
  have hTc := Tc_pos hP hm hlam
  have heq' := Tc_eq hP hm hlam
  rcases lt_trichotomy T (Tc P hP hm lam) with h | h | h
  · have hstep := theorem_1_14 P hP hm T _ hT h
    have := mul_lt_mul_of_pos_left hstep hlam
    rw [heq, heq'] at this; linarith
  · exact h
  · have hstep := theorem_1_14 P hP hm _ T hTc h
    have := mul_lt_mul_of_pos_left hstep hlam
    rw [heq, heq'] at this; linarith

/-! ### 二、Remark 1.18：严格递增 -/

/-- **Remark 1.18（严格递增）**：`λ ↦ T_c(λ,P)` 在 `(0,∞)` 严格递增。

`λ < λ'` ⇒ `λ' k(P,T_c λ) > λ k(P,T_c λ) = 1`，而 `λ'` 的解在「`k` 更小」的一侧。 -/
theorem Tc_strictMonoOn : StrictMonoOn (Tc P hP hm) (Set.Ioi 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  by_contra hle
  rw [not_lt] at hle
  have hka : a * kk P (Tc P hP hm a) = 1 := Tc_eq hP hm ha
  have hkb : b * kk P (Tc P hP hm b) = 1 := Tc_eq hP hm hb
  have hkpos : 0 < kk P (Tc P hP hm b) := kk_pos P hP hm _ (Tc_pos hP hm hb)
  -- `T_c b ≤ T_c a` ⇒ `k(T_c a) ≤ k(T_c b)`
  have hmono : kk P (Tc P hP hm a) ≤ kk P (Tc P hP hm b) := by
    rcases eq_or_lt_of_le hle with h | h
    · rw [h]
    · exact le_of_lt (theorem_1_14 P hP hm _ _ (Tc_pos hP hm hb) h)
  -- `1 = a·k(T_c a) < b·k(T_c a) ≤ b·k(T_c b) = 1`
  have h1 : (1:ℝ) < b * kk P (Tc P hP hm a) := by
    rw [← hka]
    exact mul_lt_mul_of_pos_right hab (kk_pos P hP hm _ (Tc_pos hP hm ha))
  have h2 : b * kk P (Tc P hP hm a) ≤ 1 := by
    rw [← hkb]
    exact mul_le_mul_of_nonneg_left hmono (le_of_lt hb)
  linarith

/-! ### 三、Remark 1.18：连续性 -/

/-- 夹逼：若 `T₁ < T_c λ' < T₂`（`T₁,T₂` 只依赖 `λ`），则 `|T_c λ' − T_c λ|` 受控。

关键一步：`T_c λ' ∈ (T₁,T₂) ⟺ λ' k(P,T₂) < 1 < λ' k(P,T₁)`（由 `Corollary 1.17` 的两侧刻画）。 -/
lemma Tc_mem_Ioo_of {lam' T₁ T₂ : ℝ} (hlam' : 0 < lam') (_hT₁ : 0 < T₁) (hT₂ : 0 < T₂)
    (h₁ : 1 < lam' * kk P T₁) (h₂ : lam' * kk P T₂ < 1) :
    Tc P hP hm lam' ∈ Set.Ioo T₁ T₂ := by
  have hTc := Tc_pos hP hm hlam'
  have heq := Tc_eq hP hm hlam'
  refine ⟨?_, ?_⟩
  · rcases lt_trichotomy T₁ (Tc P hP hm lam') with h | h | h
    · exact h
    · rw [h, heq] at h₁; linarith
    · have hstep := theorem_1_14 P hP hm _ _ hTc h
      have := mul_lt_mul_of_pos_left hstep hlam'
      rw [heq] at this; linarith
  · rcases lt_trichotomy (Tc P hP hm lam') T₂ with h | h | h
    · exact h
    · rw [← h, heq] at h₂; linarith
    · have hstep := theorem_1_14 P hP hm _ _ hT₂ h
      have := mul_lt_mul_of_pos_left hstep hlam'
      rw [heq] at this; linarith

/-- **Remark 1.18（连续性）**：`λ ↦ T_c(λ,P)` 在 `(0,∞)` 上每点连续。

给定 `ε > 0`，取 `T₁ := max(T_c λ − ε, T_c λ/2)`、`T₂ := T_c λ + ε`。
由 `Corollary 1.17` 的两侧刻画，`λ k(P,T₁) > 1 > λ k(P,T₂)`，两个都是**严格**不等式；
`λ' ↦ λ' k(P,T_i)` 连续（线性），故 `λ'` 近 `λ` 时两式仍成立，于是 `T_c λ' ∈ (T₁,T₂)`。 -/
theorem Tc_continuousAt {lam : ℝ} (hlam : 0 < lam) :
    ContinuousAt (Tc P hP hm) lam := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  set t := Tc P hP hm lam with ht
  have htpos : 0 < t := Tc_pos hP hm hlam
  have heq : lam * kk P t = 1 := Tc_eq hP hm hlam
  set T₁ := max (t - ε) (t / 2) with hT₁def
  have hT₁pos : 0 < T₁ := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hT₁lt : T₁ < t := by
    rw [hT₁def]
    exact max_lt (by linarith) (by linarith)
  set T₂ := t + ε with hT₂def
  have hT₂pos : 0 < T₂ := by rw [hT₂def]; linarith
  -- 两个严格不等式
  have h₁ : 1 < lam * kk P T₁ := by
    have := theorem_1_14 P hP hm _ _ hT₁pos hT₁lt
    have := mul_lt_mul_of_pos_left this hlam
    rw [heq] at this; linarith
  have h₂ : lam * kk P T₂ < 1 := by
    have := theorem_1_14 P hP hm _ _ htpos (by rw [hT₂def]; linarith : t < T₂)
    have := mul_lt_mul_of_pos_left this hlam
    rw [heq] at this; linarith
  -- 在 `λ` 处对两式取开邻域
  obtain ⟨δ₁, hδ₁, hb₁⟩ : ∃ d > 0, ∀ l, |l - lam| < d → 1 < l * kk P T₁ := by
    have hk₁ : 0 < kk P T₁ := kk_pos P hP hm _ hT₁pos
    refine ⟨(lam * kk P T₁ - 1) / kk P T₁, div_pos (by linarith) hk₁, fun l hl => ?_⟩
    have hlow : lam - (lam * kk P T₁ - 1) / kk P T₁ < l := by
      have := abs_lt.mp hl; linarith [this.1]
    have := mul_lt_mul_of_pos_right hlow hk₁
    rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hk₁)] at this
    linarith
  obtain ⟨δ₂, hδ₂, hb₂⟩ : ∃ d > 0, ∀ l, |l - lam| < d → l * kk P T₂ < 1 := by
    have hk₂ : 0 < kk P T₂ := kk_pos P hP hm _ hT₂pos
    refine ⟨(1 - lam * kk P T₂) / kk P T₂, div_pos (by linarith) hk₂, fun l hl => ?_⟩
    have hhigh : l < lam + (1 - lam * kk P T₂) / kk P T₂ := by
      have := abs_lt.mp hl; linarith [this.2]
    have := mul_lt_mul_of_pos_right hhigh hk₂
    rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hk₂)] at this
    linarith
  refine ⟨min (min δ₁ δ₂) (lam / 2), lt_min (lt_min hδ₁ hδ₂) (by linarith), fun l hl => ?_⟩
  rw [Real.dist_eq] at hl ⊢
  have hlmin := lt_of_lt_of_le hl (min_le_left _ _)
  have hlpos : 0 < l := by
    have := lt_of_lt_of_le hl (min_le_right _ _)
    have := abs_lt.mp this; linarith [this.1]
  obtain ⟨hlo, hhi⟩ := Tc_mem_Ioo_of hP hm hlpos hT₁pos hT₂pos
    (hb₁ l (lt_of_lt_of_le hlmin (min_le_left _ _)))
    (hb₂ l (lt_of_lt_of_le hlmin (min_le_right _ _)))
  rw [abs_lt]
  constructor
  · have : t - ε ≤ T₁ := le_max_left _ _
    linarith
  · linarith

/-! ### 四、Remark 0.4：朴素分解的反例 -/

/-- **Remark 0.4**：朴素分解 `x = M·1 − (M·1 − x)` 不行——第二项未必非增。

论文的例子 `x = (1,0,1,0)`、`M = 10`：`M − x = (9,10,9,10)`，在 `0 → 1` 处从 `9` 升到 `10`，
所以 `M·1 − x` 不是非增的，朴素分解不能把 `x` 写成两个锥元素之差。论文改用 Abel 分解
（本库 `abel_decomp`）。 -/
theorem naive_split_fails :
    ∃ (x : ℕ → ℝ) (M : ℝ), (∀ n, 0 ≤ x n) ∧ (∀ n, x n ≤ M) ∧
      ¬ (∀ n, M - x (n + 1) ≤ M - x n) := by
  refine ⟨fun n => if n % 2 = 0 then 1 else 0, 10, fun n => ?_, fun n => ?_, ?_⟩
  · simp only []; split_ifs <;> norm_num
  · simp only []; split_ifs <;> norm_num
  · intro h
    have := h 0
    norm_num at this

end

end Eliashberg
