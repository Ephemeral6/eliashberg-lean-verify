import Eliashberg.JensenBound
import Mathlib.Analysis.Convex.Continuous

/-!
# Conjecture 3.1 → Theorem B：把猜想接到 (1.8) 上

`JensenBound` 里的 `integral_hh_le_of_concave` 与 `theorem_2_1_of_theorem_1_8` 要的是
`ConcaveOn ℝ (Set.Ici 0) HH` **加** `ContinuousOn HH (Set.Ici 0)`；
而 `SectionThree` 里的 `ConjectureThreeOne` 是 `StrictConcaveOn ℝ (Set.Ioi 0) HH`。
两者差一个端点 `0`，**猜想没法直接代进那两条定理**——在本模块之前，
「Conjecture 3.1 ⇒ Theorem B 是 (1.8) 的推论」这句话在库内是接不通的。

本模块补上这一段，全部由已证结果推出，不新增任何假设：

* `HH_zero`：`H(0) = 0`（由 `hh_zero`）。
* `HH_tendsto_zero`：`H(x) → 0`（`x ↓ 0`）。由**已证的 Lemma 2.2**（`HH_div_tendsto`：
  `H(x)/x → g(2)`）乘以 `x → 0` 得到，与猜想无关。
* `HH_continuousOn_of_concave`：`(0,∞)` 上的凹性给内部连续（`ConvexOn.continuousOn_interior`），
  端点 `0` 处的连续性由上面那条右极限给。
* `HH_smul_le`：`a·H(x) ≤ H(a·x)`。`(0,∞)` 上的凹性作用在 `x` 与 `ε` 上，沿 `ε ↓ 0` 取极限。
  **不经过 `Ici 0` 上的凹性**，因此与 `HH_concaveOn_Ici_of_Ioi` 无循环依赖。
* `HH_concaveOn_Ici_of_Ioi`：凹性从 `Ioi 0` 延到 `Ici 0`。
* `theorem_2_1_of_conjecture`：**终点**。`ConjectureThreeOne → k(P,T) ≤ h(ϖ_rms)`。

注意 `theorem_2_1_of_conjecture` 把猜想作为**显式假设**取用，本库仍然不证明、不假设
Conjecture 3.1；这条定理说的只是「若猜想成立，则 Theorem B 随之而来」。
Theorem B 本身在 `MainB` 里是**无条件**证明的，不依赖本模块。
-/

open Filter Topology Set

namespace Eliashberg

/-- `H(0) = 0`。 -/
theorem HH_zero : HH 0 = 0 := by
  simp only [HH, Real.sqrt_zero]; exact hh_zero

/-- `H(x) → 0`（`x ↓ 0`）。由已证的 Lemma 2.2 得到，与 Conjecture 3.1 无关。 -/
theorem HH_tendsto_zero : Tendsto HH (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have h := HH_div_tendsto
  have hx : Tendsto (fun x : ℝ => x) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hmul := h.mul hx
  rw [mul_zero] at hmul
  apply hmul.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx0
  exact div_mul_cancel₀ _ (ne_of_gt hx0)

/-- `(0,∞)` 上凹 ⇒ `[0,∞)` 上连续：内部由凹性，端点由右极限。 -/
theorem HH_continuousOn_of_concave (h : ConcaveOn ℝ (Ioi (0:ℝ)) HH) :
    ContinuousOn HH (Ici 0) := by
  have hint : ContinuousOn HH (Ioi 0) := by
    have := h.neg.continuousOn_interior
    rw [interior_Ioi] at this
    simpa using this.neg
  intro x hx
  rcases eq_or_lt_of_le (mem_Ici.mp hx) with rfl | hx0
  · rw [ContinuousWithinAt, HH_zero]
    have hsplit : 𝓝[Ici (0:ℝ)] (0:ℝ) = 𝓝[>] (0:ℝ) ⊔ 𝓝[{0}] (0:ℝ) := by
      rw [← nhdsWithin_union]
      congr 1
      ext y; simp [mem_Ici, eq_comm, le_iff_lt_or_eq]
    rw [hsplit]
    refine Tendsto.sup HH_tendsto_zero ?_
    rw [nhdsWithin_singleton]
    simpa [HH_zero] using tendsto_pure_nhds HH 0
  · exact (hint.continuousAt (Ioi_mem_nhds hx0)).continuousWithinAt

/-- 端点引理：`a·H(x) ≤ H(a·x)`（`x > 0`，`a, b > 0`，`a + b = 1`）。

`(0,∞)` 上的凹性给 `H(a·x + b·ε) ≥ a·H(x) + b·H(ε)`；沿 `ε ↓ 0` 取极限，
左边 → `H(a·x)`（`a·x > 0` 处连续），右边 → `a·H(x)`（`H(0⁺) = 0`）。
证明只用 `Ioi 0` 上的凹性，不用 `Ici 0` 上的凹性，故与下一条无循环。 -/
theorem HH_smul_le (h : ConcaveOn ℝ (Ioi (0:ℝ)) HH) {x a b : ℝ} (hx : 0 < x)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    a * HH x ≤ HH (a * x) := by
  have hax : 0 < a * x := mul_pos ha hx
  have hcont : ContinuousOn HH (Ici 0) := HH_continuousOn_of_concave h
  have hL : Tendsto (fun ε => a * HH x + b * HH ε) (𝓝[>] (0:ℝ)) (𝓝 (a * HH x)) := by
    have := HH_tendsto_zero.const_mul b
    rw [mul_zero] at this
    simpa using tendsto_const_nhds.add this
  have hR : Tendsto (fun ε => HH (a * x + b * ε)) (𝓝[>] (0:ℝ)) (𝓝 (HH (a * x))) := by
    have hinner : Tendsto (fun ε : ℝ => a * x + b * ε) (𝓝[>] (0:ℝ)) (𝓝 (a * x)) := by
      have hmain : Tendsto (fun ε : ℝ => a * x + b * ε) (𝓝 (0:ℝ)) (𝓝 (a * x)) := by
        have h0 : Tendsto (fun ε : ℝ => b * ε) (𝓝 (0:ℝ)) (𝓝 0) := by
          have hc : Continuous (fun ε : ℝ => b * ε) := continuous_const.mul continuous_id
          simpa using hc.tendsto (0:ℝ)
        simpa using tendsto_const_nhds.add h0
      exact hmain.mono_left nhdsWithin_le_nhds
    have hcontat : ContinuousAt HH (a * x) :=
      (hcont.mono Ioi_subset_Ici_self).continuousAt (Ioi_mem_nhds hax)
    exact hcontat.tendsto.comp hinner
  refine le_of_tendsto_of_tendsto hL hR ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have := h.2 (mem_Ioi.mpr hx) (mem_Ioi.mpr hε) (le_of_lt ha) (le_of_lt hb) hab
  simpa using this

/-- 凹性从 `Ioi 0` 延到 `Ici 0`。 -/
theorem HH_concaveOn_Ici_of_Ioi (h : ConcaveOn ℝ (Ioi (0:ℝ)) HH) :
    ConcaveOn ℝ (Ici (0:ℝ)) HH := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [mem_Ici] at hx hy
  simp only [smul_eq_mul]
  rcases eq_or_lt_of_le ha with rfl | ha'
  · rw [show b = 1 by linarith]; simp
  rcases eq_or_lt_of_le hb with rfl | hb'
  · rw [show a = 1 by linarith]; simp
  rcases eq_or_lt_of_le hx with rfl | hx'
  · rcases eq_or_lt_of_le hy with rfl | hy'
    · simp [HH_zero]
    · rw [HH_zero, mul_zero, zero_add, zero_add]
      exact HH_smul_le h hy' hb' ha' (by linarith)
  rcases eq_or_lt_of_le hy with rfl | hy'
  · rw [HH_zero, mul_zero, add_zero, add_zero]
    exact HH_smul_le h hx' ha' hb' hab
  · exact h.2 (mem_Ioi.mpr hx') (mem_Ioi.mpr hy') ha hb hab

variable (P : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure P]

/-- **Conjecture 3.1 ⇒ Theorem B 是 (1.8) 的推论**。

论文 Remark 1.16(a) 原先写 Theorem B「strictly stronger than (1.8) and not a consequence of
convexity」；实际方向相反——**若**猜想成立，(1.8) 才是更锐的那个，Theorem B 随之而来。
本定理把「若猜想成立」这一步在库内接通：此前 `theorem_2_1_of_theorem_1_8` 要的
`ConcaveOn (Ici 0)` + `ContinuousOn` 无法由 `ConjectureThreeOne` 提供。

Theorem B 本身（`MainB` 中的 `theorem_2_1`）是**无条件**成立的，不依赖本定理，也不依赖猜想。 -/
theorem theorem_2_1_of_conjecture (hcj : ConjectureThreeOne)
    (hP : ∀ᵐ ω ∂P, 0 < ω) (hm : MeasureTheory.Integrable (fun ω => ω ^ 2) P)
    (T : ℝ) (hT : 0 < T) :
    kk P T ≤ hh (varpiRms P T) :=
  theorem_2_1_of_theorem_1_8 P hP hm T hT
    (HH_concaveOn_Ici_of_Ioi hcj.concaveOn) (HH_continuousOn_of_concave hcj.concaveOn)

end Eliashberg
