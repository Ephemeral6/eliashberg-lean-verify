import Eliashberg

set_option pp.numericTypes true
open Eliashberg MeasureTheory

/-! 非空性：主定理的三条假设能被一个具体的测度（点质量 `δ₁`）同时满足，
且从它们确实能实例化出结论。这排除「假设集合矛盾、定理空成立」的可能。 -/

lemma dirac_pos : ∀ᵐ ω ∂(Measure.dirac (1:ℝ)), (0:ℝ) < ω := by
  rw [ae_dirac_iff measurableSet_Ioi]; exact one_pos

lemma dirac_int : Integrable (fun ω : ℝ => ω ^ 2) (Measure.dirac (1:ℝ)) :=
  integrable_dirac (by simp)

example : ∃ T₀ : ℝ, 0 < T₀ ∧ 1 < (1:ℝ) * kk (Measure.dirac (1:ℝ)) T₀ :=
  theorem_1_1_a _ dirac_pos dirac_int 1 one_pos

example : ∃! Tc : ℝ, 0 < Tc ∧ (1:ℝ) * kk (Measure.dirac (1:ℝ)) Tc = 1 ∧
    (∀ T, 0 < T → T < Tc → 1 < (1:ℝ) * kk (Measure.dirac (1:ℝ)) T) ∧
    (∀ T, Tc < T → (1:ℝ) * kk (Measure.dirac (1:ℝ)) T < 1) :=
  corollary_1_17 _ dirac_pos dirac_int 1 one_pos

example : kk (Measure.dirac (1:ℝ)) 1 ≤ hh (varpiRms (Measure.dirac (1:ℝ)) 1) :=
  theorem_2_1 _ dirac_pos dirac_int 1 one_pos

-- 等号情形在点质量上确实取到：ω² 几乎处处等于 moment2
example : kk (Measure.dirac (1:ℝ)) 1 = hh (varpiRms (Measure.dirac (1:ℝ)) 1) := by
  rw [theorem_2_1_iff _ dirac_pos dirac_int 1 one_pos]
  rw [Filter.EventuallyEq, ae_dirac_iff]
  · simp [moment2]
  · exact measurableSet_eq_fun (by fun_prop) (by fun_prop)

-- 有限截断非空：lamN 用 N+1，top 的 Finset.univ 非空
#check @lamN
#check @lam1_eq_iSup_lamN
#check @raySet_bddAbove

-- 有限维顶特征值（Cinf）与 g2 的关系是定义
example : Cinf = Real.sqrt g2 / (2 * Real.pi) := rfl
