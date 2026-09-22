import Eliashberg

open Eliashberg MeasureTheory

/-! 桥：「ω² 几乎处处为常数」⟺「P 是点质量」（概率测度、a.e. ω > 0）。
这是 Theorem B 等号情形的 Lean 陈述与论文陈述之间唯一的差异，量一下它有多大。 -/

theorem ae_sq_const_iff_dirac (P : Measure ℝ) [IsProbabilityMeasure P]
    (hP : ∀ᵐ ω ∂P, 0 < ω) :
    ((fun ω => ω ^ 2) =ᵐ[P] fun _ => moment2 P) ↔ ∃ c : ℝ, 0 < c ∧ P = Measure.dirac c := by
  constructor
  · intro h
    set c := Real.sqrt (moment2 P) with hc_def
    have hc : (id : ℝ → ℝ) =ᵐ[P] fun _ => c := by
      filter_upwards [hP, h] with ω hω hω2
      simp only [id] at hω2 ⊢
      rw [hc_def, ← hω2, Real.sqrt_sq hω.le]
    have hPc : P = Measure.dirac c := by
      calc P = Measure.map id P := Measure.map_id.symm
        _ = Measure.map (fun _ => c) P := Measure.map_congr hc
        _ = Measure.dirac c := by rw [Measure.map_const, measure_univ, one_smul]
    refine ⟨c, ?_, hPc⟩
    -- c > 0：否则 P = δ₀ 与 a.e. ω > 0 矛盾
    by_contra hc0
    push_neg at hc0
    have h0 : c = 0 := le_antisymm hc0 (Real.sqrt_nonneg _)
    rw [hPc, ae_dirac_iff measurableSet_Ioi] at hP
    simp [h0] at hP
  · rintro ⟨c, hc, rfl⟩
    rw [Filter.EventuallyEq, ae_dirac_iff (measurableSet_eq_fun (by fun_prop) (by fun_prop))]
    simp [moment2]

/-- 于是 Theorem B 的等号情形可以按论文原话陈述：等号成立 ⟺ `P` 是（正）点质量。 -/
theorem theorem_2_1_iff_dirac (P : Measure ℝ) [IsProbabilityMeasure P]
    (hP : ∀ᵐ ω ∂P, 0 < ω) (hm : Integrable (fun ω => ω ^ 2) P) (T : ℝ) (hT : 0 < T) :
    kk P T = hh (varpiRms P T) ↔ ∃ c : ℝ, 0 < c ∧ P = Measure.dirac c := by
  rw [theorem_2_1_iff P hP hm T hT, ae_sq_const_iff_dirac P hP]
