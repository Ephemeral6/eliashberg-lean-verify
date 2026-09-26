import Eliashberg.MainB

/-!
# Theorem B 等号情形：库内陈述与论文原话的桥

`MainB` 里的 `theorem_2_1_iff` 把 Theorem 2.1（Theorem B）的等号条件陈述成
「`ω²` 几乎处处等于 `⟨ω²⟩`」；论文写的是「`P` 是点质量」。本模块证明：对概率测度、
`a.e. ω > 0` 而言两者等价，于是 `theorem_2_1_iff_dirac` 可以照论文原话陈述等号情形。

* `ae_sq_const_iff_dirac`：`ω² =ᵐ[P] ⟨ω²⟩` ⟺ `∃ c > 0, P = δ_c`
* `theorem_2_1_iff_dirac`：`k(P,T) = h(ϖ_rms)` ⟺ `∃ c > 0, P = δ_c`（论文 Theorem B 末句）

本模块原先是库外审计脚本 `audit/DiracBridge.lean`，单独编译；入库后纳入全库公理审计的覆盖范围。
-/

namespace Eliashberg

open MeasureTheory

/-- 桥：「`ω²` 几乎处处为常数」⟺「`P` 是点质量」（概率测度、a.e. `ω > 0`）。
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

end Eliashberg
