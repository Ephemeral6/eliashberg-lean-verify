import Eliashberg.CertD
import Eliashberg.Enclosure

/-!
# Corollary 2.4(iii)：`C_∞ ∈ [0.182726247746, 0.182726247790]` 与 `T_c < T̃_c = C_∞√(λ⟨ω²⟩)`

论文 Cor 2.4(iii)：用 Appendix A 的包围区间 (†)（本库 `CertD.lean` 的 `certD_g2`）得到

* `C_∞ := √g(2)/(2π) ∈ [0.182726247746, 0.182726247790]`（`Cinf_enclosure`）；
* `T̃_c := C_∞ √(λ⟨ω²⟩)`，且 `T_c < T̃_c < 0.18273 √(λ⟨ω²⟩)`（`Tec_lt`、`corollary_2_4_iii_Tec`）。
-/

namespace Eliashberg

open MeasureTheory Filter Topology

/-- `C_∞` 的包围区间，写成小数形式（= `Cinf_enclosure`）。 -/
theorem Cinf_mem : (0.182726247746 : ℝ) ≤ Cinf ∧ Cinf ≤ 0.182726247790 := by
  obtain ⟨h1, h2⟩ := Cinf_enclosure
  refine ⟨?_, ?_⟩
  · have : (182726247746:ℝ) / 10^12 = 0.182726247746 := by norm_num
    linarith [this.le, this.ge, h1]
  · have : (182726247790:ℝ) / 10^12 = 0.182726247790 := by norm_num
    linarith [this.le, this.ge, h2]

/-- `T̃_c := C_∞ √(λ⟨ω²⟩)`。 -/
noncomputable def Tec (P : Measure ℝ) (lam : ℝ) : ℝ :=
  Cinf * Real.sqrt (lam * moment2 P)

/-- `T̃_c = √(g(2)·λ⟨ω²⟩)/(2π)`（与 Theorem 2.3 的第二句同形）。 -/
theorem Tec_eq (P : Measure ℝ) (lam : ℝ) (hlam : 0 < lam) (hm : 0 ≤ moment2 P) :
    Tec P lam = Real.sqrt (g2 * moment2 P * lam) / (2 * Real.pi) := by
  unfold Tec Cinf
  have hg : 0 < g2 := lt_of_lt_of_le one_pos one_le_g2
  have h1 : Real.sqrt (g2 * moment2 P * lam) = Real.sqrt g2 * Real.sqrt (lam * moment2 P) := by
    rw [← Real.sqrt_mul (le_of_lt hg)]
    congr 1; ring
  rw [h1]; ring

/-- **Cor 2.4(iii)（第二句）**：`T_c < T̃_c`。 -/
theorem Tec_lt (P : Measure ℝ) [IsProbabilityMeasure P] (hP : ∀ᵐ ω ∂P, 0 < ω)
    (hm : Integrable (fun ω => ω ^ 2) P) (lam Tc : ℝ) (hlam : 0 < lam) (hTc : 0 < Tc)
    (hcrit : lam * kk P Tc = 1) : Tc < Tec P lam := by
  have h := theorem_2_3_Tc P hP hm lam Tc hlam hTc hcrit
  have hm0 : 0 ≤ moment2 P := integral_nonneg (fun ω => sq_nonneg _)
  rw [Tec_eq P lam hlam hm0]
  exact h

/-- **Cor 2.4(iii)**：`T_c < 0.18273 √(λ⟨ω²⟩)`。 -/
theorem corollary_2_4_iii_Tec (P : Measure ℝ) [IsProbabilityMeasure P] (hP : ∀ᵐ ω ∂P, 0 < ω)
    (hm : Integrable (fun ω => ω ^ 2) P) (lam Tc : ℝ) (hlam : 0 < lam) (hTc : 0 < Tc)
    (hcrit : lam * kk P Tc = 1) :
    Tc < 18273 / 10^5 * Real.sqrt (lam * moment2 P) := by
  refine (Tec_lt P hP hm lam Tc hlam hTc hcrit).trans_le ?_
  unfold Tec
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  have h := Cinf_mem.2
  have : (0.182726247790 : ℝ) ≤ 0.18273 := by norm_num
  linarith

end Eliashberg
