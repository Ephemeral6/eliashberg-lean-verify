import Eliashberg.TheoremA10
import Eliashberg.Certificates

/-!
# 论文 Theorem (∗) 的数值结论：`g(2)` 的包围区间（CERT-A、CERT-A′、CERT-B）与 Cor 2.4(iii)

`Certificates.lean` 用 `norm_num`/`decide` 精确核对了 (A.4)–(A.5) 的**有理数**；`TheoremA10.lean` 证明了
Theorem A.10 对**实数**定义 `rhoR`/`r2R` 成立。本文件把两者接起来：

* `rhoR_cast`、`r2R_cast`：实数版定义等于有理数版定义的 cast；
* `enclosure_of_cert`：**Theorem A.10 的有理数形式**——`p` 支撑在 `[0,M)` 且严格正、`ρ > 13/25` ⇒
  `(ρ : ℝ) ≤ g(2) ≤ (ρ + r²/(ρ − 13/25) : ℝ)`；
* `certA_g2`、`certA'_g2`、`certB_g2`：论文 Appendix B 表中三个证书的包围区间，作为 `g2` 的定理；
* `corollary_2_4_iii_Tc`：Cor 2.4(iii) 的 `T_c < 0.18273 √(λ⟨ω²⟩)`（用 CERT-B 与 `π > 3.141592`）；
* `Cinf_enclosure_B`：`C_∞ := √g(2)/(2π)` 的包围区间（CERT-B 版）。

CERT-D（`M = 200`、`N₁ = 500`）见 `CertD.lean`。
-/

namespace Eliashberg

open scoped BigOperators

/-! ### 有理数定义与实数定义的一致性 -/

lemma KA_cast (n m : ℕ) : KA n m = ((KAq n m : ℚ) : ℝ) := by
  unfold KA KAq
  split_ifs <;> push_cast <;> ring

lemma H2_cast (n : ℕ) : H2 n = ((H2q n : ℚ) : ℝ) := by
  rw [H2_eq_range]; unfold H2q; push_cast; rfl

/-- 有理系数向量的实数化。 -/
noncomputable def pR (p : ℕ → ℚ) : ℕ → ℝ := fun n => ((p n : ℚ) : ℝ)

lemma nv2R_cast (p : ℕ → ℚ) (M : ℕ) : nv2R (pR p) M = ((nv2 p M : ℚ) : ℝ) := by
  unfold nv2R nv2 pR; push_cast; rfl

lemma QR_cast (p : ℕ → ℚ) (M : ℕ) : QR (pR p) M = ((Qc p M : ℚ) : ℝ) := by
  unfold QR Qc pR
  simp only [KA_cast, H2_cast]
  push_cast; rfl

lemma gR_cast (p : ℕ → ℚ) (M n : ℕ) : gR (pR p) M n = ((gc p M n : ℚ) : ℝ) := by
  unfold gR gc pR
  simp only [KA_cast, H2_cast]
  split_ifs <;> push_cast <;> rfl

lemma WR_cast (p : ℕ → ℚ) (M N₁ : ℕ) : WR (pR p) M N₁ = ((Wc p M N₁ : ℚ) : ℝ) := by
  unfold WR Wc pR; push_cast; rfl

lemma rhoR_cast (p : ℕ → ℚ) (M : ℕ) : rhoR (pR p) M = ((rhoc p M : ℚ) : ℝ) := by
  unfold rhoR rhoc; rw [QR_cast, nv2R_cast]; push_cast; rfl

lemma resT_cast (p : ℕ → ℚ) (M n : ℕ) :
    resT (pR p) M n = (((gc p M n - rhoc p M * (2 * (n:ℚ) + 1) * p n) ^ 2 / (2 * (n:ℚ) + 1) : ℚ) : ℝ) := by
  unfold resT
  rw [gR_cast, rhoR_cast]
  unfold pR; push_cast; rfl

lemma RR_cast (p : ℕ → ℚ) (M N₁ : ℕ) : RR (pR p) M N₁ = ((Rc p M N₁ : ℚ) : ℝ) := by
  unfold RR Rc
  simp only [resT_cast, gR_cast, WR_cast]
  push_cast; rfl

lemma r2R_cast (p : ℕ → ℚ) (M N₁ : ℕ) : r2R (pR p) M N₁ = ((r2c p M N₁ : ℚ) : ℝ) := by
  unfold r2R r2c; rw [RR_cast, nv2R_cast]; push_cast; rfl

/-- **Theorem A.10，有理数形式**：`p` 支撑在 `[0,M)` 且严格正，`ρ > 13/25` ⇒
`(ρ:ℝ) ≤ g(2) ≤ (ρ + r²/(ρ − 13/25) : ℝ)`。 -/
theorem enclosure_of_cert (p : ℕ → ℚ) (M N₁ : ℕ) (hs : ∀ n, M ≤ n → p n = 0)
    (hp : ∀ n, n < M → 0 < p n) (hM : 1 ≤ M) (hMN : M ≤ N₁) (hρ : 13/25 < rhoc p M) :
    ((rhoc p M : ℚ) : ℝ) ≤ g2 ∧ g2 ≤ ((hic p M N₁ : ℚ) : ℝ) := by
  have hs' : ∀ n, M ≤ n → pR p n = 0 := by
    intro n hn; unfold pR; rw [hs n hn]; simp
  have hp' : ∀ n, n < M → 0 < pR p n := by
    intro n hn; unfold pR; exact_mod_cast hp n hn
  have hρ' : (13:ℝ)/25 < rhoR (pR p) M := by
    rw [rhoR_cast]
    have h := (Rat.cast_lt (K := ℝ)).mpr hρ
    push_cast at h
    exact h
  have h := theorem_A10 hs' hp' hM hMN hρ'
  rw [rhoR_cast, r2R_cast] at h
  unfold hic
  push_cast
  exact h

/-! ### 三个证书的包围区间 -/

lemma pA_supp : ∀ n, 3 ≤ n → pA n = 0 := by
  intro n hn; unfold pA
  have h0 : n ≠ 0 := by omega
  have h1 : n ≠ 1 := by omega
  have h2 : n ≠ 2 := by omega
  simp [h0, h1, h2]

lemma pA_pos : ∀ n, n < 3 → 0 < pA n := by
  intro n hn; interval_cases n <;> simp [pA]

/-- **CERT-A**：`1.3081876124846073 ≤ g(2) ≤ 1.3271238342298657`（论文 Appendix B 表第一行）。 -/
theorem certA_g2 : (13081876124846073:ℝ) / 10^16 < g2 ∧ g2 < 13271238342298658 / 10^16 := by
  have h := enclosure_of_cert pA 3 12 pA_supp pA_pos (by norm_num) (by norm_num) certA_rho_gt_beta
  obtain ⟨hlo, hhi⟩ := certA_enclosure
  constructor
  · calc (13081876124846073:ℝ) / 10^16 = (((13081876124846073:ℚ) / 10^16 : ℚ) : ℝ) := by push_cast; rfl
      _ < ((rhoc pA 3 : ℚ) : ℝ) := by exact_mod_cast hlo
      _ ≤ g2 := h.1
  · calc g2 ≤ ((hic pA 3 12 : ℚ) : ℝ) := h.2
      _ < (((13271238342298658:ℚ) / 10^16 : ℚ) : ℝ) := by exact_mod_cast hhi
      _ = 13271238342298658 / 10^16 := by push_cast; rfl

lemma pA'_supp : ∀ n, 4 ≤ n → pA' n = 0 := by
  intro n hn; unfold pA'
  have h0 : n ≠ 0 := by omega
  have h1 : n ≠ 1 := by omega
  have h2 : n ≠ 2 := by omega
  have h3 : n ≠ 3 := by omega
  simp [h0, h1, h2, h3]

lemma pA'_pos : ∀ n, n < 4 → 0 < pA' n := by
  intro n hn; interval_cases n <;> simp [pA']

theorem certA'_rho_gt_beta : (13:ℚ)/25 < rhoc pA' 4 := by rw [certA'_rho]; norm_num

/-- **CERT-A′**：`1.3150590714847450 ≤ g(2) ≤ 1.3206569343393933`。 -/
theorem certA'_g2 : (1315059071484745:ℝ) / 10^15 < g2 ∧ g2 < 13206569343393933 / 10^16 := by
  have h := enclosure_of_cert pA' 4 16 pA'_supp pA'_pos (by norm_num) (by norm_num) certA'_rho_gt_beta
  obtain ⟨hlo, hhi⟩ := certA'_enclosure
  constructor
  · calc (1315059071484745:ℝ) / 10^15 = (((1315059071484745:ℚ) / 10^15 : ℚ) : ℝ) := by push_cast; rfl
      _ < ((rhoc pA' 4 : ℚ) : ℝ) := by exact_mod_cast hlo
      _ ≤ g2 := h.1
  · calc g2 ≤ ((hic pA' 4 16 : ℚ) : ℝ) := h.2
      _ < (((13206569343393933:ℚ) / 10^16 : ℚ) : ℝ) := by exact_mod_cast hhi
      _ = 13206569343393933 / 10^16 := by push_cast; rfl

lemma pB_supp : ∀ n, 12 ≤ n → pB n = 0 := by
  intro n hn; unfold pB
  have : ∀ k, k < 12 → n ≠ k := fun k hk => by omega
  simp [this 0 (by norm_num), this 1 (by norm_num), this 2 (by norm_num), this 3 (by norm_num),
    this 4 (by norm_num), this 5 (by norm_num), this 6 (by norm_num), this 7 (by norm_num),
    this 8 (by norm_num), this 9 (by norm_num), this 10 (by norm_num), this 11 (by norm_num)]

lemma pB_pos : ∀ n, n < 12 → 0 < pB n := by
  intro n hn; interval_cases n <;> simp [pB]

set_option maxRecDepth 100000 in
/-- CERT-B 的精确有理端点（论文表中的 16 位小数）：`ρ > 1.3181093293757127`，
`ρ + r²/(ρ−13/25) < 1.3181615785`。由 Lean 内核精确计算（`decide +kernel`，无额外公理）。 -/
theorem certB_endpoints :
    (13181093293757127:ℚ) / 10^16 < rhoc pB 12 ∧ hic pB 12 40 < 13181615785 / 10^10 := by
  decide +kernel

/-- **CERT-B（论文的主证书）**：`1.3181093293757127 ≤ g(2) ≤ 1.3181615785`。 -/
theorem certB_g2 : (13181093293757127:ℝ) / 10^16 < g2 ∧ g2 < 13181615785 / 10^10 := by
  have h := enclosure_of_cert pB 12 40 pB_supp pB_pos (by norm_num) (by norm_num) (certB_rho_gt).1
  obtain ⟨hlo, hhi⟩ := certB_endpoints
  constructor
  · calc (13181093293757127:ℝ) / 10^16 = (((13181093293757127:ℚ) / 10^16 : ℚ) : ℝ) := by push_cast; rfl
      _ < ((rhoc pB 12 : ℚ) : ℝ) := by exact_mod_cast hlo
      _ ≤ g2 := h.1
  · calc g2 ≤ ((hic pB 12 40 : ℚ) : ℝ) := h.2
      _ < (((13181615785:ℚ) / 10^10 : ℚ) : ℝ) := by exact_mod_cast hhi
      _ = 13181615785 / 10^10 := by push_cast; rfl

/-! ### Cor 2.4(iii) -/

open MeasureTheory in
/-- **Cor 2.4(iii)**：`T_c < 0.18273 √(λ⟨ω²⟩)`（由 Theorem 2.3、CERT-B 与 `π > 3.141592`）。 -/
theorem corollary_2_4_iii_Tc (P : Measure ℝ) [IsProbabilityMeasure P] (hP : ∀ᵐ ω ∂P, 0 < ω)
    (hm : Integrable (fun ω => ω ^ 2) P) (lam Tc : ℝ) (hlam : 0 < lam) (hTc : 0 < Tc)
    (hcrit : lam * kk P Tc = 1) :
    Tc < 18273 / 10^5 * Real.sqrt (lam * moment2 P) := by
  have h := theorem_2_3_Tc P hP hm lam Tc hlam hTc hcrit
  have hg := certB_g2.2
  have hpi := Real.pi_gt_d6
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have hm0 : 0 ≤ moment2 P := by
    unfold moment2; exact integral_nonneg (fun ω => sq_nonneg _)
  -- `√(g2·m·λ)/(2π) < 0.18273 √(λ m)` ⟸ `g2 < (0.18273·2π)²`
  have hg2pos : 0 < g2 := lt_of_lt_of_le one_pos one_le_g2
  have hsq : Real.sqrt (g2 * moment2 P * lam) = Real.sqrt g2 * Real.sqrt (lam * moment2 P) := by
    rw [← Real.sqrt_mul hg2pos.le]; congr 1; ring
  have hsg : Real.sqrt g2 < 18273 / 10^5 * (2 * Real.pi) := by
    rw [Real.sqrt_lt' (by positivity)]
    nlinarith [hg, hpi]
  rw [hsq] at h
  calc Tc < Real.sqrt g2 * Real.sqrt (lam * moment2 P) / (2 * Real.pi) := h
    _ ≤ (18273 / 10^5 * (2 * Real.pi)) * Real.sqrt (lam * moment2 P) / (2 * Real.pi) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right hsg.le (Real.sqrt_nonneg _)
    _ = 18273 / 10^5 * Real.sqrt (lam * moment2 P) := by field_simp

/-- `C_∞ := √g(2)/(2π)`。 -/
noncomputable def Cinf : ℝ := Real.sqrt g2 / (2 * Real.pi)

/-- `C_∞` 的包围区间（CERT-B 版）：`0.182723 < C_∞ < 0.182729`（论文 (†) 用 CERT-D 给出更窄的
`[0.182726247746, 0.182726247790]`，见 `CertD.lean`）。 -/
theorem Cinf_enclosure_B : (182723:ℝ) / 10^6 < Cinf ∧ Cinf < 182729 / 10^6 := by
  unfold Cinf
  have hpi0 : 0 < Real.pi := Real.pi_pos
  obtain ⟨hlo, hhi⟩ := certB_g2
  constructor
  · rw [lt_div_iff₀ (by positivity), Real.lt_sqrt (by positivity)]
    have hpi2 : Real.pi ^ 2 < (3.141593:ℝ) ^ 2 := by nlinarith [Real.pi_lt_d6, Real.pi_pos]
    calc (182723 / 10^6 * (2 * Real.pi)) ^ 2 = 4 * (182723 / 10^6) ^ 2 * Real.pi ^ 2 := by ring
      _ < 4 * (182723 / 10^6) ^ 2 * (3.141593:ℝ) ^ 2 := by gcongr
      _ < 13181093293757127 / 10^16 := by norm_num
      _ < g2 := hlo
  · rw [div_lt_iff₀ (by positivity), Real.sqrt_lt' (by positivity)]
    have hpi2 : (3.141592:ℝ) ^ 2 < Real.pi ^ 2 := by nlinarith [Real.pi_gt_d6, Real.pi_pos]
    calc g2 < 13181615785 / 10^10 := hhi
      _ < 4 * (182729 / 10^6) ^ 2 * (3.141592:ℝ) ^ 2 := by norm_num
      _ < 4 * (182729 / 10^6) ^ 2 * Real.pi ^ 2 := by gcongr
      _ = (182729 / 10^6 * (2 * Real.pi)) ^ 2 := by ring

end Eliashberg
