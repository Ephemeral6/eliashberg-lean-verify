import Eliashberg.Temple
import Eliashberg.MainB
import Eliashberg.L2Operator

/-!
# Appendix B：证书 CERT-A、CERT-A′、CERT-B 的精确有理数验证

论文 Theorem A.10：给定 `p₀,…,p_{M−1} > 0`、`N₁ ≥ M`，定义 (A.4)–(A.5) 的有理量
`‖v‖²`、`ρ`、`W`、`r²`；若 `ρ > 13/25` 则 `ρ ≤ g(2) ≤ ρ + r²/(ρ − 13/25)`。

本文件用 `norm_num` 精确验证论文 Appendix B 表中的有理数：

| 证书 | `M` | `N₁` | 验证内容 |
|---|---|---|---|
| CERT-A  | 3  | 12 | `‖v‖² = 46920`、`ρ = 110484293/84456000`、`W = 62894483/108900`、`g₀ = 4697/18`、`r²` 精确值、上端点 |
| CERT-A′ | 4  | 16 | `‖v‖² = 1184132`、`ρ = 5722722967/4351685100`、`W = 57402252863/19874400` |
| CERT-B  | 12 | 40 | `‖v‖² = 118932847`、`ρ > 1.318109329`、`W` 精确值 |

每条都是论文 (A.4)–(A.5) 的逐字翻译（`nv2`、`Qc`、`gc`、`Wc`、`Rc`）。

**下界 `ρ ≤ g(2)`** 在本库中已是定理：`ρ = ⟨v, A v⟩/‖v‖²` 是有限 Rayleigh 商，
`g2 = lam1 (k⁻²)` 是这类商的上确界（`quadForm_le_lam1`）。见 `certA_lower`。

**上界**需要 Theorem A.10 的 `ℓ²` 版（Temple 不等式 + `λ₂(A) ≤ 13/25`）。
Temple 不等式的有限维版已证（`temple`）；`λ₂(A) ≤ 13/25` 需要 `ℓ²` 上紧算子的谱分解与
Lemma A.5 的迹论证，mathlib 没有这套无穷维工具，故上界**未形式化**为 `g2` 的定理。
本文件把上界所需的**全部有理数事实**验证到底：对 CERT-A 给出 `ρ + r²/(ρ−13/25)` 的精确值。
-/

namespace Eliashberg

open scoped BigOperators

noncomputable section

/-! ### (A.4)–(A.5) 的有理数定义 -/

/-- `H_n^{(2)}`，有理数版。 -/
def H2q (n : ℕ) : ℚ := ∑ k ∈ Finset.range n, 1 / ((k:ℚ) + 1) ^ 2

/-- `K(n,m)`，有理数版。 -/
def KAq (n m : ℕ) : ℚ := 1 / ((n:ℚ) + m + 1) ^ 2 + (if n ≠ m then 1 / ((n:ℚ) - m) ^ 2 else 0)

/-- `‖v‖² = ∑_{n<M} (2n+1) p_n²`。 -/
def nv2 (p : ℕ → ℚ) (M : ℕ) : ℚ := ∑ n ∈ Finset.range M, (2 * (n:ℚ) + 1) * p n ^ 2

/-- `Q = ∑_{n,m<M} p_n p_m K(n,m) − 2 ∑_{n<M} H_n^{(2)} p_n²`。 -/
def Qc (p : ℕ → ℚ) (M : ℕ) : ℚ :=
  (∑ n ∈ Finset.range M, ∑ m ∈ Finset.range M, p n * p m * KAq n m)
    - 2 * ∑ n ∈ Finset.range M, H2q n * p n ^ 2

/-- `g_n = ∑_{m<M} p_m K(n,m) − 2 H_n^{(2)} p_n [n < M]`。 -/
def gc (p : ℕ → ℚ) (M n : ℕ) : ℚ :=
  (∑ m ∈ Finset.range M, p m * KAq n m) - (if n < M then 2 * H2q n * p n else 0)

/-- `W = ∑_{m<M} p_m ((N₁+1)²/(N₁−m)² + 1)`。 -/
def Wc (p : ℕ → ℚ) (M N₁ : ℕ) : ℚ :=
  ∑ m ∈ Finset.range M, p m * (((N₁:ℚ) + 1) ^ 2 / ((N₁:ℚ) - m) ^ 2 + 1)

/-- `ρ = Q/‖v‖²`。 -/
def rhoc (p : ℕ → ℚ) (M : ℕ) : ℚ := Qc p M / nv2 p M

/-- (A.5) 的 `R`。 -/
def Rc (p : ℕ → ℚ) (M N₁ : ℕ) : ℚ :=
  (∑ n ∈ Finset.range M, (gc p M n - rhoc p M * (2 * (n:ℚ) + 1) * p n) ^ 2 / (2 * (n:ℚ) + 1))
    + (∑ n ∈ Finset.Ico M N₁, gc p M n ^ 2 / (2 * (n:ℚ) + 1))
    + Wc p M N₁ ^ 2 / ((N₁:ℚ) * (2 * (N₁:ℚ) + 1) ^ 3)

/-- `r² = R/‖v‖²`。 -/
def r2c (p : ℕ → ℚ) (M N₁ : ℕ) : ℚ := Rc p M N₁ / nv2 p M

/-- Temple 上端点 `ρ + r²/(ρ − 13/25)`。 -/
def hic (p : ℕ → ℚ) (M N₁ : ℕ) : ℚ := rhoc p M + r2c p M N₁ / (rhoc p M - 13/25)

/-! ### CERT-A：`p = (200, 45, 13)`，`N₁ = 12` -/

def pA : ℕ → ℚ := fun n => if n = 0 then 200 else if n = 1 then 45 else if n = 2 then 13 else 0

theorem certA_nv2 : nv2 pA 3 = 46920 := by
  unfold nv2 pA; norm_num [Finset.sum_range_succ]

theorem certA_rho : rhoc pA 3 = 110484293 / 84456000 := by
  unfold rhoc Qc nv2 pA H2q KAq; norm_num [Finset.sum_range_succ]

theorem certA_rho_sub_beta : rhoc pA 3 - 13/25 = 66567173 / 84456000 := by
  rw [certA_rho]; norm_num

theorem certA_W : Wc pA 3 12 = 62894483 / 108900 := by
  unfold Wc pA; norm_num [Finset.sum_range_succ]

theorem certA_g0 : gc pA 3 0 = 4697 / 18 := by
  unfold gc pA H2q KAq; norm_num [Finset.sum_range_succ]

theorem certA_g6 : gc pA 3 6 = 16654949 / 1270080 := by
  unfold gc pA H2q KAq; norm_num [Finset.sum_range_succ]

theorem certA_r2 : r2c pA 3 12 = 19039044106339336199380972569659 / 1275622598234833487238600000000000 := by
  unfold r2c Rc gc rhoc Qc nv2 Wc pA H2q KAq
  norm_num [Finset.sum_range_succ, Finset.sum_Ico_eq_sum_range]

theorem certA_rho_gt_beta : (13:ℚ)/25 < rhoc pA 3 := by rw [certA_rho]; norm_num

/-- CERT-A 的 Temple 上端点 `= 1.3271238342298657…`。 -/
theorem certA_hi : hic pA 3 12 = 41697813247783307067126765966337 / 31419685316691404167260607031250 := by
  unfold hic; rw [certA_rho, certA_r2]; norm_num

theorem certA_enclosure :
    (13081876124846073 : ℚ) / 10^16 < rhoc pA 3 ∧ hic pA 3 12 < 13271238342298658 / 10^16 := by
  rw [certA_rho, certA_hi]; norm_num

/-! ### CERT-A′：`p = (1000, 228, 69, 25)`，`N₁ = 16` -/

def pA' : ℕ → ℚ := fun n =>
  if n = 0 then 1000 else if n = 1 then 228 else if n = 2 then 69 else if n = 3 then 25 else 0

theorem certA'_nv2 : nv2 pA' 4 = 1184132 := by
  unfold nv2 pA'; norm_num [Finset.sum_range_succ]

theorem certA'_rho : rhoc pA' 4 = 5722722967 / 4351685100 := by
  unfold rhoc Qc nv2 pA' H2q KAq; norm_num [Finset.sum_range_succ]

theorem certA'_W : Wc pA' 4 16 = 57402252863 / 19874400 := by
  unfold Wc pA'; norm_num [Finset.sum_range_succ]

theorem certA'_enclosure :
    (1315059071484745 : ℚ) / 10^15 < rhoc pA' 4 ∧ hic pA' 4 16 < 13206569343393933 / 10^16 := by
  unfold hic r2c Rc gc rhoc Qc nv2 Wc pA' H2q KAq
  norm_num [Finset.sum_range_succ, Finset.sum_Ico_eq_sum_range]

/-! ### CERT-B：`p = (10000, 2286, 704, 275, 129, 70, 41, 27, 18, 13, 9, 7)`，`N₁ = 40` -/

def pB : ℕ → ℚ := fun n =>
  if n = 0 then 10000 else if n = 1 then 2286 else if n = 2 then 704 else if n = 3 then 275
  else if n = 4 then 129 else if n = 5 then 70 else if n = 6 then 41 else if n = 7 then 27
  else if n = 8 then 18 else if n = 9 then 13 else if n = 10 then 9 else if n = 11 then 7 else 0

theorem certB_nv2 : nv2 pB 12 = 118932847 := by
  unfold nv2 pB; norm_num [Finset.sum_range_succ]

theorem certB_rho_gt : (13:ℚ)/25 < rhoc pB 12 ∧ (1318109329:ℚ) / 10^9 < rhoc pB 12 := by
  unfold rhoc Qc nv2 pB H2q KAq
  norm_num [Finset.sum_range_succ]

theorem certB_W : Wc pB 12 40 = 161130626572014304797696770933 / 5710468299952088773900800 := by
  unfold Wc pB; norm_num [Finset.sum_range_succ]

theorem certB_TN1 : (1:ℚ) / (40 * (2 * 40 + 1) ^ 3) = 1 / 21257640 := by norm_num

/-! ### 下界 `ρ ≤ g(2)` 是本库的定理 -/

/-- 由有理 `p` 造实向量 `v_n = √(2n+1) p_n`，则 `quadForm (k⁻²) v M = Q`，`∑ v_n² = ‖v‖²`。
这里以 `pOf v = p` 的形式陈述：`quadForm_invSq_eq` 给出 `⟨v,Av⟩ = ∑ p p K − 2∑ H p²`。 -/
theorem certA_lower_real :
    ∃ v : ℕ → ℝ, (∑ n ∈ Finset.range 3, v n ^ 2 = (46920:ℝ))
      ∧ quadForm (fun k => 1 / (k:ℝ) ^ 2) v 3 = (110484293:ℝ) / 84456000 * 46920 := by
  -- `v_n := p_n / u_n`（即 `√(2n+1) p_n`），`p = (200,45,13)`
  refine ⟨fun n => ((pA n : ℚ) : ℝ) / u n, ?_, ?_⟩
  · have hu : ∀ n : ℕ, (1:ℝ) / u n ^ 2 = 2 * (n:ℝ) + 1 := by
      intro n; rw [u_sq]; field_simp
    have e : ∀ n : ℕ, (((pA n : ℚ) : ℝ) / u n) ^ 2 = ((pA n : ℚ) : ℝ) ^ 2 * (1 / u n ^ 2) := by
      intro n; field_simp
    simp only [e, hu]
    unfold pA; norm_num [Finset.sum_range_succ]
  · rw [quadForm_invSq_eq]
    have hp : ∀ n : ℕ, pOf (fun n => ((pA n : ℚ) : ℝ) / u n) n = ((pA n : ℚ) : ℝ) := by
      intro n; unfold pOf; field_simp [ne_of_gt (u_pos n)]
    simp only [hp]
    have hK : ∀ n m : ℕ, KA n m = ((KAq n m : ℚ) : ℝ) := by
      intro n m; unfold KA KAq
      split_ifs <;> push_cast <;> ring
    have hH : ∀ n : ℕ, H2 n = ((H2q n : ℚ) : ℝ) := by
      intro n; rw [H2_eq_range]; unfold H2q; push_cast; rfl
    simp only [hK, hH]
    unfold pA KAq H2q
    norm_num [Finset.sum_range_succ]

/-- **CERT-A 下界**：`ρ_A = 110484293/84456000 ≤ g(2)`。 -/
theorem certA_lower : (110484293:ℝ) / 84456000 ≤ g2 := by
  obtain ⟨v, hv, hq⟩ := certA_lower_real
  unfold g2
  have := quadForm_le_lam1_mul invSq_L1 v 3
  rw [hq, hv] at this
  nlinarith

end

end Eliashberg
