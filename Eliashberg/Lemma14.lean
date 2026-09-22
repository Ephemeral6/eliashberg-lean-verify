import Eliashberg.Basic

/-!
# Lemma 1.4（Lemma A）—— 矩形部分和的非负性

论文 §1.2.1。对 `L, L' ≥ 1` 与 `k ≥ 1`，`Q_{LL'}(δ_k) = ⟨e_L, O[δ_k] e_{L'}⟩ ≥ 0`。

按论文 (1.2)，在 `L ≤ L'` 时 `Q_{LL'}(δ_k)` 分解为三组：

* group 1：`2 ∑_{j=k}^{L-1} u_j (u_{j-k} - u_j)`，因 `u` 递减而每项非负
* group 2：`∑_{n=max(0,L-k)}^{min(L,L'-k)-1} u_n u_{n+k}`，因 `u > 0` 而每项为正
* group 3：`∑_{n=max(0,k-L')}^{min(L,k)-1} u_n u_{k-1-n}`，同上

本文件证三组的非负性（已完成），并组装 `Q ≥ 0`。
-/

namespace Eliashberg

open scoped BigOperators

/-- group 1 的每一项非负。 -/
lemma group1_nonneg (k L : ℕ) :
    0 ≤ ∑ j ∈ Finset.Ico k L, u j * (u (j - k) - u j) := by
  apply Finset.sum_nonneg
  intro j hj
  rw [Finset.mem_Ico] at hj
  have h1 : u j ≤ u (j - k) := u_anti (Nat.sub_le j k)
  nlinarith [u_pos j]

/-- group 2 的每一项非负。 -/
lemma group2_nonneg (k lo hi : ℕ) :
    0 ≤ ∑ n ∈ Finset.Ico lo hi, u n * u (n + k) := by
  apply Finset.sum_nonneg
  intro n _
  exact mul_nonneg (le_of_lt (u_pos n)) (le_of_lt (u_pos (n + k)))

/-- group 3 的每一项非负。 -/
lemma group3_nonneg (k lo hi : ℕ) :
    0 ≤ ∑ n ∈ Finset.Ico lo hi, u n * u (k - 1 - n) := by
  apply Finset.sum_nonneg
  intro n _
  exact mul_nonneg (le_of_lt (u_pos n)) (le_of_lt (u_pos (k - 1 - n)))

/-! ### (1.2) 的组装：把双重和化为单和

论文 (1.2) 把 `Q_{LL'}(δ_k)` 写成三组。第一步是把每个「单条件」的双重和化为单重和。
-/

/-- 条件 `m = n + k`：内层和只取一项。 -/
lemma band1 (k L Lp : ℕ) :
    (∑ n ∈ Finset.range L, ∑ m ∈ Finset.range Lp, if m = n + k then (u n * u m : ℝ) else 0)
  = ∑ n ∈ Finset.range L, if n + k < Lp then u n * u (n + k) else 0 := by
  apply Finset.sum_congr rfl
  intro n _
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_range]

/-- 条件 `n = m + k`：交换求和次序后同上。 -/
lemma band2 (k L Lp : ℕ) :
    (∑ n ∈ Finset.range L, ∑ m ∈ Finset.range Lp, if n = m + k then (u m * u n : ℝ) else 0)
  = ∑ m ∈ Finset.range Lp, if m + k < L then u m * u (m + k) else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_range]

/-- 条件 `n + m + 1 = k`：内层和化为单项 `m = k - 1 - n`。 -/
lemma band3 (k L Lp : ℕ) :
    (∑ n ∈ Finset.range L, ∑ m ∈ Finset.range Lp, if n + m + 1 = k then (u n * u m : ℝ) else 0)
  = ∑ n ∈ Finset.range L, if n < k ∧ k - 1 - n < Lp then u n * u (k - 1 - n) else 0 := by
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : n < k
  · have hiff : ∀ m : ℕ, (n + m + 1 = k) ↔ (m = k - 1 - n) := by
      intro m; constructor <;> intro h <;> omega
    simp only [hiff]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_range]
    by_cases h2 : k - 1 - n < Lp
    · simp [hn, h2]
    · simp [hn, h2]
  · have hne : ∀ m : ℕ, n + m + 1 ≠ k := by intro m h; omega
    simp only [hne, ite_false, Finset.sum_const_zero]
    simp [hn]

/-- `2n+1 = k` 与 `k ≤ n` 互斥（对角两块不重叠）。 -/
lemma diag_disjoint (k n : ℕ) : ¬ (2 * n + 1 = k ∧ k ≤ n) := by omega

/-- 有限和可逐项相加（对角两块合并用）。 -/
lemma sum_add_merge {L : ℕ} (f g : ℕ → ℝ) :
    (∑ n ∈ Finset.range L, (f n + g n))
  = (∑ n ∈ Finset.range L, f n) + (∑ n ∈ Finset.range L, g n) :=
  Finset.sum_add_distrib


end Eliashberg
