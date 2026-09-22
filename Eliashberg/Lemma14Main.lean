import Eliashberg.Lemma14Assembly

/-!
# Lemma 1.4（Lemma A）—— 主结论

本文件把 `Q2 = S1 + S2 + S3 + Sd` 的四分量形式重组为论文 (1.2) 的三组，并证成
Lemma 1.4 的三条结论：

* `Q2_nonneg`：`k ≥ 1` 时 `Q_{LL'}(δ_k) ≥ 0`（对一切 `L, L'`，含 0）
* `Q2_eq_zero_iff`：`L, L' ≥ 1` 时 `Q_{LL'}(δ_k) = 0 ⟺ L + L' ≤ k`
* `Q2_LL_one`：`L ≥ 1` 时 `Q_{LL}(δ_1) ≥ 1`

## 与论文的对应

论文 (1.2)（`L ≤ L'`）：
```
Q_{LL'}(δ_k) = 2 ∑_{j=k}^{L-1} u_j (u_{j-k} - u_j)          group 1
             + ∑_{n=max(0,L-k)}^{min(L,L'-k)-1} u_n u_{n+k}   group 2
             + ∑_{n=max(0,k-L')}^{min(L,k)-1} u_n u_{k-1-n}   group 3
```
这里 `max(0, a-b)` 用 ℕ 的截断减法 `a - b` 表示，`Finset.Ico lo hi` 在 `hi ≤ lo` 时为空。

论文的推导（§1.2.1）：`L ≤ L'` 时 `min(L, L'-k) ≥ L-k`，于是 `m = n+k` 的和
（`S1`）在 `n = L-k` 处劈开；前半段换元 `j = n+k` 后等于 `∑_{j=k}^{L-1} u_{j-k} u_j`，
与 `m = n-k` 的和（`S2`，此时 `min(L', L-k) = L-k`）相同，两者再与对角 `Sd`
（范围 `k ≤ n < min(L,L') = L`）合并成 group 1；后半段即 group 2；`S3` 即 group 3。

`L > L'` 时用对称性 `Q_{LL'} = Q_{L'L}`（`Q2_symm`），见 Remark 1.5。
-/

namespace Eliashberg

open scoped BigOperators

/-! ### 把 `if n < Lp` 型的和收进求和范围 -/

lemma filter_lt_range (L Lp : ℕ) :
    (Finset.range L).filter (fun n => n < Lp) = Finset.range (min L Lp) := by
  ext n; simp only [Finset.mem_filter, Finset.mem_range]; omega

lemma sum_range_ite_lt (L Lp : ℕ) (g : ℕ → ℝ) :
    (∑ n ∈ Finset.range L, if n < Lp then g n else 0)
      = ∑ n ∈ Finset.range (min L Lp), g n := by
  rw [← Finset.sum_filter, filter_lt_range]

/-- 对角一重和 = `Sd` + 对角上的 L3 项。 -/
lemma diag_reduce' (k L Lp : ℕ) :
    (∑ n ∈ Finset.range L,
       if n < Lp then ((if k ≤ n then -(2 * (u n) ^ 2) else 0)
                     + (if 2 * n + 1 = k then (u n) ^ 2 else 0)) else 0)
  = Sd k L Lp + ∑ n ∈ Finset.range L, if 2 * n + 1 = k ∧ n < Lp then (u n) ^ 2 else 0 := by
  rw [sum_range_ite_lt, Finset.sum_add_distrib]
  unfold Sd
  congr 1
  rw [← sum_range_ite_lt L Lp (fun n => if 2 * n + 1 = k then (u n)^2 else 0)]
  apply Finset.sum_congr rfl
  intro n _
  by_cases h1 : n < Lp <;> by_cases h2 : 2 * n + 1 = k <;> simp [h1, h2]

/-- **四分量分解**：`k ≥ 1` 时 `Q_{LL'}(δ_k) = S1 + S2 + S3 + Sd`，对一切 `L, L'`。

对角上的 L3 项（`2n+1 = k`）在 `off3_eq` 中被减去、在 `diag_reduce'` 中被加回，恰好抵消。 -/
lemma Q2_eq_four (k L Lp : ℕ) (hk : 1 ≤ k) :
    Q2 k L Lp = S1 k L Lp + S2 k L Lp + S3 k L Lp + Sd k L Lp := by
  rw [Q2_split, offdiag_split, off1_eq k L Lp hk, off2_eq k L Lp hk, off3_eq, diag_l3_eq,
    diag_reduce, diag_reduce']
  ring

/-! ### 论文 (1.2) 的三组 -/

/-- group 1：`∑_{j=k}^{L-1} u_j (u_{j-k} - u_j)`（论文里带系数 2）。 -/
noncomputable def group1 (k L : ℕ) : ℝ := ∑ j ∈ Finset.Ico k L, u j * (u (j - k) - u j)

/-- group 2：`∑_{n=max(0,L-k)}^{min(L,L'-k)-1} u_n u_{n+k}`。 -/
noncomputable def group2 (k L Lp : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico (L - k) (min L (Lp - k)), u n * u (n + k)

/-- group 3：`∑_{n=max(0,k-L')}^{min(L,k)-1} u_n u_{k-1-n}`。 -/
noncomputable def group3 (k L Lp : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico (k - Lp) (min L k), u n * u (k - 1 - n)

/-- `S1`：条件 `n + k < L'` 收进范围 `n < min(L, L'-k)`。 -/
lemma S1_eq_range (k L Lp : ℕ) :
    S1 k L Lp = ∑ n ∈ Finset.range (min L (Lp - k)), u n * u (n + k) := by
  unfold S1
  rw [← Finset.sum_filter]
  congr 1
  ext n; simp only [Finset.mem_filter, Finset.mem_range]; omega

/-- `S2`：条件 `m + k < L` 收进范围 `m < min(L', L-k)`。 -/
lemma S2_eq_range (k L Lp : ℕ) :
    S2 k L Lp = ∑ m ∈ Finset.range (min Lp (L - k)), u m * u (m + k) := by
  unfold S2
  rw [← Finset.sum_filter]
  congr 1
  ext n; simp only [Finset.mem_filter, Finset.mem_range]; omega

/-- `Sd`：条件 `k ≤ n` 收进范围 `Ico k (min L L')`。 -/
lemma Sd_eq_Ico (k L Lp : ℕ) :
    Sd k L Lp = ∑ n ∈ Finset.Ico k (min L Lp), -(2 * u n ^ 2) := by
  unfold Sd
  rw [← Finset.sum_filter]
  congr 1
  ext n; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega

/-- `S3` 即 group 3（对一切 `L, L'`，不需要 `L ≤ L'`）。 -/
lemma S3_eq_group3 (k L Lp : ℕ) : S3 k L Lp = group3 k L Lp := by
  rw [S3_eq]
  unfold group3
  rw [← Finset.sum_filter]
  congr 1
  ext n; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega

/-- 换元 `j = n + k`：`∑_{n<L-k} u_n u_{n+k} = ∑_{j=k}^{L-1} u_{j-k} u_j`。 -/
lemma shift_sum (k L : ℕ) :
    (∑ n ∈ Finset.range (L - k), u n * u (n + k)) = ∑ j ∈ Finset.Ico k L, u (j - k) * u j := by
  rw [Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr rfl
  intro n _
  rw [Nat.add_sub_cancel_left, add_comm k n]

/-- **论文 (1.2)**：`k ≥ 1`、`L ≤ L'` 时
`Q_{LL'}(δ_k) = 2·group1 + group2 + group3`。 -/
theorem Q2_eq_groups (k L Lp : ℕ) (hk : 1 ≤ k) (hL : L ≤ Lp) :
    Q2 k L Lp = 2 * group1 k L + group2 k L Lp + group3 k L Lp := by
  rw [Q2_eq_four k L Lp hk, S1_eq_range, S2_eq_range, Sd_eq_Ico, S3_eq_group3]
  have hmin1 : min Lp (L - k) = L - k := by omega
  have hmin2 : min L Lp = L := by omega
  rw [hmin1, hmin2]
  have hsplit : L - k ≤ min L (Lp - k) := by omega
  rw [← Finset.sum_range_add_sum_Ico (fun n => u n * u (n + k)) hsplit, shift_sum]
  unfold group1 group2
  have key : (∑ j ∈ Finset.Ico k L, u (j - k) * u j) + (∑ j ∈ Finset.Ico k L, u (j - k) * u j)
      + (∑ n ∈ Finset.Ico k L, -(2 * u n ^ 2))
      = 2 * ∑ j ∈ Finset.Ico k L, u j * (u (j - k) - u j) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _; ring
  linarith [key]

/-! ### 对称性（Remark 1.5） -/

/-- `O[δ_k]` 对称。 -/
lemma Ok_symm (k n m : ℕ) : Ok k n m = Ok k m n := by
  unfold Ok
  by_cases h : n = m
  · subst h; rfl
  · have h' : m ≠ n := Ne.symm h
    simp only [h, h', ne_eq, not_false_eq_true, ite_true, ite_false, add_zero]
    rw [add_comm m n, mul_comm (u m) (u n)]
    ring

/-- `Q_{LL'} = Q_{L'L}`。 -/
lemma Q2_symm (k L Lp : ℕ) : Q2 k L Lp = Q2 k Lp L := by
  unfold Q2
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro m _
  apply Finset.sum_congr rfl; intro n _
  exact Ok_symm k n m

/-! ### Lemma 1.4 的三条结论 -/

lemma group1_nonneg' (k L : ℕ) : 0 ≤ group1 k L := group1_nonneg k L
lemma group2_nonneg' (k L Lp : ℕ) : 0 ≤ group2 k L Lp := group2_nonneg k _ _
lemma group3_nonneg' (k L Lp : ℕ) : 0 ≤ group3 k L Lp := group3_nonneg k _ _

/-- **Lemma 1.4，非负性**：`k ≥ 1` 时 `Q_{LL'}(δ_k) ≥ 0`。

论文假设 `L, L' ≥ 1`；这里对一切 `L, L' ∈ ℕ` 成立（`L = 0` 或 `L' = 0` 时和为空）。 -/
theorem Q2_nonneg (k L Lp : ℕ) (hk : 1 ≤ k) : 0 ≤ Q2 k L Lp := by
  rcases le_total L Lp with h | h
  · rw [Q2_eq_groups k L Lp hk h]
    linarith [group1_nonneg' k L, group2_nonneg' k L Lp, group3_nonneg' k L Lp]
  · rw [Q2_symm, Q2_eq_groups k Lp L hk h]
    linarith [group1_nonneg' k Lp, group2_nonneg' k Lp L, group3_nonneg' k Lp L]

/-- `L + L' ≤ k` 时整块 `L × L'` 矩阵元为零：`|n-m| < k`、`n+m+1 < k`、`n < k`。 -/
lemma Ok_eq_zero_of_far (k L Lp n m : ℕ) (hn : n < L) (hm : m < Lp) (h : L + Lp ≤ k) :
    Ok k n m = 0 := by
  unfold Ok
  have h1 : ¬ n + k = m := by omega
  have h2 : ¬ m + k = n := by omega
  have h3 : ¬ n + m + 1 = k := by omega
  have h4 : ¬ k ≤ n := by omega
  by_cases hnm : n = m
  · subst hnm
    have h5 : ¬ 2 * n + 1 = k := by omega
    simp [h4, h5]
  · simp [h1, h2, h3, hnm]

/-- 等号条件的「⇐」：`L + L' ≤ k ⇒ Q_{LL'}(δ_k) = 0`。 -/
lemma Q2_eq_zero_of_le (k L Lp : ℕ) (h : L + Lp ≤ k) : Q2 k L Lp = 0 := by
  unfold Q2
  apply Finset.sum_eq_zero; intro n hn
  apply Finset.sum_eq_zero; intro m hm
  rw [Finset.mem_range] at hn hm
  exact Ok_eq_zero_of_far k L Lp n m hn hm h

/-- group 1 在 `k < L` 时严格正（每项严格正，因 `u` 严格递减且 `j - k < j`）。 -/
lemma group1_pos (k L : ℕ) (hk : 1 ≤ k) (h : k < L) : 0 < group1 k L := by
  unfold group1
  apply Finset.sum_pos
  · intro j hj
    rw [Finset.mem_Ico] at hj
    have hlt : j - k < j := by omega
    have h1 : u j < u (j - k) := u_strictAnti hlt
    exact mul_pos (u_pos j) (sub_pos.mpr h1)
  · exact Finset.nonempty_Ico.mpr h

/-- group 3 在 `L, L' ≥ 1`、`k < L + L'` 时严格正：范围 `[k-L', min(L,k))` 非空。 -/
lemma group3_pos (k L Lp : ℕ) (hk : 1 ≤ k) (hL : 1 ≤ L) (hLp : 1 ≤ Lp) (h : k < L + Lp) :
    0 < group3 k L Lp := by
  unfold group3
  apply Finset.sum_pos
  · intro n _; exact mul_pos (u_pos n) (u_pos _)
  · exact Finset.nonempty_Ico.mpr (by omega)

/-- 等号条件的「⇒」的逆否：`L + L' > k ⇒ Q_{LL'}(δ_k) > 0`。

论文的论证分 `L > k`（group 1 非空）与 `L ≤ k`（group 3 非空）两种情形；
这里只用 group 3 一种：`k < L + L'` 时 `k - L' < L` 且 `k - L' < k`（因 `L' ≥ 1`），
故 group 3 的范围 `[k-L', min(L,k))` 总是非空。 -/
theorem Q2_pos (k L Lp : ℕ) (hk : 1 ≤ k) (hL : 1 ≤ L) (hLp : 1 ≤ Lp) (h : k < L + Lp) :
    0 < Q2 k L Lp := by
  rcases le_total L Lp with hle | hle
  · rw [Q2_eq_groups k L Lp hk hle]
    linarith [group1_nonneg' k L, group2_nonneg' k L Lp, group3_pos k L Lp hk hL hLp h]
  · rw [Q2_symm, Q2_eq_groups k Lp L hk hle]
    linarith [group1_nonneg' k Lp, group2_nonneg' k Lp L,
      group3_pos k Lp L hk hLp hL (by omega)]

/-- **Lemma 1.4，等号条件**：`k, L, L' ≥ 1` 时 `Q_{LL'}(δ_k) = 0 ⟺ L + L' ≤ k`。 -/
theorem Q2_eq_zero_iff (k L Lp : ℕ) (hk : 1 ≤ k) (hL : 1 ≤ L) (hLp : 1 ≤ Lp) :
    Q2 k L Lp = 0 ↔ L + Lp ≤ k := by
  constructor
  · intro h0
    by_contra hlt
    exact absurd h0 (ne_of_gt (Q2_pos k L Lp hk hL hLp (not_le.mp hlt)))
  · exact Q2_eq_zero_of_le k L Lp

/-- `u_0 = 1`。 -/
lemma u_zero : u 0 = 1 := by
  unfold u; simp

/-- `k = 1`、`L' = L ≥ 1` 时 group 3 的范围是 `[0, 1)`，只有一项 `u_0 u_0 = 1`。 -/
lemma group3_one (L : ℕ) (hL : 1 ≤ L) : group3 1 L L = 1 := by
  unfold group3
  have h1 : (1 - L) = 0 := by omega
  have h2 : min L 1 = 1 := by omega
  rw [h1, h2]
  simp [u_zero]

/-- **Lemma 1.4，末句**：`L ≥ 1` 时 `Q_{LL}(δ_1) ≥ u_0² = 1`。 -/
theorem Q2_LL_one (L : ℕ) (hL : 1 ≤ L) : 1 ≤ Q2 1 L L := by
  rw [Q2_eq_groups 1 L L le_rfl le_rfl, group3_one L hL]
  linarith [group1_nonneg' 1 L, group2_nonneg' 1 L L]

end Eliashberg
