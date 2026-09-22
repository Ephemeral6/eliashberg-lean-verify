import Eliashberg.Lemma18Setup

/-!
# Lemma 1.8（Lemma B）—— 阶梯基是 Metzler 的

论文 §1.2.2。对 `K ≥ 0`、`L ≠ L'`（`L, L' ≥ 1`）：

* `W_nonneg`：`W_{L,L'}(K) ≥ 0`
* `W_eq_zero_iff`：`W_{L,L'}(K) = 0 ⟺ K = 0 ∨ L ≥ L' + K + 1`
* `g_nonneg_of_ge`：`(M e_{L'})_n ≥ 0`，`n ≥ L'`

## 证明结构（照论文，以 `n := L - 1`、`N' := L'`）

`W = g(n) - g(n+1)`，`g` 由 (1.4) 给出（`g_eq`）。

* `K = 0`：`M = 0`，`W = 0`。
* **Case I**（`L > L'`，即 `n ≥ N'`）：两行都没有对角项，`g(n) = u_n R(n)`，
  `R` 单调不增、`u` 递减 ⇒ `W ≥ 0`；`W = 0 ⟺ R(n) = 0 ⟺ n ≥ N' + K`。
* **Case II**（`L < L'`，即 `n + 2 ≤ N'`）：两行都有对角项。
  * **II.a**（`n < K`）：对角项都等于 `-1`，`R(n+1) ≤ R(n)`，
    `W ≥ d_n R(n) ≥ d_n u_0 > 0`。
  * **II.b**（`K ≤ n`）：对角项都是 `-(2K+1) u²`，L3 项为空。引入行权重
    `c_m := d_n u_m + u_{n+1} d_m`（递减、凸），(1.5) `c_n = u_n² - u_{n+1}²`。
    * **II.b.1**（`N' ≥ n + K + 2`，完整窗口）：
      `W = ∑_{m=n-K}^{n+K} c_m - (2K+1) c_n = ∑_{j=1}^K (c_{n-j} + c_{n+j} - 2c_n) > 0`（凸性）。
    * **II.b.2**（`n + 2 ≤ N' ≤ n + K + 1`，右截窗口）：`W` 关于 `N'` 不减，
      `W ≥ F = ∑_{m=n-K}^{n} c_m + u_n u_{n+1} - (2K+1) c_n ≥ u_n u_{n+1}(1 - 2K u_n u_{n+1}) > 0`
      （`c` 递减 + Lemma 1.3(3)(4)）。

## 与论文的两处小偏离

1. 论文 II.b.1 用「配对求和」`∑_{j=1}^K (c_{n-j}+c_{n+j}-2c_n)`；这里改成对 `K` 归纳
   （`T_succ`），每一步加上 `c_{n-(K+1)} + c_{n+(K+1)} - 2c_n ≥ 0`（`c_sym_nonneg`），
   避免了 Finset 的反射重排。数学内容相同。
2. 论文说 `c` 由 Lemma 1.3(1)–(2) 得「严格递减、凸」；证明中只用到递减（II.b.2）
   与凸（II.b.1）以及 `j = 1` 项的严格凸，这里就只证这些。
-/

namespace Eliashberg

open scoped BigOperators

/-! ### `K = 0` -/

lemma Mk_zero (n m : ℕ) : Mk 0 n m = 0 := by
  unfold Mk
  have h1 : (if 1 ≤ Nat.dist n m ∧ Nat.dist n m ≤ 0 then (1:ℝ) else 0) = 0 := by
    split_ifs with h
    · exfalso; omega
    · rfl
  have h2 : (if n + m + 1 ≤ 0 then (1:ℝ) else 0) = 0 := by
    split_ifs with h
    · exfalso; omega
    · rfl
  rw [h1, h2]
  simp

lemma g_zero (Np n : ℕ) : g 0 Np n = 0 := by
  unfold g; simp [Mk_zero]

lemma W'_zero (Np n : ℕ) : W' 0 Np n = 0 := by
  unfold W'; simp [g_zero]

/-! ### Case I：`n ≥ N'` -/

/-- `n ≥ N'` 时无对角项，且 `min N' (n+K+1) = N'`。 -/
lemma g_of_ge (K Np n : ℕ) (h : Np ≤ n) :
    g K Np n = u n * (S (n - K) Np + S 0 (min Np (K - n))) := by
  rw [g_eq]
  have h1 : ¬ n < Np := by omega
  have h2 : min Np (n + K + 1) = Np := by omega
  rw [ite_eq_right h1, sub_zero]
  unfold R
  rw [h2]

/-- Lemma 1.8 末句：`(M e_{N'})_n ≥ 0`，`n ≥ N'`。 -/
theorem g_nonneg_of_ge (K Np n : ℕ) (h : Np ≤ n) : 0 ≤ g K Np n := by
  rw [g_of_ge K Np n h]
  exact mul_nonneg (le_of_lt (u_pos n)) (add_nonneg (S_nonneg _ _) (S_nonneg _ _))

/-- Case I 的 `R` 关于 `n` 不增：第一项下限增大，第二项上限减小。 -/
lemma R1_anti (K Np n : ℕ) :
    S (n + 1 - K) Np + S 0 (min Np (K - (n + 1))) ≤ S (n - K) Np + S 0 (min Np (K - n)) := by
  apply add_le_add
  · exact S_mono_left _ _ _ (by omega)
  · exact S_mono_right _ _ _ (by omega)

lemma W'_caseI_nonneg (K Np n : ℕ) (h : Np ≤ n) : 0 ≤ W' K Np n := by
  unfold W'
  rw [g_of_ge K Np n h, g_of_ge K Np (n+1) (by omega)]
  have hR := R1_anti K Np n
  have hu : u (n+1) ≤ u n := u_anti (Nat.le_succ n)
  have hA0 : 0 ≤ S (n - K) Np + S 0 (min Np (K - n)) := add_nonneg (S_nonneg _ _) (S_nonneg _ _)
  have h1 : 0 ≤ (u n - u (n+1)) * (S (n - K) Np + S 0 (min Np (K - n))) :=
    mul_nonneg (sub_nonneg.mpr hu) hA0
  have h2 : 0 ≤ u (n+1) * ((S (n - K) Np + S 0 (min Np (K - n)))
      - (S (n + 1 - K) Np + S 0 (min Np (K - (n + 1))))) :=
    mul_nonneg (le_of_lt (u_pos _)) (sub_nonneg.mpr hR)
  linarith

/-- Case I，严格正：`n < N' + K` 时 `R(n) > 0`，于是 `W ≥ d_n R(n) > 0`。 -/
lemma W'_caseI_pos (K Np n : ℕ) (hNp : 1 ≤ Np) (h : Np ≤ n) (hlt : n < Np + K) :
    0 < W' K Np n := by
  unfold W'
  rw [g_of_ge K Np n h, g_of_ge K Np (n+1) (by omega)]
  have hR := R1_anti K Np n
  have hu : u (n+1) < u n := u_strictAnti (Nat.lt_succ_self n)
  have hApos : 0 < S (n - K) Np + S 0 (min Np (K - n)) := by
    have : 0 < S (n - K) Np := S_pos _ _ (by omega)
    linarith [S_nonneg 0 (min Np (K - n))]
  have h1 : 0 < (u n - u (n+1)) * (S (n - K) Np + S 0 (min Np (K - n))) :=
    mul_pos (sub_pos.mpr hu) hApos
  have h2 : 0 ≤ u (n+1) * ((S (n - K) Np + S 0 (min Np (K - n)))
      - (S (n + 1 - K) Np + S 0 (min Np (K - (n + 1))))) :=
    mul_nonneg (le_of_lt (u_pos _)) (sub_nonneg.mpr hR)
  linarith

/-- Case I，等号：`n ≥ N' + K` 时两行的 `R` 都为零。 -/
lemma W'_caseI_zero (K Np n : ℕ) (h : Np + K ≤ n) : W' K Np n = 0 := by
  unfold W'
  rw [g_of_ge K Np n (by omega), g_of_ge K Np (n+1) (by omega)]
  have e1 : S (n - K) Np = 0 := (S_eq_zero_iff _ _).mpr (by omega)
  have e2 : S (n + 1 - K) Np = 0 := (S_eq_zero_iff _ _).mpr (by omega)
  have e3 : min Np (K - n) = 0 := by omega
  have e4 : min Np (K - (n + 1)) = 0 := by omega
  rw [e1, e2, e3, e4, S_self]
  ring

/-! ### Case II.a：`n + 2 ≤ N'`，`n < K` -/

/-- `u_n² (1 + 2n) = 1`。 -/
lemma u_sq_mul (n : ℕ) : u n ^ 2 * (1 + 2 * (n:ℝ)) = 1 := by
  rw [u_sq]
  have h : (2 * (n:ℝ) + 1) ≠ 0 := ne_of_gt (two_mul_add_one_pos n)
  field_simp
  ring

/-- `n ≤ K`、`n < N'` 时对角项恰为 `-1`。 -/
lemma g_caseII_a (K Np n : ℕ) (hn : n < Np) (hK : n ≤ K) :
    g K Np n = u n * R K Np n - 1 := by
  rw [g_eq, ite_eq_left hn]
  have e : min n K = n := by omega
  rw [e, u_sq_mul]

/-- II.a：`R(n+1) ≤ R(n)`。两个差分是 `u_{n+K+1} 1_{n+K+1<N'} - u_{K-n-1} 1_{K-n-1<N'}`，
因 `K-n-1 ≤ n+K+1` 且 `u` 递减而 `≤ 0`。 -/
lemma R_caseII_a_le (K Np n : ℕ) (hK : n < K) : R K Np (n+1) ≤ R K Np n := by
  unfold R
  have e1 : n + 1 - K = 0 := by omega
  have e2 : n - K = 0 := by omega
  have e3 : n + 1 + K + 1 = (n + K + 1) + 1 := by omega
  have e4 : K - n = (K - (n + 1)) + 1 := by omega
  rw [e1, e2, e3, e4, S_zero_min_succ Np (n + K + 1), S_zero_min_succ Np (K - (n + 1))]
  have hle : u (n + K + 1) ≤ u (K - (n + 1)) := u_anti (by omega)
  by_cases h1 : n + K + 1 < Np
  · have h2 : K - (n + 1) < Np := by omega
    rw [ite_eq_left h1, ite_eq_left h2]; linarith
  · rw [ite_eq_right h1]
    split_ifs with h2
    · linarith [u_pos (K - (n + 1))]
    · linarith

lemma W'_caseII_a_pos (K Np n : ℕ) (hn : n + 1 < Np) (hK : n < K) : 0 < W' K Np n := by
  unfold W'
  rw [g_caseII_a K Np n (by omega) (by omega), g_caseII_a K Np (n+1) hn (by omega)]
  have hR := R_caseII_a_le K Np n hK
  have hu : u (n+1) < u n := u_strictAnti (Nat.lt_succ_self n)
  have hRlow : u 0 ≤ R K Np n := by
    unfold R
    have : 1 ≤ min Np (K - n) := by omega
    linarith [S_nonneg (n - K) (min Np (n + K + 1)), u_zero_le_S _ this]
  have hu0 : 0 < u 0 := u_pos 0
  have h1 : 0 ≤ u (n+1) * (R K Np n - R K Np (n+1)) :=
    mul_nonneg (le_of_lt (u_pos _)) (sub_nonneg.mpr hR)
  have h2 : (u n - u (n+1)) * u 0 ≤ (u n - u (n+1)) * R K Np n :=
    mul_le_mul_of_nonneg_left hRlow (le_of_lt (sub_pos.mpr hu))
  have h3 : 0 < (u n - u (n+1)) * u 0 := mul_pos (sub_pos.mpr hu) hu0
  linarith

/-! ### Case II.b：`n + 2 ≤ N'`，`K ≤ n`；行权重 `c` -/

/-- `K ≤ n < N'` 时对角系数是 `1 + 2K`，L3 项为空。 -/
lemma g_caseII_b (K Np n : ℕ) (hn : n < Np) (hK : K ≤ n) :
    g K Np n = u n * S (n - K) (min Np (n + K + 1)) - u n ^ 2 * (1 + 2 * (K:ℝ)) := by
  rw [g_eq, ite_eq_left hn]
  have e : min n K = K := by omega
  rw [e]
  unfold R
  have e2 : min Np (K - n) = 0 := by omega
  rw [e2, S_self]
  ring

/-- 行权重 `c_m := d_n u_m + u_{n+1} d_m`（`n` 固定）。 -/
noncomputable def c (n m : ℕ) : ℝ := d n * u m + u (n+1) * d m

/-- (1.5)：`c_n = d_n (u_n + u_{n+1}) = u_n² - u_{n+1}²`。 -/
lemma c_self (n : ℕ) : c n n = u n ^ 2 - u (n+1) ^ 2 := by
  unfold c; rw [u_sq_sub_sq_eq_d]; ring

/-- `c` 递减（`u`、`d` 都递减，系数非负）。 -/
lemma c_anti (n : ℕ) : Antitone (c n) := by
  apply antitone_nat_of_succ_le
  intro m
  unfold c
  have h1 : u (m+1) ≤ u m := u_anti (Nat.le_succ m)
  have h2 : d (m+1) ≤ d m := d_anti (Nat.le_succ m)
  have h3 : 0 ≤ d n := le_of_lt (d_pos n)
  have h4 : 0 ≤ u (n+1) := le_of_lt (u_pos _)
  linarith [mul_le_mul_of_nonneg_left h1 h3, mul_le_mul_of_nonneg_left h2 h4]

/-- `c` 凸：`2 c_{m+1} ≤ c_m + c_{m+2}`（`u` 凸、`d` 凸）。 -/
lemma c_convex (n m : ℕ) : 2 * c n (m+1) ≤ c n m + c n (m+2) := by
  unfold c
  have h1 := u_convex m
  have h2 := d_convex m
  have h3 : 0 ≤ d n := le_of_lt (d_pos n)
  have h4 : 0 ≤ u (n+1) := le_of_lt (u_pos _)
  linarith [mul_le_mul_of_nonneg_left (le_of_lt h1) h3, mul_le_mul_of_nonneg_left h2 h4]

/-- `c` 严格凸（`u` 严格凸、`d_n > 0`）。 -/
lemma c_strict_convex (n m : ℕ) : 2 * c n (m+1) < c n m + c n (m+2) := by
  unfold c
  have h1 := u_convex m
  have h2 := d_convex m
  have h3 : 0 < d n := d_pos n
  have h4 : 0 ≤ u (n+1) := le_of_lt (u_pos _)
  linarith [mul_lt_mul_of_pos_left h1 h3, mul_le_mul_of_nonneg_left h2 h4]

/-- 一阶差分 `Δ_m := c_{m+1} - c_m` 单调不减（即凸性）。 -/
lemma c_delta_mono (n : ℕ) : Monotone (fun m => c n (m+1) - c n m) := by
  apply monotone_nat_of_le_succ
  intro m
  show c n (m+1) - c n m ≤ c n (m+1+1) - c n (m+1)
  have h := c_convex n m
  have e : m + 2 = m + 1 + 1 := rfl
  rw [e] at h
  linarith

/-- 对称二阶差分非负：`j ≤ n ⇒ c_{n-j} + c_{n+j} ≥ 2 c_n`。 -/
lemma c_sym_nonneg (n j : ℕ) (hj : j ≤ n) : 2 * c n n ≤ c n (n - j) + c n (n + j) := by
  induction j with
  | zero =>
    show 2 * c n n ≤ c n (n - 0) + c n (n + 0)
    rw [Nat.sub_zero, Nat.add_zero]; linarith
  | succ j ih =>
    have ih' := ih (by omega)
    have hmono := c_delta_mono n (show n - (j+1) ≤ n + j by omega)
    simp only at hmono
    have e : n - (j+1) + 1 = n - j := by omega
    rw [e] at hmono
    have e2 : n + (j+1) = n + j + 1 := by omega
    rw [e2]
    linarith

/-- `j = 1` 的对称二阶差分严格正（`n ≥ 1`）。 -/
lemma c_sym_one_pos (n : ℕ) (hn : 1 ≤ n) : 2 * c n n < c n (n - 1) + c n (n + 1) := by
  have h := c_strict_convex n (n - 1)
  have e1 : n - 1 + 1 = n := by omega
  have e2 : n - 1 + 2 = n + 1 := by omega
  rw [e1, e2] at h
  exact h

/-- `T(K) := ∑_{m=n-K}^{n+K} c_m - (2K+1) c_n`，即 (1.6) 的左端。 -/
noncomputable def T (n K : ℕ) : ℝ :=
  (∑ m ∈ Finset.Ico (n - K) (n + K + 1), c n m) - (2 * (K:ℝ) + 1) * c n n

lemma T_zero (n : ℕ) : T n 0 = 0 := by
  unfold T
  rw [Nat.sub_zero, Nat.add_zero, Nat.Ico_succ_singleton, Finset.sum_singleton]
  simp

/-- 窗口两端各加一项：`T(K+1) = T(K) + (c_{n-(K+1)} + c_{n+(K+1)} - 2c_n)`。 -/
lemma T_succ (n K : ℕ) (hK : K + 1 ≤ n) :
    T n (K+1) = T n K + (c n (n - (K+1)) + c n (n + (K+1)) - 2 * c n n) := by
  unfold T
  have h1 : n - (K+1) < n + (K+1) + 1 := by omega
  rw [Finset.sum_eq_sum_Ico_succ_bot h1]
  have e1 : n - (K+1) + 1 = n - K := by omega
  rw [e1]
  have h2 : n - K ≤ n + K + 1 := by omega
  have e2 : n + (K+1) + 1 = (n + K + 1) + 1 := by omega
  rw [e2, Finset.sum_Ico_succ_top h2]
  have e3 : n + (K+1) = n + K + 1 := by omega
  rw [e3]
  push_cast
  ring

/-- (1.6)：`1 ≤ K ≤ n` 时 `T(K) > 0`。归纳：`T(1) = c_{n-1} + c_{n+1} - 2c_n > 0`，
每一步再加非负项。 -/
lemma T_pos (n K : ℕ) (hK1 : 1 ≤ K) (hKn : K ≤ n) : 0 < T n K := by
  induction K, hK1 using Nat.le_induction with
  | base =>
    have h := T_succ n 0 hKn
    rw [T_zero, zero_add] at h
    have h' : T n 1 = c n (n - 1) + c n (n + 1) - 2 * c n n := by simpa using h
    rw [h']
    exact sub_pos.mpr (c_sym_one_pos n hKn)
  | succ K hK ih =>
    rw [T_succ n K hKn]
    have h1 := ih (by omega)
    have h2 := c_sym_nonneg n (K+1) hKn
    linarith

/-- Case II.b.1 的恒等式：
`u_n S(n-K, n+K+1) - u_{n+1} S(n-K+1, n+K+2) = ∑_{m=n-K}^{n+K} c_m`。 -/
lemma window_identity (n K : ℕ) (hK : K ≤ n) :
    u n * S (n - K) (n + K + 1) - u (n+1) * S (n - K + 1) (n + K + 2)
      = ∑ m ∈ Finset.Ico (n - K) (n + K + 1), c n m := by
  have h1 : S (n - K) (n + K + 2) = u (n - K) + S (n - K + 1) (n + K + 2) :=
    S_succ_bot _ _ (by omega)
  have h2 : S (n - K) (n + K + 2) = S (n - K) (n + K + 1) + u (n + K + 1) :=
    S_succ_top (n - K) (n + K + 1) (by omega)
  have h3 : ∑ m ∈ Finset.Ico (n - K) (n + K + 1), d m = u (n - K) - u (n + K + 1) :=
    sum_d_Ico _ _ (by omega)
  have hS : S (n - K) (n + K + 1) = ∑ m ∈ Finset.Ico (n - K) (n + K + 1), u m := rfl
  have hS' : S (n - K + 1) (n + K + 2) = S (n - K) (n + K + 1) + u (n + K + 1) - u (n - K) := by
    linarith
  unfold c
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h3, ← hS, hS']
  have hd : d n = u n - u (n+1) := rfl
  rw [hd]
  ring

/-- Case II.b.1：完整窗口，`W = T(K) > 0`。 -/
lemma W'_caseII_b1_pos (K Np n : ℕ) (hK1 : 1 ≤ K) (hK : K ≤ n) (hNp : n + K + 2 ≤ Np) :
    0 < W' K Np n := by
  unfold W'
  rw [g_caseII_b K Np n (by omega) hK, g_caseII_b K Np (n+1) (by omega) (by omega)]
  have e1 : min Np (n + K + 1) = n + K + 1 := by omega
  have e2 : min Np (n + 1 + K + 1) = n + K + 2 := by omega
  have e3 : n + 1 - K = n - K + 1 := by omega
  rw [e1, e2, e3]
  have hw := window_identity n K hK
  have hT := T_pos n K hK1 hK
  unfold T at hT
  rw [c_self] at hT
  linarith

/-- Case II.b.2：右截窗口。`W(N') ≥ W(n+2) = F`，
`F = ∑_{m=n-K}^{n} c_m + u_n u_{n+1} - (2K+1) c_n ≥ u_n u_{n+1} (1 - 2K u_n u_{n+1}) > 0`。 -/
lemma W'_caseII_b2_pos (K Np n : ℕ) (hK1 : 1 ≤ K) (hK : K ≤ n)
    (hNp1 : n + 2 ≤ Np) (hNp2 : Np ≤ n + K + 1) : 0 < W' K Np n := by
  unfold W'
  rw [g_caseII_b K Np n (by omega) hK, g_caseII_b K Np (n+1) (by omega) (by omega)]
  have e1 : min Np (n + K + 1) = Np := by omega
  have e2 : min Np (n + 1 + K + 1) = Np := by omega
  have e3 : n + 1 - K = n - K + 1 := by omega
  rw [e1, e2, e3]
  -- `S(n-K+1, N') = S(n-K, N') - u_{n-K}`
  have h1 : S (n - K) Np = u (n - K) + S (n - K + 1) Np := S_succ_bot _ _ (by omega)
  have hB : S (n - K + 1) Np = S (n - K) Np - u (n - K) := by linarith
  rw [hB]
  -- 关于 `N'` 的单调性：`S(n-K, N') ≥ S(n-K, n+2)`
  have h2 : S (n - K) (n + 2) ≤ S (n - K) Np := S_mono_right _ _ _ hNp1
  have h3 : S (n - K) (n + 2) = S (n - K) (n + 1) + u (n + 1) :=
    S_succ_top (n - K) (n + 1) (by omega)
  have h4 : ∑ m ∈ Finset.Ico (n - K) (n + 1), d m = u (n - K) - u (n + 1) :=
    sum_d_Ico _ _ (by omega)
  -- `c` 递减 ⇒ `∑_{m=n-K}^{n} c_m ≥ (K+1) c_n`
  have h5 : ((K:ℝ) + 1) * c n n ≤ ∑ m ∈ Finset.Ico (n - K) (n + 1), c n m := by
    have hcard : (Finset.Ico (n - K) (n + 1)).card = K + 1 := by rw [Nat.card_Ico]; omega
    have := Finset.card_nsmul_le_sum (Finset.Ico (n - K) (n + 1)) (c n) (c n n)
      (fun m hm => c_anti n (by rw [Finset.mem_Ico] at hm; omega))
    rw [hcard, nsmul_eq_mul] at this
    push_cast at this
    exact this
  -- `∑ c_m = d_n S(n-K, n+1) + u_{n+1} (u_{n-K} - u_{n+1})`
  have h6 : ∑ m ∈ Finset.Ico (n - K) (n + 1), c n m
      = (u n - u (n+1)) * S (n - K) (n + 1) + u (n+1) * (u (n - K) - u (n + 1)) := by
    unfold c
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h4]
    rfl
  -- Lemma 1.3(4)：`2K u_n u_{n+1} < 1`
  have h7 := lemma_1_3_4 K n hK
  have h7' : 2 * (K:ℝ) * (u n * u (n+1)) < 1 := by linarith [h7.1, h7.2]
  have hun : 0 < u n * u (n+1) := mul_pos (u_pos n) (u_pos (n+1))
  have h8 : 0 < u n * u (n+1) * (1 - 2 * (K:ℝ) * (u n * u (n+1))) :=
    mul_pos hun (by linarith)
  have hd : 0 < u n - u (n+1) := sub_pos.mpr (u_strictAnti (Nat.lt_succ_self n))
  have hprod : (u n - u (n+1)) * (S (n - K) (n + 1) + u (n + 1)) ≤ (u n - u (n+1)) * S (n - K) Np :=
    mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hd)
  have hc := c_self n
  have hsq := u_sq_sub_sq n
  -- `K c_n = 2K u_n² u_{n+1}²`，与 Lemma 1.3(4) 配合
  have hcK : (K:ℝ) * c n n = 2 * (K:ℝ) * (u n ^ 2 * u (n+1) ^ 2) := by rw [hc, hsq]; ring
  have hK2 : (K:ℝ) * (u n ^ 2 - u (n+1) ^ 2) = 2 * (K:ℝ) * (u n ^ 2 * u (n+1) ^ 2) := by
    rw [hsq]; ring
  nlinarith [hprod, h6, h5, hc, hsq, h8, hcK, hK2]

/-! ### 组装 -/

/-- 严格正的统一入口：`K ≥ 1`、`N' ≥ 1`、`n + 1 ≠ N'`、`n < N' + K`。 -/
theorem W'_pos (K Np n : ℕ) (hK : 1 ≤ K) (hNp : 1 ≤ Np) (hne : n + 1 ≠ Np)
    (hlt : n < Np + K) : 0 < W' K Np n := by
  rcases le_or_gt Np n with h | h
  · exact W'_caseI_pos K Np n hNp h hlt
  · have hn2 : n + 2 ≤ Np := by omega
    rcases lt_or_ge n K with hnK | hKn
    · exact W'_caseII_a_pos K Np n (by omega) hnK
    · rcases le_or_gt (n + K + 2) Np with hb1 | hb2
      · exact W'_caseII_b1_pos K Np n hK hKn hb1
      · exact W'_caseII_b2_pos K Np n hK hKn hn2 (by omega)

theorem W'_nonneg (K Np n : ℕ) (hNp : 1 ≤ Np) (hne : n + 1 ≠ Np) : 0 ≤ W' K Np n := by
  rcases Nat.eq_zero_or_pos K with hK0 | hK
  · subst hK0; exact le_of_eq (W'_zero Np n).symm
  · rcases le_or_gt (Np + K) n with h | h
    · exact le_of_eq (W'_caseI_zero K Np n h).symm
    · exact le_of_lt (W'_pos K Np n hK hNp hne h)

theorem W'_eq_zero_iff (K Np n : ℕ) (hNp : 1 ≤ Np) (hne : n + 1 ≠ Np) :
    W' K Np n = 0 ↔ (K = 0 ∨ Np + K ≤ n) := by
  constructor
  · intro h0
    by_contra hcon
    have hK : 1 ≤ K := by omega
    have hlt : n < Np + K := by omega
    exact absurd h0 (ne_of_gt (W'_pos K Np n hK hNp hne hlt))
  · rintro (hK0 | hge)
    · subst hK0; exact W'_zero Np n
    · exact W'_caseI_zero K Np n hge

/-- **Lemma 1.8，非负性**：`L ≠ L'`（`L, L' ≥ 1`）时 `W_{L,L'}(K) ≥ 0`。 -/
theorem W_nonneg (K L Lp : ℕ) (hL : 1 ≤ L) (hLp : 1 ≤ Lp) (hne : L ≠ Lp) : 0 ≤ W K L Lp := by
  rw [W_eq_W' K L Lp hL]
  exact W'_nonneg K Lp (L - 1) hLp (by omega)

/-- **Lemma 1.8，等号条件**：`W_{L,L'}(K) = 0 ⟺ K = 0 ∨ L ≥ L' + K + 1`。 -/
theorem W_eq_zero_iff (K L Lp : ℕ) (hL : 1 ≤ L) (hLp : 1 ≤ Lp) (hne : L ≠ Lp) :
    W K L Lp = 0 ↔ (K = 0 ∨ Lp + K + 1 ≤ L) := by
  rw [W_eq_W' K L Lp hL, W'_eq_zero_iff K Lp (L - 1) hLp (by omega)]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by omega)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by omega)

/-- **Lemma 1.8，末句**：`(M e_{L'})_n ≥ 0`，`n ≥ L'`。 -/
theorem Mk_row_nonneg (K Lp n : ℕ) (h : Lp ≤ n) : 0 ≤ g K Lp n := g_nonneg_of_ge K Lp n h

/-- Remark 1.9(a) 的反例数值：`k = 3`、`(L, L') = (2, 1)` 时 `O[δ_3]` 的阶梯系数
`(O[δ_3] e_1)_1 - (O[δ_3] e_1)_2 = 0 - u_2 u_0 = -1/√5 < 0`。
这说明 Lemma 1.8 对非单调核 `δ_k` 不成立。 -/
lemma remark_1_9_a : Q2 3 2 1 - Q2 3 1 1 - (Q2 3 3 1 - Q2 3 2 1) < 0 := by
  -- `(O[δ_3] e_1)_n = Ok 3 n 0`；`Q2 3 (n+1) 1 - Q2 3 n 1 = Ok 3 n 0`
  have h1 : Q2 3 2 1 - Q2 3 1 1 = Ok 3 1 0 := by
    unfold Q2; simp [Finset.sum_range_succ]
  have h2 : Q2 3 3 1 - Q2 3 2 1 = Ok 3 2 0 := by
    unfold Q2; simp [Finset.sum_range_succ]
  rw [h1, h2]
  unfold Ok
  norm_num
  exact mul_pos (u_pos 2) (u_pos 0)

end Eliashberg
