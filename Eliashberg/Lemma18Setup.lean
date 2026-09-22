import Eliashberg.Lemma14Main

/-!
# Lemma 1.8（Lemma B）的准备：`O[f]`、阶梯核 `M`、行和 `g` 与 (1.4)

论文 §1.2.2。

## 定义

* `Of f n m`：(0.1) 的一般核算子 `O[f]` 的矩阵元
  `O[f]_{nm} = -δ_{nm} 2u_n² ∑_{k=1}^n f(k) + (1-δ_{nm}) f(|n-m|) u_n u_m + f(n+m+1) u_n u_m`
* `delta k`：`δ_k`；`step K`：`1_{k ≤ K}`（`{1,…,K}` 的指示函数，`K = 0` 时恒零）
* `Mk K n m`：(1.3) 的显式形式
  `M_{nm} = u_n u_m (1_{1≤|n-m|≤K} + 1_{n+m+1≤K}) - 2u_n² min(n,K) δ_{nm}`
* `g K N' n = (M e_{N'})_n = ∑_{m<N'} M_{nm}`（论文证明中的 `g(n)`）
* `R K N' n = S(max(0,n-K), min(N',n+K+1)) + S(0, min(N',K-n))`（(1.4)）
* `W K L L' = g K L' (L-1) - g K L' L`（阶梯非对角系数 `W_{L,L'}(K)`）

## 与 (0.1) 的一致性

`Of_delta`：`O[δ_k] = Ok`（Lemma 1.4 用的矩阵元），`Of_step`：`O[1_{k≤K}] = Mk`。
两者都从同一个 `Of` 推出，故 (1.3) 与 Lemma 1.4 所用的 (0.1) 特例互相一致。
-/

namespace Eliashberg

open scoped BigOperators

/-- (0.1)：一般核 `f` 的算子 `O[f]` 的矩阵元。 -/
noncomputable def Of (f : ℕ → ℝ) (n m : ℕ) : ℝ :=
  (if n = m then -(2 * u n ^ 2 * ∑ k ∈ Finset.Icc 1 n, f k) else 0)
  + (if n ≠ m then f (Nat.dist n m) * (u n * u m) else 0)
  + f (n + m + 1) * (u n * u m)

/-- `δ_k`。 -/
def delta (k : ℕ) : ℕ → ℝ := fun j => if j = k then 1 else 0

/-- `1_{k ≤ K}`：`{1,…,K}` 的指示函数。 -/
def step (K : ℕ) : ℕ → ℝ := fun j => if 1 ≤ j ∧ j ≤ K then 1 else 0

/-- (1.3)：`M := O[1_{k≤K}]` 的显式矩阵元。 -/
noncomputable def Mk (K n m : ℕ) : ℝ :=
  u n * u m * ((if 1 ≤ Nat.dist n m ∧ Nat.dist n m ≤ K then 1 else 0)
               + (if n + m + 1 ≤ K then 1 else 0))
  - (if n = m then 2 * u n ^ 2 * ((min n K : ℕ) : ℝ) else 0)

/-- `O[δ_k] = Ok`：Lemma 1.4 所用的矩阵元确是 (0.1) 在 `f = δ_k` 的特例。 -/
lemma Of_delta (k n m : ℕ) (hk : 1 ≤ k) : Of (delta k) n m = Ok k n m := by
  unfold Of Ok delta
  by_cases h : n = m
  · subst h
    simp only [ite_true, ne_eq, not_true_eq_false, ite_false, add_zero]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_Icc]
    have e : (n + n + 1 = k) ↔ (2 * n + 1 = k) := by omega
    simp only [e]
    by_cases hkn : k ≤ n <;> by_cases h2 : 2 * n + 1 = k <;> simp [hk, hkn, h2] <;> ring
  · simp only [h, ne_eq, not_false_eq_true, ite_true, ite_false, zero_add]
    have e1 : (Nat.dist n m = k) ↔ (n + k = m ∨ m + k = n) := by unfold Nat.dist; omega
    simp only [e1]
    -- `n + k = m` 与 `m + k = n` 不能同时成立（`k ≥ 1`），故只有三种非平凡情形
    by_cases h1 : n + k = m
    · have h2 : ¬ m + k = n := by omega
      by_cases h3 : n + m + 1 = k <;> simp [h1, h2, h3]
    · by_cases h2 : m + k = n <;> by_cases h3 : n + m + 1 = k <;> simp [h1, h2, h3] <;> ring

/-- `∑_{k=1}^n 1_{k≤K} = min(n, K)`。 -/
lemma sum_step (n K : ℕ) : ∑ k ∈ Finset.Icc 1 n, step K k = ((min n K : ℕ) : ℝ) := by
  unfold step
  rw [Finset.sum_boole]
  have : (Finset.Icc 1 n).filter (fun k => 1 ≤ k ∧ k ≤ K) = Finset.Icc 1 (min n K) := by
    ext k; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  rw [this, Nat.card_Icc]
  have h2 : min n K + 1 - 1 = min n K := by omega
  rw [h2]

/-- `O[1_{k≤K}] = Mk`：(1.3) 确由 (0.1) 推出。 -/
lemma Of_step (K n m : ℕ) : Of (step K) n m = Mk K n m := by
  unfold Of Mk
  rw [sum_step]
  by_cases h : n = m
  · subst h
    have hd : Nat.dist n n = 0 := Nat.dist_self n
    simp only [ite_true, ne_eq, not_true_eq_false, ite_false, add_zero, hd]
    unfold step
    have e : (1 ≤ n + n + 1 ∧ n + n + 1 ≤ K) ↔ (n + n + 1 ≤ K) := by omega
    simp only [e]
    have e0 : ¬ (1 ≤ 0 ∧ 0 ≤ K) := by omega
    simp only [e0, ite_false, zero_add]
    ring
  · simp only [h, ne_eq, not_false_eq_true, ite_true, ite_false, zero_add, sub_zero]
    unfold step
    have e : (1 ≤ n + m + 1 ∧ n + m + 1 ≤ K) ↔ (n + m + 1 ≤ K) := by omega
    simp only [e]
    ring

/-- `Of` 对 `f` 逐点线性（有限和）。 -/
lemma Of_sum {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℝ) (n m : ℕ) :
    Of (fun j => ∑ i ∈ s, f i j) n m = ∑ i ∈ s, Of (f i) n m := by
  unfold Of
  simp only [Finset.sum_add_distrib, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_mul, Finset.mul_sum, Finset.sum_neg_distrib]
  rw [Finset.sum_comm]

/-- `1_{k≤K} = ∑_{k=1}^K δ_k`（逐点）。 -/
lemma step_eq_sum_delta (K j : ℕ) : step K j = ∑ k ∈ Finset.Icc 1 K, delta k j := by
  unfold step delta
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_Icc]

/-- `M = ∑_{k=1}^K O[δ_k]`：Lemma 1.8 的核与 Lemma 1.4 的核由线性相连。 -/
lemma Mk_eq_sum_Ok (K n m : ℕ) : Mk K n m = ∑ k ∈ Finset.Icc 1 K, Ok k n m := by
  rw [← Of_step]
  have : step K = fun j => ∑ k ∈ Finset.Icc 1 K, delta k j := by
    funext j; exact step_eq_sum_delta K j
  rw [this, Of_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_Icc] at hk
  exact Of_delta k n m hk.1

/-! ### 部分和 `S` 的基本性质 -/

lemma S_nonneg (a b : ℕ) : 0 ≤ S a b :=
  Finset.sum_nonneg (fun m _ => le_of_lt (u_pos m))

lemma S_self (a : ℕ) : S a a = 0 := by unfold S; simp

/-- `S 0 0 = 0`（`min N' 0 = 0` 后用）。 -/
lemma S_zero_zero : S 0 0 = 0 := S_self 0

lemma S_mono_left (a a' b : ℕ) (h : a ≤ a') : S a' b ≤ S a b := by
  unfold S
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico h le_rfl)
  intro m _ _; exact le_of_lt (u_pos m)

lemma S_mono_right (a b b' : ℕ) (h : b ≤ b') : S a b ≤ S a b' := by
  unfold S
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico le_rfl h)
  intro m _ _; exact le_of_lt (u_pos m)

lemma S_pos (a b : ℕ) (h : a < b) : 0 < S a b := by
  unfold S
  apply Finset.sum_pos
  · intro m _; exact u_pos m
  · exact Finset.nonempty_Ico.mpr h

lemma S_eq_zero_iff (a b : ℕ) : S a b = 0 ↔ b ≤ a := by
  constructor
  · intro h0
    by_contra hlt
    exact absurd h0 (ne_of_gt (S_pos a b (not_le.mp hlt)))
  · intro h
    unfold S
    rw [Finset.Ico_eq_empty_of_le h]
    simp

lemma S_succ_bot (a b : ℕ) (h : a < b) : S a b = u a + S (a + 1) b := by
  unfold S; exact Finset.sum_eq_sum_Ico_succ_bot h u

lemma S_succ_top (a b : ℕ) (h : a ≤ b) : S a (b + 1) = S a b + u b := by
  unfold S; exact Finset.sum_Ico_succ_top h u

/-- `b ≥ 1` 时 `S 0 b ≥ u_0`。 -/
lemma u_zero_le_S (b : ℕ) (hb : 1 ≤ b) : u 0 ≤ S 0 b := by
  unfold S
  exact Finset.single_le_sum (fun m _ => le_of_lt (u_pos m)) (Finset.mem_Ico.mpr ⟨le_rfl, hb⟩)

/-- 望远镜：`∑_{m=a}^{b-1} d_m = u_a - u_b`。 -/
lemma sum_d_Ico (a b : ℕ) (h : a ≤ b) : ∑ m ∈ Finset.Ico a b, d m = u a - u b := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hd : ∀ i, d (a + i) = u (a + i) - u (a + (i + 1)) := by
    intro i; unfold d; rw [add_assoc]
  simp only [hd]
  rw [Finset.sum_range_sub' (fun i => u (a + i))]
  simp only [add_zero]
  rw [Nat.add_sub_cancel' h]

/-- `S 0 (min N' (a+1)) = S 0 (min N' a) + u_a 1_{a<N'}`。 -/
lemma S_zero_min_succ (Np a : ℕ) :
    S 0 (min Np (a + 1)) = S 0 (min Np a) + (if a < Np then u a else 0) := by
  by_cases h : a < Np
  · have h1 : min Np (a + 1) = a + 1 := by omega
    have h2 : min Np a = a := by omega
    rw [h1, h2, S_succ_top 0 a (Nat.zero_le a)]
    simp [h]
  · have h1 : min Np (a + 1) = Np := by omega
    have h2 : min Np a = Np := by omega
    rw [h1, h2]
    simp [h]

/-! ### 行和 `g` 与 (1.4) -/

/-- `g(n) := (M e_{N'})_n = ∑_{m<N'} M_{nm}`。 -/
noncomputable def g (K Np n : ℕ) : ℝ := ∑ m ∈ Finset.range Np, Mk K n m

/-- (1.4) 的 `R(n) := S(max(0,n-K), min(N',n+K+1)) + S(0, min(N',K-n))`。 -/
noncomputable def R (K Np n : ℕ) : ℝ :=
  S (n - K) (min Np (n + K + 1)) + S 0 (min Np (K - n))

/-- L2 窗口和收进求和范围。 -/
lemma sum_window (K Np n : ℕ) :
    (∑ m ∈ Finset.range Np, if n - K ≤ m ∧ m < n + K + 1 then u m else 0)
      = S (n - K) (min Np (n + K + 1)) := by
  unfold S
  rw [← Finset.sum_filter]
  congr 1
  ext m; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega

/-- L3 和收进求和范围。 -/
lemma sum_l3 (K Np n : ℕ) :
    (∑ m ∈ Finset.range Np, if m < K - n then u m else 0) = S 0 (min Np (K - n)) := by
  unfold S
  rw [← Finset.sum_filter]
  congr 1
  ext m; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega

/-- `Mk` 逐项改写：把 `1_{1≤|n-m|≤K}` 写成「窗口减对角」。 -/
lemma Mk_pointwise (K n m : ℕ) :
    Mk K n m = u n * (if n - K ≤ m ∧ m < n + K + 1 then u m else 0)
             - (if n = m then u n * u n else 0)
             + u n * (if m < K - n then u m else 0)
             - (if n = m then 2 * u n ^ 2 * ((min n K : ℕ) : ℝ) else 0) := by
  unfold Mk
  by_cases hnm : n = m
  · subst hnm
    have hd : Nat.dist n n = 0 := Nat.dist_self n
    have e0 : ¬ (1 ≤ 0 ∧ 0 ≤ K) := by omega
    have e1 : (n - K ≤ n ∧ n < n + K + 1) := by omega
    have e2 : (n + n + 1 ≤ K) ↔ (n < K - n) := by omega
    simp only [hd, e0, e1, e2, ite_true, ite_false, and_true, zero_add]
    split_ifs <;> ring
  · have e1 : (1 ≤ Nat.dist n m ∧ Nat.dist n m ≤ K) ↔ (n - K ≤ m ∧ m < n + K + 1) := by
      unfold Nat.dist; omega
    have e2 : (n + m + 1 ≤ K) ↔ (m < K - n) := by omega
    simp only [e1, e2, hnm, ite_false, sub_zero]
    split_ifs <;> ring

/-- **(1.4)**：`g(n) = u_n R(n) - u_n² (1 + 2 min(n,K)) 1_{n<N'}`。 -/
lemma g_eq (K Np n : ℕ) :
    g K Np n = u n * R K Np n
      - (if n < Np then u n ^ 2 * (1 + 2 * ((min n K : ℕ) : ℝ)) else 0) := by
  unfold g
  simp only [Mk_pointwise]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, sum_window, sum_l3,
    Finset.sum_ite_eq, Finset.sum_ite_eq]
  simp only [Finset.mem_range]
  unfold R
  split_ifs <;> ring

/-- 阶梯非对角系数 `W_{L,L'}(K) := (M e_{L'})_{L-1} - (M e_{L'})_L`。 -/
noncomputable def W (K L Lp : ℕ) : ℝ := g K Lp (L - 1) - g K Lp L

/-- 以 `n := L - 1` 为变量的版本：`W' K N' n = g(n) - g(n+1)`。 -/
noncomputable def W' (K Np n : ℕ) : ℝ := g K Np n - g K Np (n + 1)

lemma W_eq_W' (K L Lp : ℕ) (hL : 1 ≤ L) : W K L Lp = W' K Lp (L - 1) := by
  unfold W W'
  have : L - 1 + 1 = L := by omega
  rw [this]

lemma R_nonneg (K Np n : ℕ) : 0 ≤ R K Np n := add_nonneg (S_nonneg _ _) (S_nonneg _ _)

end Eliashberg
