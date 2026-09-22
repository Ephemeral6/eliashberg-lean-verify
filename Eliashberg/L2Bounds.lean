import Eliashberg.Corollaries
import Eliashberg.Kernel

/-!
# Lemma 0.2.1 的实质：`O[f]` 的 Rayleigh 界与 Hilbert–Schmidt 界（有限截断形式）

论文 Lemma 0.2.1：`f ∈ ℓ¹` 时 `‖O[f]‖ ≤ ‖O[f]‖_HS ≤ 5‖f‖_ℓ¹`。

这里以**有限截断**的形式证成两条独立的界（论文的证明也是逐矩阵元估计后求和）：

* **Rayleigh 界**（`rayleigh_abs_le`）：对任意 `v` 与 `N`，
  `|∑_{n,m<N} v_n O[f]_{nm} v_m| ≤ 5 ‖f‖_ℓ¹ ∑_{n<N} v_n²`。
  证法是 Schur 检验：行和 `∑_m |O[f]_{nm}| ≤ 5‖f‖_ℓ¹`（`row_abs_sum_le`），
  配 `|v_n v_m| ≤ (v_n² + v_m²)/2` 与对称性。这就是 `‖O[f]‖ ≤ 5‖f‖_ℓ¹`
  在 Rayleigh 商意义下的形式。
* **HS 界**（`hs_le`）：`∑_{n,m<K} O[f]_{nm}² ≤ (13π²/6 + 2) ‖f‖_ℓ¹² ≤ 25 ‖f‖_ℓ¹²`，
  与论文同样的分块（对角 `9ζ(2)`，非对角 `L2` 部分 `4ζ(2)`，`L3` 部分 `2`），
  只是 `∑ u_n⁴ = π²/8` 放宽为 `≤ ζ(2) = π²/6`。

记号：`l1 f := ∑'_{k≥0} |f(k+1)| = ∑_{k≥1} |f(k)|`，`L1 f := Summable (fun k => |f (k+1)|)`。
`f(0)` 从不出现在 (0.1) 中，故 `ℓ¹` 范数只算 `k ≥ 1`。
-/

namespace Eliashberg

open scoped BigOperators

/-! ### `u ≤ 1` -/

lemma u_le_one (n : ℕ) : u n ≤ 1 := by
  unfold u
  apply Real.rpow_le_one_of_one_le_of_nonpos
  · have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    linarith
  · norm_num

lemma u_sq_le_one (n : ℕ) : u n ^ 2 ≤ 1 := by
  have h := u_le_one n
  have h0 := le_of_lt (u_pos n)
  nlinarith

lemma u_mul_u_le_one (n m : ℕ) : u n * u m ≤ 1 := by
  have h1 := u_le_one n; have h2 := u_le_one m
  have h3 := le_of_lt (u_pos n); have h4 := le_of_lt (u_pos m)
  nlinarith

lemma u_pow_four_le (n : ℕ) : u n ^ 4 ≤ 1 / ((n:ℝ) + 1) ^ 2 := by
  have h : u n ^ 4 = (u n ^ 2) ^ 2 := by ring
  rw [h, u_sq]
  have hpos : (0:ℝ) < (n:ℝ) + 1 := by positivity
  rw [div_pow, one_pow]
  apply one_div_le_one_div_of_le (by positivity)
  have : (n:ℝ) + 1 ≤ 2 * (n:ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  nlinarith

/-- `ζ(2)` 的移位形式：`∑_{k≥0} 1/(k+1)² = π²/6`。 -/
lemma hasSum_zeta_two_shift : HasSum (fun k : ℕ => 1 / ((k:ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
  have h := hasSum_zeta_two
  have h' := (hasSum_nat_add_iff' 1).mpr h
  simp only [Finset.sum_range_one, Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, div_zero, sub_zero] at h'
  convert h' using 2
  push_cast; ring

/-- `∑_{n<K} u_n⁴ ≤ ζ(2) = π²/6`。 -/
lemma sum_u_pow_four_le (K : ℕ) : ∑ n ∈ Finset.range K, u n ^ 4 ≤ Real.pi ^ 2 / 6 := by
  calc ∑ n ∈ Finset.range K, u n ^ 4 ≤ ∑ n ∈ Finset.range K, 1 / ((n:ℝ) + 1) ^ 2 :=
        Finset.sum_le_sum (fun n _ => u_pow_four_le n)
    _ ≤ Real.pi ^ 2 / 6 :=
        hasSum_zeta_two_shift.summable.sum_le_tsum _ (fun n _ => by positivity)
          |>.trans_eq hasSum_zeta_two_shift.tsum_eq

/-! ### `ℓ¹` 范数 -/

/-- `‖f‖_{ℓ¹} := ∑_{k≥1} |f(k)|`。 -/
noncomputable def l1 (f : ℕ → ℝ) : ℝ := ∑' k, |f (k+1)|

/-- `f ∈ ℓ¹(ℕ_{≥1})`。 -/
def L1 (f : ℕ → ℝ) : Prop := Summable (fun k => |f (k+1)|)

lemma l1_nonneg (f : ℕ → ℝ) : 0 ≤ l1 f := tsum_nonneg (fun k => abs_nonneg _)

lemma abs_le_l1 {f : ℕ → ℝ} (hf : L1 f) (k : ℕ) (hk : 1 ≤ k) : |f k| ≤ l1 f := by
  have := hf.le_tsum (k - 1) (fun j _ => abs_nonneg _)
  have e : k - 1 + 1 = k := by omega
  rw [e] at this
  exact this

/-- `∑_{k=1}^n |f(k)| ≤ ‖f‖_ℓ¹`。 -/
lemma sum_Icc_abs_le_l1 {f : ℕ → ℝ} (hf : L1 f) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, |f k| ≤ l1 f := by
  have e : Finset.Icc 1 n = Finset.Ico 1 (n+1) := rfl
  rw [e, Finset.sum_Ico_eq_sum_range]
  have : ∀ i, |f (1 + i)| = |f (i + 1)| := fun i => by rw [add_comm]
  simp only [this]
  exact hf.sum_le_tsum _ (fun i _ => abs_nonneg _)

/-- `∑_{m<M} |f(n+m+1)| ≤ ‖f‖_ℓ¹`。 -/
lemma sum_shift_abs_le_l1 {f : ℕ → ℝ} (hf : L1 f) (n M : ℕ) :
    ∑ m ∈ Finset.range M, |f (n + m + 1)| ≤ l1 f := by
  have e : ∑ m ∈ Finset.range M, |f (n + m + 1)| = ∑ i ∈ Finset.Ico n (n + M), |f (i + 1)| := by
    rw [Finset.sum_Ico_eq_sum_range]
    have : n + M - n = M := by omega
    rw [this]
  rw [e]
  exact hf.sum_le_tsum _ (fun i _ => abs_nonneg _)

/-- `∑_{m<n} |f(n−m)| ≤ ‖f‖_ℓ¹`。 -/
lemma sum_lt_abs_le_l1 {f : ℕ → ℝ} (hf : L1 f) (n : ℕ) :
    ∑ m ∈ Finset.range n, |f (n - m)| ≤ l1 f := by
  have e : ∑ m ∈ Finset.range n, |f (n - m)| = ∑ j ∈ Finset.range n, |f (j + 1)| := by
    rw [← Finset.sum_range_reflect (fun j => |f (j + 1)|) n]
    apply Finset.sum_congr rfl; intro m hm
    rw [Finset.mem_range] at hm
    congr 2; omega
  rw [e]
  exact hf.sum_le_tsum _ (fun i _ => abs_nonneg _)

/-- `∑_{m<M, m>n} |f(m−n)| ≤ ‖f‖_ℓ¹`。 -/
lemma sum_gt_abs_le_l1 {f : ℕ → ℝ} (hf : L1 f) (n M : ℕ) :
    ∑ m ∈ Finset.Ico (n+1) M, |f (m - n)| ≤ l1 f := by
  rw [Finset.sum_Ico_eq_sum_range]
  have : ∀ i, |f (n + 1 + i - n)| = |f (i + 1)| := fun i => by congr 2; omega
  simp only [this]
  exact hf.sum_le_tsum _ (fun i _ => abs_nonneg _)

/-- `∑_{m<M, m≠n} |f(|n−m|)| ≤ 2‖f‖_ℓ¹`：`|n−m| = k` 至多两个 `m`。 -/
lemma sum_dist_abs_le_l1 {f : ℕ → ℝ} (hf : L1 f) (n M : ℕ) :
    ∑ m ∈ Finset.range M, (if n ≠ m then |f (Nat.dist n m)| else 0) ≤ 2 * l1 f := by
  have hsplit : ∀ m, (if n ≠ m then |f (Nat.dist n m)| else 0)
      = (if m < n then |f (n - m)| else 0) + (if n < m then |f (m - n)| else 0) := by
    intro m
    rcases lt_trichotomy m n with h | h | h
    · have h1 : n ≠ m := by omega
      have h2 : ¬ n < m := by omega
      have hd : Nat.dist n m = n - m := Nat.dist_eq_sub_of_le_right (le_of_lt h)
      rw [hd]
      simp only [h1, h, h2, ne_eq, not_false_eq_true, ite_true, ite_false, add_zero]
    · subst h; simp
    · have h1 : n ≠ m := by omega
      have h2 : ¬ m < n := by omega
      have hd : Nat.dist n m = m - n := Nat.dist_eq_sub_of_le (le_of_lt h)
      rw [hd]
      simp only [h1, h, h2, ne_eq, not_false_eq_true, ite_true, ite_false, zero_add]
  simp only [hsplit, Finset.sum_add_distrib]
  have h1 : ∑ m ∈ Finset.range M, (if m < n then |f (n - m)| else 0) ≤ l1 f := by
    rw [← Finset.sum_filter]
    calc ∑ m ∈ (Finset.range M).filter (fun m => m < n), |f (n - m)|
        ≤ ∑ m ∈ Finset.range n, |f (n - m)| := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro m hm; simp only [Finset.mem_filter, Finset.mem_range] at hm ⊢; exact hm.2
          · intro m _ _; exact abs_nonneg _
      _ ≤ l1 f := sum_lt_abs_le_l1 hf n
  have h2 : ∑ m ∈ Finset.range M, (if n < m then |f (m - n)| else 0) ≤ l1 f := by
    rw [← Finset.sum_filter]
    have e : (Finset.range M).filter (fun m => n < m) = Finset.Ico (n+1) M := by
      ext m; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
    rw [e]
    exact sum_gt_abs_le_l1 hf n M
  linarith

/-! ### 行和界 -/

/-- 矩阵元的逐项界：`|O[f]_{nm}| ≤ 2·1_{n=m} ∑_{k≤n}|f(k)| + 1_{n≠m}|f(|n−m|)| + |f(n+m+1)|`。 -/
lemma abs_Of_le (f : ℕ → ℝ) (n m : ℕ) :
    |Of f n m| ≤ (if n = m then 2 * ∑ k ∈ Finset.Icc 1 n, |f k| else 0)
      + (if n ≠ m then |f (Nat.dist n m)| else 0) + |f (n + m + 1)| := by
  unfold Of
  refine (abs_add_three _ _ _).trans ?_
  have hu := u_mul_u_le_one n m
  have hu0 : 0 ≤ u n * u m := mul_nonneg (le_of_lt (u_pos n)) (le_of_lt (u_pos m))
  have hsq := u_sq_le_one n
  have hsq0 : 0 ≤ u n ^ 2 := sq_nonneg _
  apply add_le_add (add_le_add _ _) _
  · split_ifs
    · rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg hsq0, abs_two]
      have := Finset.abs_sum_le_sum_abs (fun k => f k) (Finset.Icc 1 n)
      have hS0 : 0 ≤ ∑ k ∈ Finset.Icc 1 n, |f k| := Finset.sum_nonneg (fun k _ => abs_nonneg _)
      calc 2 * u n ^ 2 * |∑ k ∈ Finset.Icc 1 n, f k|
          ≤ 2 * 1 * ∑ k ∈ Finset.Icc 1 n, |f k| := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left hsq (by norm_num)) this (abs_nonneg _)
              (by norm_num)
        _ = 2 * ∑ k ∈ Finset.Icc 1 n, |f k| := by ring
    · simp
  · split_ifs
    · rw [abs_mul, abs_of_nonneg hu0]
      exact mul_le_of_le_one_right (abs_nonneg _) hu
    · simp
  · rw [abs_mul, abs_of_nonneg hu0]
    exact mul_le_of_le_one_right (abs_nonneg _) hu

/-- **行和界**：`∑_{m<M} |O[f]_{nm}| ≤ 5 ‖f‖_ℓ¹`。 -/
lemma row_abs_sum_le {f : ℕ → ℝ} (hf : L1 f) (n M : ℕ) :
    ∑ m ∈ Finset.range M, |Of f n m| ≤ 5 * l1 f := by
  calc ∑ m ∈ Finset.range M, |Of f n m|
      ≤ ∑ m ∈ Finset.range M, ((if n = m then 2 * ∑ k ∈ Finset.Icc 1 n, |f k| else 0)
          + (if n ≠ m then |f (Nat.dist n m)| else 0) + |f (n + m + 1)|) :=
        Finset.sum_le_sum (fun m _ => abs_Of_le f n m)
    _ = (∑ m ∈ Finset.range M, (if n = m then 2 * ∑ k ∈ Finset.Icc 1 n, |f k| else 0))
        + (∑ m ∈ Finset.range M, (if n ≠ m then |f (Nat.dist n m)| else 0))
        + ∑ m ∈ Finset.range M, |f (n + m + 1)| := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ 2 * l1 f + 2 * l1 f + l1 f := by
        apply add_le_add (add_le_add _ (sum_dist_abs_le_l1 hf n M)) (sum_shift_abs_le_l1 hf n M)
        rw [Finset.sum_ite_eq]
        split_ifs
        · linarith [sum_Icc_abs_le_l1 hf n]
        · linarith [l1_nonneg f]
    _ = 5 * l1 f := by ring

/-! ### Rayleigh 界（Schur 检验） -/

/-- 一般的 Schur 检验：对称矩阵 `M`（在 `[0,N)²` 上）、行和 `≤ C` ⇒ `|∑ v_n M_{nm} v_m| ≤ C ∑ v_n²`。 -/
lemma schur_bound (M : ℕ → ℕ → ℝ) (hsymm : ∀ n m, M n m = M m n) (C : ℝ) (N : ℕ)
    (hrow : ∀ n, ∑ m ∈ Finset.range N, |M n m| ≤ C) (v : ℕ → ℝ) :
    |∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, v n * M n m * v m|
      ≤ C * ∑ n ∈ Finset.range N, v n ^ 2 := by
  -- `|v_n M v_m| ≤ |M|(v_n² + v_m²)/2`
  have hterm : ∀ n m, |v n * M n m * v m| ≤ |M n m| * ((v n ^ 2 + v m ^ 2) / 2) := by
    intro n m
    rw [abs_mul, abs_mul, mul_comm |v n| |M n m|, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have := two_mul_le_add_sq |v n| |v m|
    rw [sq_abs, sq_abs] at this
    linarith
  calc |∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, v n * M n m * v m|
      ≤ ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, |v n * M n m * v m| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        exact Finset.sum_le_sum (fun n _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, |M n m| * ((v n ^ 2 + v m ^ 2) / 2) :=
        Finset.sum_le_sum (fun n _ => Finset.sum_le_sum (fun m _ => hterm n m))
    _ = (∑ n ∈ Finset.range N, v n ^ 2 * ∑ m ∈ Finset.range N, |M n m|) / 2
        + (∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, |M n m| * v m ^ 2) / 2 := by
        rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro n _
        rw [Finset.mul_sum, Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro m _
        ring
    _ = (∑ n ∈ Finset.range N, v n ^ 2 * ∑ m ∈ Finset.range N, |M n m|) / 2
        + (∑ m ∈ Finset.range N, v m ^ 2 * ∑ n ∈ Finset.range N, |M m n|) / 2 := by
        congr 1
        rw [Finset.sum_comm]
        congr 1
        apply Finset.sum_congr rfl; intro m _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro n _
        rw [hsymm n m]; ring
    _ ≤ (∑ n ∈ Finset.range N, v n ^ 2 * C) / 2 + (∑ m ∈ Finset.range N, v m ^ 2 * C) / 2 := by
        apply add_le_add
        · apply div_le_div_of_nonneg_right _ (by norm_num)
          exact Finset.sum_le_sum (fun n _ => mul_le_mul_of_nonneg_left (hrow n) (sq_nonneg _))
        · apply div_le_div_of_nonneg_right _ (by norm_num)
          exact Finset.sum_le_sum (fun m _ => mul_le_mul_of_nonneg_left (hrow m) (sq_nonneg _))
    _ = C * ∑ n ∈ Finset.range N, v n ^ 2 := by
        rw [← Finset.sum_mul]; ring

/-- **Rayleigh 界**（Lemma 0.2.1 的 `‖O[f]‖ ≤ 5‖f‖_ℓ¹`）：
`|⟨P_N v, O[f] P_N v⟩| ≤ 5 ‖f‖_ℓ¹ ‖P_N v‖²`。 -/
lemma Of_symm' (f : ℕ → ℝ) (n m : ℕ) : Of f n m = Of f m n := by
  unfold Of
  rw [Nat.dist_comm]
  by_cases h : n = m
  · subst h; rfl
  · have h' : m ≠ n := Ne.symm h
    simp only [h, h', ite_false, ne_eq, not_false_eq_true, ite_true, zero_add]
    rw [show n + m + 1 = m + n + 1 by ring, mul_comm (u n) (u m)]

theorem rayleigh_abs_le {f : ℕ → ℝ} (hf : L1 f) (v : ℕ → ℝ) (N : ℕ) :
    |quadForm f v N| ≤ 5 * l1 f * ∑ n ∈ Finset.range N, v n ^ 2 := by
  unfold quadForm
  exact schur_bound (Of f) (Of_symm' f) (5 * l1 f) N (fun n => row_abs_sum_le hf n N) v

/-! ### Hilbert–Schmidt 界 -/

/-- `∑_{k≥1} f(k)² ≤ ‖f‖_ℓ¹²`（`|f(k)| ≤ ‖f‖_ℓ¹`）。 -/
lemma sum_sq_le_l1_sq {f : ℕ → ℝ} (hf : L1 f) (s : Finset ℕ) (hs : ∀ k ∈ s, 1 ≤ k) :
    ∑ k ∈ s, f k ^ 2 ≤ l1 f ^ 2 := by
  -- `∑_{k∈s} f(k)² ≤ ‖f‖₁ ∑_{k∈s} |f(k)| ≤ ‖f‖₁ · ‖f‖₁`
  have h1 : ∀ k ∈ s, f k ^ 2 ≤ l1 f * |f k| := by
    intro k hk
    rw [← sq_abs]
    have := abs_le_l1 hf k (hs k hk)
    nlinarith [abs_nonneg (f k)]
  have h2 : ∑ k ∈ s, |f k| ≤ l1 f := by
    -- 平移到 `k+1` 索引
    have e : ∑ k ∈ s, |f k| = ∑ j ∈ s.image (fun k => k - 1), |f (j + 1)| := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl; intro k hk
        have := hs k hk
        congr 2; omega
      · intro a ha b hb hab
        have := hs a ha; have := hs b hb
        simp only at hab; omega
    rw [e]
    exact hf.sum_le_tsum _ (fun i _ => abs_nonneg _)
  calc ∑ k ∈ s, f k ^ 2 ≤ ∑ k ∈ s, l1 f * |f k| := Finset.sum_le_sum h1
    _ = l1 f * ∑ k ∈ s, |f k| := by rw [Finset.mul_sum]
    _ ≤ l1 f * l1 f := mul_le_mul_of_nonneg_left h2 (l1_nonneg f)
    _ = l1 f ^ 2 := by ring

/-- 对角元：`|O[f]_{nn}| ≤ 3 ‖f‖_ℓ¹ u_n²`。 -/
lemma abs_Of_diag_le {f : ℕ → ℝ} (hf : L1 f) (n : ℕ) : |Of f n n| ≤ 3 * l1 f * u n ^ 2 := by
  unfold Of
  simp only [ite_true, ne_eq, not_true_eq_false, ite_false, add_zero]
  refine (abs_add_le _ _).trans ?_
  have hsq0 : 0 ≤ u n ^ 2 := sq_nonneg _
  have hS := Finset.abs_sum_le_sum_abs (fun k => f k) (Finset.Icc 1 n)
  have hS1 := sum_Icc_abs_le_l1 hf n
  have h3 := abs_le_l1 hf (n + n + 1) (by omega)
  rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg hsq0, abs_two, abs_mul, abs_of_nonneg
    (mul_nonneg (le_of_lt (u_pos n)) (le_of_lt (u_pos n)))]
  have e : u n * u n = u n ^ 2 := by ring
  rw [e]
  nlinarith [abs_nonneg (∑ k ∈ Finset.Icc 1 n, f k), abs_nonneg (f (n + n + 1))]

/-- 非对角元：`n ≠ m` 时 `O[f]_{nm}² ≤ 2(f(|n−m|)² + f(n+m+1)²) u_n² u_m²`。 -/
lemma sq_Of_offdiag_le (f : ℕ → ℝ) (n m : ℕ) (h : n ≠ m) :
    Of f n m ^ 2 ≤ 2 * (f (Nat.dist n m) ^ 2 + f (n + m + 1) ^ 2) * (u n ^ 2 * u m ^ 2) := by
  unfold Of
  simp only [h, ite_false, ne_eq, not_false_eq_true, ite_true, zero_add]
  have e : (f (Nat.dist n m) * (u n * u m) + f (n + m + 1) * (u n * u m)) ^ 2
      = (f (Nat.dist n m) + f (n + m + 1)) ^ 2 * (u n ^ 2 * u m ^ 2) := by ring
  rw [e]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  nlinarith [sq_nonneg (f (Nat.dist n m) - f (n + m + 1))]

/-- `L2` 块的 HS 和：`∑_{n<K}∑_{m<K, m≠n} f(|n−m|)² u_n² u_m² ≤ 2 ζ(2) ‖f‖_ℓ¹²`。 -/
lemma hs_L2_le {f : ℕ → ℝ} (hf : L1 f) (K : ℕ) :
    ∑ n ∈ Finset.range K, ∑ m ∈ Finset.range K,
      (if n ≠ m then f (Nat.dist n m) ^ 2 * (u n ^ 2 * u m ^ 2) else 0)
      ≤ 2 * (Real.pi ^ 2 / 6) * l1 f ^ 2 := by
  -- `u_n² u_m² ≤ (u_n⁴ + u_m⁴)/2`，再用对称性把 `u_m⁴` 项换成 `u_n⁴` 项
  have hterm : ∀ n m, (if n ≠ m then f (Nat.dist n m) ^ 2 * (u n ^ 2 * u m ^ 2) else 0)
      ≤ (if n ≠ m then f (Nat.dist n m) ^ 2 * (u n ^ 4 / 2) else 0)
        + (if n ≠ m then f (Nat.dist n m) ^ 2 * (u m ^ 4 / 2) else 0) := by
    intro n m
    split_ifs
    · have := two_mul_le_add_sq (u n ^ 2) (u m ^ 2)
      have e1 : (u n ^ 2) ^ 2 = u n ^ 4 := by ring
      have e2 : (u m ^ 2) ^ 2 = u m ^ 4 := by ring
      rw [e1, e2] at this
      nlinarith [sq_nonneg (f (Nat.dist n m))]
    · simp
  -- `g` 是 `L1`-可和的：`f(k)²` 的有限和 `≤ ‖f‖₁²`
  have hrow : ∀ n, ∑ m ∈ Finset.range K, (if n ≠ m then f (Nat.dist n m) ^ 2 else 0)
      ≤ 2 * l1 f ^ 2 := by
    intro n
    -- 与 `sum_dist_abs_le_l1` 同样的拆分，用 `f(k)² ≤ ‖f‖₁ |f(k)|`
    have hsplit : ∀ m, (if n ≠ m then f (Nat.dist n m) ^ 2 else 0)
        = (if m < n then f (n - m) ^ 2 else 0) + (if n < m then f (m - n) ^ 2 else 0) := by
      intro m
      rcases lt_trichotomy m n with h | h | h
      · have h1 : n ≠ m := by omega
        have h2 : ¬ n < m := by omega
        have hd : Nat.dist n m = n - m := Nat.dist_eq_sub_of_le_right (le_of_lt h)
        rw [hd]
        simp only [h1, h, h2, ne_eq, not_false_eq_true, ite_true, ite_false, add_zero]
      · subst h; simp
      · have h1 : n ≠ m := by omega
        have h2 : ¬ m < n := by omega
        have hd : Nat.dist n m = m - n := Nat.dist_eq_sub_of_le (le_of_lt h)
        rw [hd]
        simp only [h1, h, h2, ne_eq, not_false_eq_true, ite_true, ite_false, zero_add]
    simp only [hsplit, Finset.sum_add_distrib]
    have h1 : ∑ m ∈ Finset.range K, (if m < n then f (n - m) ^ 2 else 0) ≤ l1 f ^ 2 := by
      rw [← Finset.sum_filter]
      calc ∑ m ∈ (Finset.range K).filter (fun m => m < n), f (n - m) ^ 2
          ≤ ∑ m ∈ Finset.range n, f (n - m) ^ 2 := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro m hm; simp only [Finset.mem_filter, Finset.mem_range] at hm ⊢; exact hm.2
            · intro m _ _; exact sq_nonneg _
        _ = ∑ k ∈ Finset.Icc 1 n, f k ^ 2 := by
            have e : Finset.Icc 1 n = Finset.Ico 1 (n+1) := rfl
            rw [e, Finset.sum_Ico_eq_sum_range]
            have : n + 1 - 1 = n := by omega
            rw [this, ← Finset.sum_range_reflect (fun j => f (1 + j) ^ 2) n]
            apply Finset.sum_congr rfl; intro m hm
            rw [Finset.mem_range] at hm
            congr 2; omega
        _ ≤ l1 f ^ 2 := sum_sq_le_l1_sq hf _ (fun k hk => (Finset.mem_Icc.mp hk).1)
    have h2 : ∑ m ∈ Finset.range K, (if n < m then f (m - n) ^ 2 else 0) ≤ l1 f ^ 2 := by
      rw [← Finset.sum_filter]
      have e : (Finset.range K).filter (fun m => n < m) = Finset.Ico (n+1) K := by
        ext m; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
      rw [e]
      calc ∑ m ∈ Finset.Ico (n+1) K, f (m - n) ^ 2
          = ∑ k ∈ (Finset.Ico (n+1) K).image (fun m => m - n), f k ^ 2 := by
            rw [Finset.sum_image]
            intro a ha b hb hab
            simp only [Finset.coe_Ico, Set.mem_Ico] at ha hb
            have hab' : a - n = b - n := hab
            omega
        _ ≤ l1 f ^ 2 := by
            apply sum_sq_le_l1_sq hf
            intro k hk
            rw [Finset.mem_image] at hk
            obtain ⟨m, hm, rfl⟩ := hk
            simp only [Finset.mem_Ico] at hm; omega
    linarith
  calc ∑ n ∈ Finset.range K, ∑ m ∈ Finset.range K,
        (if n ≠ m then f (Nat.dist n m) ^ 2 * (u n ^ 2 * u m ^ 2) else 0)
      ≤ ∑ n ∈ Finset.range K, ∑ m ∈ Finset.range K,
        ((if n ≠ m then f (Nat.dist n m) ^ 2 * (u n ^ 4 / 2) else 0)
          + (if n ≠ m then f (Nat.dist n m) ^ 2 * (u m ^ 4 / 2) else 0)) :=
        Finset.sum_le_sum (fun n _ => Finset.sum_le_sum (fun m _ => hterm n m))
    _ = 2 * ∑ n ∈ Finset.range K, ∑ m ∈ Finset.range K,
        (if n ≠ m then f (Nat.dist n m) ^ 2 * (u n ^ 4 / 2) else 0) := by
        simp only [Finset.sum_add_distrib]
        rw [two_mul]
        congr 1
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro n _
        apply Finset.sum_congr rfl; intro m _
        rw [Nat.dist_comm]
        by_cases h : n = m
        · subst h; rfl
        · have h' : m ≠ n := Ne.symm h
          simp only [h, h', ne_eq, not_false_eq_true, ite_true]
    _ = ∑ n ∈ Finset.range K, u n ^ 4 * ∑ m ∈ Finset.range K,
        (if n ≠ m then f (Nat.dist n m) ^ 2 else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro n _
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro m _
        split_ifs <;> ring
    _ ≤ ∑ n ∈ Finset.range K, u n ^ 4 * (2 * l1 f ^ 2) :=
        Finset.sum_le_sum (fun n _ => mul_le_mul_of_nonneg_left (hrow n) (by positivity))
    _ = (∑ n ∈ Finset.range K, u n ^ 4) * (2 * l1 f ^ 2) := by rw [Finset.sum_mul]
    _ ≤ (Real.pi ^ 2 / 6) * (2 * l1 f ^ 2) :=
        mul_le_mul_of_nonneg_right (sum_u_pow_four_le K) (by positivity)
    _ = 2 * (Real.pi ^ 2 / 6) * l1 f ^ 2 := by ring

/-- `u_n² u_m² ≤ 1/(n+m+1)`：因 `(2n+1)(2m+1) ≥ 2n+2m+1 ≥ n+m+1`。 -/
lemma u_sq_mul_u_sq_le (n m : ℕ) : u n ^ 2 * u m ^ 2 ≤ 1 / ((n:ℝ) + m + 1) := by
  rw [u_sq, u_sq, div_mul_div_comm, one_mul]
  have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have hm : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

/-- `L3` 块的 HS 和：`∑_{n<K}∑_{m<K} f(n+m+1)² u_n² u_m² ≤ ‖f‖_ℓ¹²`。
每个 `j = n+m+1` 至多 `j` 对 `(n,m)`，每对 `≤ f(j)²/j`。 -/
lemma hs_L3_le {f : ℕ → ℝ} (hf : L1 f) (K : ℕ) :
    ∑ n ∈ Finset.range K, ∑ m ∈ Finset.range K, f (n + m + 1) ^ 2 * (u n ^ 2 * u m ^ 2)
      ≤ l1 f ^ 2 := by
  -- 按 `j = n+m+1` 分组：插入指示 `∑_{j<2K} [n+m+1=j]`
  have hidx : ∀ n ∈ Finset.range K, ∀ m ∈ Finset.range K,
      f (n + m + 1) ^ 2 * (u n ^ 2 * u m ^ 2)
        = ∑ j ∈ Finset.range (2 * K), if n + m + 1 = j then f j ^ 2 * (u n ^ 2 * u m ^ 2) else 0 := by
    intro n hn m hm
    rw [Finset.mem_range] at hn hm
    rw [Finset.sum_ite_eq]
    rw [ite_eq_left (Finset.mem_range.mpr (by omega))]
  calc ∑ n ∈ Finset.range K, ∑ m ∈ Finset.range K, f (n + m + 1) ^ 2 * (u n ^ 2 * u m ^ 2)
      = ∑ n ∈ Finset.range K, ∑ m ∈ Finset.range K, ∑ j ∈ Finset.range (2 * K),
          (if n + m + 1 = j then f j ^ 2 * (u n ^ 2 * u m ^ 2) else 0) :=
        Finset.sum_congr rfl (fun n hn => Finset.sum_congr rfl (fun m hm => hidx n hn m hm))
    _ = ∑ j ∈ Finset.range (2 * K), ∑ n ∈ Finset.range K, ∑ m ∈ Finset.range K,
          (if n + m + 1 = j then f j ^ 2 * (u n ^ 2 * u m ^ 2) else 0) := by
        rw [sum3_comm]
    _ ≤ ∑ j ∈ Finset.range (2 * K), ∑ n ∈ Finset.range K, ∑ m ∈ Finset.range K,
          (if n + m + 1 = j then f j ^ 2 * (1 / (j:ℝ)) else 0) := by
        apply Finset.sum_le_sum; intro j _
        apply Finset.sum_le_sum; intro n _
        apply Finset.sum_le_sum; intro m _
        split_ifs with h
        · apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          have := u_sq_mul_u_sq_le n m
          have e : ((n:ℝ) + m + 1) = (j:ℝ) := by rw [← h]; push_cast; ring
          rw [e] at this; exact this
        · exact le_refl _
    _ = ∑ j ∈ Finset.range (2 * K), f j ^ 2 * (1 / (j:ℝ))
          * ∑ n ∈ Finset.range K, ∑ m ∈ Finset.range K, (if n + m + 1 = j then (1:ℝ) else 0) := by
        apply Finset.sum_congr rfl; intro j _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro n _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro m _
        split_ifs <;> simp
    _ ≤ ∑ j ∈ Finset.range (2 * K), f j ^ 2 * (1 / (j:ℝ)) * (j:ℝ) := by
        apply Finset.sum_le_sum; intro j _
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        -- 每个 `n` 至多一个 `m`，且需要 `n < j`
        calc ∑ n ∈ Finset.range K, ∑ m ∈ Finset.range K, (if n + m + 1 = j then (1:ℝ) else 0)
            ≤ ∑ n ∈ Finset.range K, (if n < j then (1:ℝ) else 0) := by
              apply Finset.sum_le_sum; intro n _
              by_cases hn : n < j
              · rw [ite_eq_left hn]
                have hiff : ∀ m, (n + m + 1 = j) ↔ (m = j - 1 - n) := by
                  intro m; constructor <;> intro h <;> omega
                simp only [hiff]
                rw [Finset.sum_ite_eq']
                split_ifs <;> norm_num
              · rw [ite_eq_right hn]
                apply le_of_eq
                apply Finset.sum_eq_zero; intro m _
                rw [ite_eq_right]; omega
          _ ≤ (j:ℝ) := by
              rw [Finset.sum_boole]
              have : ((Finset.range K).filter (fun n => n < j)).card ≤ j := by
                calc ((Finset.range K).filter (fun n => n < j)).card
                    ≤ (Finset.range j).card := by
                      apply Finset.card_le_card
                      intro n hn; simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢; exact hn.2
                  _ = j := Finset.card_range j
              exact_mod_cast this
    _ ≤ ∑ j ∈ (Finset.range (2 * K)).filter (fun j => 1 ≤ j), f j ^ 2 := by
        rw [Finset.sum_filter]
        apply Finset.sum_le_sum; intro j _
        by_cases hj : 1 ≤ j
        · rw [ite_eq_left hj]
          have : (j:ℝ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
          apply le_of_eq
          field_simp
        · rw [ite_eq_right hj]
          have : j = 0 := by omega
          subst this; simp
    _ ≤ l1 f ^ 2 := sum_sq_le_l1_sq hf _ (fun j hj => (Finset.mem_filter.mp hj).2)

/-- HS 平方和的有限框：`hs f K := ∑_{n<K}∑_{m<K} O[f]_{nm}²`。 -/
noncomputable def hs (f : ℕ → ℝ) (K : ℕ) : ℝ :=
  ∑ n ∈ Finset.range K, ∑ m ∈ Finset.range K, Of f n m ^ 2

/-- **HS 界**（Lemma 0.2.1）：`hs f K ≤ (13π²/6 + 2) ‖f‖_ℓ¹²`，对一切 `K`。
论文的常数是 `25`；这里 `13π²/6 + 2 < 25`。 -/
theorem hs_le {f : ℕ → ℝ} (hf : L1 f) (K : ℕ) :
    hs f K ≤ (13 * (Real.pi ^ 2 / 6) + 2) * l1 f ^ 2 := by
  unfold hs
  -- 拆成对角与非对角
  have hsplit : ∀ n m, Of f n m ^ 2
      = (if n = m then Of f n n ^ 2 else 0) + (if n ≠ m then Of f n m ^ 2 else 0) := by
    intro n m
    by_cases h : n = m
    · subst h; simp
    · simp [h]
  rw [Finset.sum_congr rfl (fun n _ => Finset.sum_congr rfl (fun m _ => hsplit n m))]
  simp only [Finset.sum_add_distrib]
  -- 对角
  have hdiag : ∑ n ∈ Finset.range K, ∑ m ∈ Finset.range K, (if n = m then Of f n n ^ 2 else 0)
      ≤ 9 * (Real.pi ^ 2 / 6) * l1 f ^ 2 := by
    calc ∑ n ∈ Finset.range K, ∑ m ∈ Finset.range K, (if n = m then Of f n n ^ 2 else 0)
        = ∑ n ∈ Finset.range K, (if n < K then Of f n n ^ 2 else 0) := by
          apply Finset.sum_congr rfl; intro n _
          rw [Finset.sum_ite_eq]; simp only [Finset.mem_range]
      _ = ∑ n ∈ Finset.range K, Of f n n ^ 2 := by
          apply Finset.sum_congr rfl; intro n hn
          rw [Finset.mem_range] at hn; rw [ite_eq_left hn]
      _ ≤ ∑ n ∈ Finset.range K, (3 * l1 f) ^ 2 * u n ^ 4 := by
          apply Finset.sum_le_sum; intro n _
          have h := abs_Of_diag_le hf n
          have h0 : 0 ≤ 3 * l1 f * u n ^ 2 := by
            have := l1_nonneg f; positivity
          calc Of f n n ^ 2 = |Of f n n| ^ 2 := (sq_abs _).symm
            _ ≤ (3 * l1 f * u n ^ 2) ^ 2 := by
                exact pow_le_pow_left₀ (abs_nonneg _) h 2
            _ = (3 * l1 f) ^ 2 * u n ^ 4 := by ring
      _ = (3 * l1 f) ^ 2 * ∑ n ∈ Finset.range K, u n ^ 4 := by rw [Finset.mul_sum]
      _ ≤ (3 * l1 f) ^ 2 * (Real.pi ^ 2 / 6) :=
          mul_le_mul_of_nonneg_left (sum_u_pow_four_le K) (by positivity)
      _ = 9 * (Real.pi ^ 2 / 6) * l1 f ^ 2 := by ring
  -- 非对角
  have hoff : ∑ n ∈ Finset.range K, ∑ m ∈ Finset.range K, (if n ≠ m then Of f n m ^ 2 else 0)
      ≤ (4 * (Real.pi ^ 2 / 6) + 2) * l1 f ^ 2 := by
    calc ∑ n ∈ Finset.range K, ∑ m ∈ Finset.range K, (if n ≠ m then Of f n m ^ 2 else 0)
        ≤ ∑ n ∈ Finset.range K, ∑ m ∈ Finset.range K,
            ((if n ≠ m then 2 * (f (Nat.dist n m) ^ 2 * (u n ^ 2 * u m ^ 2)) else 0)
             + 2 * (f (n + m + 1) ^ 2 * (u n ^ 2 * u m ^ 2))) := by
          apply Finset.sum_le_sum; intro n _
          apply Finset.sum_le_sum; intro m _
          split_ifs with h
          · have := sq_Of_offdiag_le f n m h
            linarith
          · positivity
      _ = 2 * (∑ n ∈ Finset.range K, ∑ m ∈ Finset.range K,
            (if n ≠ m then f (Nat.dist n m) ^ 2 * (u n ^ 2 * u m ^ 2) else 0))
          + 2 * ∑ n ∈ Finset.range K, ∑ m ∈ Finset.range K,
            f (n + m + 1) ^ 2 * (u n ^ 2 * u m ^ 2) := by
          simp only [Finset.sum_add_distrib, Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl; intro n _
          apply Finset.sum_congr rfl; intro m _
          split_ifs <;> simp
      _ ≤ 2 * (2 * (Real.pi ^ 2 / 6) * l1 f ^ 2) + 2 * l1 f ^ 2 := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left (hs_L2_le hf K) (by norm_num)
          · exact mul_le_mul_of_nonneg_left (hs_L3_le hf K) (by norm_num)
      _ = (4 * (Real.pi ^ 2 / 6) + 2) * l1 f ^ 2 := by ring
  linarith

/-- `13π²/6 + 2 ≤ 25`（`π² < 10`）。 -/
lemma hs_const_le : 13 * (Real.pi ^ 2 / 6) + 2 ≤ 25 := by
  have := Real.pi_lt_d2
  have h : Real.pi ^ 2 < 10 := by nlinarith [Real.pi_pos]
  linarith

theorem hs_le_25 {f : ℕ → ℝ} (hf : L1 f) (K : ℕ) : hs f K ≤ 25 * l1 f ^ 2 :=
  (hs_le hf K).trans (mul_le_mul_of_nonneg_right hs_const_le (sq_nonneg _))

lemma hs_mono (f : ℕ → ℝ) : Monotone (hs f) := by
  intro K K' hKK
  unfold hs
  have hsub : Finset.range K ⊆ Finset.range K' := Finset.range_subset_range.mpr hKK
  calc ∑ n ∈ Finset.range K, ∑ m ∈ Finset.range K, Of f n m ^ 2
      ≤ ∑ n ∈ Finset.range K, ∑ m ∈ Finset.range K', Of f n m ^ 2 := by
        apply Finset.sum_le_sum; intro n _
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => sq_nonneg _)
    _ ≤ ∑ n ∈ Finset.range K', ∑ m ∈ Finset.range K', Of f n m ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun n _ _ => Finset.sum_nonneg (fun m _ => sq_nonneg _))

lemma hs_nonneg (f : ℕ → ℝ) (K : ℕ) : 0 ≤ hs f K :=
  Finset.sum_nonneg (fun n _ => Finset.sum_nonneg (fun m _ => sq_nonneg _))

/-- `‖O[f]‖_HS² := sup_K hs f K`。 -/
noncomputable def hsSup (f : ℕ → ℝ) : ℝ := ⨆ K, hs f K

lemma hs_bddAbove {f : ℕ → ℝ} (hf : L1 f) : BddAbove (Set.range (hs f)) :=
  ⟨25 * l1 f ^ 2, by rintro _ ⟨K, rfl⟩; exact hs_le_25 hf K⟩

lemma hs_le_hsSup {f : ℕ → ℝ} (hf : L1 f) (K : ℕ) : hs f K ≤ hsSup f :=
  le_ciSup (hs_bddAbove hf) K

lemma hs_tendsto_hsSup {f : ℕ → ℝ} (hf : L1 f) :
    Filter.Tendsto (hs f) Filter.atTop (nhds (hsSup f)) :=
  tendsto_atTop_ciSup (hs_mono f) (hs_bddAbove hf)

/-- HS 尾部：`τ_M := ‖O[f]‖_HS² − hs f M → 0`。 -/
lemma hs_tail_tendsto_zero {f : ℕ → ℝ} (hf : L1 f) :
    Filter.Tendsto (fun M => hsSup f - hs f M) Filter.atTop (nhds 0) := by
  have := (hs_tendsto_hsSup hf).const_sub (hsSup f)
  rwa [sub_self] at this

/-- 尾部框的界：`∑_{M≤n<N}∑_{m<N} O_{nm}² ≤ hs f N − hs f M ≤ hsSup f − hs f M`。 -/
lemma hs_tail_box_le {f : ℕ → ℝ} (hf : L1 f) (M N : ℕ) (hMN : M ≤ N) :
    ∑ n ∈ Finset.Ico M N, ∑ m ∈ Finset.range N, Of f n m ^ 2 ≤ hsSup f - hs f M := by
  have h1 : ∑ n ∈ Finset.Ico M N, ∑ m ∈ Finset.range N, Of f n m ^ 2 = hs f N
      - ∑ n ∈ Finset.range M, ∑ m ∈ Finset.range N, Of f n m ^ 2 := by
    unfold hs
    rw [← Finset.sum_range_add_sum_Ico _ hMN]
    ring
  have h2 : hs f M ≤ ∑ n ∈ Finset.range M, ∑ m ∈ Finset.range N, Of f n m ^ 2 := by
    unfold hs
    apply Finset.sum_le_sum; intro n _
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hMN)
      (fun m _ _ => sq_nonneg _)
  have h3 := hs_le_hsSup hf N
  linarith

end Eliashberg
