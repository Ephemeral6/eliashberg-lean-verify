import Eliashberg.Spectral
import Eliashberg.AppendixEstimates
import Eliashberg.Lam1

/-!
# Appendix A.1–A.3 的有限截断部分：(A.1)、Hankel 正性（Lemma A.4）、`A ⪯ B`（Cor A.3）

论文 Appendix A 处理 `A := O[k ↦ k⁻²]`。记 `K(n,m) := 1/(n+m+1)² + [n≠m]/(n−m)²`，
`p_n := u_n v_n`，`H_n^{(2)} := ∑_{k=1}^n k⁻²`，`ψ'(n+1) := ζ(2) − H_n^{(2)}`。

* **(A.1)**（`quadForm_invSq_eq`）：`⟨P_N v, A P_N v⟩ = ∑_{n,m<N} p_n p_m K(n,m) − 2 ∑_{n<N} H_n^{(2)} p_n²`
* **Lemma A.4**（`hankel_nonneg`）：`∑_{n,m<N} a_n a_m/(n+m+1)² ≥ 0`。
  论文用 `1/(s+1)² = ∫_0^∞ t e^{-st} dt`；这里用等价的 `1/(k+1)² = ∫_0^1∫_0^1 (xy)^k dx dy`，
  于是二次型 `= ∫∫ (∑_n a_n (xy)^n)² ≥ 0`，只涉及 `[0,1]` 上多项式的积分。
* **Lemma A.2 / Cor A.3**（`quadForm_le_B`）：`⟨v, A v⟩ ≤ ⟨v, B v⟩`，
  `⟨v,Bv⟩ := ∑_{n,m} p_n p_m/(n+m+1)² + ∑_n ψ'(n+1) p_n²`。
  证明用 `2 p_n p_m ≤ p_n² + p_m²` 与 `c_n^{(N)} := ∑_{m<N,m≠n} 1/(n−m)² ≤ ζ(2) + H_n^{(2)}`；
  论文的 Dirichlet 形 `−½D[p]` 就是被丢掉的非正项。
-/

namespace Eliashberg

open scoped BigOperators Matrix
open Set Filter Topology

/-! ### (A.1)：`⟨v, O[k⁻²] v⟩` 的有理形式 -/

/-- `H_n^{(2)} := ∑_{k=1}^n k⁻²`。 -/
noncomputable def H2 (n : ℕ) : ℝ := ∑ k ∈ Finset.Icc 1 n, 1 / (k:ℝ) ^ 2

lemma H2_eq_range (n : ℕ) : H2 n = ∑ k ∈ Finset.range n, 1 / ((k:ℝ) + 1) ^ 2 := by
  unfold H2
  rw [show Finset.Icc 1 n = Finset.Ico 1 (n+1) from rfl, Finset.sum_Ico_eq_sum_range]
  have : n + 1 - 1 = n := by omega
  rw [this]
  apply Finset.sum_congr rfl; intro k _
  push_cast; ring_nf

lemma H2_nonneg (n : ℕ) : 0 ≤ H2 n := Finset.sum_nonneg (fun k _ => by positivity)

/-- `ψ'(n+1) = ζ(2) − H_n^{(2)}`。 -/
lemma psi'_eq (n : ℕ) : psi' n = zeta2 - H2 n := by
  rw [zeta2_split n, H2_eq_range]; unfold psi'; ring

/-- `K(n,m) := 1/(n+m+1)² + [n≠m]/(n−m)²`。 -/
noncomputable def KA (n m : ℕ) : ℝ :=
  1 / ((n:ℝ) + m + 1) ^ 2 + (if n ≠ m then 1 / ((n:ℝ) - m) ^ 2 else 0)

lemma KA_symm (n m : ℕ) : KA n m = KA m n := by
  unfold KA
  by_cases h : n = m
  · subst h; rfl
  · have h' : m ≠ n := Ne.symm h
    simp only [h, h', ne_eq, not_false_eq_true, ite_true]
    have e1 : ((n:ℝ) + m + 1) = ((m:ℝ) + n + 1) := by ring
    have e2 : ((n:ℝ) - m) ^ 2 = ((m:ℝ) - n) ^ 2 := by ring
    rw [e1, e2]

lemma KA_nonneg (n m : ℕ) : 0 ≤ KA n m := by
  unfold KA
  apply add_nonneg (by positivity)
  split_ifs <;> positivity

lemma dist_sq_real (n m : ℕ) : ((Nat.dist n m : ℕ) : ℝ) ^ 2 = ((n:ℝ) - m) ^ 2 := by
  rcases le_total n m with h | h
  · rw [Nat.dist_eq_sub_of_le h, Nat.cast_sub h]; ring
  · rw [Nat.dist_eq_sub_of_le_right h, Nat.cast_sub h]

/-- **(A.1) 逐元**：`O[k⁻²]_{nm} = u_n u_m K(n,m) − 2 δ_{nm} u_n² H_n^{(2)}`。 -/
lemma Of_invSq (n m : ℕ) :
    Of (fun k => 1 / (k:ℝ) ^ 2) n m
      = u n * u m * KA n m - (if n = m then 2 * u n ^ 2 * H2 n else 0) := by
  unfold Of KA H2
  by_cases h : n = m
  · subst h
    simp only [ite_true, ne_eq, not_true_eq_false, ite_false, add_zero]
    have e : ((n:ℝ) + n + 1) = ((n + n + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [e]
    ring
  · simp only [h, ite_false, ne_eq, not_false_eq_true, ite_true, zero_add, sub_zero]
    have e1 : (1:ℝ) / ((Nat.dist n m : ℕ) : ℝ) ^ 2 = 1 / ((n:ℝ) - m) ^ 2 := by rw [dist_sq_real]
    have e2 : ((n:ℝ) + m + 1) = ((n + m + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [e1, e2]
    ring

/-- `p_n := u_n v_n`。 -/
noncomputable def pOf (v : ℕ → ℝ) (n : ℕ) : ℝ := u n * v n

/-- **(A.1)**：`⟨P_N v, A P_N v⟩ = ∑_{n,m<N} p_n p_m K(n,m) − 2 ∑_{n<N} H_n^{(2)} p_n²`。 -/
theorem quadForm_invSq_eq (v : ℕ → ℝ) (N : ℕ) :
    quadForm (fun k => 1 / (k:ℝ) ^ 2) v N
      = (∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, pOf v n * pOf v m * KA n m)
        - 2 * ∑ n ∈ Finset.range N, H2 n * pOf v n ^ 2 := by
  unfold quadForm pOf
  simp only [Of_invSq]
  have hsplit : ∀ n m, v n * (u n * u m * KA n m - (if n = m then 2 * u n ^ 2 * H2 n else 0)) * v m
      = u n * v n * (u m * v m) * KA n m - (if n = m then 2 * H2 n * (u n * v n) ^ 2 else 0) := by
    intro n m
    split_ifs with h
    · subst h; ring
    · ring
  simp only [hsplit, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_range]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl; intro n hn
  rw [Finset.mem_range] at hn
  rw [ite_eq_left hn]; ring

/-! ### Lemma A.4：Hankel 正性 -/

/-- 内层积分：`∫_0^1 (∑_n a_n (xy)^n)² dy = ∑_{n,m} a_n a_m x^{n+m}/(n+m+1)`。 -/
lemma hankel_inner (a : ℕ → ℝ) (N : ℕ) (x : ℝ) :
    ∫ y in (0:ℝ)..1, (∑ n ∈ Finset.range N, a n * (x * y) ^ n) ^ 2
      = ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
          a n * a m * x ^ (n + m) * (1 / (((n + m : ℕ) : ℝ) + 1)) := by
  have e : ∀ y : ℝ, (∑ n ∈ Finset.range N, a n * (x * y) ^ n) ^ 2
      = ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, a n * a m * x ^ (n + m) * y ^ (n + m) := by
    intro y
    rw [sq, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro n _
    apply Finset.sum_congr rfl; intro m _
    rw [mul_pow, mul_pow, pow_add, pow_add]; ring
  simp_rw [e]
  rw [intervalIntegral.integral_finsetSum (fun n _ => by
    apply Continuous.intervalIntegrable; fun_prop)]
  apply Finset.sum_congr rfl; intro n _
  rw [intervalIntegral.integral_finsetSum (fun m _ => by
    apply Continuous.intervalIntegrable; fun_prop)]
  apply Finset.sum_congr rfl; intro m _
  rw [intervalIntegral.integral_const_mul, integral_pow]
  simp

/-- 外层积分：`∫_0^1 ∑_{n,m} a_n a_m x^{n+m}/(n+m+1) dx = ∑_{n,m} a_n a_m/(n+m+1)²`。 -/
lemma hankel_outer (a : ℕ → ℝ) (N : ℕ) :
    ∫ x in (0:ℝ)..1, ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        a n * a m * x ^ (n + m) * (1 / (((n + m : ℕ) : ℝ) + 1))
      = ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, a n * a m * (1 / (((n:ℝ) + m + 1) ^ 2)) := by
  rw [intervalIntegral.integral_finsetSum (fun n _ => by
    apply Continuous.intervalIntegrable; fun_prop)]
  apply Finset.sum_congr rfl; intro n _
  rw [intervalIntegral.integral_finsetSum (fun m _ => by
    apply Continuous.intervalIntegrable; fun_prop)]
  apply Finset.sum_congr rfl; intro m _
  have e : (∫ x in (0:ℝ)..1, a n * a m * x ^ (n + m) * (1 / (((n + m : ℕ) : ℝ) + 1)))
      = (a n * a m * (1 / (((n + m : ℕ) : ℝ) + 1))) * ∫ x in (0:ℝ)..1, x ^ (n + m) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext x; ring
  rw [e, integral_pow]
  simp only [one_pow, ne_eq, Nat.succ_ne_zero, not_false_eq_true, zero_pow, sub_zero]
  push_cast
  have : ((n:ℝ) + m + 1) ≠ 0 := by positivity
  field_simp

/-- **Lemma A.4（Hankel 正性）**：`∑_{n,m<N} a_n a_m/(n+m+1)² ≥ 0`。 -/
theorem hankel_nonneg (a : ℕ → ℝ) (N : ℕ) :
    0 ≤ ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, a n * a m * (1 / (((n:ℝ) + m + 1) ^ 2)) := by
  rw [← hankel_outer]
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro x _
  rw [← hankel_inner a N x]
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro y _
  exact sq_nonneg _

/-! ### Cor A.3：`A ⪯ B` -/

/-- `c_n^{(N)} := ∑_{m<N, m≠n} 1/(n−m)² ≤ ζ(2) + H_n^{(2)}`。 -/
lemma cN_le (n N : ℕ) :
    ∑ m ∈ Finset.range N, (if n ≠ m then 1 / ((n:ℝ) - m) ^ 2 else 0) ≤ zeta2 + H2 n := by
  have hsplit : ∀ m, (if n ≠ m then 1 / ((n:ℝ) - m) ^ 2 else 0)
      = (if m < n then 1 / ((n:ℝ) - m) ^ 2 else 0) + (if n < m then 1 / ((m:ℝ) - n) ^ 2 else 0) := by
    intro m
    rcases lt_trichotomy m n with h | h | h
    · have h1 : n ≠ m := by omega
      have h2 : ¬ n < m := by omega
      simp only [h1, h, h2, ne_eq, not_false_eq_true, ite_true, ite_false, add_zero]
    · subst h; simp
    · have h1 : n ≠ m := by omega
      have h2 : ¬ m < n := by omega
      simp only [h1, h, h2, ne_eq, not_false_eq_true, ite_true, ite_false, zero_add]
      have e : ((n:ℝ) - m) ^ 2 = ((m:ℝ) - n) ^ 2 := by ring
      rw [e]
  simp only [hsplit, Finset.sum_add_distrib]
  have h1 : ∑ m ∈ Finset.range N, (if m < n then 1 / ((n:ℝ) - m) ^ 2 else 0) ≤ H2 n := by
    rw [← Finset.sum_filter]
    calc ∑ m ∈ (Finset.range N).filter (fun m => m < n), 1 / ((n:ℝ) - m) ^ 2
        ≤ ∑ m ∈ Finset.range n, 1 / ((n:ℝ) - m) ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro m hm; simp only [Finset.mem_filter, Finset.mem_range] at hm ⊢; exact hm.2
          · intro m _ _; positivity
      _ = H2 n := by
          rw [H2_eq_range, ← Finset.sum_range_reflect (fun j => 1 / ((j:ℝ) + 1) ^ 2) n]
          apply Finset.sum_congr rfl; intro m hm
          rw [Finset.mem_range] at hm
          have e : ((n - 1 - m : ℕ) : ℝ) + 1 = (n:ℝ) - m := by
            rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
          rw [e]
  have h2 : ∑ m ∈ Finset.range N, (if n < m then 1 / ((m:ℝ) - n) ^ 2 else 0) ≤ zeta2 := by
    rw [← Finset.sum_filter]
    have e : (Finset.range N).filter (fun m => n < m) = Finset.Ico (n+1) N := by
      ext m; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
    rw [e, Finset.sum_Ico_eq_sum_range]
    have e2 : ∀ i : ℕ, (1:ℝ) / (((n + 1 + i : ℕ) : ℝ) - n) ^ 2 = 1 / ((i:ℝ) + 1) ^ 2 := by
      intro i; push_cast; ring_nf
    simp only [e2]
    unfold zeta2
    exact hasSum_zeta_two_shift.summable.sum_le_tsum _ (fun i _ => by positivity)
  linarith

/-- `⟨P_N v, B P_N v⟩ := ∑_{n,m<N} p_n p_m/(n+m+1)² + ∑_{n<N} ψ'(n+1) p_n²`（Lemma A.2 的 `B`）。 -/
noncomputable def quadFormB (v : ℕ → ℝ) (N : ℕ) : ℝ :=
  (∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, pOf v n * pOf v m * (1 / (((n:ℝ) + m + 1) ^ 2)))
    + ∑ n ∈ Finset.range N, psi' n * pOf v n ^ 2

lemma quadFormB_nonneg (v : ℕ → ℝ) (N : ℕ) : 0 ≤ quadFormB v N := by
  unfold quadFormB
  apply add_nonneg (hankel_nonneg _ _)
  exact Finset.sum_nonneg (fun n _ => mul_nonneg (psi'_nonneg n) (sq_nonneg _))

/-- **Cor A.3（`A ⪯ B`）**：`⟨P_N v, A P_N v⟩ ≤ ⟨P_N v, B P_N v⟩`。 -/
theorem quadForm_le_B (v : ℕ → ℝ) (N : ℕ) :
    quadForm (fun k => 1 / (k:ℝ) ^ 2) v N ≤ quadFormB v N := by
  rw [quadForm_invSq_eq]
  unfold quadFormB
  set p := pOf v with hp
  have hK : ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, p n * p m * KA n m
      = (∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, p n * p m * (1 / (((n:ℝ) + m + 1) ^ 2)))
        + ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
            (if n ≠ m then p n * p m * (1 / ((n:ℝ) - m) ^ 2) else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro n _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro m _
    unfold KA
    split_ifs <;> ring
  have hterm : ∀ n m, (if n ≠ m then p n * p m * (1 / ((n:ℝ) - m) ^ 2) else 0)
      ≤ (if n ≠ m then (p n ^ 2 / 2) * (1 / ((n:ℝ) - m) ^ 2) else 0)
        + (if n ≠ m then (p m ^ 2 / 2) * (1 / ((n:ℝ) - m) ^ 2) else 0) := by
    intro n m
    split_ifs
    · have := two_mul_le_add_sq (p n) (p m)
      have h0 : 0 ≤ 1 / ((n:ℝ) - m) ^ 2 := by positivity
      nlinarith
    · simp
  have hoff : ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        (if n ≠ m then p n * p m * (1 / ((n:ℝ) - m) ^ 2) else 0)
      ≤ ∑ n ∈ Finset.range N, p n ^ 2 * ∑ m ∈ Finset.range N,
          (if n ≠ m then 1 / ((n:ℝ) - m) ^ 2 else 0) := by
    calc _ ≤ ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
          ((if n ≠ m then (p n ^ 2 / 2) * (1 / ((n:ℝ) - m) ^ 2) else 0)
            + (if n ≠ m then (p m ^ 2 / 2) * (1 / ((n:ℝ) - m) ^ 2) else 0)) :=
          Finset.sum_le_sum (fun n _ => Finset.sum_le_sum (fun m _ => hterm n m))
      _ = 2 * ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
          (if n ≠ m then (p n ^ 2 / 2) * (1 / ((n:ℝ) - m) ^ 2) else 0) := by
          simp only [Finset.sum_add_distrib]
          rw [two_mul]; congr 1
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro n _
          apply Finset.sum_congr rfl; intro m _
          by_cases h : n = m
          · subst h; rfl
          · have h' : m ≠ n := Ne.symm h
            simp only [h, h', ne_eq, not_false_eq_true, ite_true]
            have e : ((m:ℝ) - n) ^ 2 = ((n:ℝ) - m) ^ 2 := by ring
            rw [e]
      _ = ∑ n ∈ Finset.range N, p n ^ 2 * ∑ m ∈ Finset.range N,
          (if n ≠ m then 1 / ((n:ℝ) - m) ^ 2 else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro n _
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro m _
          split_ifs <;> ring
  have hc : ∑ n ∈ Finset.range N, p n ^ 2 * ∑ m ∈ Finset.range N,
        (if n ≠ m then 1 / ((n:ℝ) - m) ^ 2 else 0)
      ≤ ∑ n ∈ Finset.range N, p n ^ 2 * (zeta2 + H2 n) :=
    Finset.sum_le_sum (fun n _ => mul_le_mul_of_nonneg_left (cN_le n N) (sq_nonneg _))
  have e : ∑ n ∈ Finset.range N, psi' n * p n ^ 2
      = ∑ n ∈ Finset.range N, p n ^ 2 * (zeta2 + H2 n) - 2 * ∑ n ∈ Finset.range N, H2 n * p n ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro n _
    rw [psi'_eq]; ring
  linarith [hK, hoff, hc, e]

end Eliashberg
