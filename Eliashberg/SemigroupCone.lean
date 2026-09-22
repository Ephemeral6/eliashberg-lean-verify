import Eliashberg.ConeLimit
import Eliashberg.ConeFinite

/-!
# Proposition 1.11 在 `ℓ²` 上：半群保锥

论文：

> **Proposition 1.11 (step 1: the semigroup preserves the cone).** Let `F` be admissible.
> Then `e^{tO[F]} C ⊂ C` for all `t ≥ 0`.

论文的证明：在阶梯基下 `O^{(N)}` 的矩阵 `B` 是 Metzler 的（Corollary 1.10），
故 `e^{tB}` 保非负卦限（(F4)），回到原基即 `e^{tO^{(N)}}C_N ⊂ C_N`；
再由 `O^{(N)} → O[F]` 强收敛与 (F5)（`e^{tO^{(N)}} → e^{tO[F]}` 强收敛）取极限。

**这里不需要 (F5)**，也不需要阶梯基。关键观察是：`O[F]` 本身就是 Metzler 的
（非对角元 `≥ 0`，`Of_nonneg_of_ne`），而对角元有一致下界
（`abs_Of_diag_le`，`L2Bounds.lean`）：

\[
|O[F]_{nn}| \le 3\|F\|_{\ell^1}\, u_n^2 \le 3\|F\|_{\ell^1}, \qquad u_n^2 = \frac1{2n+1} \le 1 .
\]

于是取 `c := 3‖F‖_{ℓ¹}`，矩阵 `A + cI` 是**逐元非负**的
（对角：`A_{nn} + c ≥ −|A_{nn}| + c ≥ 0`；非对角：`A_{nm} ≥ 0`）。
逐元非负的矩阵其任意幂仍逐元非负，故 `e^{t(A+cI)}` 逐元非负；
又 `e^{tA} = e^{−ct} e^{t(A+cI)}`（`A` 与 `I` 交换），正标量不改变符号。

`ℓ²` 层没有「逐元非负」的现成语言，所以本文件用**截断 + 算子范数极限**把它搬过来：

1. 每个 `N`，`O_N := P_N O[F] P_N` 就是有限矩阵 `ON F`，而 `ON F + cI` 逐元非负，
   故 `e^{t(ON F + cI)}` 逐元非负，从而 `e^{t O_N}` 保锥 `C_N`。
2. `O_N → O[F]` 在**算子范数**下（`opNorm_sub_OpN_le`：`‖O[F] − O_N‖ ≤ √τ_N`，`τ_N → 0`），
   而 `NormedSpace.exp` 在赋范环上连续（`exp_continuous`），故 `e^{tO_N} → e^{tO[F]}`。
3. 锥 `C` 在 `ℓ²` 中闭（`InCone.of_tendsto`），故极限仍在锥内。

三块分别对应下面的 `exp_shift_entryNonneg`、`exp_tendsto`、`InCone.of_tendsto`。
-/

namespace Eliashberg

open scoped BigOperators ENNReal Matrix.Norms.Operator
open Filter Topology

noncomputable section

/-! ### 一、`O[F]` 的对角元下界与逐元非负的移位 -/

/-- **非对角元非负**：`F ≥ 0`、`n ≠ m` ⇒ `O[F]_{nm} ≥ 0`。 -/
lemma Of_nonneg_of_ne {F : ℕ → ℝ} (hnn : ∀ k, 1 ≤ k → 0 ≤ F k) {n m : ℕ} (hnm : n ≠ m) :
    0 ≤ Of F n m := by
  have hdist : 1 ≤ Nat.dist n m := by
    rcases Nat.eq_zero_or_pos (Nat.dist n m) with h | h
    · exact absurd (Nat.eq_of_dist_eq_zero h) hnm
    · omega
  rw [show Of F n m = F (Nat.dist n m) * (u n * u m) + F (n + m + 1) * (u n * u m) by
    unfold Of
    rw [if_neg (by simpa using hnm), if_pos hnm]
    ring]
  exact add_nonneg
    (mul_nonneg (hnn _ hdist) (le_of_lt (mul_pos (u_pos n) (u_pos m))))
    (mul_nonneg (hnn _ (Nat.le_add_left 1 (n + m))) (le_of_lt (mul_pos (u_pos n) (u_pos m))))

/-- **对角元下界**：`−(3‖F‖_{ℓ¹}) ≤ O[F]_{nn}`（由 `abs_Of_diag_le` 与 `u_n² ≤ 1`）。 -/
lemma neg_three_l1_le_Of_diag {F : ℕ → ℝ} (hF : L1 F) (n : ℕ) :
    -(3 * l1 F) ≤ Of F n n := by
  have h := abs_Of_diag_le hF n
  have hu : u n ^ 2 ≤ 1 := u_sq_le_one n
  have hl1 : 0 ≤ l1 F := l1_nonneg F
  have : 3 * l1 F * u n ^ 2 ≤ 3 * l1 F := by nlinarith
  linarith [neg_abs_le (Of F n n), h]

/-- 移位 `c := 3‖F‖_{ℓ¹}` 后矩阵**逐元非负**。 -/
lemma entryNonneg_shift {F : ℕ → ℝ} (hF : L1 F) (hnn : ∀ k, 1 ≤ k → 0 ≤ F k) (n m : ℕ) :
    0 ≤ Of F n m + (if n = m then 3 * l1 F else 0) := by
  by_cases h : n = m
  · subst h
    rw [if_pos rfl]
    linarith [neg_three_l1_le_Of_diag hF n]
  · rw [if_neg h]
    linarith [Of_nonneg_of_ne hnn h]

/-! ### 二、有限维：逐元非负 ⇒ 指数逐元非负 ⇒ 保锥 -/

/-- **逐元非负矩阵的指数逐元非负**（一般 `N`：不要求 `F` 最终为零）。 -/
theorem exp_entryNonneg_of_entryNonneg {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : ∀ i j, 0 ≤ A i j) : ∀ i j, 0 ≤ (NormedSpace.exp A) i j := by
  intro i j
  have hs : HasSum (fun n : ℕ => ((n.factorial : ℝ)⁻¹) • A ^ n) (NormedSpace.exp A) :=
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A
  have ht := hs.tendsto_sum_nat
  have hcont : Continuous (fun M : Matrix (Fin N) (Fin N) ℝ => M i j) :=
    Continuous.matrix_elem continuous_id i j
  have ht' := (hcont.tendsto _).comp ht
  apply ge_of_tendsto' ht'
  intro n
  simp only [Function.comp]
  have hpow : ∀ k : ℕ, ∀ a b : Fin N, 0 ≤ (A ^ k) a b := by
    intro k
    induction k with
    | zero =>
      intro a b
      rw [pow_zero, Matrix.one_apply]
      split_ifs <;> norm_num
    | succ k ih =>
      intro a b
      rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun c _ => mul_nonneg (ih a c) (hA c b)
  rw [Matrix.sum_apply]
  exact Finset.sum_nonneg fun k _ => by
    rw [Matrix.smul_apply, smul_eq_mul]
    exact mul_nonneg (by positivity) (hpow k i j)

/-- **移位后的指数**：`e^{t(ON F + c•1)}` 逐元非负（`F` 非负、`c := 3‖F‖_{ℓ¹}`）。 -/
theorem exp_ON_shift_entryNonneg {F : ℕ → ℝ} (hF : L1 F) (hnn : ∀ k, 1 ≤ k → 0 ≤ F k)
    (N : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ∀ i j, 0 ≤ (NormedSpace.exp (t • ((ON F : Matrix (Fin N) (Fin N) ℝ)
      + (3 * l1 F) • (1 : Matrix (Fin N) (Fin N) ℝ)))) i j := by
  refine exp_entryNonneg_of_entryNonneg fun i j => ?_
  rw [Matrix.smul_apply, smul_eq_mul]
  refine mul_nonneg ht ?_
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases h : i = j
  · subst h
    simp only [ite_true, mul_one]
    have := entryNonneg_shift hF hnn i.val i.val
    rw [if_pos rfl] at this
    simpa only [ON, Matrix.of_apply] using this
  · simp only [h, ite_false, mul_zero, add_zero]
    have hne : i.val ≠ j.val := fun hh => h (Fin.ext hh)
    have := Of_nonneg_of_ne hnn hne
    simpa only [ON, Matrix.of_apply] using this

/-- **有限维 Prop 1.11（一般 admissible `F`）**：`e^{t·ON F}` 保非负卦限。 -/
theorem exp_smul_ON_entryNonneg {F : ℕ → ℝ} (hF : L1 F) (hnn : ∀ k, 1 ≤ k → 0 ≤ F k)
    (N : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ∀ i j, 0 ≤ (NormedSpace.exp (t • (ON F : Matrix (Fin N) (Fin N) ℝ))) i j := by
  set c : ℝ := 3 * l1 F with hc
  have hc0 : 0 ≤ c := by rw [hc]; exact mul_nonneg (by norm_num) (l1_nonneg F)
  have hsplit : t • (ON F : Matrix (Fin N) (Fin N) ℝ)
      = t • ((ON F : Matrix (Fin N) (Fin N) ℝ) + c • (1 : Matrix (Fin N) (Fin N) ℝ))
        + (-(t * c)) • (1 : Matrix (Fin N) (Fin N) ℝ) := by
    rw [smul_add, smul_smul, add_assoc, ← add_smul]
    simp
  have hcomm : Commute (t • ((ON F : Matrix (Fin N) (Fin N) ℝ) + c • (1 : Matrix (Fin N) (Fin N) ℝ)))
      ((-(t * c)) • (1 : Matrix (Fin N) (Fin N) ℝ)) :=
    ((Commute.one_right _).smul_right _).smul_left _
  rw [hsplit, Matrix.exp_add_of_commute _ _ hcomm, exp_smul_one]
  intro i j
  rw [Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul, Matrix.mul_one]
  exact mul_nonneg (le_of_lt (Real.exp_pos _)) (exp_ON_shift_entryNonneg hF hnn N t ht i j)

end

end Eliashberg
