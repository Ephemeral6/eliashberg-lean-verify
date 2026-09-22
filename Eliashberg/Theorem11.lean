import Eliashberg.Corollaries

/-!
# Theorem 1.1 的有限维部分：(1.1) 式 `h^{(N)}(∞) = 2 S_N - 1 → ∞`

论文 §1.1。`S_N := ∑_{n<N} (2n+1)^{-1} = ‖u^{(N)}‖²`。

Theorem 1.1 的证明分四步；其中 (iii)「`P_N O[1] P_N` 的顶特征值等于 `2S_N - 1`」与
`S_N → ∞` 是纯有限维/初等分析，本文件证成：

* `SN_eq_sum_u_sq`：`S_N = ∑_{n<N} u_n²`
* `quadForm_one_eq`：`⟨x, P_N O[1] P_N x⟩ = 2 ⟨u, x⟩² - ‖x‖²`（由 (S1)）
* `quadForm_one_le`：Cauchy–Schwarz ⇒ `⟨x, O[1] x⟩ ≤ (2S_N - 1) ‖x‖²`
* `quadForm_one_u`：在 `x = u^{(N)}` 处取等
* **`hN_inf_isGreatest`**：`2S_N - 1` 是 `{⟨x, O[1]x⟩ : ‖x‖ = 1}` 的最大值，
  即论文的 `h^{(N)}(∞) := λ₁(P_N O[1] P_N) = 2S_N - 1`（λ₁ 取 Rayleigh 商上确界的定义，(F1)）
* **`SN_tendsto_atTop`**、**`hN_inf_tendsto_atTop`**：`2S_N - 1 → ∞`

步骤 (i)（压缩单调性）、(ii)（`T ↓ 0` 时 `F_T(k) → 1`，Lemma 0.1.4）与 (iv) 的介值定理
分别需要 `ℓ²` 上的算子、测度论与 `k(P,·)` 的连续性，不在本文件。
-/

namespace Eliashberg

open scoped BigOperators
open Filter Topology

/-- `S_N := ∑_{n<N} 1/(2n+1)`。 -/
noncomputable def SN (N : ℕ) : ℝ := ∑ n ∈ Finset.range N, 1 / (2 * (n:ℝ) + 1)

/-- `S_N = ‖u^{(N)}‖² = ∑_{n<N} u_n²`。 -/
lemma SN_eq_sum_u_sq (N : ℕ) : SN N = ∑ n ∈ Finset.range N, u n ^ 2 := by
  unfold SN
  apply Finset.sum_congr rfl; intro n _
  rw [u_sq]

lemma SN_pos (N : ℕ) (hN : 1 ≤ N) : 0 < SN N := by
  unfold SN
  apply Finset.sum_pos
  · intro n _; exact one_div_pos.mpr (two_mul_add_one_pos n)
  · exact ⟨0, Finset.mem_range.mpr hN⟩

/-- `1/(2n+1) ≥ (1/2)·1/(n+1)`，用于与调和级数比较。 -/
lemma one_div_two_mul_add_one_ge (n : ℕ) :
    (1/2 : ℝ) * (1 / ((n:ℝ) + 1)) ≤ 1 / (2 * (n:ℝ) + 1) := by
  rw [div_mul_div_comm, one_mul]
  apply one_div_le_one_div_of_le (two_mul_add_one_pos n)
  linarith

/-- `S_N → ∞`（调和级数发散，`Real.tendsto_sum_range_one_div_nat_succ_atTop`）。 -/
theorem SN_tendsto_atTop : Tendsto SN atTop atTop := by
  have h := Real.tendsto_sum_range_one_div_nat_succ_atTop
  have h2 : Tendsto (fun N => (1/2:ℝ) * ∑ n ∈ Finset.range N, (1:ℝ)/((n:ℝ)+1)) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num) h
  apply tendsto_atTop_mono _ h2
  intro N
  unfold SN
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n _
  exact one_div_two_mul_add_one_ge n

/-- `h^{(N)}(∞) := 2 S_N - 1`（(1.1) 的右端）。 -/
noncomputable def hN_inf (N : ℕ) : ℝ := 2 * SN N - 1

/-- (1.1)：`h^{(N)}(∞) → ∞`。 -/
theorem hN_inf_tendsto_atTop : Tendsto hN_inf atTop atTop := by
  unfold hN_inf
  apply tendsto_atTop_add_const_right
  exact Tendsto.const_mul_atTop (by norm_num) SN_tendsto_atTop

/-! ### `P_N O[1] P_N` 的 Rayleigh 商 -/

/-- 由 (S1)：`⟨x, P_N O[1] P_N x⟩ = 2 (∑_{n<N} u_n x_n)² - ∑_{n<N} x_n²`。 -/
lemma quadForm_one_eq (x : ℕ → ℝ) (N : ℕ) :
    quadForm (fun _ => (1:ℝ)) x N
      = 2 * (∑ n ∈ Finset.range N, u n * x n) ^ 2 - ∑ n ∈ Finset.range N, x n ^ 2 := by
  unfold quadForm
  simp only [Of_one]
  have h1 : ∀ n m : ℕ, x n * (2 * u n * u m - (if n = m then 1 else 0)) * x m
      = 2 * ((u n * x n) * (u m * x m)) - (if n = m then x n ^ 2 else 0) := by
    intro n m
    split_ifs with h
    · subst h; ring
    · ring
  simp only [h1, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_range]
  have h2 : ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, 2 * ((u n * x n) * (u m * x m))
      = 2 * (∑ n ∈ Finset.range N, u n * x n) ^ 2 := by
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro n _
    rw [Finset.mul_sum]
  have h3 : ∑ n ∈ Finset.range N, (if n < N then x n ^ 2 else 0) = ∑ n ∈ Finset.range N, x n ^ 2 := by
    apply Finset.sum_congr rfl; intro n hn
    rw [Finset.mem_range] at hn
    rw [ite_eq_left hn]
  rw [h2, h3]

/-- Cauchy–Schwarz：`⟨x, O[1] x⟩ ≤ (2 S_N - 1) ‖x‖²`。 -/
lemma quadForm_one_le (x : ℕ → ℝ) (N : ℕ) :
    quadForm (fun _ => (1:ℝ)) x N ≤ hN_inf N * ∑ n ∈ Finset.range N, x n ^ 2 := by
  rw [quadForm_one_eq]
  unfold hN_inf
  rw [SN_eq_sum_u_sq]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range N) u x
  linarith

/-- 在 `x = u^{(N)}` 处取等：`⟨u, O[1] u⟩ = (2 S_N - 1) S_N`。 -/
lemma quadForm_one_u (N : ℕ) :
    quadForm (fun _ => (1:ℝ)) u N = hN_inf N * SN N := by
  rw [quadForm_one_eq]
  unfold hN_inf
  rw [SN_eq_sum_u_sq]
  have : ∑ n ∈ Finset.range N, u n * u n = ∑ n ∈ Finset.range N, u n ^ 2 := by
    apply Finset.sum_congr rfl; intro n _; ring
  rw [this]
  ring

/-- **(1.1)，Rayleigh 形式**：`N ≥ 1` 时 `2 S_N - 1` 是
`{⟨x, P_N O[1] P_N x⟩ : ∑_{n<N} x_n² = 1}` 的最大值，即 `λ₁(P_N O[1] P_N) = 2 S_N - 1`
（按 (F1) 用 Rayleigh 商上确界定义 `λ₁`）。最大值在归一化的 `u^{(N)}` 处取到。 -/
theorem hN_inf_isGreatest (N : ℕ) (hN : 1 ≤ N) :
    IsGreatest {q : ℝ | ∃ x : ℕ → ℝ, ∑ n ∈ Finset.range N, x n ^ 2 = 1
                          ∧ q = quadForm (fun _ => (1:ℝ)) x N} (hN_inf N) := by
  constructor
  · -- 取 `x = u / √S_N`
    have hS : 0 < SN N := SN_pos N hN
    have hsq : 0 < Real.sqrt (SN N) := Real.sqrt_pos.mpr hS
    refine ⟨fun n => u n / Real.sqrt (SN N), ?_, ?_⟩
    · -- 归一化
      have : ∀ n, (u n / Real.sqrt (SN N)) ^ 2 = u n ^ 2 * (1 / SN N) := by
        intro n
        rw [div_pow, Real.sq_sqrt (le_of_lt hS)]
        ring
      simp only [this]
      rw [← Finset.sum_mul, ← SN_eq_sum_u_sq]
      field_simp
    · -- 二次型按齐次性缩放
      rw [quadForm_one_eq]
      have e1 : ∑ n ∈ Finset.range N, u n * (u n / Real.sqrt (SN N))
          = (∑ n ∈ Finset.range N, u n * u n) / Real.sqrt (SN N) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl; intro n _; ring
      have e2 : ∑ n ∈ Finset.range N, (u n / Real.sqrt (SN N)) ^ 2
          = (∑ n ∈ Finset.range N, u n ^ 2) / SN N := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl; intro n _
        rw [div_pow, Real.sq_sqrt (le_of_lt hS)]
      rw [e1, e2, div_pow, Real.sq_sqrt (le_of_lt hS), ← SN_eq_sum_u_sq]
      have e3 : ∑ n ∈ Finset.range N, u n * u n = SN N := by
        rw [SN_eq_sum_u_sq]; apply Finset.sum_congr rfl; intro n _; ring
      rw [e3]
      unfold hN_inf
      field_simp
  · rintro q ⟨x, hx, rfl⟩
    have := quadForm_one_le x N
    rw [hx, mul_one] at this
    exact this

end Eliashberg
