import Eliashberg.Lemma14

/-!
# Lemma 1.4 的组装：(1.2) 恒等式

把 `Q_{LL'}(δ_k)` 分解为四个分量的和，并化为论文 (1.2) 的三组。

## 分量的定义（对应 `Q2` 的五块）

* `S1`：条件 `m = n + k`
* `S2`：条件 `n = m + k`
* `S3`：条件 `n + m + 1 = k`（**注意：不带 `n ≠ m` 过滤**，
  因为对角线上的 `n = m` 也可能满足 `2n+1 = k`，论文把该项记入 group 3）
* `Sd`：对角负项 `-2 u_n^2`（仅当 `k ≤ n`）

论文 (1.2) 的三组是这四个分量的重组：
`group 1` 吸收了 `S2` 与 `Sd` 的一部分，`group 2` 即 `S1`，`group 3` 即 `S3`。
-/

namespace Eliashberg

open scoped BigOperators

/-- 条件 `m = n + k` 的分量。 -/
noncomputable def S1 (k L Lp : ℕ) : ℝ :=
  ∑ n ∈ Finset.range L, if n + k < Lp then u n * u (n + k) else 0

/-- 条件 `n = m + k` 的分量。 -/
noncomputable def S2 (k L Lp : ℕ) : ℝ :=
  ∑ m ∈ Finset.range Lp, if m + k < L then u m * u (m + k) else 0

/-- 条件 `n + m + 1 = k` 的分量（含对角情形 `2n+1 = k`）。 -/
noncomputable def S3 (k L Lp : ℕ) : ℝ :=
  ∑ n ∈ Finset.range L, ∑ m ∈ Finset.range Lp,
    if n + m + 1 = k then u n * u m else 0

/-- 对角负项。范围是 `n < min L Lp`（对角点 `(n,n)` 落在矩形内当且仅当 `n < min L Lp`），
**不是** `n < L`——这是曾踩过的坑，见 Remark 1.5。 -/
noncomputable def Sd (k L Lp : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (min L Lp), if k ≤ n then -(2 * (u n) ^ 2) else 0

/-- `S1` 即 `band1` 的左端，故可化为单和。 -/
lemma S1_eq (k L Lp : ℕ) : S1 k L Lp
    = ∑ n ∈ Finset.range L, if n + k < Lp then u n * u (n + k) else 0 := rfl

/-- `S2` 即 `band2` 的左端。 -/
lemma S2_eq (k L Lp : ℕ) : S2 k L Lp
    = ∑ m ∈ Finset.range Lp, if m + k < L then u m * u (m + k) else 0 := rfl

/-- `S3` 化为单和（`band3`）。 -/
lemma S3_eq (k L Lp : ℕ) : S3 k L Lp
    = ∑ n ∈ Finset.range L,
        if n < k ∧ k - 1 - n < Lp then u n * u (k - 1 - n) else 0 := by
  unfold S3
  exact band3 k L Lp

/-! ### Q2 的分块

`Q2` 是 `O[δ_k]` 在矩形上的双重和。把它按「对角 / 非对角」拆开，
再把非对角拆成三个条件，把对角化为一重和。 -/

/-- `O[δ_k]` 的矩阵元（按 §0 的 (0.1)，`f = δ_k`）。 -/
noncomputable def Ok (k n m : ℕ) : ℝ :=
  (if n ≠ m then
     (if n + k = m then u n * u m else 0)
   + (if m + k = n then u m * u n else 0)
   + (if n + m + 1 = k then u n * u m else 0)
   else 0)
  + (if n = m then
       ((if k ≤ n then -(2 * (u n) ^ 2) else 0) + (if 2 * n + 1 = k then (u n) ^ 2 else 0))
     else 0)

/-- `Q_{LL'}(δ_k)`：矩形上的双重和。 -/
noncomputable def Q2 (k L Lp : ℕ) : ℝ :=
  ∑ n ∈ Finset.range L, ∑ m ∈ Finset.range Lp, Ok k n m

/-- 按对角 / 非对角拆开 `Q2`。 -/
lemma Q2_split (k L Lp : ℕ) : Q2 k L Lp
    = (∑ n ∈ Finset.range L, ∑ m ∈ Finset.range Lp,
         if n ≠ m then ((if n + k = m then u n * u m else 0)
                      + (if m + k = n then u m * u n else 0)
                      + (if n + m + 1 = k then u n * u m else 0)) else 0)
    + (∑ n ∈ Finset.range L, ∑ m ∈ Finset.range Lp,
         if n = m then ((if k ≤ n then -(2 * (u n) ^ 2) else 0)
                      + (if 2 * n + 1 = k then (u n) ^ 2 else 0)) else 0) := by
  unfold Q2 Ok
  simp only [← Finset.sum_add_distrib]

/-- 非对角块拆成三个条件。 -/
lemma offdiag_split (k L Lp : ℕ) :
    (∑ n ∈ Finset.range L, ∑ m ∈ Finset.range Lp,
       if n ≠ m then ((if n + k = m then u n * u m else 0)
                    + (if m + k = n then u m * u n else 0)
                    + (if n + m + 1 = k then u n * u m else 0)) else 0)
  = (∑ n ∈ Finset.range L, ∑ m ∈ Finset.range Lp, if n ≠ m ∧ n + k = m then u n * u m else 0)
  + (∑ n ∈ Finset.range L, ∑ m ∈ Finset.range Lp, if n ≠ m ∧ m + k = n then u m * u n else 0)
  + (∑ n ∈ Finset.range L, ∑ m ∈ Finset.range Lp, if n ≠ m ∧ n + m + 1 = k then u n * u m else 0) := by
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro m _
  by_cases h : n = m <;> simp [h]

/-- 对角块化为一重和。 -/
lemma diag_reduce (k L Lp : ℕ) :
    (∑ n ∈ Finset.range L, ∑ m ∈ Finset.range Lp,
       if n = m then ((if k ≤ n then -(2 * (u n) ^ 2) else 0)
                    + (if 2 * n + 1 = k then (u n) ^ 2 else 0)) else 0)
  = ∑ n ∈ Finset.range L,
       if n < Lp then ((if k ≤ n then -(2 * (u n) ^ 2) else 0)
                     + (if 2 * n + 1 = k then (u n) ^ 2 else 0)) else 0 := by
  apply Finset.sum_congr rfl
  intro n _
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_range]


/-- 非对角块 1：条件 `n ≠ m ∧ n + k = m`（`k ≥ 1` 时 `n ≠ m` 自动）即 `S1`。 -/
lemma off1_eq (k L Lp : ℕ) (hk : 1 ≤ k) :
    (∑ n ∈ Finset.range L, ∑ m ∈ Finset.range Lp,
       if n ≠ m ∧ n + k = m then (u n * u m : ℝ) else 0) = S1 k L Lp := by
  have h1 : ∀ n m : ℕ, (n ≠ m ∧ n + k = m) ↔ (m = n + k) := by
    intro n m
    constructor
    · rintro ⟨_, h⟩; exact h.symm
    · intro h; exact ⟨by omega, h.symm⟩
  simp only [h1]
  exact band1 k L Lp

/-- 非对角块 2：条件 `n ≠ m ∧ m + k = n` 即 `S2`。 -/
lemma off2_eq (k L Lp : ℕ) (hk : 1 ≤ k) :
    (∑ n ∈ Finset.range L, ∑ m ∈ Finset.range Lp,
       if n ≠ m ∧ m + k = n then (u m * u n : ℝ) else 0) = S2 k L Lp := by
  have h1 : ∀ n m : ℕ, (n ≠ m ∧ m + k = n) ↔ (n = m + k) := by
    intro n m
    constructor
    · rintro ⟨_, h⟩; exact h.symm
    · intro h; exact ⟨by omega, h.symm⟩
  simp only [h1]
  exact band2 k L Lp

/-- 非对角块 3：条件 `n ≠ m ∧ n + m + 1 = k` 与 `S3` 相差「对角上的 L3」一项。 -/
lemma off3_eq (k L Lp : ℕ) :
    (∑ n ∈ Finset.range L, ∑ m ∈ Finset.range Lp,
       if n ≠ m ∧ n + m + 1 = k then (u n * u m : ℝ) else 0)
  = S3 k L Lp
    - (∑ n ∈ Finset.range L, ∑ m ∈ Finset.range Lp,
         if n = m ∧ n + m + 1 = k then (u n * u m : ℝ) else 0) := by
  unfold S3
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m _
  by_cases h : n = m <;> simp [h]


/-- 对角上的 L3 项：`n = m ∧ n + m + 1 = k` 化为 `2n + 1 = k`。 -/
lemma diag_l3_eq (k L Lp : ℕ) :
    (∑ n ∈ Finset.range L, ∑ m ∈ Finset.range Lp,
       if n = m ∧ n + m + 1 = k then (u n * u m : ℝ) else 0)
  = ∑ n ∈ Finset.range L, if 2 * n + 1 = k ∧ n < Lp then (u n) ^ 2 else 0 := by
  apply Finset.sum_congr rfl
  intro n _
  have hiff : ∀ m : ℕ, (n = m ∧ n + m + 1 = k) ↔ (n = m ∧ 2 * n + 1 = k) := by
    intro m
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
  simp only [hiff]
  by_cases hk : 2 * n + 1 = k
  · simp only [hk, and_true]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_range]
    by_cases h : n < Lp
    · simp only [h, true_and, ite_true]
      ring
    · simp [h]
  · simp only [hk, and_false, ite_false, Finset.sum_const_zero]
    simp


end Eliashberg
