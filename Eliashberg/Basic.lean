import Mathlib

/-!
# Eliashberg 临界温度论文 —— 形式化（task-577）

第一层：正文 §1.2 的组合引理。

## 记号（照抄论文 §0 / §1.2）

* `u n = (2n+1)^{-1/2}` —— Matsubara 权重
* `d n = u n - u (n+1)` —— 差分
* `S a b = ∑_{m=a}^{b-1} u m` —— 部分和（`b ≤ a` 时为空和，等于 0）

## 环境备注

本机的 mathlib 只编译了一部分（`Mathlib/Tactic/Omega.olean` 缺失），但 `omega` 是 Lean 核心
自带的策略（`Lean/Elab/Tactic/Omega/`），**不受影响，可正常使用**；本库大量使用它处理
ℕ 上带截断减法与 `min` 的索引算术。`linarith`、`positivity` 在个别非线性目标上会失败，
那时用显式引理或 `nlinarith` 配辅助假设。
-/

namespace Eliashberg

open scoped BigOperators

/-- Matsubara 权重 `u_n = (2n+1)^{-1/2}`。 -/
noncomputable def u (n : ℕ) : ℝ := (2 * (n : ℝ) + 1) ^ (-(1/2 : ℝ))

/-- 差分 `d_n = u_n - u_{n+1}`（论文 §1.2）。 -/
noncomputable def d (n : ℕ) : ℝ := u n - u (n + 1)

/-- 部分和 `S a b = ∑_{m=a}^{b-1} u_m`（论文 §1.2，`b ≤ a` 时为空和 = 0）。 -/
noncomputable def S (a b : ℕ) : ℝ := ∑ m ∈ Finset.Ico a b, u m

/-! ### 基本事实 -/

lemma u_pos (n : ℕ) : 0 < u n := by
  unfold u; exact Real.rpow_pos_of_pos (by positivity) _

/-- `2n+1 > 0`。 -/
lemma two_mul_add_one_pos (n : ℕ) : (0:ℝ) < 2 * (n : ℝ) + 1 := by
  have h : (0:ℕ) < 2 * n + 1 := Nat.succ_pos _
  exact_mod_cast h

/-- `u_n^2 = 1/(2n+1)`。 -/
lemma u_sq (n : ℕ) : u n ^ 2 = 1 / (2 * (n : ℝ) + 1) := by
  unfold u
  rw [sq, ← Real.rpow_add (two_mul_add_one_pos n)]
  have h : (-(1/2:ℝ)) + (-(1/2:ℝ)) = -1 := by norm_num
  rw [h, Real.rpow_neg_one, one_div]

/-! ### Lemma 1.3(1) —— `u` 严格递减 -/

lemma u_strictAnti : StrictAnti u := by
  intro n m hnm
  unfold u
  have hnmR : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
  have hbase : 2 * (n : ℝ) + 1 < 2 * (m : ℝ) + 1 := by linarith
  have ha : 0 < 2 * (n : ℝ) + 1 := two_mul_add_one_pos n
  have hb : 0 < 2 * (m : ℝ) + 1 := two_mul_add_one_pos m
  -- (2n+1)^{-1/2} = ((2n+1)^{-1})^{1/2}，两边同形
  rw [Real.rpow_neg_eq_inv_rpow, Real.rpow_neg_eq_inv_rpow]
  apply Real.rpow_lt_rpow (le_of_lt (inv_pos.mpr hb)) _ (by norm_num)
  exact (inv_lt_inv₀ hb ha).mpr hbase

/-! ### Lemma 1.3(2) —— 积分表示

论文：`d_m = ∫_m^{m+1} (2x+1)^{-3/2} dx`。
-/

/-- 被积函数的导数：`d/dx (2x+1)^{-1/2} = -(2x+1)^{-3/2}`。 -/
lemma hasDerivAt_u (x : ℝ) (hx : 0 < 2*x + 1) :
    HasDerivAt (fun y : ℝ => (2*y+1) ^ (-(1/2:ℝ))) (-((2*x+1) ^ (-(3/2:ℝ)))) x := by
  have h1 : HasDerivAt (fun y : ℝ => 2*y + 1) 2 x := by
    simpa using (hasDerivAt_id x).const_mul 2 |>.add_const 1
  have h2 : HasDerivAt (fun y : ℝ => (2*y+1) ^ (-(1/2:ℝ)))
      (2 * (-(1/2:ℝ)) * (2*x+1) ^ (-(1/2:ℝ) - 1)) x :=
    h1.rpow_const (Or.inl (ne_of_gt hx))
  convert h2 using 1
  ring_nf

/-- Lemma 1.3(2)，积分表示：`d_m = ∫_m^{m+1} (2x+1)^{-3/2} dx`。 -/
lemma d_eq_integral (n : ℕ) :
    d n = ∫ x in (n:ℝ)..((n:ℝ)+1), (2*x+1) ^ (-(3/2:ℝ)) := by
  rw [d, u, u]
  have hcast : (2 * ((n+1 : ℕ) : ℝ) + 1) = 2 * ((n:ℝ) + 1) + 1 := by push_cast; ring
  rw [hcast]
  rw [show (∫ x in (n:ℝ)..((n:ℝ)+1), (2*x+1) ^ (-(3/2:ℝ)))
        = -(∫ x in (n:ℝ)..((n:ℝ)+1), -((2*x+1) ^ (-(3/2:ℝ)))) by
        rw [intervalIntegral.integral_neg]; ring]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun y : ℝ => (2*y+1) ^ (-(1/2:ℝ)))
        (f' := fun y : ℝ => -((2*y+1) ^ (-(3/2:ℝ))))]
  · ring
  · intro x hx
    rw [Set.uIcc_of_le (by simp)] at hx
    exact hasDerivAt_u x (by linarith [hx.1])
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.neg
    apply ContinuousOn.rpow_const
    · fun_prop
    · intro x hx
      left
      have h1 : (n:ℝ) ≤ x := by
        rw [Set.uIcc_of_le (by simp)] at hx; exact hx.1
      linarith

/-- `psi x = (2x+1)^{-3/2}`，即 Lemma 1.3(2) 的被积函数。 -/
noncomputable def psi (x : ℝ) : ℝ := (2*x+1) ^ (-(3/2:ℝ))

lemma psi_pos (x : ℝ) (hx : 0 < 2*x+1) : 0 < psi x := by
  unfold psi; exact Real.rpow_pos_of_pos hx _

lemma psi_strictAnti {x y : ℝ} (h : x < y) (hx : 0 < 2*x+1) : psi y < psi x := by
  unfold psi
  have hy : 0 < 2*y + 1 := by linarith
  have hbase : 2*x + 1 < 2*y + 1 := by linarith
  rw [Real.rpow_neg_eq_inv_rpow, Real.rpow_neg_eq_inv_rpow]
  apply Real.rpow_lt_rpow (le_of_lt (inv_pos.mpr hy)) _ (by norm_num)
  exact (inv_lt_inv₀ hy hx).mpr hbase

lemma contOn_shift (n : ℕ) :
    ContinuousOn (fun t : ℝ => (2*((n:ℝ)+t)+1) ^ (-(3/2:ℝ))) (Set.Icc 0 1) := by
  apply ContinuousOn.rpow_const
  · fun_prop
  · intro x hx; left; have : (0:ℝ) ≤ x := hx.1; linarith

lemma contOn_shift1 (n : ℕ) :
    ContinuousOn (fun t : ℝ => (2*((n:ℝ)+1+t)+1) ^ (-(3/2:ℝ))) (Set.Icc 0 1) := by
  apply ContinuousOn.rpow_const
  · fun_prop
  · intro x hx; left; have : (0:ℝ) ≤ x := hx.1; linarith

/-- `psi` 的凸性（中点形式）：`A^{-3/2} + C^{-3/2} ≥ 2((A+C)/2)^{-3/2}`。

这是 Lemma 1.3(2) 中 `d_{m-1}+d_{m+1}-2d_m ≥ 0` 所依赖的凸性。
证法为 AM-GM 三步：
1. `√(AC) ≤ (A+C)/2`
2. 负指数下底数越大值越小：`((A+C)/2)^{-3/2} ≤ (√(AC))^{-3/2}`
3. `2(AC)^{-3/4} ≤ A^{-3/2} + C^{-3/2}` -/
lemma psi_convex_mid (A C : ℝ) (hA : 0 < A) (hC : 0 < C) :
    A ^ (-(3/2:ℝ)) + C ^ (-(3/2:ℝ)) ≥ 2 * ((A+C)/2) ^ (-(3/2:ℝ)) := by
  have hAM : Real.sqrt (A*C) ≤ (A+C)/2 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by linarith, by nlinarith [sq_nonneg (A - C)]⟩
  have hsp : 0 < Real.sqrt (A*C) := Real.sqrt_pos.mpr (mul_pos hA hC)
  have hmp : 0 < (A+C)/2 := by linarith
  have h1 : ((A+C)/2) ^ (-(3/2:ℝ)) ≤ (Real.sqrt (A*C)) ^ (-(3/2:ℝ)) := by
    rw [Real.rpow_neg_eq_inv_rpow, Real.rpow_neg_eq_inv_rpow]
    apply Real.rpow_le_rpow
    · exact le_of_lt (inv_pos.mpr hmp)
    · rw [inv_le_inv₀ hmp hsp]; exact hAM
    · norm_num
  have h2 : (Real.sqrt (A*C)) ^ (-(3/2:ℝ)) = (A*C) ^ (-(3/4:ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt (mul_pos hA hC))]
    ring_nf
  have h3 : 2 * (A*C) ^ (-(3/4:ℝ)) ≤ A ^ (-(3/2:ℝ)) + C ^ (-(3/2:ℝ)) := by
    have hgm := Real.geom_mean_le_arith_mean2_weighted (show (0:ℝ) ≤ 1/2 by norm_num)
      (show (0:ℝ) ≤ 1/2 by norm_num) (le_of_lt (Real.rpow_pos_of_pos hA (-(3/2:ℝ))))
      (le_of_lt (Real.rpow_pos_of_pos hC (-(3/2:ℝ)))) (by norm_num)
    have e1 : (A ^ (-(3/2:ℝ))) ^ (1/2:ℝ) = A ^ (-(3/4:ℝ)) := by
      rw [← Real.rpow_mul (le_of_lt hA)]; ring_nf
    have e2 : (C ^ (-(3/2:ℝ))) ^ (1/2:ℝ) = C ^ (-(3/4:ℝ)) := by
      rw [← Real.rpow_mul (le_of_lt hC)]; ring_nf
    rw [e1, e2, ← Real.mul_rpow (le_of_lt hA) (le_of_lt hC)] at hgm
    linarith
  rw [h2] at h1
  linarith

/-- 逐点比较：`t ≥ 0` 时 `psi (n+1+t) < psi (n+t)`。 -/
lemma psi_shift_lt (k : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    psi ((k:ℝ)+1+t) < psi ((k:ℝ)+t) := by
  apply psi_strictAnti
  · linarith
  · have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
    linarith

/-- Lemma 1.3(2) 的第二段：`d` 严格递减。

证法：由 `d_eq_integral`，两个相邻差分都是 `[0,1]` 上的积分，
被积函数为 `t ↦ psi (n+t)` 与 `t ↦ psi (n+1+t)`；后者逐点严格小于前者
（`psi` 严格递减），故积分严格更小。 -/
lemma d_strictAnti : StrictAnti d := by
  intro n m hnm
  -- 只需证相邻一步 d (k+1) < d k，再由传递性
  have step : ∀ k : ℕ, d (k+1) < d k := by
    intro k
    rw [d_eq_integral (k+1), d_eq_integral k]
    -- 把两个积分都搬到 [0,1]
    have hcast : ((k+1 : ℕ) : ℝ) = (k:ℝ) + 1 := by push_cast; ring
    rw [hcast]
    have e1 : (∫ x in ((k:ℝ)+1)..((k:ℝ)+1 + 1), (2*x+1) ^ (-(3/2:ℝ)))
            = ∫ t in (0:ℝ)..1, (2*((k:ℝ)+1 + t)+1) ^ (-(3/2:ℝ)) := by
      rw [intervalIntegral.integral_comp_add_left (fun x => (2*x+1) ^ (-(3/2:ℝ))) ((k:ℝ)+1)]
      norm_num
    have e2 : (∫ x in (↑k : ℝ)..(↑k + 1), (2*x+1) ^ (-(3/2:ℝ)))
            = ∫ t in (0:ℝ)..1, (2*(↑k + t)+1) ^ (-(3/2:ℝ)) := by
      rw [intervalIntegral.integral_comp_add_left (fun x => (2*x+1) ^ (-(3/2:ℝ))) (↑k : ℝ)]
      norm_num
    rw [e1, e2]
    apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt (by norm_num)
    · -- 连续性：psi (↑k+1+t) = psi (↑(k+1)+t)
      exact contOn_shift1 k
    · exact contOn_shift k
    · intro t ht
      exact le_of_lt (psi_shift_lt k t (le_of_lt ht.1))
    · exact ⟨0, ⟨le_refl _, by norm_num⟩, psi_shift_lt k 0 le_rfl⟩
  induction hnm with
  | refl => exact step n
  | step hlt ih => exact lt_trans (step _) ih

/-! ### Lemma 1.3(3) —— 关键恒等式

论文：`u_n^2 - u_{n+1}^2 = 2 u_n^2 u_{n+1}^2 = d_n (u_n + u_{n+1})`。
-/

/-- Lemma 1.3(3)，第一段：`u_n^2 - u_{n+1}^2 = 2 u_n^2 u_{n+1}^2`。 -/
lemma u_sq_sub_sq (n : ℕ) :
    u n ^ 2 - u (n+1) ^ 2 = 2 * u n ^ 2 * u (n+1) ^ 2 := by
  rw [u_sq, u_sq]
  have hcast : (2 * ((n+1 : ℕ) : ℝ) + 1) = 2 * (n : ℝ) + 3 := by push_cast; ring
  rw [hcast]
  have h1 : 2 * (n : ℝ) + 1 ≠ 0 := ne_of_gt (two_mul_add_one_pos n)
  have h3 : 2 * (n : ℝ) + 3 ≠ 0 := by
    have : (0:ℝ) < 2 * (n : ℝ) + 3 := by
      have hp := two_mul_add_one_pos n
      linarith
    exact ne_of_gt this
  field_simp
  ring

/-- Lemma 1.3(3)，第二段：`u_n^2 - u_{n+1}^2 = d_n (u_n + u_{n+1})`。 -/
lemma u_sq_sub_sq_eq_d (n : ℕ) :
    u n ^ 2 - u (n+1) ^ 2 = d n * (u n + u (n+1)) := by
  unfold d
  ring

/-! ### Lemma 1.3(4) —— 乘积界

论文：`K ≥ 1` 且 `n ≥ K` 时 `2K u_n u_{n+1} ≤ 2K u_K u_{K+1} = 2K/√((2K+1)(2K+3)) < 1`。
-/

/-- `u` 的乘积版本单调性：`n ≥ K` 时 `u_n u_{n+1} ≤ u_K u_{K+1}`。 -/
lemma u_mul_u_le (K n : ℕ) (h : K ≤ n) : u n * u (n+1) ≤ u K * u (K+1) := by
  have h1 : u n ≤ u K := (u_strictAnti.antitone h)
  have h2 : u (n+1) ≤ u (K+1) := u_strictAnti.antitone (Nat.succ_le_succ h)
  exact mul_le_mul h1 h2 (le_of_lt (u_pos _)) (le_of_lt (u_pos _))

/-- 核心恒等式：`√a⁻¹ · √b⁻¹ = (√(a·b))⁻¹`。 -/
lemma sqrt_inv_mul_sqrt_inv (a b : ℝ) (ha : 0 < a) :
    Real.sqrt a⁻¹ * Real.sqrt b⁻¹ = (Real.sqrt (a * b))⁻¹ := by
  rw [Real.sqrt_inv, Real.sqrt_inv, ← mul_inv, ← Real.sqrt_mul (le_of_lt ha)]

lemma two_mul_u_mul_u (K : ℕ) :
    (2*(K:ℝ)) * u K * u (K+1) = 2*(K:ℝ) / Real.sqrt ((2*(K:ℝ)+1) * (2*(K:ℝ)+3)) := by
  have hcast : (2 * ((K+1 : ℕ) : ℝ) + 1) = 2 * (K : ℝ) + 3 := by push_cast; ring
  have hK1 : (0:ℝ) < 2 * (K:ℝ) + 1 := two_mul_add_one_pos K
  have huK : u K = Real.sqrt (2*(K:ℝ)+1)⁻¹ := by
    unfold u; rw [Real.rpow_neg_eq_inv_rpow, Real.sqrt_eq_rpow]
  have huK1 : u (K+1) = Real.sqrt (2*(K:ℝ)+3)⁻¹ := by
    unfold u; rw [hcast, Real.rpow_neg_eq_inv_rpow, Real.sqrt_eq_rpow]
  rw [huK, huK1, div_eq_mul_inv, mul_assoc, sqrt_inv_mul_sqrt_inv _ _ hK1]

/-- `2K/√((2K+1)(2K+3)) < 1`。 -/
lemma two_mul_u_mul_u_lt_one (K : ℕ) :
    (2*(K:ℝ)) / Real.sqrt ((2*(K:ℝ)+1) * (2*(K:ℝ)+3)) < 1 := by
  have hsq : (2*(K:ℝ))^2 < (2*(K:ℝ)+1) * (2*(K:ℝ)+3) := by
    have hKnn : (0:ℝ) ≤ (K:ℝ) := Nat.cast_nonneg K
    nlinarith
  have hprod_pos : 0 < (2*(K:ℝ)+1) * (2*(K:ℝ)+3) := by
    have h1 : (0:ℝ) < 2*(K:ℝ)+1 := two_mul_add_one_pos K
    have h2 : (0:ℝ) < 2*(K:ℝ)+3 := by linarith
    exact mul_pos h1 h2
  have h2K_nn : 0 ≤ 2*(K:ℝ) := by
    have : (0:ℕ) ≤ 2*K := Nat.zero_le _; exact_mod_cast this
  have hlt : 2*(K:ℝ) < Real.sqrt ((2*(K:ℝ)+1) * (2*(K:ℝ)+3)) :=
    (Real.lt_sqrt h2K_nn).mpr hsq
  rw [div_lt_one (Real.sqrt_pos.mpr hprod_pos)]
  exact hlt

/-- Lemma 1.3(4)。

论文陈述：`K ≥ 1` 且 `n ≥ K` 时
`2K u_n u_{n+1} ≤ 2K u_K u_{K+1} = 2K/√((2K+1)(2K+3)) < 1`。

这里的第一个不等号**对一切 `K ∈ ℕ` 成立**（不依赖 `K ≥ 1`），
因为 `u` 单调递减；`K ≥ 1` 在论文中服务于该式的第二段（`< 1`），
而后者经复核同样对一切 `K` 成立（见 `two_mul_u_mul_u_lt_one`）。
故本形式严格强于论文所陈述者。 -/
lemma lemma_1_3_4 (K n : ℕ) (h : K ≤ n) :
    2 * (K:ℝ) * (u n * u (n+1)) ≤ 2 * (K:ℝ) * (u K * u (K+1))
    ∧ 2 * (K:ℝ) * u K * u (K+1) < 1 := by
  have hKnn : (0:ℝ) ≤ 2 * (K:ℝ) := by
    have : (0:ℕ) ≤ 2*K := Nat.zero_le _; exact_mod_cast this
  refine ⟨mul_le_mul_of_nonneg_left (u_mul_u_le K n h) hKnn, ?_⟩
  rw [two_mul_u_mul_u K]
  exact two_mul_u_mul_u_lt_one K

/-- `u` 的非严格单调性：`n ≤ m ⇒ u m ≤ u n`。 -/
lemma u_anti : Antitone u := by
  intro a b hab
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact le_refl _
  · exact le_of_lt (u_strictAnti hlt)

/-! ### Lemma 1.3(1) 的后半句与 1.3(2) 的末句 —— 凸性

* `u` 严格凸（离散二阶差分 `u_m + u_{m+2} - 2u_{m+1} > 0`）：
  这正是 `d_m - d_{m+1} > 0`，即 `d` 严格递减。
* `d` 凸（`d_m + d_{m+2} - 2d_{m+1} ≥ 0`）：论文的证法——三个差分都写成 `[0,1]` 上的积分，
  被积函数 `psi` 在中点处的凸性（`psi_convex_mid`）逐点给出不等式，再积分。
-/

lemma d_pos (n : ℕ) : 0 < d n := by
  unfold d; linarith [u_strictAnti (Nat.lt_succ_self n)]

lemma d_anti : Antitone d := d_strictAnti.antitone

/-- Lemma 1.3(1) 后半句：`u` 严格凸（离散形式）。 -/
lemma u_convex (m : ℕ) : 2 * u (m+1) < u m + u (m+2) := by
  have h := d_strictAnti (Nat.lt_succ_self m)
  unfold d at h
  linarith

/-- `d_j` 搬到 `[0,1]` 上的积分。 -/
lemma d_eq_integral01 (j : ℕ) :
    d j = ∫ t in (0:ℝ)..1, (2*((j:ℝ)+t)+1) ^ (-(3/2:ℝ)) := by
  rw [d_eq_integral j]
  rw [intervalIntegral.integral_comp_add_left (fun x => (2*x+1) ^ (-(3/2:ℝ))) (j:ℝ)]
  norm_num

lemma contOn_shift_gen (c : ℝ) (hc : 0 ≤ c) :
    ContinuousOn (fun t : ℝ => (2*(c+t)+1) ^ (-(3/2:ℝ))) (Set.Icc 0 1) := by
  apply ContinuousOn.rpow_const
  · fun_prop
  · intro x hx; left; have : (0:ℝ) ≤ x := hx.1; linarith

lemma intInt_shift (c : ℝ) (hc : 0 ≤ c) :
    IntervalIntegrable (fun t : ℝ => (2*(c+t)+1) ^ (-(3/2:ℝ))) MeasureTheory.volume 0 1 :=
  (contOn_shift_gen c hc).intervalIntegrable_of_Icc (by norm_num)

/-- Lemma 1.3(2) 末句：`d` 凸，`d_m + d_{m+2} - 2 d_{m+1} ≥ 0`
（论文写法 `d_{m-1} + d_{m+1} - 2d_m ≥ 0`，`m ≥ 1`）。 -/
lemma d_convex (m : ℕ) : 2 * d (m+1) ≤ d m + d (m+2) := by
  rw [d_eq_integral01 m, d_eq_integral01 (m+1), d_eq_integral01 (m+2)]
  push_cast
  have hm : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
  rw [← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add (intInt_shift _ hm) (intInt_shift _ (by linarith))]
  apply intervalIntegral.integral_mono_on (by norm_num)
  · exact (intInt_shift _ (by linarith)).const_mul 2
  · exact (intInt_shift _ hm).add (intInt_shift _ (by linarith))
  · intro x hx
    have hx0 : (0:ℝ) ≤ x := hx.1
    have hA : (0:ℝ) < 2*((m:ℝ)+x)+1 := by linarith
    have hC : (0:ℝ) < 2*((m:ℝ)+2+x)+1 := by linarith
    have h := psi_convex_mid _ _ hA hC
    have e : (2*((m:ℝ)+x)+1 + (2*((m:ℝ)+2+x)+1))/2 = 2*((m:ℝ)+1+x)+1 := by ring
    rw [e] at h
    linarith

end Eliashberg
