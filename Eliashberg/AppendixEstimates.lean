import Eliashberg.Kernel
import Eliashberg.L2Bounds

/-!
# Appendix A.5：三条初等估计（Lemma A.7、A.8、A.9）与 A.5(iii)–(iv) 的有理数界

* **Lemma A.7**（`kernel_comparison`）：`0 ≤ m < N₁ ≤ n` ⇒ `1/(n−m)² ≤ (N₁+1)²/((n+1)²(N₁−m)²)`
* **Lemma A.8**（`midpoint_rule`、`midpoint_sum`）：凸函数的中点法则
  `f(a) ≤ ∫_{a−1/2}^{a+1/2} f`，以及 `∑_{k=K}^{K+n−1} f(k) ≤ ∫_{K−1/2}^{K+n−1/2} f`
* 尾和估计：`∑_{k≥K} k⁻² ≤ 2/(2K−1)`（`tail_inv_sq_le`），`∑_{k≥K} k⁻³ ≤ 1/(2(K−1/2)²)`（`tail_inv_cube_le`）
* **Lemma A.9**（`tail_T_le`）：`T(N₁) := ∑_{n≥N₁} 1/((n+1)⁴(2n+1)) ≤ 1/(N₁(2N₁+1)³)`
* **A.5(iii)**：`ψ'(n+1) := ∑_{k>n} k⁻² ≤ 2/(2n+1)`（`psi'_le`）
* **A.5(iv)**：`ζ(2) ≤ R₂ := 2089289/1270080`（`zeta2_le_R2`），`ζ(3) ≤ R₃ := 19236689947/16003008000`（`zeta3_le_R3`），
  以及 (A.3) `(7/8)R₃ + (3/2)R₂ − 3 < 13/25`（`A3_rational`，`norm_num`）

`ζ(s)` 这里一律写成 `∑'_{k≥0} 1/(k+1)^s`（`zeta2`、`zeta3`），不依赖 mathlib 的 `riemannZeta`。
-/

namespace Eliashberg

open MeasureTheory intervalIntegral Set Filter Topology

/-! ### Lemma A.7 -/

/-- **Lemma A.7（核比较）**。 -/
theorem kernel_comparison (m N₁ n : ℕ) (hm : m < N₁) (hn : N₁ ≤ n) :
    (1:ℝ) / ((n:ℝ) - m) ^ 2 ≤ ((N₁:ℝ) + 1) ^ 2 / (((n:ℝ) + 1) ^ 2 * ((N₁:ℝ) - m) ^ 2) := by
  have hm' : (m:ℝ) < N₁ := by exact_mod_cast hm
  have hn' : (N₁:ℝ) ≤ n := by exact_mod_cast hn
  have h1 : 0 < (n:ℝ) - m := by linarith
  have h2 : 0 < (N₁:ℝ) - m := by linarith
  have h3 : 0 < (n:ℝ) + 1 := by linarith
  have h4 : 0 < (N₁:ℝ) + 1 := by linarith
  -- `(n−m)(N₁+1) ≥ (n+1)(N₁−m)`，两边正，可平方
  have hkey : ((n:ℝ) + 1) * ((N₁:ℝ) - m) ≤ ((n:ℝ) - m) * ((N₁:ℝ) + 1) := by
    have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have := pow_le_pow_left₀ (by positivity) hkey 2
  nlinarith [this]

/-! ### Lemma A.8：中点法则 -/

/-- **Lemma A.8（中点法则，逐点）**：`f` 在 `[c,∞)` 凸连续，`c ≤ a − 1/2` ⇒ `f(a) ≤ ∫_{a−1/2}^{a+1/2} f`。 -/
theorem midpoint_rule (c a : ℝ) (f : ℝ → ℝ) (hf : ConvexOn ℝ (Ici c) f) (hc : ContinuousOn f (Ici c))
    (ha : c ≤ a - 1/2) : f a ≤ ∫ x in (a - 1/2)..(a + 1/2), f x := by
  have hsub : Icc (a - 1/2) (a + 1/2) ⊆ Ici c := fun x hx => by
    simp only [mem_Icc] at hx; simp only [mem_Ici]; linarith [hx.1]
  have hμ : (volume.restrict (Icc (a - 1/2) (a + 1/2))).real univ = 1 := by
    simp [measureReal_def, Real.volume_Icc]; norm_num
  have hfin : IsFiniteMeasure (volume.restrict (Icc (a - 1/2) (a + 1/2))) := by
    constructor; rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top
  have hne : NeZero (volume.restrict (Icc (a - 1/2) (a + 1/2))) := by
    constructor; intro h
    have := congrArg (fun μ : Measure ℝ => μ.real univ) h
    simp only [hμ] at this
    simp at this
  have hint1 : Integrable (fun x : ℝ => x) (volume.restrict (Icc (a - 1/2) (a + 1/2))) :=
    (continuous_id.integrableOn_Icc)
  have hint2 : Integrable (f ∘ fun x : ℝ => x) (volume.restrict (Icc (a - 1/2) (a + 1/2))) :=
    (hc.mono hsub).integrableOn_Icc
  have hJ := hf.map_average_le hc isClosed_Ici
    ((ae_restrict_mem measurableSet_Icc).mono (fun x hx => hsub hx)) hint1 hint2
  have e1 : (⨍ x, x ∂(volume.restrict (Icc (a - 1/2) (a + 1/2)))) = a := by
    rw [average_eq, hμ, inv_one, one_smul, integral_Icc_eq_integral_Ioc, ← integral_of_le (by linarith)]
    rw [integral_id]; ring
  have e2 : (⨍ x, f x ∂(volume.restrict (Icc (a - 1/2) (a + 1/2)))) = ∫ x in (a - 1/2)..(a + 1/2), f x := by
    rw [average_eq, hμ, inv_one, one_smul, integral_Icc_eq_integral_Ioc, ← integral_of_le (by linarith)]
  have hJ' : f (⨍ x, x ∂(volume.restrict (Icc (a - 1/2) (a + 1/2))))
      ≤ ⨍ x, f x ∂(volume.restrict (Icc (a - 1/2) (a + 1/2))) := hJ
  rw [e1, e2] at hJ'
  exact hJ'

/-- **Lemma A.8（求和形式）**：`∑_{i<n} f(K+i) ≤ ∫_{K−1/2}^{K+n−1/2} f`。 -/
theorem midpoint_sum (c : ℝ) (f : ℝ → ℝ) (hf : ConvexOn ℝ (Ici c) f) (hc : ContinuousOn f (Ici c))
    (K : ℕ) (hK : c ≤ (K:ℝ) - 1/2) (n : ℕ) :
    ∑ i ∈ Finset.range n, f ((K:ℝ) + i) ≤ ∫ x in ((K:ℝ) - 1/2)..((K:ℝ) + n - 1/2), f x := by
  have hint : ∀ k < n, IntervalIntegrable f volume ((K:ℝ) + k - 1/2) ((K:ℝ) + (k+1:ℕ) - 1/2) := by
    intro k _
    apply ContinuousOn.intervalIntegrable
    apply hc.mono
    intro x hx
    rw [uIcc_of_le (by push_cast; linarith)] at hx
    simp only [mem_Icc] at hx; simp only [mem_Ici]
    have : (0:ℝ) ≤ k := Nat.cast_nonneg k
    linarith [hx.1]
  have h := sum_integral_adjacent_intervals (f := f) (μ := volume) (a := fun k : ℕ => (K:ℝ) + k - 1/2)
    (n := n) hint
  simp only [Nat.cast_zero, add_zero] at h
  rw [← h]
  apply Finset.sum_le_sum
  intro i _
  have := midpoint_rule c ((K:ℝ) + i) f hf hc (by have : (0:ℝ) ≤ i := Nat.cast_nonneg i; linarith)
  convert this using 2 <;> push_cast <;> ring

/-! ### 幂函数的凸性与积分 -/

lemma convexOn_zpow_Ici (m : ℤ) (c : ℝ) (hc : 0 < c) :
    ConvexOn ℝ (Ici c) (fun x : ℝ => x ^ m) :=
  (convexOn_zpow m).subset (fun x hx => lt_of_lt_of_le hc hx) (convex_Ici c)

lemma continuousOn_zpow_Ici (m : ℤ) (c : ℝ) (hc : 0 < c) :
    ContinuousOn (fun x : ℝ => x ^ m) (Ici c) := by
  apply ContinuousOn.zpow₀ continuousOn_id
  intro x hx; left; exact ne_of_gt (lt_of_lt_of_le hc hx)

lemma integral_zpow_neg (m : ℕ) (hm : 2 ≤ m) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∫ x in a..b, x ^ (-(m:ℤ)) = (a ^ (-(m:ℤ) + 1) - b ^ (-(m:ℤ) + 1)) / ((m:ℝ) - 1) := by
  have h0 : (0:ℝ) ∉ uIcc a b := by
    rw [uIcc_of_le hab]; intro h; simp only [mem_Icc] at h; linarith
  rw [integral_zpow (Or.inr ⟨by omega, h0⟩)]
  have : ((-(m:ℤ) : ℤ) : ℝ) + 1 = -((m:ℝ) - 1) := by push_cast; ring
  rw [this]
  have hm1 : (m:ℝ) - 1 ≠ 0 := by
    have : (2:ℝ) ≤ m := by exact_mod_cast hm
    linarith
  rw [div_neg]
  ring

/-! ### `∑_{k≥K} k⁻ˢ` 的尾和估计 -/

/-- `∑_{i<n} (K+i)⁻² ≤ 1/(K−1/2)`，`K ≥ 1`。 -/
lemma partial_inv_sq_le (K : ℕ) (hK : 1 ≤ K) (n : ℕ) :
    ∑ i ∈ Finset.range n, 1 / ((K:ℝ) + i) ^ 2 ≤ 1 / ((K:ℝ) - 1/2) := by
  have hK' : (1:ℝ) ≤ K := by exact_mod_cast hK
  have hpos : (0:ℝ) < (K:ℝ) - 1/2 := by linarith
  have h := midpoint_sum (1/2) (fun x => x ^ (-2:ℤ)) (convexOn_zpow_Ici (-2) _ (by norm_num))
    (continuousOn_zpow_Ici (-2) _ (by norm_num)) K (by linarith) n
  have e : ∀ i : ℕ, ((K:ℝ) + i) ^ (-2:ℤ) = 1 / ((K:ℝ) + i) ^ 2 := by
    intro i; rw [zpow_neg, zpow_ofNat, one_div]
  simp only [e] at h
  refine h.trans ?_
  rw [show (-2:ℤ) = -((2:ℕ):ℤ) by norm_num,
    integral_zpow_neg 2 le_rfl _ _ hpos (by linarith [Nat.cast_nonneg (α := ℝ) n])]
  have hb : (0:ℝ) < (K:ℝ) + n - 1/2 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  norm_num
  have : 0 ≤ ((K:ℝ) + n - 1/2)⁻¹ := by positivity
  linarith

/-- `∑_{k≥K} k⁻² ≤ 2/(2K−1)`（`K ≥ 1`），写成 `∑'_{i} (K+i)⁻²`。 -/
theorem tail_inv_sq_le (K : ℕ) (hK : 1 ≤ K) :
    ∑' i : ℕ, 1 / ((K:ℝ) + i) ^ 2 ≤ 2 / (2 * (K:ℝ) - 1) := by
  have hs : Summable (fun i : ℕ => 1 / ((K:ℝ) + i) ^ 2) := by
    have := (summable_nat_add_iff K).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    refine this.congr (fun i => ?_)
    push_cast; ring_nf
  have := hs.tsum_le_of_sum_range_le (partial_inv_sq_le K hK)
  refine this.trans (le_of_eq ?_)
  have hK' : (1:ℝ) ≤ K := by exact_mod_cast hK
  field_simp

/-- `∑_{i<n} (K+i)⁻³ ≤ 1/(2(K−1/2)²)`，`K ≥ 1`。 -/
lemma partial_inv_cube_le (K : ℕ) (hK : 1 ≤ K) (n : ℕ) :
    ∑ i ∈ Finset.range n, 1 / ((K:ℝ) + i) ^ 3 ≤ 1 / (2 * ((K:ℝ) - 1/2) ^ 2) := by
  have hK' : (1:ℝ) ≤ K := by exact_mod_cast hK
  have hpos : (0:ℝ) < (K:ℝ) - 1/2 := by linarith
  have h := midpoint_sum (1/2) (fun x => x ^ (-3:ℤ)) (convexOn_zpow_Ici (-3) _ (by norm_num))
    (continuousOn_zpow_Ici (-3) _ (by norm_num)) K (by linarith) n
  have e : ∀ i : ℕ, ((K:ℝ) + i) ^ (-3:ℤ) = 1 / ((K:ℝ) + i) ^ 3 := by
    intro i; rw [zpow_neg, zpow_ofNat, one_div]
  simp only [e] at h
  refine h.trans ?_
  rw [show (-3:ℤ) = -((3:ℕ):ℤ) by norm_num,
    integral_zpow_neg 3 (by norm_num) _ _ hpos (by linarith [Nat.cast_nonneg (α := ℝ) n])]
  have hb : (0:ℝ) < (K:ℝ) + n - 1/2 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  norm_num
  have h2 : 0 ≤ (((K:ℝ) + n - 1/2) ^ 2)⁻¹ := by positivity
  linarith

theorem tail_inv_cube_le (K : ℕ) (hK : 1 ≤ K) :
    ∑' i : ℕ, 1 / ((K:ℝ) + i) ^ 3 ≤ 1 / (2 * ((K:ℝ) - 1/2) ^ 2) := by
  have hs : Summable (fun i : ℕ => 1 / ((K:ℝ) + i) ^ 3) := by
    have := (summable_nat_add_iff K).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3))
    refine this.congr (fun i => ?_)
    push_cast; ring_nf
  exact hs.tsum_le_of_sum_range_le (partial_inv_cube_le K hK)

/-! ### `ψ'(n+1)` 与 `ζ(2)`、`ζ(3)` 的有理数上界 -/

/-- `ψ'(n+1) := ∑_{k>n} k⁻² = ∑'_{i} (n+1+i)⁻²`。 -/
noncomputable def psi' (n : ℕ) : ℝ := ∑' i : ℕ, 1 / (((n:ℝ) + 1) + i) ^ 2

/-- **A.5(iii)**：`ψ'(n+1) ≤ 2/(2n+1)`。 -/
theorem psi'_le (n : ℕ) : psi' n ≤ 2 / (2 * (n:ℝ) + 1) := by
  unfold psi'
  have := tail_inv_sq_le (n+1) (by omega)
  push_cast at this
  convert this using 2
  ring

lemma psi'_nonneg (n : ℕ) : 0 ≤ psi' n := tsum_nonneg (fun i => by positivity)

/-- `ζ(2) := ∑'_{k≥0} 1/(k+1)²`。 -/
noncomputable def zeta2 : ℝ := ∑' k : ℕ, 1 / ((k:ℝ) + 1) ^ 2

/-- `ζ(3) := ∑'_{k≥0} 1/(k+1)³`。 -/
noncomputable def zeta3 : ℝ := ∑' k : ℕ, 1 / ((k:ℝ) + 1) ^ 3

lemma zeta2_eq_pi : zeta2 = Real.pi ^ 2 / 6 := hasSum_zeta_two_shift.tsum_eq

lemma zeta3_summable : Summable (fun k : ℕ => 1 / ((k:ℝ) + 1) ^ 3) := by
  have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3))
  simpa using this

/-- 头 `K` 项 + 尾和：`ζ(s) = H_K^{(s)} + ∑_{k>K} k⁻ˢ`。 -/
lemma zeta2_split (K : ℕ) :
    zeta2 = ∑ k ∈ Finset.range K, 1 / ((k:ℝ) + 1) ^ 2 + ∑' i : ℕ, 1 / (((K:ℝ) + 1) + i) ^ 2 := by
  unfold zeta2
  rw [← hasSum_zeta_two_shift.summable.sum_add_tsum_nat_add K]
  congr 1
  congr 1; funext i; push_cast; ring_nf

lemma zeta3_split (K : ℕ) :
    zeta3 = ∑ k ∈ Finset.range K, 1 / ((k:ℝ) + 1) ^ 3 + ∑' i : ℕ, 1 / (((K:ℝ) + 1) + i) ^ 3 := by
  unfold zeta3
  rw [← zeta3_summable.sum_add_tsum_nat_add K]
  congr 1
  congr 1; funext i; push_cast; ring_nf

/-- **A.5(iv)**：`ζ(2) ≤ H₁₀^{(2)} + 1/(10 + 1/2) = 2089289/1270080 =: R₂`。 -/
theorem zeta2_le_R2 : zeta2 ≤ 2089289 / 1270080 := by
  rw [zeta2_split 10]
  have htail := tail_inv_sq_le 11 (by norm_num)
  have e : (∑' i : ℕ, 1 / (((10:ℕ):ℝ) + 1 + i) ^ 2) = ∑' i : ℕ, 1 / (((11:ℕ):ℝ) + i) ^ 2 := by
    congr 1; funext i; norm_num
  rw [e]
  have hhead : ∑ k ∈ Finset.range 10, 1 / ((k:ℝ) + 1) ^ 2 = 1968329 / 1270080 := by
    norm_num [Finset.sum_range_succ]
  rw [hhead]
  norm_num at htail ⊢
  linarith

/-- **A.5(iv)**：`ζ(3) ≤ H₁₀^{(3)} + 1/(2(10+1/2)²) = 19236689947/16003008000 =: R₃`。 -/
theorem zeta3_le_R3 : zeta3 ≤ 19236689947 / 16003008000 := by
  rw [zeta3_split 10]
  have htail := tail_inv_cube_le 11 (by norm_num)
  have e : (∑' i : ℕ, 1 / (((10:ℕ):ℝ) + 1 + i) ^ 3) = ∑' i : ℕ, 1 / (((11:ℕ):ℝ) + i) ^ 3 := by
    congr 1; funext i; norm_num
  rw [e]
  have hhead : ∑ k ∈ Finset.range 10, 1 / ((k:ℝ) + 1) ^ 3 = 19164113947 / 16003008000 := by
    norm_num [Finset.sum_range_succ]
  rw [hhead]
  norm_num at htail ⊢
  linarith

/-- **(A.3)**：`(7/8)R₃ + (3/2)R₂ − 3 = 9497876347/18289152000 < 13/25`。 -/
theorem A3_rational :
    (7:ℝ)/8 * (19236689947/16003008000) + 3/2 * (2089289/1270080) - 3 < 13/25 := by norm_num

/-! ### Lemma A.9：尾和 `T(N₁)` -/

/-- `h(x) := 1/((x+1)⁴(2x+1))`。 -/
noncomputable def hA9 (x : ℝ) : ℝ := ((x + 1) ^ (-4:ℤ)) * ((2 * x + 1) ^ (-1:ℤ))

lemma hA9_eq (x : ℝ) (hx : -1/2 < x) : hA9 x = 1 / ((x + 1) ^ 4 * (2 * x + 1)) := by
  unfold hA9
  rw [zpow_neg, zpow_neg, zpow_ofNat, zpow_one]
  have h1 : (0:ℝ) < x + 1 := by linarith
  have h2 : (0:ℝ) < 2 * x + 1 := by linarith
  field_simp

/-- `hA9` 在 `[c, ∞)`（`c > −1/2`）上凸：两个凸、非负、同向单调（都递减）的因子之积。
论文用对数凸性；这里用 mathlib 的 `ConvexOn.mul`（单调同向的非负凸函数之积仍凸）。 -/
lemma hA9_convexOn (c : ℝ) (hc : -1/2 < c) : ConvexOn ℝ (Ici c) hA9 := by
  have h1 : ConvexOn ℝ (Ici c) (fun x : ℝ => (x + 1) ^ (-4:ℤ)) := by
    have hz := convexOn_zpow (𝕜 := ℝ) (-4)
    refine ⟨convex_Ici c, ?_⟩
    intro x hx y hy a b ha hb hab
    have hx' : x + 1 ∈ Ioi (0:ℝ) := by simp only [mem_Ioi]; simp only [mem_Ici] at hx; linarith
    have hy' : y + 1 ∈ Ioi (0:ℝ) := by simp only [mem_Ioi]; simp only [mem_Ici] at hy; linarith
    have := hz.2 hx' hy' ha hb hab
    simp only [smul_eq_mul] at this ⊢
    have e : a * x + b * y + 1 = a * (x + 1) + b * (y + 1) := by linarith [hab]
    rw [e]; exact this
  have h2 : ConvexOn ℝ (Ici c) (fun x : ℝ => (2 * x + 1) ^ (-1:ℤ)) := by
    have hz := convexOn_zpow (𝕜 := ℝ) (-1)
    refine ⟨convex_Ici c, ?_⟩
    intro x hx y hy a b ha hb hab
    have hx' : 2 * x + 1 ∈ Ioi (0:ℝ) := by simp only [mem_Ioi]; simp only [mem_Ici] at hx; linarith
    have hy' : 2 * y + 1 ∈ Ioi (0:ℝ) := by simp only [mem_Ioi]; simp only [mem_Ici] at hy; linarith
    have := hz.2 hx' hy' ha hb hab
    simp only [smul_eq_mul] at this ⊢
    have e : 2 * (a * x + b * y) + 1 = a * (2 * x + 1) + b * (2 * y + 1) := by linarith [hab]
    rw [e]; exact this
  have hp1 : ∀ x ∈ Ici c, 0 ≤ (x + 1) ^ (-4:ℤ) := by
    intro x hx; simp only [mem_Ici] at hx; have : 0 < x + 1 := by linarith
    positivity
  have hp2 : ∀ x ∈ Ici c, 0 ≤ (2 * x + 1) ^ (-1:ℤ) := by
    intro x hx; simp only [mem_Ici] at hx; have : 0 < 2 * x + 1 := by linarith
    positivity
  have hm1 : AntitoneOn (fun x : ℝ => (x + 1) ^ (-4:ℤ)) (Ici c) := by
    intro x hx y hy hxy
    simp only [mem_Ici] at hx hy
    have hx1 : 0 < x + 1 := by linarith
    simp only [zpow_neg, zpow_ofNat]
    apply inv_anti₀ (by positivity)
    exact pow_le_pow_left₀ (le_of_lt hx1) (by linarith) 4
  have hm2 : AntitoneOn (fun x : ℝ => (2 * x + 1) ^ (-1:ℤ)) (Ici c) := by
    intro x hx y hy hxy
    simp only [mem_Ici] at hx hy
    have hx1 : 0 < 2 * x + 1 := by linarith
    simp only [zpow_neg, zpow_one]
    apply inv_anti₀ (by positivity)
    linarith
  exact ConvexOn.mul h1 h2 hp1 hp2 (hm1.monovaryOn hm2)

lemma hA9_continuousOn (c : ℝ) (hc : -1/2 < c) : ContinuousOn hA9 (Ici c) := by
  unfold hA9
  apply ContinuousOn.mul
  · apply ContinuousOn.zpow₀ (by fun_prop)
    intro x hx; left; simp only [mem_Ici] at hx; linarith
  · apply ContinuousOn.zpow₀ (by fun_prop)
    intro x hx; left; simp only [mem_Ici] at hx; linarith

/-- `x + 1 ≥ a`（`a ≥ 1`）时 `hA9 x ≤ (2a/(2a−1)) · (1/2) (x+1)^{-5}`，
论文的 `2t⁵ − t⁴ ≥ 2t⁵(2a−1)/(2a)`（`t = x + 1 ≥ a`）。 -/
lemma hA9_le (a x : ℝ) (ha : 1 ≤ a) (hx : a - 1 ≤ x) :
    hA9 x ≤ (2 * a / (2 * a - 1)) * (1 / 2) * (x + 1) ^ (-5:ℤ) := by
  have hx1 : 0 < x + 1 := by linarith
  have hx2 : 0 < 2 * x + 1 := by linarith
  have ha1 : 0 < 2 * a - 1 := by linarith
  rw [hA9_eq x (by linarith), zpow_neg, zpow_ofNat]
  -- `(x+1)⁴(2x+1) = 2(x+1)⁵ − (x+1)⁴ ≥ (x+1)⁵ (2a−1)/a`
  have hkey : (x + 1) ^ 5 * ((2 * a - 1) / a) ≤ (x + 1) ^ 4 * (2 * x + 1) := by
    have hxa : a ≤ x + 1 := by linarith
    have h4 : 0 < (x + 1) ^ 4 := by positivity
    have : (x + 1) ^ 5 * ((2 * a - 1) / a) = (x + 1) ^ 4 * ((x + 1) * (2 - 1 / a)) := by
      field_simp
    rw [this]
    apply mul_le_mul_of_nonneg_left _ (le_of_lt h4)
    have h5 : 1 / a ≤ 1 := by rw [div_le_one (by linarith)]; exact ha
    have h6 : 2 * x + 1 = (x + 1) * 2 - 1 := by ring
    have h7 : (x + 1) * (1 / a) ≥ 1 := by
      rw [ge_iff_le, ← div_eq_mul_one_div, le_div_iff₀ (by linarith)]; linarith
    nlinarith
  have hpos : 0 < (x + 1) ^ 4 * (2 * x + 1) := by positivity
  have hpos5 : 0 < (x + 1) ^ 5 * ((2 * a - 1) / a) := by positivity
  calc 1 / ((x + 1) ^ 4 * (2 * x + 1)) ≤ 1 / ((x + 1) ^ 5 * ((2 * a - 1) / a)) :=
        one_div_le_one_div_of_le hpos5 hkey
    _ = (2 * a / (2 * a - 1)) * (1 / 2) * ((x + 1) ^ 5)⁻¹ := by
        field_simp

/-- `T(N₁) := ∑_{n≥N₁} 1/((n+1)⁴(2n+1))`。 -/
noncomputable def TA9 (N₁ : ℕ) : ℝ := ∑' i : ℕ, 1 / ((((N₁:ℝ) + i) + 1) ^ 4 * (2 * ((N₁:ℝ) + i) + 1))

lemma TA9_summable (N₁ : ℕ) :
    Summable (fun i : ℕ => 1 / ((((N₁:ℝ) + i) + 1) ^ 4 * (2 * ((N₁:ℝ) + i) + 1))) := by
  apply Summable.of_nonneg_of_le (fun i => by positivity) _ hasSum_zeta_two_shift.summable
  intro i
  have hN : (0:ℝ) ≤ N₁ := Nat.cast_nonneg N₁
  have hi : (0:ℝ) ≤ i := Nat.cast_nonneg i
  apply one_div_le_one_div_of_le (by positivity)
  have h1 : ((i:ℝ) + 1) ^ 2 ≤ (((N₁:ℝ) + i) + 1) ^ 4 := by
    have : (i:ℝ) + 1 ≤ ((N₁:ℝ) + i) + 1 := by linarith
    have h2 : ((i:ℝ) + 1) ^ 2 ≤ (((N₁:ℝ) + i) + 1) ^ 2 := pow_le_pow_left₀ (by linarith) this 2
    have h3 : (((N₁:ℝ) + i) + 1) ^ 2 ≤ (((N₁:ℝ) + i) + 1) ^ 4 := by
      have : 1 ≤ ((N₁:ℝ) + i) + 1 := by linarith
      exact pow_le_pow_right₀ this (by norm_num)
    linarith
  nlinarith [show (1:ℝ) ≤ 2 * ((N₁:ℝ) + i) + 1 by linarith]

/-- **Lemma A.9（尾和）**：`N₁ ≥ 1` ⇒ `T(N₁) ≤ 1/(N₁(2N₁+1)³)`。 -/
theorem tail_T_le (N₁ : ℕ) (hN : 1 ≤ N₁) : TA9 N₁ ≤ 1 / ((N₁:ℝ) * (2 * (N₁:ℝ) + 1) ^ 3) := by
  have hN' : (1:ℝ) ≤ N₁ := by exact_mod_cast hN
  set a : ℝ := (N₁:ℝ) + 1/2 with ha
  have ha1 : 1 ≤ a := by linarith
  have hc : -1/2 < (N₁:ℝ) - 1/2 := by linarith
  -- 中点法则：`∑_{i<n} hA9(N₁+i) ≤ ∫_{N₁−1/2}^{N₁+n−1/2} hA9`
  have hmid : ∀ n : ℕ, ∑ i ∈ Finset.range n, hA9 ((N₁:ℝ) + i)
      ≤ ∫ x in ((N₁:ℝ) - 1/2)..((N₁:ℝ) + n - 1/2), hA9 x :=
    fun n => midpoint_sum ((N₁:ℝ) - 1/2) hA9 (hA9_convexOn _ hc) (hA9_continuousOn _ hc) N₁ le_rfl n
  -- 积分上界：`∫ hA9 ≤ (2a/(2a−1))(1/2) ∫ (x+1)^{-5} ≤ (2a/(2a−1))(1/2) · a^{-4}/4`
  have hbound : ∀ n : ℕ, ∫ x in ((N₁:ℝ) - 1/2)..((N₁:ℝ) + n - 1/2), hA9 x
      ≤ (2 * a / (2 * a - 1)) * (1 / 2) * (a ^ (-4:ℤ) / 4) := by
    intro n
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
    have hle : (N₁:ℝ) - 1/2 ≤ (N₁:ℝ) + n - 1/2 := by linarith
    have hint1 : IntervalIntegrable hA9 volume ((N₁:ℝ) - 1/2) ((N₁:ℝ) + n - 1/2) := by
      apply ContinuousOn.intervalIntegrable
      apply (hA9_continuousOn _ hc).mono
      intro x hx; rw [uIcc_of_le hle] at hx; simp only [mem_Icc] at hx; simp only [mem_Ici]; linarith [hx.1]
    have hint2 : IntervalIntegrable (fun x : ℝ => (2 * a / (2 * a - 1)) * (1 / 2) * (x + 1) ^ (-5:ℤ))
        volume ((N₁:ℝ) - 1/2) ((N₁:ℝ) + n - 1/2) := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.zpow₀ (by fun_prop)
      intro x hx; left; rw [uIcc_of_le hle] at hx; simp only [mem_Icc] at hx; linarith [hx.1]
    calc ∫ x in ((N₁:ℝ) - 1/2)..((N₁:ℝ) + n - 1/2), hA9 x
        ≤ ∫ x in ((N₁:ℝ) - 1/2)..((N₁:ℝ) + n - 1/2), (2 * a / (2 * a - 1)) * (1 / 2) * (x + 1) ^ (-5:ℤ) := by
          apply integral_mono_on hle hint1 hint2
          intro x hx; simp only [mem_Icc] at hx
          exact hA9_le a x ha1 (by rw [ha]; linarith [hx.1])
      _ = (2 * a / (2 * a - 1)) * (1 / 2) * ∫ x in ((N₁:ℝ) - 1/2)..((N₁:ℝ) + n - 1/2), (x + 1) ^ (-5:ℤ) :=
          integral_const_mul _ _
      _ ≤ (2 * a / (2 * a - 1)) * (1 / 2) * (a ^ (-4:ℤ) / 4) := by
          apply mul_le_mul_of_nonneg_left _ (by
            have : 0 < 2 * a - 1 := by linarith
            positivity)
          rw [integral_comp_add_right (fun x => x ^ (-5:ℤ)) 1]
          have e1 : (N₁:ℝ) - 1/2 + 1 = a := by rw [ha]; ring
          have e2 : (N₁:ℝ) + n - 1/2 + 1 = a + n := by rw [ha]; ring
          rw [e1, e2, show (-5:ℤ) = -((5:ℕ):ℤ) by norm_num,
            integral_zpow_neg 5 (by norm_num) a (a + n) (by linarith) (by linarith)]
          have hb : 0 < a + n := by linarith
          have e3 : (-((5:ℕ):ℤ) + 1) = (-4:ℤ) := by norm_num
          rw [e3]
          norm_num
          have h5 : 0 ≤ ((a + n) ^ 4)⁻¹ := by positivity
          apply div_le_div_of_nonneg_right _ (by norm_num)
          linarith
  -- 收尾：`T(N₁) = ∑' hA9(N₁+i) ≤ 上界 = 1/(N₁(2N₁+1)³)`
  have hs := TA9_summable N₁
  have hT : TA9 N₁ ≤ (2 * a / (2 * a - 1)) * (1 / 2) * (a ^ (-4:ℤ) / 4) := by
    unfold TA9
    apply hs.tsum_le_of_sum_range_le
    intro n
    have := (hmid n).trans (hbound n)
    refine le_trans (le_of_eq ?_) this
    apply Finset.sum_congr rfl; intro i _
    rw [hA9_eq _ (by linarith [Nat.cast_nonneg (α := ℝ) i])]
  refine hT.trans (le_of_eq ?_)
  rw [ha, zpow_neg, zpow_ofNat]
  have h1 : (2 * ((N₁:ℝ) + 1/2) - 1) ≠ 0 := by linarith
  have h2 : ((N₁:ℝ) + 1/2) ≠ 0 := by linarith
  have h3 : (2 * (N₁:ℝ) + 1) ≠ 0 := by linarith
  have h4 : (N₁:ℝ) ≠ 0 := by linarith
  field_simp
  ring

end Eliashberg
