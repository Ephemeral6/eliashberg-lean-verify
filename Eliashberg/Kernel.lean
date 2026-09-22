import Eliashberg.Basic

/-!
# §0.2 的核函数 `[[k]](ϖ) := ϖ²/(k²+ϖ²)`：实分析事实

论文 §0.2、Lemma 0.1 的证明、Corollary 1.6 末段、(S2)、Theorem B 的 `χ`。
全部是关于一个显式有理函数的初等事实，不涉及测度。

* `kern_pos`、`kern_lt_one`：`0 < [[k]](ϖ) < 1`（`k ≥ 1`，`ϖ > 0`）
* `kern_le_div`：`[[k]](ϖ) ≤ ϖ²/k²`
* `kern_strictAnti_k`、`kern_tendsto_zero_k`：`k ↦ [[k]](ϖ)` 严格递减、趋于 0
* `kern_strictMonoOn_ϖ`、`kern_continuous`：`ϖ ↦ [[k]](ϖ)` 在 `[0,∞)` 严格递增、连续
* `kern_tendsto_one_atTop`：`[[k]](ϖ) → 1`（`ϖ → ∞`），即 Lemma 0.1.4 的被积函数极限
* `kern_summable`、`kern_tsum_le`：`∑_{k≥1} [[k]](ϖ) ≤ (π²/6) ϖ²`（Lemma 0.1.2 的被积函数版本）
* `kern_div_sq_eq`、`kern_S2`：(S2) 的逐点形式 `[[k]](ϖ)/ϖ² = k⁻² − ϖ²/(k²(k²+ϖ²))`
* `kern_sub_le`：`[[k]](ϖ') − [[k]](ϖ) ≤ (ϖ'² − ϖ²)/k²`（Corollary 1.6 末段）
* `chi`、`chi_strictConcaveOn`：Theorem B 的 `χ(x) = x/(y+x)` 在 `[0,∞)` 严格凹
* `kern_eq_chi`：`[[k]](ω/2πT) = χ_{(2πTk)²}(ω²)`
-/

namespace Eliashberg

open Filter Topology

/-- `[[k]](ϖ) := ϖ²/(k²+ϖ²)`。 -/
noncomputable def kern (k : ℕ) (ϖ : ℝ) : ℝ := ϖ ^ 2 / ((k:ℝ) ^ 2 + ϖ ^ 2)

lemma kern_nonneg (k : ℕ) (ϖ : ℝ) : 0 ≤ kern k ϖ := by
  unfold kern; positivity

lemma kern_pos (k : ℕ) (ϖ : ℝ) (hϖ : ϖ ≠ 0) : 0 < kern k ϖ := by
  unfold kern
  apply div_pos (by positivity)
  have : 0 < ϖ ^ 2 := by positivity
  positivity

lemma kern_le_one (k : ℕ) (ϖ : ℝ) : kern k ϖ ≤ 1 := by
  unfold kern
  rcases eq_or_ne ((k:ℝ) ^ 2 + ϖ ^ 2) 0 with h | h
  · rw [h, div_zero]; norm_num
  · rw [div_le_one (lt_of_le_of_ne (by positivity) (Ne.symm h))]
    linarith [sq_nonneg (k:ℝ)]

lemma kern_lt_one (k : ℕ) (hk : 1 ≤ k) (ϖ : ℝ) : kern k ϖ < 1 := by
  unfold kern
  have hk' : (0:ℝ) < (k:ℝ) ^ 2 := by
    have : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    positivity
  rw [div_lt_one (by positivity)]
  linarith

/-- `[[k]](ϖ) ≤ ϖ²/k²`。 -/
lemma kern_le_div (k : ℕ) (hk : 1 ≤ k) (ϖ : ℝ) : kern k ϖ ≤ ϖ ^ 2 / (k:ℝ) ^ 2 := by
  unfold kern
  have hk' : (0:ℝ) < (k:ℝ) ^ 2 := by
    have : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    positivity
  apply div_le_div_of_nonneg_left (by positivity) hk'
  linarith [sq_nonneg ϖ]

/-- `k ↦ [[k]](ϖ)` 严格递减（`ϖ ≠ 0`）。 -/
lemma kern_strictAnti_k (ϖ : ℝ) (hϖ : ϖ ≠ 0) : StrictAnti (fun k : ℕ => kern k ϖ) := by
  intro a b hab
  simp only [kern]
  have hϖ2 : 0 < ϖ ^ 2 := by positivity
  have hab' : (a:ℝ) < (b:ℝ) := by exact_mod_cast hab
  have ha : (0:ℝ) ≤ (a:ℝ) := Nat.cast_nonneg a
  have hsq : (a:ℝ) ^ 2 < (b:ℝ) ^ 2 := by nlinarith
  apply div_lt_div_of_pos_left hϖ2 (by positivity)
  linarith

/-- `[[k]](ϖ) → 0`（`k → ∞`）：由 `0 ≤ [[k]](ϖ) ≤ ϖ²/k²` 夹逼。 -/
lemma kern_tendsto_zero_k (ϖ : ℝ) : Tendsto (fun k : ℕ => kern k ϖ) atTop (𝓝 0) := by
  have hup : Tendsto (fun k : ℕ => ϖ ^ 2 / (k:ℝ) ^ 2) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => ((k:ℝ) ^ 2)) atTop atTop :=
      (Filter.tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop
    exact Tendsto.div_atTop tendsto_const_nhds h1
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
  · exact Eventually.of_forall (fun k => kern_nonneg k ϖ)
  · rw [eventually_atTop]
    exact ⟨1, fun k hk => kern_le_div k hk ϖ⟩

/-- `[[k]](ϖ) = 1 − k²/(k²+ϖ²)`。 -/
lemma kern_eq_one_sub (k : ℕ) (ϖ : ℝ) (h : (k:ℝ) ^ 2 + ϖ ^ 2 ≠ 0) :
    kern k ϖ = 1 - (k:ℝ) ^ 2 / ((k:ℝ) ^ 2 + ϖ ^ 2) := by
  unfold kern
  field_simp
  ring

/-- `ϖ ↦ [[k]](ϖ)` 在 `[0,∞)` 严格递增（`k ≥ 1`）。 -/
lemma kern_strictMonoOn_ϖ (k : ℕ) (hk : 1 ≤ k) : StrictMonoOn (fun ϖ => kern k ϖ) (Set.Ici 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ici] at ha hb
  have hk' : (0:ℝ) < (k:ℝ) ^ 2 := by
    have : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    positivity
  have ha2 : a ^ 2 < b ^ 2 := by nlinarith
  simp only
  rw [kern_eq_one_sub k a (by positivity), kern_eq_one_sub k b (by positivity)]
  have : (k:ℝ) ^ 2 / ((k:ℝ) ^ 2 + b ^ 2) < (k:ℝ) ^ 2 / ((k:ℝ) ^ 2 + a ^ 2) :=
    div_lt_div_of_pos_left hk' (by positivity) (by linarith)
  linarith

/-- `ϖ ↦ [[k]](ϖ)` 连续（`k ≥ 1`，分母恒正）。 -/
lemma kern_continuous (k : ℕ) (hk : 1 ≤ k) : Continuous (fun ϖ => kern k ϖ) := by
  unfold kern
  have hk' : (0:ℝ) < (k:ℝ) ^ 2 := by
    have : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    positivity
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro ϖ; positivity

/-- `[[k]](ϖ) → 1`（`ϖ → ∞`）：Lemma 0.1.4 的被积函数极限。 -/
lemma kern_tendsto_one_atTop (k : ℕ) : Tendsto (fun ϖ => kern k ϖ) atTop (𝓝 1) := by
  have h1 : Tendsto (fun ϖ : ℝ => (k:ℝ) ^ 2 / ((k:ℝ) ^ 2 + ϖ ^ 2)) atTop (𝓝 0) := by
    apply Tendsto.div_atTop tendsto_const_nhds
    apply tendsto_atTop_add_const_left
    exact Filter.tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0)
  have h2 : Tendsto (fun ϖ : ℝ => 1 - (k:ℝ) ^ 2 / ((k:ℝ) ^ 2 + ϖ ^ 2)) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub h1
  rw [sub_zero] at h2
  apply h2.congr'
  rw [EventuallyEq, eventually_atTop]
  refine ⟨1, fun ϖ hϖ => ?_⟩
  rw [kern_eq_one_sub k ϖ (by positivity)]

/-- `k ↦ [[k+1]](ϖ)` 可和（与 `ϖ²/(k+1)²` 比较）。 -/
lemma kern_summable (ϖ : ℝ) : Summable (fun k : ℕ => kern (k+1) ϖ) := by
  have hs : Summable (fun k : ℕ => ϖ ^ 2 * (1 / ((k:ℝ) + 1) ^ 2)) := by
    apply Summable.mul_left
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    simpa using this
  apply Summable.of_nonneg_of_le (fun k => kern_nonneg _ _) _ hs
  intro k
  have := kern_le_div (k+1) (Nat.succ_pos k) ϖ
  push_cast at this
  rw [mul_one_div]
  exact this

/-- Lemma 0.1.2 的被积函数版本：`∑_{k≥1} [[k]](ϖ) ≤ (π²/6) ϖ²`。 -/
lemma kern_tsum_le (ϖ : ℝ) : ∑' k : ℕ, kern (k+1) ϖ ≤ Real.pi ^ 2 / 6 * ϖ ^ 2 := by
  have hz : HasSum (fun k : ℕ => 1 / ((k:ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    have h := hasSum_zeta_two
    have h' := (hasSum_nat_add_iff' 1).mpr h
    simp only [Finset.sum_range_one, Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, div_zero, sub_zero] at h'
    convert h' using 2
    push_cast; ring
  have hz' : HasSum (fun k : ℕ => ϖ ^ 2 * (1 / ((k:ℝ) + 1) ^ 2)) (ϖ ^ 2 * (Real.pi ^ 2 / 6)) :=
    hz.mul_left _
  have hle : ∑' k : ℕ, kern (k+1) ϖ ≤ ∑' k : ℕ, ϖ ^ 2 * (1 / ((k:ℝ) + 1) ^ 2) := by
    apply (kern_summable ϖ).tsum_le_tsum _ hz'.summable
    intro k
    have := kern_le_div (k+1) (Nat.succ_pos k) ϖ
    push_cast at this
    rw [mul_one_div]
    exact this
  rw [hz'.tsum_eq] at hle
  linarith

/-! ### (S2) 的逐点形式 -/

/-- `[[k]](ϖ)/ϖ² = 1/(k²+ϖ²)`（`ϖ ≠ 0`）。 -/
lemma kern_div_sq_eq (k : ℕ) (ϖ : ℝ) (hϖ : ϖ ≠ 0) :
    kern k ϖ / ϖ ^ 2 = 1 / ((k:ℝ) ^ 2 + ϖ ^ 2) := by
  unfold kern
  have : ϖ ^ 2 ≠ 0 := pow_ne_zero 2 hϖ
  field_simp

/-- (S2) 逐点：`1/(k²+ϖ²) = k⁻² − ϖ²/(k²(k²+ϖ²))`（`k ≥ 1`）。 -/
lemma kern_S2 (k : ℕ) (hk : 1 ≤ k) (ϖ : ℝ) :
    1 / ((k:ℝ) ^ 2 + ϖ ^ 2) = 1 / (k:ℝ) ^ 2 - ϖ ^ 2 / ((k:ℝ) ^ 2 * ((k:ℝ) ^ 2 + ϖ ^ 2)) := by
  have hk' : (k:ℝ) ^ 2 ≠ 0 := by
    have : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    positivity
  have h2 : (k:ℝ) ^ 2 + ϖ ^ 2 ≠ 0 := by
    have : (0:ℝ) < (k:ℝ) ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hk')
    positivity
  field_simp
  ring

/-- Corollary 1.6 末段：`ϖ < ϖ'` 时
`[[k]](ϖ') − [[k]](ϖ) = k²(ϖ'²−ϖ²)/((k²+ϖ'²)(k²+ϖ²)) ≤ (ϖ'²−ϖ²)/k²`，且差 `≥ 0`。 -/
lemma kern_sub_eq (k : ℕ) (hk : 1 ≤ k) (ϖ ϖ' : ℝ) :
    kern k ϖ' - kern k ϖ
      = (k:ℝ) ^ 2 * (ϖ' ^ 2 - ϖ ^ 2) / (((k:ℝ) ^ 2 + ϖ' ^ 2) * ((k:ℝ) ^ 2 + ϖ ^ 2)) := by
  unfold kern
  have hk' : (0:ℝ) < (k:ℝ) ^ 2 := by
    have : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    positivity
  have h1 : (k:ℝ) ^ 2 + ϖ' ^ 2 ≠ 0 := by positivity
  have h2 : (k:ℝ) ^ 2 + ϖ ^ 2 ≠ 0 := by positivity
  field_simp
  ring

lemma kern_sub_le (k : ℕ) (hk : 1 ≤ k) (ϖ ϖ' : ℝ) (hϖ : 0 ≤ ϖ) (h : ϖ ≤ ϖ') :
    kern k ϖ' - kern k ϖ ≤ (ϖ' ^ 2 - ϖ ^ 2) / (k:ℝ) ^ 2 := by
  rw [kern_sub_eq k hk]
  have hk' : (0:ℝ) < (k:ℝ) ^ 2 := by
    have : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    positivity
  have hd : 0 ≤ ϖ' ^ 2 - ϖ ^ 2 := by nlinarith
  rw [div_le_div_iff₀ (by positivity) hk']
  have : (k:ℝ) ^ 2 * (k:ℝ) ^ 2 ≤ ((k:ℝ) ^ 2 + ϖ' ^ 2) * ((k:ℝ) ^ 2 + ϖ ^ 2) := by
    nlinarith [sq_nonneg ϖ, sq_nonneg ϖ']
  nlinarith

/-! ### Theorem B 的 `χ` -/

/-- `χ_y(x) := 1 − y/(y+x)`（在 `x ≥ 0`、`y > 0` 上等于 `x/(y+x)`）。用这一形式定义是为了
直接从 `x ↦ (y+x)⁻¹` 的严格凸性得到严格凹性。 -/
noncomputable def chi (y x : ℝ) : ℝ := -(y * (y + x)⁻¹) + 1

lemma chi_eq (y x : ℝ) (hy : 0 < y) (hx : 0 ≤ x) : chi y x = x / (y + x) := by
  unfold chi
  have : y + x ≠ 0 := by positivity
  field_simp
  ring

/-- `x ↦ (y+x)⁻¹` 在 `[0,∞)` 严格凸（`y > 0`）：`x ↦ x⁻¹` 在 `(0,∞)` 严格凸的平移。 -/
lemma inv_add_strictConvexOn (y : ℝ) (hy : 0 < y) :
    StrictConvexOn ℝ (Set.Ici 0) (fun x : ℝ => (y + x)⁻¹) := by
  have h := (strictConvexOn_zpow (m := -1) (by norm_num) (by norm_num)).translate_right y
  simp only [zpow_neg_one] at h
  apply h.subset _ (convex_Ici 0)
  intro x hx
  simp only [Set.mem_preimage, Set.mem_Ioi]
  simp only [Set.mem_Ici] at hx
  linarith

/-- **`χ_y` 在 `[0,∞)` 严格凹**（Theorem B 证明中的 `χ''(x) = −2y/(y+x)³ < 0`）。 -/
lemma chi_strictConcaveOn (y : ℝ) (hy : 0 < y) : StrictConcaveOn ℝ (Set.Ici 0) (chi y) := by
  have h1 := inv_add_strictConvexOn y hy
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx z hz hxz a b ha hb hab
  have h2 := mul_lt_mul_of_pos_left (h1.2 hx hz hxz ha hb hab) hy
  simp only [smul_eq_mul] at h2 ⊢
  unfold chi
  linarith

lemma chi_continuousOn (y : ℝ) (hy : 0 < y) : ContinuousOn (chi y) (Set.Ici 0) := by
  unfold chi
  apply ContinuousOn.add _ continuousOn_const
  apply ContinuousOn.neg
  apply ContinuousOn.mul continuousOn_const
  apply ContinuousOn.inv₀ (by fun_prop)
  intro x hx
  simp only [Set.mem_Ici] at hx
  positivity

/-- `[[k]](ω/(2πT)) = χ_{(2πTk)²}(ω²)`（`T > 0`，`k ≥ 1`）：Theorem B 证明的第一句。 -/
lemma kern_eq_chi (k : ℕ) (hk : 1 ≤ k) (T ω : ℝ) (hT : 0 < T) :
    kern k (ω / (2 * Real.pi * T)) = chi ((2 * Real.pi * T * k) ^ 2) (ω ^ 2) := by
  have hy : 0 < (2 * Real.pi * T * k) ^ 2 := by
    have : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    have := Real.pi_pos
    positivity
  rw [chi_eq _ _ hy (sq_nonneg ω)]
  unfold kern
  have hpi : 2 * Real.pi * T ≠ 0 := by have := Real.pi_pos; positivity
  have hk' : (k:ℝ) ≠ 0 := by
    have : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    positivity
  field_simp

/-- 参数 `ϖ = ω/(2πT)` 关于 `T` 严格递减（`ω > 0`）。 -/
lemma varpi_strictAntiOn (ω : ℝ) (hω : 0 < ω) :
    StrictAntiOn (fun T : ℝ => ω / (2 * Real.pi * T)) (Set.Ioi 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  simp only
  have := Real.pi_pos
  apply div_lt_div_of_pos_left hω (by positivity)
  nlinarith

/-- `ω/(2πT) → ∞`（`T ↓ 0`，`ω > 0`）。 -/
lemma varpi_tendsto_atTop (ω : ℝ) (hω : 0 < ω) :
    Tendsto (fun T : ℝ => ω / (2 * Real.pi * T)) (𝓝[>] 0) atTop := by
  have h1 : Tendsto (fun T : ℝ => 2 * Real.pi * T) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Tendsto (fun T : ℝ => 2 * Real.pi * T) (𝓝 0) (𝓝 (2 * Real.pi * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with T hT
      simp only [Set.mem_Ioi] at hT ⊢
      have := Real.pi_pos
      positivity
  have h2 : Tendsto (fun s : ℝ => s⁻¹) (𝓝[>] 0) atTop := tendsto_inv_nhdsGT_zero
  have h3 := (h2.comp h1).const_mul_atTop hω
  apply h3.congr
  intro T
  simp only [Function.comp_apply, div_eq_mul_inv]

/-- Lemma 0.1.4 的被积函数：`[[k]](ω/(2πT)) → 1`（`T ↓ 0`，`ω > 0`）。 -/
lemma kern_varpi_tendsto_one (k : ℕ) (ω : ℝ) (hω : 0 < ω) :
    Tendsto (fun T : ℝ => kern k (ω / (2 * Real.pi * T))) (𝓝[>] 0) (𝓝 1) :=
  (kern_tendsto_one_atTop k).comp (varpi_tendsto_atTop ω hω)

end Eliashberg
