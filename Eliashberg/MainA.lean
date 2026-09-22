import Eliashberg.LemmaMInf
import Eliashberg.AveragedKernel
import Eliashberg.Theorem11

/-!
# 主定理 I：Theorem 1.1（Theorem A(a)）、Lemma 0.2.3、Theorem 1.14（Theorem A(b)）、Corollary 1.17

记 `k(P,T) := λ₁(O[F_{P,T}])`（`kk P T := lam1 (FT P T)`），`λ₁` 是 Remark 1.2(b) 的有限 Rayleigh 商上确界。

* **`kk_pos`**：`k(P,T) ≥ F_T(1) > 0`（Prop 1.12(1)）
* **`kk_tendsto_zero`**：`k(P,T) → 0`（`T → ∞`）——Lemma 0.2.3 后半：`k ≤ 5‖F_T‖_ℓ¹ ≤ (5π²/6)⟨ω²⟩/(2πT)²`
* **`kk_continuousAt`**：`T ↦ k(P,T)` 在 `(0,∞)` 连续——Lemma 0.2.3 前半：`|k(T) − k(T')| ≤ 5‖F_T − F_{T'}‖_ℓ¹`
  与 `ℓ¹` 上的控制收敛（Tannery 定理，控制函数 `5⟨ϖ²⟩_{T₀/2}/(k+1)²`）
* **`theorem_1_1_a`**：`∀ λ > 0, ∃ T₀ > 0, λ k(P,T₀) > 1`——论文步骤 (i)–(iii)：取 `N` 使 `λ(2S_N − 1) > 1`，
  `T ↓ 0` 时 `⟨x, P_N K_T P_N x⟩ → ⟨x, P_N O[1] P_N x⟩ = 2S_N − 1`（`x = u^{(N)}/‖u^{(N)}‖`），
  再由压缩单调性 `k ≥ ⟨x, K_T x⟩`
* **`theorem_1_1_b`**：介值定理给出 `T_c` 使 `λ k(P,T_c) = 1`
* **`theorem_1_14`**：`T ↦ k(P,T)` 在 `(0,∞)` 严格递减——严格 Lemma M（`lam1_lt`）
* **`corollary_1_17`**：`T_c` 唯一，且 `λk > 1` 于 `(0,T_c)`、`λk < 1` 于 `(T_c,∞)`

## 假设

`P : Measure ℝ`、`[IsProbabilityMeasure P]`、`hP : ∀ᵐ ω ∂P, 0 < ω`（`P((0,∞)) = 1`）、
`hm : Integrable (fun ω => ω ^ 2) P`（`⟨ω²⟩ < ∞`）。与论文 §0.1 的 `𝒫` 一致。
-/

namespace Eliashberg

open scoped BigOperators
open Filter Topology MeasureTheory

/-! ### `ℓ¹` 事实 -/

lemma L1_of_summable_nonneg {f : ℕ → ℝ} (hs : Summable (fun k => f (k+1)))
    (hnn : ∀ k, 0 ≤ f (k+1)) : L1 f := by
  unfold L1
  convert hs using 1
  funext k
  exact abs_of_nonneg (hnn k)

lemma l1_of_nonneg {f : ℕ → ℝ} (hnn : ∀ k, 0 ≤ f (k+1)) : l1 f = ∑' k, f (k+1) := by
  unfold l1
  congr 1; funext k; exact abs_of_nonneg (hnn k)

section

variable (P : Measure ℝ) [IsProbabilityMeasure P]

lemma L1_FT (hm : Integrable (fun ω => ω ^ 2) P) (T : ℝ) (hT : 0 < T) : L1 (FT P T) :=
  L1_of_summable_nonneg (FT_summable P hm T hT) (fun k => FT_nonneg P T _)

lemma l1_FT_le (hm : Integrable (fun ω => ω ^ 2) P) (T : ℝ) (hT : 0 < T) :
    l1 (FT P T) ≤ Real.pi ^ 2 / 6 * varpiSq P T := by
  rw [l1_of_nonneg (fun k => FT_nonneg P T _)]
  exact FT_tsum_le P hm T hT

lemma FT_anti_k (hP : ∀ᵐ ω ∂P, 0 < ω) (T : ℝ) (hT : 0 < T) :
    ∀ k, 1 ≤ k → FT P T (k+1) ≤ FT P T k := fun k hk =>
  le_of_lt (FT_strictAnti_k P hP T hT k (k+1) hk (Nat.lt_succ_self k))

omit [IsProbabilityMeasure P] in
lemma FT_nonneg' (T : ℝ) : ∀ k, 1 ≤ k → 0 ≤ FT P T k := fun k _ => FT_nonneg P T k

/-! ### `k(P,T)` -/

/-- `k(P,T) := λ₁(O[F_{P,T}])`。 -/
noncomputable def kk (T : ℝ) : ℝ := lam1 (FT P T)

/-- **Prop 1.12(1)**：`k(P,T) ≥ F_T(1) > 0`。 -/
theorem kk_pos (hP : ∀ᵐ ω ∂P, 0 < ω) (hm : Integrable (fun ω => ω ^ 2) P) (T : ℝ) (hT : 0 < T) :
    0 < kk P T :=
  lt_of_lt_of_le (FT_pos P hP 1 le_rfl T hT) (f1_le_lam1 (L1_FT P hm T hT))

theorem kk_nonneg (hm : Integrable (fun ω => ω ^ 2) P) (T : ℝ) (hT : 0 < T) : 0 ≤ kk P T :=
  le_trans (FT_nonneg P T 1) (f1_le_lam1 (L1_FT P hm T hT))

/-- `k(P,T) ≤ 5‖F_T‖_ℓ¹ ≤ (5π²/6)⟨ω²⟩/(2πT)²`。 -/
theorem kk_le (hm : Integrable (fun ω => ω ^ 2) P) (T : ℝ) (hT : 0 < T) :
    kk P T ≤ 5 * (Real.pi ^ 2 / 6) * varpiSq P T := by
  unfold kk
  have h1 := lam1_le_five_l1 (L1_FT P hm T hT)
  have h2 := l1_FT_le P hm T hT
  linarith

/-- **Lemma 0.2.3（后半）**：`k(P,T) → 0`（`T → ∞`）。 -/
theorem kk_tendsto_zero (hm : Integrable (fun ω => ω ^ 2) P) :
    Tendsto (fun T => kk P T) atTop (𝓝 0) := by
  have hvar : Tendsto (fun T : ℝ => 5 * (Real.pi ^ 2 / 6) * varpiSq P T) atTop (𝓝 0) := by
    unfold varpiSq
    have h1 : Tendsto (fun T : ℝ => (2 * Real.pi * T) ^ 2) atTop atTop := by
      apply Filter.tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0) |>.comp
      exact Tendsto.const_mul_atTop (by have := Real.pi_pos; positivity) tendsto_id
    have h2 : Tendsto (fun T : ℝ => moment2 P / (2 * Real.pi * T) ^ 2) atTop (𝓝 0) :=
      Tendsto.div_atTop tendsto_const_nhds h1
    have := h2.const_mul (5 * (Real.pi ^ 2 / 6))
    rwa [mul_zero] at this
  apply squeeze_zero' _ _ hvar
  · filter_upwards [Ioi_mem_atTop (0:ℝ)] with T hT
    exact kk_nonneg P hm T hT
  · filter_upwards [Ioi_mem_atTop (0:ℝ)] with T hT
    exact kk_le P hm T hT

/-! ### 连续性（Lemma 0.2.3 前半） -/

/-- `T ↦ ‖F_T − F_{T₀}‖_ℓ¹ → 0`（`T → T₀`）：Tannery 定理，控制函数 `5⟨ϖ²⟩|_{T₀/2}/(k+1)²`。 -/
lemma l1_FT_sub_tendsto (hm : Integrable (fun ω => ω ^ 2) P) (T₀ : ℝ) (hT₀ : 0 < T₀) :
    Tendsto (fun T => l1 (fun k => FT P T k - FT P T₀ k)) (𝓝 T₀) (𝓝 0) := by
  unfold l1
  -- 控制函数
  set C : ℝ := 5 * varpiSq P (T₀ / 2) with hC
  have hbound : Summable (fun k : ℕ => C * (1 / ((k:ℝ) + 1) ^ 2)) :=
    hasSum_zeta_two_shift.summable.mul_left C
  have hlim : Tendsto (fun T => ∑' k : ℕ, |FT P T (k+1) - FT P T₀ (k+1)|) (𝓝 T₀)
      (𝓝 (∑' k : ℕ, (0:ℝ))) := by
    apply tendsto_tsum_of_dominated_convergence (bound := fun k : ℕ => C * (1 / ((k:ℝ) + 1) ^ 2)) hbound
    · intro k
      have h := (FT_continuousAt P (k+1) (by omega) T₀ hT₀).tendsto
      have h' := (h.sub_const (FT P T₀ (k+1))).abs
      rwa [sub_self, abs_zero] at h'
    · filter_upwards [Ioo_mem_nhds (by linarith : T₀ / 2 < T₀) (by linarith : T₀ < 2 * T₀)]
        with T hT k
      rw [Real.norm_eq_abs, abs_abs]
      have hT1 : 0 < T := by linarith [hT.1]
      have hle1 := FT_le_moment P hm (k+1) (by omega) T hT1
      have hle2 := FT_le_moment P hm (k+1) (by omega) T₀ hT₀
      have hnn1 := FT_nonneg P T (k+1)
      have hnn2 := FT_nonneg P T₀ (k+1)
      -- `varpiSq` 在 `T ≥ T₀/2` 上 `≤ varpiSq (T₀/2)`
      have hmono : ∀ S, T₀ / 2 ≤ S → varpiSq P S ≤ varpiSq P (T₀ / 2) := by
        intro S hS
        unfold varpiSq
        have hpi := Real.pi_pos
        have hS0 : 0 < S := by linarith
        apply div_le_div_of_nonneg_left (moment2_nonneg P) (by positivity)
        have : 2 * Real.pi * (T₀ / 2) ≤ 2 * Real.pi * S := by nlinarith
        nlinarith [two_pi_T_pos (T₀/2) (by linarith)]
      have hv1 := hmono T (le_of_lt hT.1)
      have hv2 := hmono T₀ (by linarith)
      have hk : (0:ℝ) < ((k+1 : ℕ) : ℝ) ^ 2 := by positivity
      have e : ((k+1 : ℕ) : ℝ) = (k:ℝ) + 1 := by push_cast; ring
      rw [e] at hle1 hle2
      calc |FT P T (k+1) - FT P T₀ (k+1)| ≤ |FT P T (k+1)| + |FT P T₀ (k+1)| := abs_sub _ _
        _ = FT P T (k+1) + FT P T₀ (k+1) := by rw [abs_of_nonneg hnn1, abs_of_nonneg hnn2]
        _ ≤ varpiSq P T / ((k:ℝ) + 1) ^ 2 + varpiSq P T₀ / ((k:ℝ) + 1) ^ 2 := add_le_add hle1 hle2
        _ ≤ varpiSq P (T₀/2) / ((k:ℝ) + 1) ^ 2 + varpiSq P (T₀/2) / ((k:ℝ) + 1) ^ 2 := by
            apply add_le_add
            · exact div_le_div_of_nonneg_right hv1 (by positivity)
            · exact div_le_div_of_nonneg_right hv2 (by positivity)
        _ ≤ C * (1 / ((k:ℝ) + 1) ^ 2) := by
            rw [hC]
            have : 0 ≤ varpiSq P (T₀/2) := by
              unfold varpiSq; exact div_nonneg (moment2_nonneg P) (by positivity)
            have hd : 0 < 1 / ((k:ℝ) + 1) ^ 2 := by positivity
            have e1 : varpiSq P (T₀/2) / ((k:ℝ) + 1) ^ 2 = varpiSq P (T₀/2) * (1 / ((k:ℝ) + 1) ^ 2) := by
              rw [mul_one_div]
            rw [e1]
            nlinarith
  rw [tsum_zero] at hlim
  exact hlim

/-- **Lemma 0.2.3（前半）**：`T ↦ k(P,T)` 在每个 `T₀ > 0` 连续。 -/
theorem kk_continuousAt (hm : Integrable (fun ω => ω ^ 2) P) (T₀ : ℝ) (hT₀ : 0 < T₀) :
    ContinuousAt (fun T => kk P T) T₀ := by
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h := (l1_FT_sub_tendsto P hm T₀ hT₀).const_mul 5
  rw [mul_zero] at h
  apply squeeze_zero' (Eventually.of_forall (fun T => norm_nonneg _)) _ h
  filter_upwards [Ioi_mem_nhds hT₀] with T hT
  rw [Real.norm_eq_abs]
  exact abs_lam1_sub_le (L1_FT P hm T hT) (L1_FT P hm T₀ hT₀)

theorem kk_continuousOn (hm : Integrable (fun ω => ω ^ 2) P) :
    ContinuousOn (fun T => kk P T) (Set.Ioi 0) :=
  fun T hT => (kk_continuousAt P hm T hT).continuousWithinAt

/-! ### Theorem 1.1 -/

/-- 矩阵元 `O[F_T]_{nm} → O[1]_{nm}`（`T ↓ 0`）：`O[f]_{nm}` 是有限多个 `f(k)`（`k ≥ 1`）的连续函数。 -/
lemma Of_FT_tendsto (hP : ∀ᵐ ω ∂P, 0 < ω) (n m : ℕ) :
    Tendsto (fun T => Of (FT P T) n m) (𝓝[>] 0) (𝓝 (Of (fun _ => (1:ℝ)) n m)) := by
  unfold Of
  have hk : ∀ k, 1 ≤ k → Tendsto (fun T => FT P T k) (𝓝[>] 0) (𝓝 1) :=
    fun k hk => FT_tendsto_one P hP k hk
  have hsum : Tendsto (fun T => ∑ k ∈ Finset.Icc 1 n, FT P T k) (𝓝[>] 0)
      (𝓝 (∑ k ∈ Finset.Icc 1 n, (1:ℝ))) :=
    tendsto_finsetSum _ (fun k hkk => hk k (Finset.mem_Icc.mp hkk).1)
  have h1 : Tendsto (fun T => if n = m then -(2 * u n ^ 2 * ∑ k ∈ Finset.Icc 1 n, FT P T k) else 0)
      (𝓝[>] 0) (𝓝 (if n = m then -(2 * u n ^ 2 * ∑ k ∈ Finset.Icc 1 n, (1:ℝ)) else 0)) := by
    split_ifs
    · exact (hsum.const_mul _).neg
    · exact tendsto_const_nhds
  have h2 : Tendsto (fun T => if n ≠ m then FT P T (Nat.dist n m) * (u n * u m) else 0)
      (𝓝[>] 0) (𝓝 (if n ≠ m then (1:ℝ) * (u n * u m) else 0)) := by
    split_ifs with h
    · have hd : 1 ≤ Nat.dist n m := by unfold Nat.dist; omega
      exact (hk _ hd).mul_const _
    · exact tendsto_const_nhds
  have h3 : Tendsto (fun T => FT P T (n + m + 1) * (u n * u m)) (𝓝[>] 0)
      (𝓝 ((1:ℝ) * (u n * u m))) := (hk _ (by omega)).mul_const _
  exact (h1.add h2).add h3

/-- `⟨x, P_N K_T P_N x⟩ → ⟨x, P_N O[1] P_N x⟩`（`T ↓ 0`）。 -/
lemma quadForm_FT_tendsto (hP : ∀ᵐ ω ∂P, 0 < ω) (x : ℕ → ℝ) (N : ℕ) :
    Tendsto (fun T => quadForm (FT P T) x N) (𝓝[>] 0) (𝓝 (quadForm (fun _ => (1:ℝ)) x N)) := by
  unfold quadForm
  apply tendsto_finsetSum; intro n _
  apply tendsto_finsetSum; intro m _
  exact ((Of_FT_tendsto P hP n m).const_mul _).mul_const _

/-- **Theorem 1.1（Theorem A(a)）**：对每个 `λ > 0` 存在 `T₀ > 0` 使 `λ k(P,T₀) > 1`。 -/
theorem theorem_1_1_a (hP : ∀ᵐ ω ∂P, 0 < ω) (hm : Integrable (fun ω => ω ^ 2) P)
    (lam : ℝ) (hlam : 0 < lam) : ∃ T₀ : ℝ, 0 < T₀ ∧ 1 < lam * kk P T₀ := by
  -- (iii) 取 `N ≥ 1` 使 `2S_N − 1 > 1/λ`
  have hN := (hN_inf_tendsto_atTop.eventually_gt_atTop (1 / lam))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hN
  set N := max N₀ 1 with hNdef
  have hN1 : 1 ≤ N := le_max_right _ _
  have hNgt : 1 / lam < hN_inf N := hN₀ N (le_max_left _ _)
  -- Rayleigh 极大向量 `x`
  obtain ⟨x, hx, hqx⟩ := (hN_inf_isGreatest N hN1).1
  -- (ii) `T ↓ 0` 时 `⟨x, K_T x⟩ → 2S_N − 1 > 1/λ`
  have ht := quadForm_FT_tendsto P hP x N
  rw [← hqx] at ht
  have hev := ht.eventually_const_lt hNgt
  obtain ⟨T₀, hT₀gt, hT₀pos⟩ := (hev.and self_mem_nhdsWithin).exists
  refine ⟨T₀, hT₀pos, ?_⟩
  -- (i) 压缩单调性
  have hk : quadForm (FT P T₀) x N ≤ kk P T₀ := quadForm_le_lam1 (L1_FT P hm T₀ hT₀pos) x N hx
  have : 1 / lam < kk P T₀ := lt_of_lt_of_le hT₀gt hk
  rw [div_lt_iff₀ hlam] at this
  linarith

/-- **Theorem 1.1，第二句**：`L(λ,P)` 与临界曲面相交——存在 `T_c > 0` 使 `λ k(P,T_c) = 1`。 -/
theorem theorem_1_1_b (hP : ∀ᵐ ω ∂P, 0 < ω) (hm : Integrable (fun ω => ω ^ 2) P)
    (lam : ℝ) (hlam : 0 < lam) : ∃ Tc : ℝ, 0 < Tc ∧ lam * kk P Tc = 1 := by
  obtain ⟨T₀, hT₀, hgt⟩ := theorem_1_1_a P hP hm lam hlam
  -- `T → ∞` 时 `λ k → 0`，取 `T₁ > T₀` 使 `λ k(T₁) < 1`
  have hlim : Tendsto (fun T => lam * kk P T) atTop (𝓝 0) := by
    have := (kk_tendsto_zero P hm).const_mul lam
    rwa [mul_zero] at this
  obtain ⟨T₁, hT₁gt, hT₁lt⟩ :=
    ((eventually_gt_atTop T₀).and (hlim.eventually_lt_const (by norm_num : (0:ℝ) < 1))).exists
  -- 介值定理
  have hcont : ContinuousOn (fun T => lam * kk P T) (Set.Icc T₀ T₁) := by
    apply ContinuousOn.mul continuousOn_const
    apply (kk_continuousOn P hm).mono
    intro T hT; simp only [Set.mem_Icc, Set.mem_Ioi] at hT ⊢; linarith [hT.1]
  have h1 : (1:ℝ) ∈ Set.Icc (lam * kk P T₁) (lam * kk P T₀) := ⟨le_of_lt hT₁lt, le_of_lt hgt⟩
  obtain ⟨Tc, hTc, hTceq⟩ := intermediate_value_Icc' (le_of_lt hT₁gt) hcont h1
  exact ⟨Tc, by linarith [hTc.1], hTceq⟩

/-! ### Theorem 1.14 与 Corollary 1.17 -/

/-- **Theorem 1.14（Theorem A(b)）**：`T ↦ k(P,T)` 在 `(0,∞)` 严格递减。 -/
theorem theorem_1_14 (hP : ∀ᵐ ω ∂P, 0 < ω) (hm : Integrable (fun ω => ω ^ 2) P)
    (T T' : ℝ) (hT : 0 < T) (hTT : T < T') : kk P T' < kk P T := by
  have hT' : 0 < T' := lt_trans hT hTT
  unfold kk
  apply lam1_lt (L1_FT P hm T' hT') (FT_anti_k P hP T' hT') (FT_nonneg' P T')
    (FT_pos P hP 1 le_rfl T' hT') (L1_FT P hm T hT)
  · intro k hk; exact le_of_lt (FT_strictAnti_T P hP k hk T T' hT hTT)
  · exact FT_strictAnti_T P hP 1 le_rfl T T' hT hTT

theorem kk_strictAntiOn (hP : ∀ᵐ ω ∂P, 0 < ω) (hm : Integrable (fun ω => ω ^ 2) P) :
    StrictAntiOn (fun T => kk P T) (Set.Ioi 0) :=
  fun T hT _ _ hTT => theorem_1_14 P hP hm T _ hT hTT

/-- **Corollary 1.17（Theorem A(b) 第二句）**：`T_c` 唯一，`λk > 1` 于 `(0,T_c)`，`λk < 1` 于 `(T_c,∞)`。 -/
theorem corollary_1_17 (hP : ∀ᵐ ω ∂P, 0 < ω) (hm : Integrable (fun ω => ω ^ 2) P)
    (lam : ℝ) (hlam : 0 < lam) :
    ∃! Tc : ℝ, 0 < Tc ∧ lam * kk P Tc = 1 ∧
      (∀ T, 0 < T → T < Tc → 1 < lam * kk P T) ∧ (∀ T, Tc < T → lam * kk P T < 1) := by
  obtain ⟨Tc, hTc, heq⟩ := theorem_1_1_b P hP hm lam hlam
  have hbelow : ∀ T, 0 < T → T < Tc → 1 < lam * kk P T := by
    intro T hT hTTc
    have := theorem_1_14 P hP hm T Tc hT hTTc
    rw [← heq]
    exact mul_lt_mul_of_pos_left this hlam
  have habove : ∀ T, Tc < T → lam * kk P T < 1 := by
    intro T hT
    have := theorem_1_14 P hP hm Tc T hTc hT
    rw [← heq]
    exact mul_lt_mul_of_pos_left this hlam
  refine ⟨Tc, ⟨hTc, heq, hbelow, habove⟩, ?_⟩
  rintro T ⟨hT, hTeq, _, _⟩
  rcases lt_trichotomy T Tc with h | h | h
  · have := hbelow T hT h; linarith
  · exact h
  · have := habove T h; linarith

end

end Eliashberg
