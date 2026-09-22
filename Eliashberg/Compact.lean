import Eliashberg.L2Operator
import Eliashberg.LemmaA1

/-!
# `O[f]` 是紧算子；`λ₁` 是可达特征值（Lemma A.1 后半句、Prop 1.12(2)）

论文 Lemma A.1 的后半句：「HS ⇒ `A` 是紧自伴算子，`g(2) = max spec A` 是**可达特征值**，
`spec A ∖ {0}` 离散」；Prop 1.12(2)：「`λ₁` 是 `O[F]` 的特征值」（由 (F2) 紧自伴算子谱定理）。

mathlib 没有紧自伴算子的谱定理，但有 **Fredholm 择一**
（`IsCompactOperator.hasEigenvalue_iff_mem_spectrum`：紧算子的非零谱点都是特征值）。
本库已证 `lam1 f ∈ spec(O[f])`（`lam1_mem_spectrum`），所以只差一件事：**`O[f]` 是紧算子**。

**HS ⇒ 紧**（本文件主体）：`O_N := O[f] P_N`（`P_N` 截断投影）是有限秩算子，故紧；
`‖O[f] − O_N‖² ≤ τ_N := ∑_n ∑_{m≥N} O_{nm}²`（逐行 Cauchy–Schwarz），
而 `τ_N → 0`（`∑_{n,m} O_{nm}² < ∞` 由 Lemma 0.2.1 的 HS 界 + 控制收敛）；
紧算子在算子范数下闭（`isCompactOperator_of_tendsto`）。

| 定理 | 内容 |
|---|---|
| `Of_sq_summable` | `∑_{n,m≥0} O[f]_{nm}² < ∞`（一般 `f ∈ ℓ¹`） |
| `tailHS_tendsto_zero` | `τ_N → 0` |
| `PNclm`、`PNclm_apply`、`PNclm_isCompact` | 截断投影 `P_N : H →L H`，`P_N x = (x_n 1_{n<N})`，有限秩 |
| `OpN_isCompact` | `O[f] P_N` 紧 |
| `opNorm_sub_OpN_le` | `‖O[f] − O[f] P_N‖ ≤ √τ_N` |
| **`Op_isCompactOperator`** | **`O[f]` 紧**（`f ∈ ℓ¹`） |
| **`lam1_hasEigenvalue`**、**`exists_unit_eigenvector`** | `lam1 f ≠ 0 ⇒ lam1 f` 是特征值，且有单位特征向量 |
| `mem_spectrum_iff_hasEigenvalue` | `μ ≠ 0`：`μ ∈ spec(O[f]) ↔ μ` 是特征值（论文「`spec ∖ {0}` 由特征值组成」） |
| **`Aop_isCompact`、`g2_hasEigenvalue`、`exists_unit_eigenvector_g2`** | **Lemma A.1 后半句**：`A = O[k⁻²]` 紧、`g(2)` 是可达特征值 |
| **`kk_hasEigenvalue`** | **Prop 1.12(2)**：`k(P,T)` 是 `K(P,T)` 的特征值 |

**未做**：「`spec A ∖ {0}` 离散（只以 0 为聚点）」需要 Riesz 理论，mathlib 没有；
本库主线（`TheoremA10.lean`）不用它。
-/

namespace Eliashberg

open scoped BigOperators ENNReal
open Filter Topology

noncomputable section

variable {f : ℕ → ℝ}

/-! ### 一、HS 可和性与尾部 -/

/-- `∑_{n,m≥0} O[f]_{nm}² < ∞`（Lemma 0.2.1 的 HS 界 `hs f K ≤ 25‖f‖₁²` 对一切方框成立）。 -/
lemma Of_sq_summable (hf : L1 f) : Summable (fun p : ℕ × ℕ => Of f p.1 p.2 ^ 2) :=
  summable_of_sq_sums_le _ (fun _ => sq_nonneg _) (25 * l1 f ^ 2) (fun K => hs_le_25 hf K)

/-- 每一行平方可和。 -/
lemma Of_row_sq_summable (hf : L1 f) (n : ℕ) : Summable (fun m => Of f n m ^ 2) :=
  (Of_sq_summable hf).prod_factor n

/-- HS 尾部（列 `≥ N`）：`τ_N := ∑_{n≥0} ∑_{m≥N} O_{nm}²`。 -/
def tailHS (f : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑' p : ℕ × ℕ, (if N ≤ p.2 then Of f p.1 p.2 ^ 2 else 0)

lemma tail_term_nonneg (f : ℕ → ℝ) (N : ℕ) (p : ℕ × ℕ) :
    0 ≤ (if N ≤ p.2 then Of f p.1 p.2 ^ 2 else 0) := by
  split_ifs <;> positivity

lemma tail_term_le (f : ℕ → ℝ) (N : ℕ) (p : ℕ × ℕ) :
    (if N ≤ p.2 then Of f p.1 p.2 ^ 2 else 0) ≤ Of f p.1 p.2 ^ 2 := by
  split_ifs
  · exact le_rfl
  · exact sq_nonneg _

lemma tailHS_nonneg (f : ℕ → ℝ) (N : ℕ) : 0 ≤ tailHS f N :=
  tsum_nonneg (tail_term_nonneg f N)

lemma tailHS_summable (hf : L1 f) (N : ℕ) :
    Summable (fun p : ℕ × ℕ => (if N ≤ p.2 then Of f p.1 p.2 ^ 2 else 0)) :=
  Summable.of_nonneg_of_le (tail_term_nonneg f N) (tail_term_le f N) (Of_sq_summable hf)

/-- `τ_N → 0`（控制收敛：逐项 `→ 0`，被 `O_{nm}²` 控制）。 -/
lemma tailHS_tendsto_zero (hf : L1 f) : Tendsto (tailHS f) atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun (N : ℕ) (p : ℕ × ℕ) => (if N ≤ p.2 then Of f p.1 p.2 ^ 2 else 0))
    (g := fun _ => (0:ℝ)) (bound := fun p => Of f p.1 p.2 ^ 2) (Of_sq_summable hf) ?_ ?_
  · unfold tailHS; simpa using h
  · intro p
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop p.2] with N hN
    rw [if_neg (not_le.mpr hN)]
  · filter_upwards with N p
    rw [Real.norm_eq_abs, abs_of_nonneg (tail_term_nonneg f N p)]
    exact tail_term_le f N p

/-! ### 二、截断投影 `P_N` 与有限秩算子 `O[f] P_N` -/

/-- 截断投影 `P_N := ∑_{m<N} e_m ⊗ e_m^*` 作为 `H →L[ℝ] H`。 -/
def PNclm (N : ℕ) : H →L[ℝ] H :=
  ∑ m ∈ Finset.range N,
    (lp.singleContinuousLinearMap ℝ (fun _ : ℕ => ℝ) 2 m).comp (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 m)

lemma PNclm_apply (N : ℕ) (x : H) : PNclm N x = PN (x : ℕ → ℝ) N := by
  rw [PN_eq_sum_single]
  unfold PNclm
  rw [ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl; intro m _
  rw [ContinuousLinearMap.comp_apply, lp.singleContinuousLinearMap_apply]
  rfl

/-- 坐标泛函 `x ↦ x_m` 是紧算子（值域 `ℝ` 局部紧）。 -/
lemma evalCLM_isCompact (m : ℕ) : IsCompactOperator (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 m) :=
  isCompactOperator_of_locallyCompactSpace_dom _

/-- 秩一算子 `e_m ⊗ e_m^*` 紧。 -/
lemma rankOne_isCompact (m : ℕ) : IsCompactOperator
    ((lp.singleContinuousLinearMap ℝ (fun _ : ℕ => ℝ) 2 m).comp
      (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 m)) := by
  rw [ContinuousLinearMap.coe_comp']
  exact (evalCLM_isCompact m).clm_comp _

/-- 紧算子的有限和紧（函数形式）。 -/
lemma isCompactOperator_finset_sum {ι : Type*} (s : Finset ι) (T : ι → H → H)
    (h : ∀ i ∈ s, IsCompactOperator (T i)) : IsCompactOperator (∑ i ∈ s, T i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact isCompactOperator_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

lemma PNclm_isCompact (N : ℕ) : IsCompactOperator (PNclm N) := by
  unfold PNclm
  rw [ContinuousLinearMap.coe_sum']
  exact isCompactOperator_finset_sum _ _ (fun m _ => rankOne_isCompact m)

/-- `O_N := O[f] P_N`。 -/
def OpN (hf : L1 f) (N : ℕ) : H →L[ℝ] H := (Op hf).comp (PNclm N)

lemma OpN_isCompact (hf : L1 f) (N : ℕ) : IsCompactOperator (OpN hf N) := by
  unfold OpN
  rw [ContinuousLinearMap.coe_comp']
  exact (PNclm_isCompact N).clm_comp _

lemma OpN_apply_coord (hf : L1 f) (N : ℕ) (x : H) (n : ℕ) :
    ((OpN hf N x : H) : ℕ → ℝ) n = ∑ m ∈ Finset.range N, Of f n m * (x : ℕ → ℝ) m := by
  unfold OpN
  rw [ContinuousLinearMap.comp_apply, PNclm_apply, Op_PN_apply]

/-! ### 三、`‖O[f] − O_N‖ ≤ √τ_N`（逐行 Cauchy–Schwarz） -/

/-- 第 `n` 行的尾部 `(1_{m≥N} O_{nm})_m` 作为 `ℓ²` 元素。 -/
def rowTail (hf : L1 f) (N n : ℕ) : H :=
  mkH (fun m => if N ≤ m then Of f n m else 0) (∑' m, Of f n m ^ 2) (fun s => by
    calc ∑ m ∈ s, (if N ≤ m then Of f n m else 0) ^ 2
        ≤ ∑ m ∈ s, Of f n m ^ 2 := by
          apply Finset.sum_le_sum; intro m _
          split_ifs
          · exact le_rfl
          · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
            exact sq_nonneg _
      _ ≤ ∑' m, Of f n m ^ 2 := (Of_row_sq_summable hf n).sum_le_tsum s (fun m _ => sq_nonneg _))

lemma rowTail_apply (hf : L1 f) (N n m : ℕ) :
    ((rowTail hf N n : H) : ℕ → ℝ) m = if N ≤ m then Of f n m else 0 := rfl

lemma rowTail_norm_sq (hf : L1 f) (N n : ℕ) :
    ‖rowTail hf N n‖ ^ 2 = ∑' m, (if N ≤ m then Of f n m ^ 2 else 0) := by
  rw [H_norm_sq]
  congr 1; funext m
  rw [rowTail_apply]
  split_ifs
  · rfl
  · simp

/-- `((O[f] − O_N) x)_n = ∑'_{m} 1_{m≥N} O_{nm} x_m = ⟨rowTail n, x⟩`。 -/
lemma sub_OpN_apply_coord (hf : L1 f) (N : ℕ) (x : H) (n : ℕ) :
    (((Op hf - OpN hf N) x : H) : ℕ → ℝ) n = inner ℝ (rowTail hf N n) x := by
  rw [sub_apply, lp.coeFn_sub, Pi.sub_apply, Op_apply, OpN_apply_coord, H_inner]
  have hs' : Summable (fun m => ((rowTail hf N n : H) : ℕ → ℝ) m * (x : ℕ → ℝ) m) :=
    H_summable_mul _ x
  have hsplit : ∀ m, Of f n m * (x : ℕ → ℝ) m
      = (if m < N then Of f n m * (x : ℕ → ℝ) m else 0)
        + ((rowTail hf N n : H) : ℕ → ℝ) m * (x : ℕ → ℝ) m := by
    intro m
    rw [rowTail_apply]
    split_ifs <;> first | omega | ring
  have hs1 : Summable (fun m => (if m < N then Of f n m * (x : ℕ → ℝ) m else 0)) :=
    summable_of_ne_finset_zero (s := Finset.range N) (fun m hm => by
      rw [Finset.mem_range] at hm; rw [if_neg hm])
  rw [tsum_congr hsplit, hs1.tsum_add hs', tsum_eq_sum (s := Finset.range N) ?_]
  · have e : ∑ m ∈ Finset.range N, (if m < N then Of f n m * (x : ℕ → ℝ) m else 0)
        = ∑ m ∈ Finset.range N, Of f n m * (x : ℕ → ℝ) m := by
      apply Finset.sum_congr rfl; intro m hm
      rw [Finset.mem_range] at hm; rw [if_pos hm]
    rw [e]; ring
  · intro m hm
    rw [Finset.mem_range] at hm; rw [if_neg hm]

/-- 逐坐标 Cauchy–Schwarz：`|((O[f] − O_N) x)_n| ≤ ‖rowTail n‖ ‖x‖`。 -/
lemma abs_sub_OpN_apply_coord_le (hf : L1 f) (N : ℕ) (x : H) (n : ℕ) :
    |(((Op hf - OpN hf N) x : H) : ℕ → ℝ) n| ≤ ‖rowTail hf N n‖ * ‖x‖ := by
  rw [sub_OpN_apply_coord]
  exact abs_real_inner_le_norm _ _

/-- `∑_{n∈s} ∑'_{m} 1_{m≥N} O_{nm}² ≤ τ_N`。 -/
lemma sum_rowTail_norm_sq_le (hf : L1 f) (N : ℕ) (s : Finset ℕ) :
    ∑ n ∈ s, ‖rowTail hf N n‖ ^ 2 ≤ tailHS f N := by
  simp only [rowTail_norm_sq]
  have hsum := tailHS_summable hf N
  have hrow : ∀ n, Summable (fun m => (if N ≤ m then Of f n m ^ 2 else 0)) :=
    fun n => hsum.prod_factor n
  have hcol : Summable (fun n => ∑' m, (if N ≤ m then Of f n m ^ 2 else 0)) :=
    ((summable_prod_of_nonneg (tail_term_nonneg f N)).mp hsum).2
  unfold tailHS
  rw [hsum.tsum_prod' hrow]
  exact hcol.sum_le_tsum s (fun n _ => tsum_nonneg (fun m => by split_ifs <;> positivity))

/-- `‖(O[f] − O_N) x‖² ≤ τ_N ‖x‖²`。 -/
lemma norm_sub_OpN_apply_sq_le (hf : L1 f) (N : ℕ) (x : H) :
    ‖(Op hf - OpN hf N) x‖ ^ 2 ≤ tailHS f N * ‖x‖ ^ 2 := by
  rw [H_norm_sq]
  apply (H_summable_sq _).tsum_le_of_sum_le
  intro s
  calc ∑ n ∈ s, ((((Op hf - OpN hf N) x : H) : ℕ → ℝ) n) ^ 2
      ≤ ∑ n ∈ s, ‖rowTail hf N n‖ ^ 2 * ‖x‖ ^ 2 := by
        apply Finset.sum_le_sum; intro n _
        have h := abs_sub_OpN_apply_coord_le hf N x n
        calc ((((Op hf - OpN hf N) x : H) : ℕ → ℝ) n) ^ 2
            = |(((Op hf - OpN hf N) x : H) : ℕ → ℝ) n| ^ 2 := (sq_abs _).symm
          _ ≤ (‖rowTail hf N n‖ * ‖x‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
          _ = ‖rowTail hf N n‖ ^ 2 * ‖x‖ ^ 2 := by ring
    _ = (∑ n ∈ s, ‖rowTail hf N n‖ ^ 2) * ‖x‖ ^ 2 := by rw [Finset.sum_mul]
    _ ≤ tailHS f N * ‖x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (sum_rowTail_norm_sq_le hf N s) (sq_nonneg _)

lemma norm_sub_OpN_apply_le (hf : L1 f) (N : ℕ) (x : H) :
    ‖(Op hf - OpN hf N) x‖ ≤ Real.sqrt (tailHS f N) * ‖x‖ := by
  have h := norm_sub_OpN_apply_sq_le hf N x
  have hb : (Real.sqrt (tailHS f N) * ‖x‖) ^ 2 = tailHS f N * ‖x‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (tailHS_nonneg f N)]
  rw [← hb] at h
  exact pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero |>.mp h

/-- **`‖O[f] − O[f] P_N‖ ≤ √τ_N`**。 -/
theorem opNorm_sub_OpN_le (hf : L1 f) (N : ℕ) :
    ‖Op hf - OpN hf N‖ ≤ Real.sqrt (tailHS f N) :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) (norm_sub_OpN_apply_le hf N)

/-- `O[f] P_N → O[f]`（算子范数）。 -/
theorem OpN_tendsto (hf : L1 f) : Tendsto (fun N => OpN hf N) atTop (𝓝 (Op hf)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq : Tendsto (fun N => Real.sqrt (tailHS f N)) atTop (𝓝 0) := by
    have := (tailHS_tendsto_zero hf).sqrt
    rwa [Real.sqrt_zero] at this
  refine squeeze_zero_norm (fun N => ?_) hsq
  rw [norm_norm, norm_sub_rev]
  exact opNorm_sub_OpN_le hf N

/-! ### 四、`O[f]` 紧；`lam1 f` 是特征值 -/

/-- **`O[f]` 是紧算子**（`f ∈ ℓ¹`；论文 Lemma A.1「HS ⇒ 紧」）。 -/
theorem Op_isCompactOperator (hf : L1 f) : IsCompactOperator (Op hf) :=
  isCompactOperator_of_tendsto (OpN_tendsto hf) (Eventually.of_forall (fun N => OpN_isCompact hf N))

/-- **非零谱点都是特征值**（Fredholm 择一；论文「`spec A ∖ {0}` 由特征值组成」）。 -/
theorem mem_spectrum_iff_hasEigenvalue (hf : L1 f) {μ : ℝ} (hμ : μ ≠ 0) :
    μ ∈ spectrum ℝ (Op hf) ↔ Module.End.HasEigenvalue (Op hf : Module.End ℝ H) μ :=
  ((Op_isCompactOperator hf).hasEigenvalue_iff_mem_spectrum hμ).symm

/-- **`lam1 f` 是 `O[f]` 的特征值**（`lam1 f ≠ 0`）。 -/
theorem lam1_hasEigenvalue (hf : L1 f) (h0 : lam1 f ≠ 0) :
    Module.End.HasEigenvalue (Op hf : Module.End ℝ H) (lam1 f) :=
  (mem_spectrum_iff_hasEigenvalue hf h0).mp (lam1_mem_spectrum hf)

/-- 特征向量的存在。 -/
theorem exists_eigenvector (hf : L1 f) (h0 : lam1 f ≠ 0) :
    ∃ v : H, v ≠ 0 ∧ Op hf v = lam1 f • v := by
  obtain ⟨v, hv⟩ := (lam1_hasEigenvalue hf h0).exists_hasEigenvector
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hv
  exact ⟨v, hv.2, hv.1⟩

/-- **单位特征向量**：`∃ v, ‖v‖ = 1 ∧ O[f] v = lam1 f • v`（论文「可达特征值」）。 -/
theorem exists_unit_eigenvector (hf : L1 f) (h0 : lam1 f ≠ 0) :
    ∃ v : H, ‖v‖ = 1 ∧ Op hf v = lam1 f • v := by
  obtain ⟨v, hv0, hv⟩ := exists_eigenvector hf h0
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
  refine ⟨‖v‖⁻¹ • v, ?_, ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
  · rw [map_smul, hv, smul_comm]

/-- 若 `f 1 > 0` 则 `lam1 f > 0`，从而是特征值（论文「admissible ⇒ `λ₁ ≥ F(1) > 0`」）。 -/
theorem lam1_hasEigenvalue_of_pos (hf : L1 f) (h1 : 0 < f 1) :
    Module.End.HasEigenvalue (Op hf : Module.End ℝ H) (lam1 f) :=
  lam1_hasEigenvalue hf (ne_of_gt (lt_of_lt_of_le h1 (f1_le_lam1 hf)))

/-! ### 五、特化：Appendix A 的 `A = O[k⁻²]`（Lemma A.1 后半句）与 `K(P,T)`（Prop 1.12(2)） -/

/-- Appendix A 的算子 `A := O[k ↦ k⁻²]`，作为 `ℓ²` 上的有界算子。 -/
def Aop : H →L[ℝ] H := Op invSq_L1

theorem Aop_isSelfAdjoint : IsSelfAdjoint Aop := Op_isSelfAdjoint invSq_L1

/-- **Lemma A.1**：`A` 紧。 -/
theorem Aop_isCompact : IsCompactOperator Aop := Op_isCompactOperator invSq_L1

/-- `g(2) = max spec A`（`L2Operator.lean` 的忠实性桥）。 -/
theorem isGreatest_spectrum_Aop : IsGreatest (spectrum ℝ Aop) g2 := isGreatest_spectrum invSq_L1

lemma g2_ne_zero : g2 ≠ 0 := ne_of_gt (lt_of_lt_of_le one_pos one_le_g2)

/-- **Lemma A.1 后半句**：`g(2)` 是 `A` 的特征值。 -/
theorem g2_hasEigenvalue : Module.End.HasEigenvalue (Aop : Module.End ℝ H) g2 :=
  lam1_hasEigenvalue invSq_L1 g2_ne_zero

/-- **Lemma A.1 后半句**：`g(2)` 是可达的——存在单位向量 `v` 使 `A v = g(2) v`。 -/
theorem exists_unit_eigenvector_g2 : ∃ v : H, ‖v‖ = 1 ∧ Aop v = g2 • v :=
  exists_unit_eigenvector invSq_L1 g2_ne_zero

/-- `A` 的非零谱点都是特征值。 -/
theorem Aop_mem_spectrum_iff {μ : ℝ} (hμ : μ ≠ 0) :
    μ ∈ spectrum ℝ Aop ↔ Module.End.HasEigenvalue (Aop : Module.End ℝ H) μ :=
  mem_spectrum_iff_hasEigenvalue invSq_L1 hμ

open MeasureTheory in
/-- **Prop 1.12(2)**：`k(P,T) = λ₁(K(P,T))` 是 `K(P,T) = O[F_{P,T}]` 的特征值。 -/
theorem kk_hasEigenvalue (P : Measure ℝ) [IsProbabilityMeasure P] (hP : ∀ᵐ ω ∂P, 0 < ω)
    (hm : Integrable (fun ω => ω ^ 2) P) (T : ℝ) (hT : 0 < T) :
    Module.End.HasEigenvalue (Op (L1_FT P hm T hT) : Module.End ℝ H) (kk P T) :=
  lam1_hasEigenvalue (L1_FT P hm T hT) (ne_of_gt (kk_pos P hP hm T hT))

open MeasureTheory in
/-- **Prop 1.12(2)**，向量形式：存在单位向量 `v ∈ ℓ²` 使 `K(P,T) v = k(P,T) v`。 -/
theorem exists_unit_eigenvector_kk (P : Measure ℝ) [IsProbabilityMeasure P]
    (hP : ∀ᵐ ω ∂P, 0 < ω) (hm : Integrable (fun ω => ω ^ 2) P) (T : ℝ) (hT : 0 < T) :
    ∃ v : H, ‖v‖ = 1 ∧ Op (L1_FT P hm T hT) v = kk P T • v :=
  exists_unit_eigenvector (L1_FT P hm T hT) (ne_of_gt (kk_pos P hP hm T hT))

end

end Eliashberg
