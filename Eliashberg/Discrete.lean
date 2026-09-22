import Eliashberg.Compact

/-!
# `spec A ∖ {0}` 离散（Lemma A.1 最后一句）

论文 Lemma A.1 的最后一句：「`A` 是紧自伴算子，`g(2) = max spec A` 是可达特征值，
**`spec A ∖ {0}` 离散**」。前两件已在 `Compact.lean` 证成；本文件补最后一件。

论文（和标准教材）走 Riesz 理论：紧算子的谱投影有限秩。mathlib 没有 Riesz 理论，
但这条结论有一个**只用序列紧性的初等证明**，完全绕开谱投影：

设 `ε > 0` 而 `S_ε := {μ ∈ spec A : |μ| ≥ ε}` 无限。每个这样的 `μ` 都是特征值
（Fredholm 择一，`mem_spectrum_iff_hasEigenvalue`），取单位特征向量 `e_μ`。
自伴 ⇒ 不同特征值的特征向量**正交**，于是对 `μ ≠ ν`

`‖A e_μ − A e_ν‖² = ‖μ e_μ − ν e_ν‖² = μ² + ν² ≥ 2ε²`，

即 `{A e_μ}` 是紧集 `closure (A '' ball 0 2)` 里一列**两两相距 ≥ ε** 的点。
但紧集是序列紧的，任何序列有收敛子列，从而有两项相距 `< ε`，矛盾。

| 定理 | 内容 |
|---|---|
| `inner_eq_zero_of_eigen_ne` | 自伴算子不同特征值的特征向量正交 |
| `norm_sub_eigen_sq` | `‖T v − T w‖² = μ² + ν²`（单位正交特征向量） |
| `exists_unit_eigenvector_of_mem_spectrum` | 非零谱点有单位特征向量 |
| **`finite_spectrum_abs_ge`** | **`{μ ∈ spec(O[f]) : |μ| ≥ ε}` 有限**（`ε > 0`） |
| `eigenvalues_abs_ge_finite` | 同上的特征值形式 |
| **`exists_ball_inter_subset`** | **`x ≠ 0` 有只可能碰到自己的邻域**（孤立与非聚点的公共来源） |
| **`exists_ball_inter_spectrum_eq`** | **非零谱点是孤立点**：`∃ δ > 0, spec ∩ ball μ δ = {μ}` |
| `not_accPt_of_ne_zero` | `0` 是唯一可能的聚点 |
| `spectrum_diff_zero_countable` | `spec ∖ {0}` 可数 |
| **`Aop_finite_spectrum_abs_ge`、`Aop_isolated`、`Aop_not_accPt`** | **Lemma A.1 最后一句**（`A = O[k⁻²]`） |
| `Aop_spectrum_diff_zero_countable`、`g2_isolated` | `spec A ∖ {0}` 可数；`g(2)` 是孤立点 |
| `kk_finite_spectrum_abs_ge`、`kk_isolated` | `K(P,T)` 的同一结论；`k(P,T)` 是孤立点 |

于是 Lemma A.1 的三句话（HS 有限、紧自伴且 `g(2)` 可达、`spec ∖ {0}` 离散）全部证成。
-/

namespace Eliashberg

open Filter Topology Metric

noncomputable section

variable {f : ℕ → ℝ}

/-! ### 一、不同特征值的特征向量正交 -/

/-- **自伴算子不同特征值的特征向量正交**。实标量，无共轭问题：
`μ⟪v,w⟫ = ⟪Tv,w⟫ = ⟪v,Tw⟫ = ν⟪v,w⟫`，而 `μ ≠ ν`。 -/
lemma inner_eq_zero_of_eigen_ne {T : H →L[ℝ] H} (hT : IsSelfAdjoint T) {μ ν : ℝ} {v w : H}
    (hv : T v = μ • v) (hw : T w = ν • w) (hμν : μ ≠ ν) : inner ℝ v w = 0 := by
  have hsym : (↑T : H →ₗ[ℝ] H).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT
  have h1 : inner ℝ (T v) w = inner ℝ v (T w) := hsym v w
  rw [hv, hw, real_inner_smul_left, real_inner_smul_right] at h1
  have h2 : (μ - ν) * inner ℝ v w = 0 := by linarith [h1]
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd (sub_eq_zero.mp h) hμν
  · exact h

/-- `‖T v − T w‖² = μ² + ν²`（`v ⟂ w` 单位特征向量）。 -/
lemma norm_sub_eigen_sq {T : H →L[ℝ] H} {μ ν : ℝ} {v w : H}
    (hv : T v = μ • v) (hw : T w = ν • w) (hnv : ‖v‖ = 1) (hnw : ‖w‖ = 1)
    (ho : inner ℝ v w = (0:ℝ)) : ‖T v - T w‖ ^ 2 = μ ^ 2 + ν ^ 2 := by
  rw [hv, hw, norm_sub_sq_real, real_inner_smul_left, real_inner_smul_right, ho,
    norm_smul, norm_smul, hnv, hnw]
  simp [Real.norm_eq_abs, sq_abs]

/-! ### 二、非零谱点的单位特征向量 -/

/-- 非零谱点有单位特征向量（Fredholm 择一 + 归一化）。 -/
theorem exists_unit_eigenvector_of_mem_spectrum (hf : L1 f) {μ : ℝ} (hμ : μ ≠ 0)
    (hmem : μ ∈ spectrum ℝ (Op hf)) : ∃ v : H, ‖v‖ = 1 ∧ Op hf v = μ • v := by
  obtain ⟨v, hv⟩ := ((mem_spectrum_iff_hasEigenvalue hf hμ).mp hmem).exists_hasEigenvector
  have hv1 : Op hf v = μ • v := by
    have := hv.1; rw [Module.End.mem_eigenspace_iff] at this; exact this
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv.2
  refine ⟨‖v‖⁻¹ • v, ?_, ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
  · rw [map_smul, hv1, smul_comm]

/-! ### 三、主定理：远离 `0` 的谱只有有限多点 -/

/-- **`{μ ∈ spec(O[f]) : |μ| ≥ ε}` 有限**（`ε > 0`）。

反证：若无限，取一列互不相同的谱点 `μ n`（`|μ n| ≥ ε`）与单位特征向量 `e n`。
正交性给 `‖O e_n − O e_m‖² = μ_n² + μ_m² ≥ 2ε² ≥ ε²`（`n ≠ m`），
即 `{O e_n}` 在紧集 `closure (O '' ball 0 2)` 中两两相距 `≥ ε`；
而紧集序列紧，收敛子列中有两项相距 `< ε`，矛盾。 -/
theorem finite_spectrum_abs_ge (hf : L1 f) {ε : ℝ} (hε : 0 < ε) :
    {μ : ℝ | μ ∈ spectrum ℝ (Op hf) ∧ ε ≤ |μ|}.Finite := by
  by_contra hinf
  rw [Set.not_finite] at hinf
  set S := {μ : ℝ | μ ∈ spectrum ℝ (Op hf) ∧ ε ≤ |μ|} with hS
  obtain emb := hinf.natEmbedding
  set μ : ℕ → ℝ := fun n => ((emb n : ↑S) : ℝ) with hμdef
  have hμinj : Function.Injective μ := fun n m h => emb.injective (Subtype.ext h)
  have hμS : ∀ n, μ n ∈ S := fun n => (emb n).2
  have hμne : ∀ n, μ n ≠ 0 := by
    intro n h
    have h2 := (hμS n).2
    rw [h, abs_zero] at h2
    linarith
  choose e hnorm heig using fun n =>
    exists_unit_eigenvector_of_mem_spectrum hf (hμne n) (hμS n).1
  -- 两两分离
  have hsep : ∀ n m, n ≠ m → ε ≤ ‖Op hf (e n) - Op hf (e m)‖ := by
    intro n m hnm
    have hμnm : μ n ≠ μ m := fun h => hnm (hμinj h)
    have ho := inner_eq_zero_of_eigen_ne (Op_isSelfAdjoint hf) (heig n) (heig m) hμnm
    have hsq := norm_sub_eigen_sq (heig n) (heig m) (hnorm n) (hnorm m) ho
    have h1 : ε ^ 2 ≤ ‖Op hf (e n) - Op hf (e m)‖ ^ 2 := by
      rw [hsq]
      have ha : ε ^ 2 ≤ μ n ^ 2 := by
        have := (hμS n).2
        nlinarith [abs_nonneg (μ n), sq_abs (μ n)]
      have hb : (0:ℝ) ≤ μ m ^ 2 := sq_nonneg _
      linarith
    nlinarith [h1, norm_nonneg (Op hf (e n) - Op hf (e m)), hε]
  -- 紧性矛盾
  have hcpt : IsCompact (closure ((Op hf) '' ball (0:H) 2)) :=
    (Op_isCompactOperator hf).isCompact_closure_image_ball 2
  have hmem : ∀ n, Op hf (e n) ∈ closure ((Op hf) '' ball (0:H) 2) := fun n =>
    subset_closure ⟨e n, by simp [mem_ball, dist_eq_norm, hnorm n], rfl⟩
  obtain ⟨a, -, φ, hφ, hlim⟩ := hcpt.isSeqCompact hmem
  have h2 : ∀ᶠ n in atTop, dist (Op hf (e (φ n))) a < ε / 2 := by
    filter_upwards [hlim (Metric.ball_mem_nhds a (by linarith : (0:ℝ) < ε / 2))] with n hn
    simpa [mem_ball] using hn
  obtain ⟨N, hN⟩ := eventually_atTop.mp h2
  have hd1 := hN N le_rfl
  have hd2 := hN (N + 1) (by omega)
  have hne : φ N ≠ φ (N + 1) := by have := hφ (by omega : N < N + 1); omega
  have hlow := hsep _ _ hne
  rw [← dist_eq_norm] at hlow
  have htri := dist_triangle (Op hf (e (φ N))) a (Op hf (e (φ (N + 1))))
  rw [dist_comm a] at htri
  linarith

/-- 特征值形式：`{μ : μ` 是 `O[f]` 的特征值且 `|μ| ≥ ε}` 有限。 -/
theorem eigenvalues_abs_ge_finite (hf : L1 f) {ε : ℝ} (hε : 0 < ε) :
    {μ : ℝ | Module.End.HasEigenvalue (Op hf : Module.End ℝ H) μ ∧ ε ≤ |μ|}.Finite := by
  apply (finite_spectrum_abs_ge hf hε).subset
  intro μ hμ
  refine ⟨?_, hμ.2⟩
  have hμ0 : μ ≠ 0 := by
    intro h
    have h2 := hμ.2
    rw [h, abs_zero] at h2
    linarith
  exact (mem_spectrum_iff_hasEigenvalue hf hμ0).mpr hμ.1

/-! ### 四、离散性：`0` 是唯一可能的聚点 -/

/-- **`0` 之外的每一点都有一个只可能碰到自己的邻域**。
这一条同时给出「非零谱点是孤立点」与「非零点不是谱的聚点」。

证明：`F := S_{|x|/2} ∖ {x}` 有限 ⇒ 闭，而 `x ∉ F`，故 `∃ δ₁ > 0, ball x δ₁ ⊆ Fᶜ`；
取 `δ := min δ₁ (|x|/2)`，则 `ball x δ` 里的谱点 `ν` 满足 `|ν| ≥ |x| − |ν − x| > |x|/2`，
于是 `ν ∈ S_{|x|/2}` 且 `ν ∉ F`，只能 `ν = x`。 -/
theorem exists_ball_inter_subset (hf : L1 f) {x : ℝ} (hx : x ≠ 0) :
    ∃ δ > 0, spectrum ℝ (Op hf) ∩ ball x δ ⊆ {x} := by
  have hap : 0 < |x| := abs_pos.mpr hx
  have hε : 0 < |x| / 2 := by linarith
  set F := {ν : ℝ | ν ∈ spectrum ℝ (Op hf) ∧ |x| / 2 ≤ |ν|} \ {x} with hF
  have hFfin : F.Finite := (finite_spectrum_abs_ge hf hε).subset (fun y hy => hy.1)
  have hxF : x ∈ Fᶜ := fun h => h.2 rfl
  obtain ⟨δ₁, hδ₁, hball⟩ :=
    Metric.mem_nhds_iff.mp (hFfin.isClosed.isOpen_compl.mem_nhds hxF)
  refine ⟨min δ₁ (|x| / 2), lt_min hδ₁ hε, ?_⟩
  intro ν hν
  obtain ⟨hνspec, hνball⟩ := hν
  rw [mem_ball, Real.dist_eq] at hνball
  have h1 : |ν - x| < |x| / 2 := lt_of_lt_of_le hνball (min_le_right _ _)
  have h2 : |x| / 2 ≤ |ν| := by
    have h := abs_sub_abs_le_abs_sub x ν
    rw [abs_sub_comm x ν] at h
    linarith
  have h3 : ν ∈ Fᶜ := hball (by
    rw [mem_ball, Real.dist_eq]
    exact lt_of_lt_of_le hνball (min_le_left _ _))
  by_contra hne
  exact h3 ⟨⟨hνspec, h2⟩, hne⟩

/-- **非零谱点是孤立点**：`∃ δ > 0, spec ∩ ball μ δ = {μ}`。 -/
theorem exists_ball_inter_spectrum_eq (hf : L1 f) {μ : ℝ} (hμ : μ ≠ 0)
    (hmem : μ ∈ spectrum ℝ (Op hf)) :
    ∃ δ > 0, spectrum ℝ (Op hf) ∩ ball μ δ = {μ} := by
  obtain ⟨δ, hδ, hsub⟩ := exists_ball_inter_subset hf hμ
  exact ⟨δ, hδ, Set.Subset.antisymm hsub (by
    intro ν hν
    rw [Set.mem_singleton_iff] at hν
    subst hν
    exact ⟨hmem, by simpa [mem_ball] using hδ⟩)⟩

/-- **`0` 是唯一可能的聚点**：`x ≠ 0 ⇒ x` 不是 `spec(O[f])` 的聚点。 -/
theorem not_accPt_of_ne_zero (hf : L1 f) {x : ℝ} (hx : x ≠ 0) :
    ¬ AccPt x (Filter.principal (spectrum ℝ (Op hf))) := by
  rw [accPt_iff_nhds]
  intro h
  obtain ⟨δ, hδ, hsub⟩ := exists_ball_inter_subset hf hx
  obtain ⟨y, ⟨hyball, hyspec⟩, hyne⟩ := h (ball x δ) (Metric.ball_mem_nhds x hδ)
  exact hyne (hsub ⟨hyspec, hyball⟩)

/-- `spec(O[f]) ∖ {0}` 可数（可数多个有限集之并）。 -/
theorem spectrum_diff_zero_countable (hf : L1 f) :
    (spectrum ℝ (Op hf) \ {0}).Countable := by
  have hsub : spectrum ℝ (Op hf) \ {0}
      ⊆ ⋃ n : ℕ, {μ : ℝ | μ ∈ spectrum ℝ (Op hf) ∧ (1:ℝ) / (n + 1) ≤ |μ|} := by
    intro μ hμ
    obtain ⟨hspec, hne⟩ := hμ
    have hap : 0 < |μ| := abs_pos.mpr (by simpa using hne)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hap
    exact Set.mem_iUnion.mpr ⟨n, hspec, le_of_lt hn⟩
  refine Set.Countable.mono hsub (Set.countable_iUnion (fun n => ?_))
  exact (finite_spectrum_abs_ge hf (by positivity : (0:ℝ) < 1 / ((n:ℝ) + 1))).countable

/-! ### 五、特化到 `A = O[k⁻²]` 与 `K(P,T)` -/

/-- **Lemma A.1 最后一句**（定量形式）：`{μ ∈ spec A : |μ| ≥ ε}` 有限。 -/
theorem Aop_finite_spectrum_abs_ge {ε : ℝ} (hε : 0 < ε) :
    {μ : ℝ | μ ∈ spectrum ℝ Aop ∧ ε ≤ |μ|}.Finite :=
  finite_spectrum_abs_ge invSq_L1 hε

/-- **Lemma A.1 最后一句**：`A` 的非零谱点是孤立点。 -/
theorem Aop_isolated {μ : ℝ} (hμ : μ ≠ 0) (hmem : μ ∈ spectrum ℝ Aop) :
    ∃ δ > 0, spectrum ℝ Aop ∩ ball μ δ = {μ} :=
  exists_ball_inter_spectrum_eq invSq_L1 hμ hmem

/-- **Lemma A.1 最后一句**：`0` 是 `spec A` 唯一可能的聚点。 -/
theorem Aop_not_accPt {x : ℝ} (hx : x ≠ 0) :
    ¬ AccPt x (Filter.principal (spectrum ℝ Aop)) :=
  not_accPt_of_ne_zero invSq_L1 hx

/-- `spec A ∖ {0}` 可数。 -/
theorem Aop_spectrum_diff_zero_countable : (spectrum ℝ Aop \ {0}).Countable :=
  spectrum_diff_zero_countable invSq_L1

/-- `g(2)` 本身是 `spec A` 的孤立点。 -/
theorem g2_isolated : ∃ δ > 0, spectrum ℝ Aop ∩ ball g2 δ = {g2} :=
  Aop_isolated g2_ne_zero isGreatest_spectrum_Aop.1

open MeasureTheory in
/-- `K(P,T)` 的同一结论：远离 `0` 的谱只有有限多点。 -/
theorem kk_finite_spectrum_abs_ge (P : Measure ℝ) [IsProbabilityMeasure P]
    (hm : Integrable (fun ω => ω ^ 2) P) (T : ℝ) (hT : 0 < T) {ε : ℝ} (hε : 0 < ε) :
    {μ : ℝ | μ ∈ spectrum ℝ (Op (L1_FT P hm T hT)) ∧ ε ≤ |μ|}.Finite :=
  finite_spectrum_abs_ge (L1_FT P hm T hT) hε

open MeasureTheory in
/-- `k(P,T)` 是 `spec K(P,T)` 的孤立点。 -/
theorem kk_isolated (P : Measure ℝ) [IsProbabilityMeasure P] (hP : ∀ᵐ ω ∂P, 0 < ω)
    (hm : Integrable (fun ω => ω ^ 2) P) (T : ℝ) (hT : 0 < T) :
    ∃ δ > 0, spectrum ℝ (Op (L1_FT P hm T hT)) ∩ ball (kk P T) δ = {kk P T} :=
  exists_ball_inter_spectrum_eq (L1_FT P hm T hT) (ne_of_gt (kk_pos P hP hm T hT))
    (lam1_mem_spectrum (L1_FT P hm T hT))

end

end Eliashberg



