import Eliashberg.Compact

/-!
# Proposition 1.12(3) 在 `ℓ²` 上：顶特征空间与锥相交

论文：

> **Proposition 1.12(3).** Let `F` be admissible and `λ₁ := λ₁(O[F])`. Then there exists
> `v ∈ C` with `‖v‖ = 1` and `O[F] v = λ₁ v`.

论文的证明走谱投影：`Π := E({λ₁})` 非零，且由 Prop 1.11（半群保锥）与 `C` 的闭性，
`Πv = lim_{t→∞} e^{−tλ₁} e^{tO[F]} v ∈ C` 对 `v ∈ C` 成立，再用 `C − C` 稠密排除 `Π = 0`。
mathlib 没有谱投影，也没有 `e^{tA}` 的强收敛 (F5)。

本文件给一个只用**紧算子的序列紧性**的证明，与 `Discrete.lean` 的工具相同：

1. 对每个 `N`，取截断 `P_{N+1} O[F] P_{N+1}` 的锥内单位特征向量 `w_N`
   （`exists_coneEigen`，有限维 Perron–Frobenius 型结论，`Spectral.lean`），
   零延拓成 `ℓ²` 中的单位向量 `v_N := P_{N+1} w_N ∈ C`。特征值 `λ_N := λ₁^{(N+1)} ↑ λ₁`。
2. **残差趋于零**：`O[F] v_N − λ_N v_N` 只在坐标 `n ≥ N+1` 处非零，那里的值是
   `∑_{m≤N} O_{nm} w_N(m)`，由 Cauchy–Schwarz 不超过 `√(∑_{m} O_{nm}²)`；
   于是 `‖O[F] v_N − λ_N v_N‖² ≤ ∑_{n≥N+1} ∑_m O_{nm}²`，是 HS 双重级数的尾部，`→ 0`
   （`Of_sq_summable` + `tendsto_sum_nat_add`）。
3. **紧性**：`{O[F] v_N}` 落在紧集 `closure (O[F] '' closedBall 0 1)` 中，取收敛子列
   `O[F] v_{φ(k)} → y`。由 2. 与 `λ_{φ(k)} → λ₁ > 0`，`v_{φ(k)} = λ_{φ(k)}⁻¹ (O[F] v_{φ(k)} − 残差) → x := λ₁⁻¹ y`。
4. **极限的性质**：`C` 闭（逐坐标极限，`InCone.of_tendsto`）⇒ `x ∈ C`；范数连续 ⇒ `‖x‖ = 1`；
   `O[F]` 连续 ⇒ `O[F] x = lim O[F] v_{φ(k)} = y = λ₁ x`。

假设与论文一致（`F` admissible：非负、非增、`ℓ¹`、`F(1) > 0`），结论逐字相同。
`F(1) > 0` 只用来保证 `λ₁ > 0`，从而能除以 `λ_N`。
-/

namespace Eliashberg

open scoped BigOperators ENNReal
open Filter Topology

noncomputable section

/-! ### 锥 `C`：非负且递减 -/

/-- 论文的锥 `C ⊆ ℓ²`：坐标非负且递减。 -/
def InCone (x : H) : Prop :=
  (∀ n, 0 ≤ (x : ℕ → ℝ) n) ∧ (∀ i j, i ≤ j → (x : ℕ → ℝ) j ≤ (x : ℕ → ℝ) i)

/-- 锥对非负标量乘法的封闭性。 -/
lemma InCone.smul {x : H} (hx : InCone x) {c : ℝ} (hc : 0 ≤ c) : InCone (c • x) :=
  ⟨fun n => mul_nonneg hc (hx.1 n), fun i j hij => by
    simpa using mul_le_mul_of_nonneg_left (hx.2 i j hij) hc⟩

/-- 坐标泛函连续：`ℓ²` 收敛 ⇒ 逐坐标收敛。 -/
lemma tendsto_coord {u : ℕ → H} {x : H} (hx : Tendsto u atTop (𝓝 x)) (n : ℕ) :
    Tendsto (fun N => (u N : ℕ → ℝ) n) atTop (𝓝 ((x : ℕ → ℝ) n)) :=
  tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero_norm
    (fun N => by
      have h := lp.norm_apply_le_norm (p := 2) (by norm_num) (u N - x) n
      simpa [lp.coeFn_sub, Pi.sub_apply] using h)
    (tendsto_iff_norm_sub_tendsto_zero.mp hx))

/-- **锥是闭的**：锥内序列的 `ℓ²` 极限仍在锥内。 -/
lemma InCone.of_tendsto {u : ℕ → H} (hu : ∀ N, InCone (u N)) {x : H}
    (hx : Tendsto u atTop (𝓝 x)) : InCone x := by
  refine ⟨fun n => le_of_tendsto_of_tendsto tendsto_const_nhds (tendsto_coord hx n)
      (Eventually.of_forall fun N => (hu N).1 n), fun i j hij => ?_⟩
  exact le_of_tendsto_of_tendsto (tendsto_coord hx j) (tendsto_coord hx i)
    (Eventually.of_forall fun N => (hu N).2 i j hij)

/-! ### HS 尾部：`∑_{n≥K} ∑_m O_{nm}² → 0` -/

/-- 第 `n` 行的平方和 `ρ_n := ∑_m O[f]_{nm}²`。 -/
def rowSq (f : ℕ → ℝ) (n : ℕ) : ℝ := ∑' m, Of f n m ^ 2

lemma rowSq_nonneg (f : ℕ → ℝ) (n : ℕ) : 0 ≤ rowSq f n := tsum_nonneg fun m => sq_nonneg _

lemma summable_rowSq {f : ℕ → ℝ} (hf : L1 f) : Summable (rowSq f) := (Of_sq_summable hf).prod

/-- `∑_{n≥K} ρ_n → 0`。 -/
lemma rowSq_tail_tendsto {f : ℕ → ℝ} (hf : L1 f) :
    Tendsto (fun K => ∑' n, rowSq f (n + K)) atTop (𝓝 0) :=
  tendsto_sum_nat_add (rowSq f)

/-- 行内有限 Cauchy–Schwarz：`(∑_{m<M} O_{nm} w_m)² ≤ ρ_n ∑_{m<M} w_m²`。 -/
lemma sq_row_dot_le {f : ℕ → ℝ} (hf : L1 f) (w : ℕ → ℝ) (M n : ℕ) :
    (∑ m ∈ Finset.range M, Of f n m * w m) ^ 2 ≤ rowSq f n * ∑ m ∈ Finset.range M, w m ^ 2 := by
  calc (∑ m ∈ Finset.range M, Of f n m * w m) ^ 2
      ≤ (∑ m ∈ Finset.range M, Of f n m ^ 2) * (∑ m ∈ Finset.range M, w m ^ 2) :=
        Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ ≤ rowSq f n * ∑ m ∈ Finset.range M, w m ^ 2 :=
        mul_le_mul_of_nonneg_right
          (Summable.sum_le_tsum _ (fun m _ => sq_nonneg _) (Of_row_sq_summable hf n))
          (Finset.sum_nonneg fun m _ => sq_nonneg _)

/-! ### 有限锥内特征向量搬进 `ℓ²` -/

/-- `v_N := P_{N+1} w_N`。 -/
def coneVec {F : ℕ → ℝ} {N : ℕ} (E : ConeEigen F N) : H := PN E.w (N + 1)

lemma coneVec_apply_of_lt {F : ℕ → ℝ} {N : ℕ} (E : ConeEigen F N) {n : ℕ} (hn : n < N + 1) :
    ((coneVec E : H) : ℕ → ℝ) n = E.w n := PN_apply_of_lt _ _ _ hn

lemma coneVec_apply_of_ge {F : ℕ → ℝ} {N : ℕ} (E : ConeEigen F N) {n : ℕ} (hn : N + 1 ≤ n) :
    ((coneVec E : H) : ℕ → ℝ) n = 0 := PN_apply_of_ge _ _ _ hn

/-- `v_N ∈ C`。 -/
lemma coneVec_inCone {F : ℕ → ℝ} {N : ℕ} (E : ConeEigen F N) : InCone (coneVec E) := by
  refine ⟨fun n => ?_, fun i j hij => ?_⟩
  · by_cases h : n < N + 1
    · rw [coneVec_apply_of_lt E h]; exact E.nonneg n
    · rw [coneVec_apply_of_ge E (by omega)]
  · by_cases hj : j < N + 1
    · have hi : i < N + 1 := by omega
      rw [coneVec_apply_of_lt E hi, coneVec_apply_of_lt E hj]; exact E.anti i j hij
    · rw [coneVec_apply_of_ge E (by omega)]
      by_cases hi : i < N + 1
      · rw [coneVec_apply_of_lt E hi]; exact E.nonneg i
      · rw [coneVec_apply_of_ge E (by omega)]

/-- `‖v_N‖ = 1`。 -/
lemma coneVec_norm {F : ℕ → ℝ} {N : ℕ} (E : ConeEigen F N) : ‖coneVec E‖ = 1 := by
  have h := PN_norm_sq E.w (N + 1)
  rw [E.unit] at h
  have h0 : 0 ≤ ‖PN E.w (N + 1)‖ := norm_nonneg _
  unfold coneVec
  nlinarith [h, h0]

/-- 残差 `r_N := O[F] v_N − λ_N v_N` 的坐标：`n ≤ N` 处为零，`n > N` 处为 `∑_{m≤N} O_{nm} w_m`。 -/
lemma resid_apply {F : ℕ → ℝ} (hF : L1 F) {N : ℕ} (E : ConeEigen F N) (n : ℕ) :
    ((Op hF (coneVec E) - lamN F N • coneVec E : H) : ℕ → ℝ) n
      = if n < N + 1 then 0 else ∑ m ∈ Finset.range (N + 1), Of F n m * E.w m := by
  rw [lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  unfold coneVec
  rw [Op_PN_apply]
  split_ifs with h
  · rw [PN_apply_of_lt _ _ _ h, E.eigen n h]; ring
  · rw [PN_apply_of_ge _ _ _ (by omega)]; ring

/-- **残差界**：`‖r_N‖² ≤ ∑_{n≥N+1} ρ_n`。 -/
lemma resid_norm_sq_le {F : ℕ → ℝ} (hF : L1 F) {N : ℕ} (E : ConeEigen F N) :
    ‖Op hF (coneVec E) - lamN F N • coneVec E‖ ^ 2 ≤ ∑' n, rowSq F (n + (N + 1)) := by
  set r : H := Op hF (coneVec E) - lamN F N • coneVec E with hr
  have hcoord : ∀ n, ((r : H) : ℕ → ℝ) n ^ 2 ≤ if n < N + 1 then 0 else rowSq F n := by
    intro n
    rw [hr, resid_apply hF E n]
    split_ifs with h
    · simp
    · have := sq_row_dot_le hF E.w (N + 1) n
      rw [E.unit, mul_one] at this
      exact this
  -- `∑_n (r n)² ≤ ∑_n [n ≥ N+1] ρ_n = ∑_k ρ_{k+N+1}`
  have hsum_shift : Summable (fun n => if n < N + 1 then (0:ℝ) else rowSq F n) :=
    Summable.of_nonneg_of_le (fun n => by split_ifs <;> [exact le_rfl; exact rowSq_nonneg F n])
      (fun n => by split_ifs <;> [exact rowSq_nonneg F n; exact le_rfl]) (summable_rowSq hF)
  have h1 : ‖r‖ ^ 2 ≤ ∑' n, (if n < N + 1 then (0:ℝ) else rowSq F n) := by
    rw [H_norm_sq]
    exact Summable.tsum_le_tsum hcoord (H_summable_sq r) hsum_shift
  have h2 : (∑' n, (if n < N + 1 then (0:ℝ) else rowSq F n)) = ∑' n, rowSq F (n + (N + 1)) := by
    rw [← hsum_shift.sum_add_tsum_nat_add (N + 1)]
    rw [Finset.sum_eq_zero (fun n hn => by rw [if_pos (Finset.mem_range.mp hn)]), zero_add]
    exact tsum_congr fun n => by rw [if_neg (by omega)]
  rw [h2] at h1
  exact h1

/-- **残差趋于零**。 -/
lemma resid_tendsto_zero {F : ℕ → ℝ} (hF : L1 F) (E : ∀ N, ConeEigen F N) :
    Tendsto (fun N => Op hF (coneVec (E N)) - lamN F N • coneVec (E N)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have htail : Tendsto (fun N => ∑' n, rowSq F (n + (N + 1))) atTop (𝓝 0) :=
    (rowSq_tail_tendsto hF).comp (tendsto_add_atTop_nat 1)
  have hsq : Tendsto (fun N => Real.sqrt (∑' n, rowSq F (n + (N + 1)))) atTop (𝓝 0) := by
    have := htail.sqrt
    rwa [Real.sqrt_zero] at this
  refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) hsq
  have h := resid_norm_sq_le hF (E N)
  calc ‖Op hF (coneVec (E N)) - lamN F N • coneVec (E N)‖
      = Real.sqrt (‖Op hF (coneVec (E N)) - lamN F N • coneVec (E N)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (∑' n, rowSq F (n + (N + 1))) := Real.sqrt_le_sqrt h

/-! ### 主定理 -/

/-- **Proposition 1.12(3)（`ℓ²` 版）**：`F` admissible ⇒ 存在锥内单位向量 `x` 使 `O[F] x = λ₁ x`。

`F` admissible 按论文：非负、在 `k ≥ 1` 上非增、`ℓ¹`、`F(1) > 0`。 -/
theorem exists_cone_eigenvector_l2 {F : ℕ → ℝ} (hF : L1 F) (hnn : ∀ k, 1 ≤ k → 0 ≤ F k)
    (hanti : ∀ k, 1 ≤ k → F (k + 1) ≤ F k) (h1 : 0 < F 1) :
    ∃ x : H, InCone x ∧ ‖x‖ = 1 ∧ Op hF x = lam1 F • x := by
  -- 有限锥内单位特征向量
  have hE : ∀ N, Nonempty (ConeEigen F N) := fun N => exists_coneEigen F hanti hnn N
  let E : ∀ N, ConeEigen F N := fun N => (hE N).some
  set v : ℕ → H := fun N => coneVec (E N) with hv
  have hvnorm : ∀ N, ‖v N‖ = 1 := fun N => coneVec_norm (E N)
  have hvcone : ∀ N, InCone (v N) := fun N => coneVec_inCone (E N)
  -- `λ_N → λ₁ > 0`
  have hlam : Tendsto (lamN F) atTop (𝓝 (lam1 F)) := lamN_tendsto hF
  have hlam1pos : 0 < lam1 F := lt_of_lt_of_le h1 (f1_le_lam1 hF)
  have hlamNpos : ∀ N, 0 < lamN F N := fun N => lt_of_lt_of_le h1 (f1_le_lamN F N)
  -- 残差 → 0
  have hres : Tendsto (fun N => Op hF (v N) - lamN F N • v N) atTop (𝓝 0) :=
    resid_tendsto_zero hF E
  -- 紧性：`O[F] v_N` 落在紧集里，取收敛子列
  have hcpt : IsCompact (closure ((Op hF) '' Metric.closedBall (0:H) 1)) :=
    (Op_isCompactOperator hF).isCompact_closure_image_closedBall 1
  have hmem : ∀ N, Op hF (v N) ∈ closure ((Op hF) '' Metric.closedBall (0:H) 1) := fun N =>
    subset_closure ⟨v N, by simp [Metric.mem_closedBall, dist_eq_norm, hvnorm N], rfl⟩
  obtain ⟨y, -, φ, hφ, hy⟩ := hcpt.isSeqCompact hmem
  -- 沿子列：`v_{φ k} = λ_{φ k}⁻¹ • (O[F] v_{φ k} − 残差) → λ₁⁻¹ • y`
  have hφtop : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hlamφ : Tendsto (fun k => lamN F (φ k)) atTop (𝓝 (lam1 F)) := hlam.comp hφtop
  have hresφ : Tendsto (fun k => Op hF (v (φ k)) - lamN F (φ k) • v (φ k)) atTop (𝓝 0) :=
    hres.comp hφtop
  have hinv : Tendsto (fun k => (lamN F (φ k))⁻¹) atTop (𝓝 (lam1 F)⁻¹) :=
    hlamφ.inv₀ (ne_of_gt hlam1pos)
  set x : H := (lam1 F)⁻¹ • y with hx
  have hvφ : Tendsto (fun k => v (φ k)) atTop (𝓝 x) := by
    have hformula : ∀ k, v (φ k) = (lamN F (φ k))⁻¹ •
        (Op hF (v (φ k)) - (Op hF (v (φ k)) - lamN F (φ k) • v (φ k))) := by
      intro k
      rw [sub_sub_cancel, smul_smul, inv_mul_cancel₀ (ne_of_gt (hlamNpos (φ k))), one_smul]
    have hlim : Tendsto (fun k => (lamN F (φ k))⁻¹ •
        (Op hF (v (φ k)) - (Op hF (v (φ k)) - lamN F (φ k) • v (φ k)))) atTop
        (𝓝 ((lam1 F)⁻¹ • (y - 0))) :=
      hinv.smul (hy.sub hresφ)
    rw [sub_zero] at hlim
    exact hlim.congr (fun k => (hformula k).symm)
  refine ⟨x, InCone.of_tendsto (fun k => hvcone (φ k)) hvφ, ?_, ?_⟩
  · -- 范数连续
    have h := hvφ.norm
    have hc : Tendsto (fun k => ‖v (φ k)‖) atTop (𝓝 1) := by
      simp only [hvnorm]; exact tendsto_const_nhds
    exact tendsto_nhds_unique h hc
  · -- `O[F] x = y = λ₁ x`
    have hOx : Tendsto (fun k => Op hF (v (φ k))) atTop (𝓝 (Op hF x)) :=
      ((Op hF).continuous.tendsto x).comp hvφ
    have hOxy : Op hF x = y := tendsto_nhds_unique hOx hy
    rw [hOxy, hx, smul_smul, mul_inv_cancel₀ (ne_of_gt hlam1pos), one_smul]

/-! ### 特化：`K(P,T)` 与 `A = O[k⁻²]` -/

open MeasureTheory in
/-- **Prop 1.12(3)** 对 `K(P,T) = O[F_{P,T}]`：`k(P,T)` 有锥内单位特征向量。 -/
theorem kk_exists_cone_eigenvector (P : Measure ℝ) [IsProbabilityMeasure P] (hP : ∀ᵐ ω ∂P, 0 < ω)
    (hm : Integrable (fun ω => ω ^ 2) P) (T : ℝ) (hT : 0 < T) :
    ∃ x : H, InCone x ∧ ‖x‖ = 1 ∧ Op (L1_FT P hm T hT) x = kk P T • x :=
  exists_cone_eigenvector_l2 (L1_FT P hm T hT) (FT_nonneg' P T) (FT_anti_k P hP T hT)
    (FT_pos P hP 1 le_rfl T hT)

/-- **Prop 1.12(3)** 对 Appendix A 的 `A = O[k⁻²]`：`g(2)` 有锥内单位特征向量。 -/
theorem g2_exists_cone_eigenvector : ∃ x : H, InCone x ∧ ‖x‖ = 1 ∧ Aop x = g2 • x :=
  exists_cone_eigenvector_l2 invSq_L1 (fun k _ => by positivity)
    (fun k hk => by
      have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
      apply one_div_le_one_div_of_le (by positivity)
      push_cast
      nlinarith)
    (by norm_num)

end

end Eliashberg
