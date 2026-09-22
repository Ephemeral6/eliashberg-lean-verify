import Eliashberg.Lam1

/-!
# `O[f]` 作为 `ℓ²` 上的有界自伴算子；`λ₁ = max spec`

本文件补上「忠实性」：论文把 `k(P,T)` 定义为紧自伴算子 `K(P,T)` 在 `ℓ²` 上的顶谱点
`λ₁ = max spec`，而本库此前用 Remark 1.2(b) 的「有限 Rayleigh 商上确界」`lam1`。这里证明两者相等：

* `Op f hf : H →L[ℝ] H`（`H := lp (ℕ → ℝ) 2`）：由 Schur 检验（`row_abs_sum_le`）构造，
  `(Op f x)_n = ∑_m O[f]_{nm} x_m`，`‖Op f‖ ≤ 5‖f‖_ℓ¹`（Lemma 0.2.1）
* `Op_isSelfAdjoint`：自伴（在有限支撑向量上验证，再由连续性与 `lp.hasSum_single` 的稠密性延拓）
* `inner_Op_self_le`：`⟨Op x, x⟩ ≤ lam1 f ‖x‖²`
* `spectrum_le_lam1`：`spec(Op f) ⊆ (−∞, lam1 f]`——由 `lam1·1 − Op` 正、mathlib 的
  `IsPositive.spectrumRestricts`
* `lam1_mem_spectrum`：`lam1 f ∈ spec(Op f)`——由 mathlib 的
  `rayleighQuotient_le_of_norm_mem_resolventSet`（自伴算子的 `‖T‖` 在谱中）作用于 `Op + c`
* **`sSup_spectrum_eq_lam1`**：`sSup (spectrum ℝ (Op f hf)) = lam1 f`，且是最大值

于是本库全部主定理中的 `lam1` 可以逐字换成论文的 `λ₁(K)`。
-/

namespace Eliashberg

open scoped BigOperators ENNReal
open Filter Topology

noncomputable section

/-- `ℓ² := lp (ℕ → ℝ) 2`。 -/
abbrev H := lp (fun _ : ℕ => ℝ) 2

instance : Nontrivial H := ⟨⟨lp.single 2 0 (1:ℝ), 0, by
  intro h
  have := congrFun (congrArg (fun (v : H) => (v : ℕ → ℝ)) h) 0
  simp at this⟩⟩

/-! ### `ℓ²` 的坐标算术 -/

lemma H_inner (x y : H) : inner ℝ x y = ∑' n, (x : ℕ → ℝ) n * (y : ℕ → ℝ) n := by
  rw [lp.inner_eq_tsum]
  congr 1; funext n
  simp [RCLike.inner_apply, mul_comm]

lemma H_summable_mul (x y : H) : Summable (fun n => (x : ℕ → ℝ) n * (y : ℕ → ℝ) n) := by
  have h := lp.hasSum_inner (𝕜 := ℝ) x y
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial] at h
  exact (h.summable).congr (fun n => by ring)

lemma H_hasSum_sq (x : H) : HasSum (fun n => ((x : ℕ → ℝ) n) ^ 2) (‖x‖ ^ 2) := by
  have h := lp.hasSum_norm (p := 2) (by norm_num) x
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using h

lemma H_norm_sq (x : H) : ‖x‖ ^ 2 = ∑' n, ((x : ℕ → ℝ) n) ^ 2 := (H_hasSum_sq x).tsum_eq.symm

lemma H_summable_sq (x : H) : Summable (fun n => ((x : ℕ → ℝ) n) ^ 2) := (H_hasSum_sq x).summable

lemma H_sum_sq_le (x : H) (s : Finset ℕ) : ∑ n ∈ s, ((x : ℕ → ℝ) n) ^ 2 ≤ ‖x‖ ^ 2 :=
  (H_summable_sq x).sum_le_tsum s (fun n _ => sq_nonneg _) |>.trans_eq (H_norm_sq x).symm

lemma H_abs_le_norm (x : H) (n : ℕ) : |(x : ℕ → ℝ) n| ≤ ‖x‖ := by
  have := lp.norm_apply_le_norm (p := 2) (by norm_num) x n
  simpa using this

/-- 由「所有有限平方和 `≤ C`」造 `ℓ²` 元素。 -/
def mkH (g : ℕ → ℝ) (C : ℝ) (h : ∀ s : Finset ℕ, ∑ n ∈ s, g n ^ 2 ≤ C) : H :=
  ⟨g, memℓp_gen' (C := C) (fun s => by simpa [Real.rpow_two, sq_abs] using h s)⟩

lemma mkH_apply (g : ℕ → ℝ) (C : ℝ) (h : ∀ s : Finset ℕ, ∑ n ∈ s, g n ^ 2 ≤ C) (n : ℕ) :
    ((mkH g C h : H) : ℕ → ℝ) n = g n := rfl

lemma mkH_norm_le (g : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C) (h : ∀ s : Finset ℕ, ∑ n ∈ s, g n ^ 2 ≤ C ^ 2) :
    ‖mkH g (C ^ 2) h‖ ≤ C := by
  have h1 : ‖mkH g (C ^ 2) h‖ ^ 2 ≤ C ^ 2 := by
    rw [H_norm_sq]
    exact (H_summable_sq _).tsum_le_of_sum_le (fun s => h s)
  exact pow_le_pow_iff_left₀ (norm_nonneg _) hC two_ne_zero |>.mp h1

/-! ### 行和的可和性 -/

variable {f : ℕ → ℝ}

lemma row_summable (hf : L1 f) (n : ℕ) : Summable (fun m => |Of f n m|) :=
  summable_of_sum_range_le (fun m => abs_nonneg _) (fun M => row_abs_sum_le hf n M)

lemma row_tsum_le (hf : L1 f) (n : ℕ) : ∑' m, |Of f n m| ≤ 5 * l1 f :=
  (row_summable hf n).tsum_le_of_sum_range_le (fun M => row_abs_sum_le hf n M)

/-- 列和（由对称性 = 行和）。 -/
lemma col_sum_le (hf : L1 f) (m : ℕ) (s : Finset ℕ) : ∑ n ∈ s, |Of f n m| ≤ 5 * l1 f := by
  obtain ⟨M, hM⟩ := Finset.exists_nat_subset_range s
  calc ∑ n ∈ s, |Of f n m| = ∑ n ∈ s, |Of f m n| := by
        apply Finset.sum_congr rfl; intro n _; rw [Of_symm']
    _ ≤ ∑ n ∈ Finset.range M, |Of f m n| :=
        Finset.sum_le_sum_of_subset_of_nonneg hM (fun n _ _ => abs_nonneg _)
    _ ≤ 5 * l1 f := row_abs_sum_le hf m M

lemma apply_summable (hf : L1 f) (x : H) (n : ℕ) :
    Summable (fun m => Of f n m * (x : ℕ → ℝ) m) := by
  apply Summable.of_norm_bounded ((row_summable hf n).mul_right ‖x‖)
  intro m
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (H_abs_le_norm x m) (abs_nonneg _)

lemma apply_abs_summable (hf : L1 f) (x : H) (n : ℕ) :
    Summable (fun m => |Of f n m| * |(x : ℕ → ℝ) m|) := by
  apply Summable.of_nonneg_of_le (fun m => by positivity) _ ((row_summable hf n).mul_right ‖x‖)
  intro m
  exact mul_le_mul_of_nonneg_left (H_abs_le_norm x m) (abs_nonneg _)

lemma apply_abs_sq_summable (hf : L1 f) (x : H) (n : ℕ) :
    Summable (fun m => |Of f n m| * ((x : ℕ → ℝ) m) ^ 2) := by
  apply Summable.of_nonneg_of_le (fun m => by positivity) _ ((row_summable hf n).mul_right (‖x‖ ^ 2))
  intro m
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  have := H_abs_le_norm x m
  have h0 := abs_nonneg ((x : ℕ → ℝ) m)
  calc ((x : ℕ → ℝ) m) ^ 2 = |(x : ℕ → ℝ) m| ^ 2 := (sq_abs _).symm
    _ ≤ ‖x‖ ^ 2 := pow_le_pow_left₀ h0 this 2

/-! ### 加权 Cauchy–Schwarz（`tsum` 版） -/

/-- 有限版：`(∑ a|b|)² ≤ (∑ a)(∑ a b²)`，`a ≥ 0`。 -/
lemma finset_weighted_cs (s : Finset ℕ) (a b : ℕ → ℝ) (ha : ∀ m, 0 ≤ a m) :
    (∑ m ∈ s, a m * |b m|) ^ 2 ≤ (∑ m ∈ s, a m) * ∑ m ∈ s, a m * b m ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun m => Real.sqrt (a m))
    (fun m => Real.sqrt (a m) * |b m|)
  have e1 : ∀ m, Real.sqrt (a m) * (Real.sqrt (a m) * |b m|) = a m * |b m| := by
    intro m; rw [← mul_assoc, Real.mul_self_sqrt (ha m)]
  have e2 : ∀ m, Real.sqrt (a m) ^ 2 = a m := fun m => Real.sq_sqrt (ha m)
  have e3 : ∀ m, (Real.sqrt (a m) * |b m|) ^ 2 = a m * b m ^ 2 := by
    intro m; rw [mul_pow, Real.sq_sqrt (ha m), sq_abs]
  simp only [e1, e2, e3] at h
  exact h

/-- `tsum` 版。 -/
lemma tsum_weighted_cs (a b : ℕ → ℝ) (ha : ∀ m, 0 ≤ a m) (hsa : Summable a)
    (hsab : Summable (fun m => a m * |b m|)) (hsab2 : Summable (fun m => a m * b m ^ 2)) :
    (∑' m, a m * |b m|) ^ 2 ≤ (∑' m, a m) * ∑' m, a m * b m ^ 2 := by
  have h1 : Tendsto (fun M => (∑ m ∈ Finset.range M, a m * |b m|) ^ 2) atTop
      (𝓝 ((∑' m, a m * |b m|) ^ 2)) :=
    (hsab.hasSum.tendsto_sum_nat).pow 2
  have h2 : Tendsto (fun M => (∑ m ∈ Finset.range M, a m) * ∑ m ∈ Finset.range M, a m * b m ^ 2)
      atTop (𝓝 ((∑' m, a m) * ∑' m, a m * b m ^ 2)) :=
    (hsa.hasSum.tendsto_sum_nat).mul (hsab2.hasSum.tendsto_sum_nat)
  exact le_of_tendsto_of_tendsto' h1 h2 (fun M => finset_weighted_cs _ a b ha)

/-! ### 算子的构造 -/

/-- `(O[f] x)_n := ∑_m O[f]_{nm} x_m`。 -/
def applyRaw (f : ℕ → ℝ) (x : H) : ℕ → ℝ := fun n => ∑' m, Of f n m * (x : ℕ → ℝ) m

lemma applyRaw_sq_le (hf : L1 f) (x : H) (n : ℕ) :
    (applyRaw f x n) ^ 2 ≤ 5 * l1 f * ∑' m, |Of f n m| * ((x : ℕ → ℝ) m) ^ 2 := by
  have h1 : |applyRaw f x n| ≤ ∑' m, |Of f n m| * |(x : ℕ → ℝ) m| := by
    unfold applyRaw
    have := norm_tsum_le_tsum_norm (f := fun m => Of f n m * (x : ℕ → ℝ) m)
      (by simpa only [Real.norm_eq_abs, abs_mul] using apply_abs_summable hf x n)
    simpa only [Real.norm_eq_abs, abs_mul] using this
  have h2 := tsum_weighted_cs (fun m => |Of f n m|) (fun m => (x : ℕ → ℝ) m)
    (fun m => abs_nonneg _) (row_summable hf n) (apply_abs_summable hf x n)
    (apply_abs_sq_summable hf x n)
  have h3 := row_tsum_le hf n
  have h0 : 0 ≤ ∑' m, |Of f n m| * ((x : ℕ → ℝ) m) ^ 2 := tsum_nonneg (fun m => by positivity)
  calc (applyRaw f x n) ^ 2 = |applyRaw f x n| ^ 2 := (sq_abs _).symm
    _ ≤ (∑' m, |Of f n m| * |(x : ℕ → ℝ) m|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    _ ≤ (∑' m, |Of f n m|) * ∑' m, |Of f n m| * ((x : ℕ → ℝ) m) ^ 2 := h2
    _ ≤ 5 * l1 f * ∑' m, |Of f n m| * ((x : ℕ → ℝ) m) ^ 2 :=
        mul_le_mul_of_nonneg_right h3 h0

/-- Schur 检验：`∑_{n∈s} (O[f]x)_n² ≤ (5‖f‖₁)² ‖x‖²`。 -/
lemma applyRaw_sum_sq_le (hf : L1 f) (x : H) (s : Finset ℕ) :
    ∑ n ∈ s, (applyRaw f x n) ^ 2 ≤ (5 * l1 f) ^ 2 * ‖x‖ ^ 2 := by
  have hl := l1_nonneg f
  have hs2 : Summable (fun m => (5 * l1 f) * ((x : ℕ → ℝ) m) ^ 2) := (H_summable_sq x).mul_left _
  have hs1 : Summable (fun m => (∑ n ∈ s, |Of f n m|) * ((x : ℕ → ℝ) m) ^ 2) := by
    apply Summable.of_nonneg_of_le (fun m => by positivity) _ hs2
    intro m
    exact mul_le_mul_of_nonneg_right (col_sum_le hf m s) (sq_nonneg _)
  calc ∑ n ∈ s, (applyRaw f x n) ^ 2
      ≤ ∑ n ∈ s, 5 * l1 f * ∑' m, |Of f n m| * ((x : ℕ → ℝ) m) ^ 2 :=
        Finset.sum_le_sum (fun n _ => applyRaw_sq_le hf x n)
    _ = 5 * l1 f * ∑' m, (∑ n ∈ s, |Of f n m|) * ((x : ℕ → ℝ) m) ^ 2 := by
        rw [← Finset.mul_sum]
        congr 1
        rw [← Summable.tsum_finsetSum (fun n _ => apply_abs_sq_summable hf x n)]
        congr 1; funext m
        rw [Finset.sum_mul]
    _ ≤ 5 * l1 f * ∑' m, (5 * l1 f) * ((x : ℕ → ℝ) m) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Summable.tsum_le_tsum _ hs1 hs2
        intro m
        exact mul_le_mul_of_nonneg_right (col_sum_le hf m s) (sq_nonneg _)
    _ = (5 * l1 f) ^ 2 * ‖x‖ ^ 2 := by
        rw [tsum_mul_left, H_norm_sq]; ring

/-- `O[f] x ∈ ℓ²`。 -/
def applyH (hf : L1 f) (x : H) : H :=
  mkH (applyRaw f x) ((5 * l1 f * ‖x‖) ^ 2)
    (fun s => by rw [mul_pow]; exact applyRaw_sum_sq_le hf x s)

lemma applyH_apply (hf : L1 f) (x : H) (n : ℕ) :
    ((applyH hf x : H) : ℕ → ℝ) n = ∑' m, Of f n m * (x : ℕ → ℝ) m := rfl

lemma applyH_norm_le (hf : L1 f) (x : H) : ‖applyH hf x‖ ≤ 5 * l1 f * ‖x‖ :=
  mkH_norm_le _ _ (by have := l1_nonneg f; positivity) _

lemma applyH_add (hf : L1 f) (x y : H) : applyH hf (x + y) = applyH hf x + applyH hf y := by
  apply lp.ext
  funext n
  simp only [lp.coeFn_add, Pi.add_apply, applyH_apply]
  rw [← (apply_summable hf x n).tsum_add (apply_summable hf y n)]
  congr 1; funext m
  ring

lemma applyH_smul (hf : L1 f) (c : ℝ) (x : H) : applyH hf (c • x) = c • applyH hf x := by
  apply lp.ext
  funext n
  simp only [lp.coeFn_smul, Pi.smul_apply, applyH_apply, smul_eq_mul]
  rw [← tsum_mul_left]
  congr 1; funext m
  ring

/-- 线性映射。 -/
def opLin (hf : L1 f) : H →ₗ[ℝ] H where
  toFun := applyH hf
  map_add' := applyH_add hf
  map_smul' := fun c x => by simp [applyH_smul hf c x]

/-- **`O[f]` 作为 `ℓ²` 上的有界算子**，`‖O[f]‖ ≤ 5‖f‖_ℓ¹`（Lemma 0.2.1）。 -/
def Op (hf : L1 f) : H →L[ℝ] H :=
  (opLin hf).mkContinuous (5 * l1 f) (fun x => applyH_norm_le hf x)

lemma Op_apply (hf : L1 f) (x : H) (n : ℕ) :
    ((Op hf x : H) : ℕ → ℝ) n = ∑' m, Of f n m * (x : ℕ → ℝ) m := rfl

lemma Op_norm_le (hf : L1 f) : ‖Op hf‖ ≤ 5 * l1 f :=
  LinearMap.mkContinuous_norm_le _ (by have := l1_nonneg f; positivity) _

/-! ### 有限支撑向量 -/

/-- 截断 `P_N v`：`(P_N v)_n = v_n 1_{n<N}`。 -/
def PN (v : ℕ → ℝ) (N : ℕ) : H :=
  mkH (fun n => if n < N then v n else 0) (∑ n ∈ Finset.range N, v n ^ 2) (fun s => by
    calc ∑ n ∈ s, (if n < N then v n else 0) ^ 2
        = ∑ n ∈ s.filter (fun n => n < N), v n ^ 2 := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl; intro n _
          split_ifs <;> simp
      _ ≤ ∑ n ∈ Finset.range N, v n ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro n hn; simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢; exact hn.2
          · intro n _ _; exact sq_nonneg _)

lemma PN_apply (v : ℕ → ℝ) (N n : ℕ) : ((PN v N : H) : ℕ → ℝ) n = if n < N then v n else 0 := rfl

lemma PN_apply_of_lt (v : ℕ → ℝ) (N n : ℕ) (h : n < N) : ((PN v N : H) : ℕ → ℝ) n = v n := by
  rw [PN_apply, ite_eq_left h]

lemma PN_apply_of_ge (v : ℕ → ℝ) (N n : ℕ) (h : N ≤ n) : ((PN v N : H) : ℕ → ℝ) n = 0 := by
  rw [PN_apply, ite_eq_right (by omega)]

lemma PN_norm_sq (v : ℕ → ℝ) (N : ℕ) : ‖PN v N‖ ^ 2 = ∑ n ∈ Finset.range N, v n ^ 2 := by
  rw [H_norm_sq]
  rw [tsum_eq_sum (s := Finset.range N)]
  · apply Finset.sum_congr rfl; intro n hn
    rw [Finset.mem_range] at hn
    rw [PN_apply_of_lt v N n hn]
  · intro n hn
    rw [Finset.mem_range, not_lt] at hn
    rw [PN_apply_of_ge v N n hn]; ring

lemma Op_PN_apply (hf : L1 f) (v : ℕ → ℝ) (N n : ℕ) :
    ((Op hf (PN v N) : H) : ℕ → ℝ) n = ∑ m ∈ Finset.range N, Of f n m * v m := by
  rw [Op_apply]
  rw [tsum_eq_sum (s := Finset.range N)]
  · apply Finset.sum_congr rfl; intro m hm
    rw [Finset.mem_range] at hm
    rw [PN_apply_of_lt v N m hm]
  · intro m hm
    rw [Finset.mem_range, not_lt] at hm
    rw [PN_apply_of_ge v N m hm]; ring

/-- `⟨O[f] P_N v, P_N v⟩ = quadForm f v N`。 -/
lemma inner_Op_PN (hf : L1 f) (v : ℕ → ℝ) (N : ℕ) :
    inner ℝ (Op hf (PN v N)) (PN v N) = quadForm f v N := by
  rw [H_inner]
  rw [tsum_eq_sum (s := Finset.range N)]
  · unfold quadForm
    apply Finset.sum_congr rfl; intro n hn
    rw [Finset.mem_range] at hn
    rw [Op_PN_apply, PN_apply_of_lt v N n hn, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro m _; ring
  · intro n hn
    rw [Finset.mem_range, not_lt] at hn
    rw [PN_apply_of_ge v N n hn]; ring

/-- `P_N x = ∑_{i<N} e_i x_i`，故 `P_N x → x`（`lp.hasSum_single`）。 -/
lemma coeFn_sum_apply {ι : Type*} [DecidableEq ι] (s : Finset ι) (g : ι → H) (n : ℕ) :
    ((∑ i ∈ s, g i : H) : ℕ → ℝ) n = ∑ i ∈ s, ((g i : H) : ℕ → ℝ) n := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, lp.coeFn_add, Pi.add_apply, ih]

lemma PN_eq_sum_single (x : H) (N : ℕ) :
    PN (x : ℕ → ℝ) N = ∑ i ∈ Finset.range N, lp.single 2 i ((x : ℕ → ℝ) i) := by
  apply lp.ext
  funext n
  rw [PN_apply, coeFn_sum_apply]
  have : ∀ i, ((lp.single 2 i ((x : ℕ → ℝ) i) : H) : ℕ → ℝ) n
      = if n = i then (x : ℕ → ℝ) i else 0 := by
    intro i
    rw [lp.single_apply, Pi.single_apply]
  simp only [this]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_range]

lemma PN_tendsto (x : H) : Tendsto (fun N => PN (x : ℕ → ℝ) N) atTop (𝓝 x) := by
  have h := (lp.hasSum_single (p := 2) (by norm_num) x).tendsto_sum_nat
  simp only [PN_eq_sum_single]
  exact h

/-! ### 自伴性 -/

/-- 在有限支撑向量上的对称性：只涉及有限和与 `tsum` 的交换。 -/
lemma inner_Op_PN_symm (hf : L1 f) (x y : H) (N : ℕ) :
    inner ℝ (Op hf (PN (x : ℕ → ℝ) N)) y = inner ℝ (PN (x : ℕ → ℝ) N) (Op hf y) := by
  rw [H_inner, H_inner]
  -- 右边：只有 `n < N` 的项
  rw [tsum_eq_sum (s := Finset.range N) (f := fun n => ((PN (x : ℕ → ℝ) N : H) : ℕ → ℝ) n
      * ((Op hf y : H) : ℕ → ℝ) n)]
  · -- 左边：`∑' m, (∑_{n<N} O_{mn} x_n) y_m = ∑_{n<N} x_n ∑' m, O_{mn} y_m`
    have hs : ∀ n ∈ Finset.range N,
        Summable (fun m => Of f m n * (x : ℕ → ℝ) n * (y : ℕ → ℝ) m) := by
      intro n _
      have := (apply_summable hf y n).mul_left ((x : ℕ → ℝ) n)
      refine this.congr (fun m => ?_)
      rw [Of_symm']; ring
    calc ∑' m, ((Op hf (PN (x : ℕ → ℝ) N) : H) : ℕ → ℝ) m * (y : ℕ → ℝ) m
        = ∑' m, ∑ n ∈ Finset.range N, Of f m n * (x : ℕ → ℝ) n * (y : ℕ → ℝ) m := by
          congr 1; funext m
          rw [Op_PN_apply, Finset.sum_mul]
      _ = ∑ n ∈ Finset.range N, ∑' m, Of f m n * (x : ℕ → ℝ) n * (y : ℕ → ℝ) m :=
          Summable.tsum_finsetSum hs
      _ = ∑ n ∈ Finset.range N, ((PN (x : ℕ → ℝ) N : H) : ℕ → ℝ) n * ((Op hf y : H) : ℕ → ℝ) n := by
          apply Finset.sum_congr rfl; intro n hn
          rw [Finset.mem_range] at hn
          rw [PN_apply_of_lt _ N n hn, Op_apply, ← tsum_mul_left]
          congr 1; funext m
          rw [Of_symm']; ring
  · intro n hn
    rw [Finset.mem_range, not_lt] at hn
    rw [PN_apply_of_ge _ N n hn]; ring

/-- **`O[f]` 自伴**。 -/
theorem Op_isSelfAdjoint (hf : L1 f) : IsSelfAdjoint (Op hf) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  have h1 : Tendsto (fun N => inner ℝ (Op hf (PN (x : ℕ → ℝ) N)) y) atTop
      (𝓝 (inner ℝ (Op hf x) y)) :=
    (((Op hf).continuous.tendsto x).comp (PN_tendsto x)).inner tendsto_const_nhds
  have h2 : Tendsto (fun N => inner ℝ (PN (x : ℕ → ℝ) N) (Op hf y)) atTop
      (𝓝 (inner ℝ x (Op hf y))) :=
    (PN_tendsto x).inner tendsto_const_nhds
  have heq : (fun N => inner ℝ (Op hf (PN (x : ℕ → ℝ) N)) y)
      = fun N => inner ℝ (PN (x : ℕ → ℝ) N) (Op hf y) := by
    funext N; exact inner_Op_PN_symm hf x y N
  rw [heq] at h1
  exact tendsto_nhds_unique h1 h2

/-! ### Rayleigh 商与 `lam1` -/

lemma quadForm_smul_vec (f : ℕ → ℝ) (c : ℝ) (v : ℕ → ℝ) (N : ℕ) :
    quadForm f (fun n => c * v n) N = c ^ 2 * quadForm f v N := by
  unfold quadForm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro n _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro m _
  ring

lemma quadForm_eq_zero_of_sum_sq (f : ℕ → ℝ) (v : ℕ → ℝ) (N : ℕ)
    (h : ∑ n ∈ Finset.range N, v n ^ 2 = 0) : quadForm f v N = 0 := by
  have hz : ∀ n ∈ Finset.range N, v n = 0 := by
    intro n hn
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun n _ => sq_nonneg (v n))).mp h n hn
    exact pow_eq_zero_iff (two_ne_zero) |>.mp this
  unfold quadForm
  apply Finset.sum_eq_zero; intro n hn
  apply Finset.sum_eq_zero; intro m _
  rw [hz n hn]; ring

/-- 齐次形式：`quadForm f v N ≤ lam1 f · ∑_{n<N} v_n²`。 -/
lemma quadForm_le_lam1_mul (hf : L1 f) (v : ℕ → ℝ) (N : ℕ) :
    quadForm f v N ≤ lam1 f * ∑ n ∈ Finset.range N, v n ^ 2 := by
  set S := ∑ n ∈ Finset.range N, v n ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun n _ => sq_nonneg _)
  rcases eq_or_lt_of_le hS0 with h | h
  · rw [quadForm_eq_zero_of_sum_sq f v N h.symm, ← h, mul_zero]
  · set c := (Real.sqrt S)⁻¹ with hc
    have hsq : 0 < Real.sqrt S := Real.sqrt_pos.mpr h
    have hc2 : c ^ 2 = S⁻¹ := by rw [hc, inv_pow, Real.sq_sqrt hS0]
    have hunit : ∑ n ∈ Finset.range N, (c * v n) ^ 2 = 1 := by
      have : ∑ n ∈ Finset.range N, (c * v n) ^ 2 = c ^ 2 * S := by
        rw [hS, Finset.mul_sum]; apply Finset.sum_congr rfl; intro n _; ring
      rw [this, hc2]; exact inv_mul_cancel₀ (ne_of_gt h)
    have := quadForm_le_lam1 hf (fun n => c * v n) N hunit
    rw [quadForm_smul_vec, hc2] at this
    rw [inv_mul_le_iff₀ h] at this
    linarith

/-- `⟨O[f] x, x⟩ ≤ lam1 f ‖x‖²`（由有限支撑向量的稠密性）。 -/
theorem inner_Op_self_le (hf : L1 f) (x : H) : inner ℝ (Op hf x) x ≤ lam1 f * ‖x‖ ^ 2 := by
  have h1 : Tendsto (fun N => inner ℝ (Op hf (PN (x : ℕ → ℝ) N)) (PN (x : ℕ → ℝ) N)) atTop
      (𝓝 (inner ℝ (Op hf x) x)) :=
    (((Op hf).continuous.tendsto x).comp (PN_tendsto x)).inner (PN_tendsto x)
  have h2 : Tendsto (fun N => lam1 f * ‖PN (x : ℕ → ℝ) N‖ ^ 2) atTop (𝓝 (lam1 f * ‖x‖ ^ 2)) :=
    (((continuous_norm.tendsto x).comp (PN_tendsto x)).pow 2).const_mul _
  apply le_of_tendsto_of_tendsto' h1 h2
  intro N
  rw [inner_Op_PN, PN_norm_sq]
  exact quadForm_le_lam1_mul hf _ N

/-- 反向：`lam1 f ≤ sup_{‖x‖=1} ⟨O[f] x, x⟩`——每个有限 Rayleigh 商都是某个 `⟨O[f]x,x⟩`。 -/
lemma exists_PN_of_lt_lam1 (hf : L1 f) (ε : ℝ) (hε : 0 < ε) :
    ∃ x : H, ‖x‖ = 1 ∧ lam1 f - ε < inner ℝ (Op hf x) x := by
  have hlt : lam1 f - ε < sSup (raySetM (Of f)) := by unfold lam1 lamM at *; linarith
  obtain ⟨q, ⟨N, v, hv, rfl⟩, hq⟩ := exists_lt_of_lt_csSup (raySetM_nonempty _) hlt
  refine ⟨PN v N, ?_, ?_⟩
  · have := PN_norm_sq v N
    rw [hv] at this
    have h0 := norm_nonneg (PN v N)
    nlinarith
  · rw [inner_Op_PN]; exact hq

/-! ### 谱 -/

lemma isSelfAdjoint_algebraMap' (c : ℝ) : IsSelfAdjoint (algebraMap ℝ (H →L[ℝ] H) c) := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact (IsSelfAdjoint.all c).smul (IsSelfAdjoint.one _)

lemma algebraMap_apply' (c : ℝ) (x : H) : (algebraMap ℝ (H →L[ℝ] H) c) x = c • x := by
  rw [Algebra.algebraMap_eq_smul_one]; simp

/-- `lam1 f · 1 − O[f]` 是正算子。 -/
lemma isPositive_lam1_sub (hf : L1 f) :
    (algebraMap ℝ (H →L[ℝ] H) (lam1 f) - Op hf).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff']
  refine ⟨(isSelfAdjoint_algebraMap' _).sub (Op_isSelfAdjoint hf), fun x => ?_⟩
  rw [sub_apply, algebraMap_apply', inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have := inner_Op_self_le hf x
  linarith

/-- **`spec(O[f]) ⊆ (−∞, lam1 f]`**。 -/
theorem spectrum_le_lam1 (hf : L1 f) (μ : ℝ) (hμ : μ ∈ spectrum ℝ (Op hf)) : μ ≤ lam1 f := by
  have h := (isPositive_lam1_sub hf).spectrumRestricts
  rw [SpectrumRestricts.nnreal_iff] at h
  have hmem : lam1 f - μ ∈ spectrum ℝ (algebraMap ℝ (H →L[ℝ] H) (lam1 f) - Op hf) := by
    rw [← spectrum.singleton_sub_eq]
    exact Set.sub_mem_sub (Set.mem_singleton _) hμ
  linarith [h _ hmem]

/-- `Rayleigh 商`的显式形式。 -/
lemma rayleigh_eq (T : H →L[ℝ] H) (x : H) :
    T.rayleighQuotient x = inner ℝ (T x) x / ‖x‖ ^ 2 := by
  simp [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply]

/-- **`lam1 f ∈ spec(O[f])`**：把 mathlib 的「自伴算子的 `‖T‖` 属于谱」用到 `T := O[f] + c·1`（`c` 大到 `T ≥ 0`）。 -/
theorem lam1_mem_spectrum (hf : L1 f) : lam1 f ∈ spectrum ℝ (Op hf) := by
  set c : ℝ := 5 * l1 f + 1 with hc
  set T : H →L[ℝ] H := Op hf + algebraMap ℝ (H →L[ℝ] H) c with hT
  have hl := l1_nonneg f
  have hf1 := f1_le_lam1 hf
  have hfl : -(l1 f) ≤ f 1 := by
    have := abs_le_l1 hf 1 le_rfl
    linarith [neg_abs_le (f 1)]
  have hΛc : 0 < lam1 f + c := by linarith
  have hTsym : (↑T : H →ₗ[ℝ] H).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      ((Op_isSelfAdjoint hf).add (isSelfAdjoint_algebraMap' c))
  -- `⟨T x, x⟩ = ⟨O x, x⟩ + c‖x‖²`
  have hTx : ∀ x : H, inner ℝ (T x) x = inner ℝ (Op hf x) x + c * ‖x‖ ^ 2 := by
    intro x
    rw [hT, add_apply, algebraMap_apply', inner_add_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
  -- Rayleigh 商在 `[0, lam1 + c]` 内
  have hlow : ∀ x : H, 0 ≤ T.rayleighQuotient x := by
    intro x
    rw [rayleigh_eq, hTx]
    apply div_nonneg _ (sq_nonneg _)
    have h1 : -(5 * l1 f) * ‖x‖ ^ 2 ≤ inner ℝ (Op hf x) x := by
      have := real_inner_le_norm (Op hf x) x
      have h2 := (Op hf).le_opNorm x
      have h3 := Op_norm_le hf
      have h4 : inner ℝ (Op hf x) x = -(inner ℝ (-(Op hf x)) x) := by rw [inner_neg_left]; ring
      have h5 := real_inner_le_norm (-(Op hf x)) x
      rw [norm_neg] at h5
      have h6 : ‖Op hf x‖ * ‖x‖ ≤ 5 * l1 f * ‖x‖ ^ 2 := by
        have := mul_le_mul_of_nonneg_right h2 (norm_nonneg x)
        have := mul_le_mul_of_nonneg_right h3 (mul_nonneg (norm_nonneg x) (norm_nonneg x))
        nlinarith [norm_nonneg x, norm_nonneg (Op hf x)]
      linarith
    nlinarith [sq_nonneg ‖x‖]
  have hup : ∀ x : H, T.rayleighQuotient x ≤ lam1 f + c := by
    intro x
    rw [rayleigh_eq, hTx]
    by_cases hx : ‖x‖ = 0
    · rw [hx]; simp; exact le_of_lt hΛc
    · have hx2 : 0 < ‖x‖ ^ 2 := by positivity
      rw [div_le_iff₀ hx2]
      have := inner_Op_self_le hf x
      linarith
  -- `‖T‖ = lam1 + c`
  have hsup : (⨆ x : H, |T.rayleighQuotient x|) = lam1 f + c := by
    apply le_antisymm
    · apply ciSup_le
      intro x
      rw [abs_of_nonneg (hlow x)]
      exact hup x
    · apply le_of_forall_pos_lt_add
      intro ε hε
      obtain ⟨x, hx1, hx2⟩ := exists_PN_of_lt_lam1 hf ε hε
      have hle := le_ciSup (T.bddAbove_rayleighQuotient) x
      have hval : T.rayleighQuotient x = inner ℝ (Op hf x) x + c := by
        rw [rayleigh_eq, hTx, hx1]; simp
      rw [abs_of_nonneg (hlow x), hval] at hle
      linarith
  have hnorm : ‖T‖ = lam1 f + c := by
    rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient T hTsym, hsup]
  -- `‖T‖ ∈ spec T`
  have hmemT : ‖T‖ ∈ spectrum ℝ T := by
    by_contra hres
    have hres' : algebraMap ℝ ℝ ‖T‖ ∈ resolventSet ℝ T := by
      simpa [spectrum, Set.mem_compl_iff] using hres
    obtain ⟨ε, hε, hbound⟩ := T.rayleighQuotient_le_of_norm_mem_resolventSet hres'
    obtain ⟨x, hx1, hx2⟩ := exists_PN_of_lt_lam1 hf ε hε
    have hval : T.rayleighQuotient x = inner ℝ (Op hf x) x + c := by
      rw [rayleigh_eq, hTx, hx1]; simp
    have := hbound x
    rw [hval, hnorm] at this
    linarith
  -- 移回 `Op`
  rw [hnorm, hT, ← spectrum.add_singleton_eq] at hmemT
  obtain ⟨μ, hμ, r, hr, hμr⟩ := Set.mem_add.mp hmemT
  rw [Set.mem_singleton_iff] at hr
  have : μ = lam1 f := by linarith
  rw [← this]; exact hμ

/-- **忠实性定理**：论文的 `λ₁(O[f]) := max spec O[f]` 等于本库的 `lam1 f`。 -/
theorem isGreatest_spectrum (hf : L1 f) : IsGreatest (spectrum ℝ (Op hf)) (lam1 f) :=
  ⟨lam1_mem_spectrum hf, fun μ hμ => spectrum_le_lam1 hf μ hμ⟩

theorem sSup_spectrum_eq_lam1 (hf : L1 f) : sSup (spectrum ℝ (Op hf)) = lam1 f :=
  (isGreatest_spectrum hf).csSup_eq

end

end Eliashberg
