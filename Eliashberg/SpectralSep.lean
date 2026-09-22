import Eliashberg.TheoremA10
import Eliashberg.Discrete

/-!
# Corollary A.6：`spec(A) ∩ (13/25, ∞) = {g(2)}`，且 `g(2)` 单重（`ℓ²` 层）

`TheoremA10.lean` 里的谱分离 `AN_spec_le` 只对**有限截断** `A_N` 成立，主线也只需要那一条。
论文 Corollary A.6 的陈述本身是在 `ℓ²` 上的：`spec(A) ∩ (13/25,∞) = {λ₁}`，且 `λ₁` 单重。
论文用 Riesz 理论（谱投影有限秩），本文件改用**已证的件**拼出来，不引入新的谱论：

* `A ⪯ B`（`quadForm_le_B`，已证）在 `ℓ²` 上就是 `⟪v,Av⟫ ≤ ⟪v,Bv⟫`（对有限支撑向量成立，取极限）；
* `B` 的迹界 `BN_trace_sub_le`（已证）给「`B` 除一个方向外 `≤ 13/25`」；
* 二维子空间论证（`eigen_le_of_dominated` 的思路）搬到 `ℓ²`：若有两个 `> 13/25` 的特征值，
  在它们张成的平面里取与 `B` 的「顶方向」正交的向量即得矛盾。

**实现上更省的一条路**：`A` 的特征向量都落在 `ℓ²` 里，而 `A` 的二次型被 `B` 的二次型控制，
`B` 的二次型又被「对角和 − `B₀₀`」控制**在与 `e₀` 正交的方向上**。这正是 `Bf` 为对角占优时
的初等事实，且 `Bf` 的非对角元非负、行和有限。于是只需在 `ℓ²` 上重做一次：

`v ⟂ w` 单位、`Av = μv`、`Aw = g(2)w` ⇒ `μ = ⟪v,Av⟫ ≤ ⟪v,Bv⟫ ≤ 13/25`。

中间的 `⟪v,Bv⟫ ≤ 13/25` 用 `B` 的**逐点对角优势**：`Bf` 的非对角元 `≤ 0`？——不成立。
故这里走真正的路：把 `v` 截断成 `P_N v`，对每个 `N` 用有限维的 `AN_spec_le`，再取极限。

| 定理 | 内容 |
|---|---|
| `lamN_lt_of_eigen_ne` | `μ ∈ spec(A)`、`μ ≠ g(2)`、`μ > 13/25` ⇒ 矛盾（截断 + 有限维谱分离） |
| **`Aop_spectrum_inter_eq`** | **Cor A.6 第一句**：`spec(A) ∩ (13/25,∞) = {g(2)}` |
| **`g2_eigenspace_dim_one`** | **Cor A.6 第二句**：`g(2)` 的特征空间一维（单重） |
| `Aop_spectrum_le_of_ne` | `μ ∈ spec(A)`、`μ ≠ g(2)` ⇒ `μ ≤ 13/25` |
-/

namespace Eliashberg

open scoped BigOperators Matrix
open Filter Topology Metric

noncomputable section

/-! ### 一、有限维谱分离传到 `ℓ²`：两个正交特征向量的截断 -/

/-- `A` 的二次型在有限支撑向量上被 `B` 的二次型控制（`quadForm_le_B` 的 `ℓ²` 读法）。 -/
lemma quadForm_invSq_le_B (v : ℕ → ℝ) (N : ℕ) :
    quadForm (fun k => 1 / (k:ℝ) ^ 2) v N ≤ quadFormB v N :=
  quadForm_le_B v N

/-- 有限维谱分离的**向量形式**：`x ∈ ℝ^{K+1}` 与 `A_{K+1}` 的顶特征向量正交
⇒ `x ⬝ A_{K+1} x ≤ (13/25)‖x‖²`。这是 `AN_spec_le` 在特征基下的重述。 -/
lemma dot_AN_le_of_orth (K : ℕ) {x : Fin (K+1) → ℝ}
    (hx : ∀ i, (ON_isHermitian (N := K+1) (fun k => 1 / (k:ℝ) ^ 2)).eigenvalues i
        = top (ON_isHermitian (N := K+1) (fun k => 1 / (k:ℝ) ^ 2)) →
      coeff (ON_isHermitian (N := K+1) (fun k => 1 / (k:ℝ) ^ 2)) x i = 0) :
    x ⬝ᵥ (ON (fun k => 1 / (k:ℝ) ^ 2) : Matrix (Fin (K+1)) (Fin (K+1)) ℝ) *ᵥ x
      ≤ 13/25 * (x ⬝ᵥ x) := by
  set hA := ON_isHermitian (N := K+1) (fun k => 1 / (k:ℝ) ^ 2) with hAdef
  rw [dot_mulVec_eq hA, dot_self_eq hA, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : hA.eigenvalues i = top hA
  · rw [hx i hi]; simp
  · exact mul_le_mul_of_nonneg_right (AN_spec_le K i hi) (sq_nonneg _)

/-- 按下标的正交形式：若除 `j₀` 外特征值都 `≤ 13/25`，且 `y` 在 `j₀` 方向的系数为 `0`，
则 `y ⬝ A y ≤ (13/25)‖y‖²`。 -/
lemma dot_le_of_orth_index (K : ℕ) {j₀ : Fin (K+1)}
    (hj : ∀ i, i ≠ j₀ → (ON_isHermitian (N := K+1) (fun k => 1 / (k:ℝ) ^ 2)).eigenvalues i
      ≤ 13/25) {y : Fin (K+1) → ℝ}
    (hy : coeff (ON_isHermitian (N := K+1) (fun k => 1 / (k:ℝ) ^ 2)) y j₀ = 0) :
    y ⬝ᵥ (ON (fun k => 1 / (k:ℝ) ^ 2) : Matrix (Fin (K+1)) (Fin (K+1)) ℝ) *ᵥ y
      ≤ 13/25 * (y ⬝ᵥ y) := by
  set hA := ON_isHermitian (N := K+1) (fun k => 1 / (k:ℝ) ^ 2) with hAdef
  rw [dot_mulVec_eq hA, dot_self_eq hA, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i = j₀
  · subst hi; rw [hy]; simp
  · exact mul_le_mul_of_nonneg_right (hj i hi) (sq_nonneg _)

/-! ### 一′、`ℓ²` 向量的有限截断作为 `Fin (K+1) → ℝ` -/

/-- 把 `v : ℕ → ℝ` 截成 `Fin (K+1) → ℝ`。 -/
def truncVec (v : ℕ → ℝ) (K : ℕ) : Fin (K+1) → ℝ := fun i => v i.val

lemma extN_truncVec (v : ℕ → ℝ) (K : ℕ) (n : ℕ) (hn : n < K + 1) :
    extN (truncVec v K) n = v n := by
  unfold extN truncVec
  rw [dite_eq_left hn]

/-- `x ⬝ x = ‖P_{K+1} v‖²`。 -/
lemma truncVec_dot_self (v : ℕ → ℝ) (K : ℕ) :
    truncVec v K ⬝ᵥ truncVec v K = ∑ n ∈ Finset.range (K+1), v n ^ 2 := by
  rw [dotProduct, ← Fin.sum_univ_eq_sum_range (fun n => v n ^ 2) (K+1)]
  apply Finset.sum_congr rfl; intro i _
  unfold truncVec; ring

/-- `x ⬝ A x = quadForm f v (K+1)`。 -/
lemma truncVec_dot_ON (f : ℕ → ℝ) (v : ℕ → ℝ) (K : ℕ) :
    truncVec v K ⬝ᵥ (ON f : Matrix (Fin (K+1)) (Fin (K+1)) ℝ) *ᵥ truncVec v K
      = quadForm f v (K+1) := by
  rw [quadForm_eq_dot]
  apply quadForm_congr
  intro n hn
  exact extN_truncVec v K n hn

/-! ### 一″、双线性形式与三条极限 -/

/-- `quadForm` 的双线性版本。 -/
def bilinForm (f : ℕ → ℝ) (v w : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, v n * Of f n m * w m

lemma bilinForm_self (f : ℕ → ℝ) (v : ℕ → ℝ) (N : ℕ) :
    bilinForm f v v N = quadForm f v N := rfl

/-- `bilinForm` 对称（`Of` 对称 + 交换求和次序）。 -/
lemma bilinForm_symm (f : ℕ → ℝ) (v w : ℕ → ℝ) (N : ℕ) :
    bilinForm f v w N = bilinForm f w v N := by
  unfold bilinForm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro n _
  apply Finset.sum_congr rfl; intro m _
  rw [Of_symm' f m n]; ring

/-- `⟨O[f] P_N v, P_N w⟩ = bilinForm f w v N`（`inner_Op_PN` 的双线性版）。 -/
lemma inner_Op_PN_bilin {f : ℕ → ℝ} (hf : L1 f) (v w : ℕ → ℝ) (N : ℕ) :
    inner ℝ (Op hf (PN v N)) (PN w N) = bilinForm f w v N := by
  rw [H_inner]
  rw [tsum_eq_sum (s := Finset.range N)]
  · unfold bilinForm
    apply Finset.sum_congr rfl; intro n hn
    rw [Finset.mem_range] at hn
    rw [Op_PN_apply, PN_apply_of_lt w N n hn, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro m _
    ring
  · intro n hn
    rw [Finset.mem_range, not_lt] at hn
    rw [PN_apply_of_ge w N n hn]; ring

/-- `x ⬝ A z = bilinForm f v w (K+1)`。 -/
lemma truncVec_dot_ON_bilin (f : ℕ → ℝ) (v w : ℕ → ℝ) (K : ℕ) :
    truncVec v K ⬝ᵥ (ON f : Matrix (Fin (K+1)) (Fin (K+1)) ℝ) *ᵥ truncVec w K
      = bilinForm f v w (K+1) := by
  unfold bilinForm
  simp only [dotProduct, Matrix.mulVec, ON, Matrix.of_apply]
  rw [← Fin.sum_univ_eq_sum_range (fun n => ∑ m ∈ Finset.range (K+1),
    v n * Of f n m * w m) (K+1)]
  apply Finset.sum_congr rfl; intro i _
  rw [← Fin.sum_univ_eq_sum_range (fun m => v i.val * Of f i.val m * w m) (K+1),
    Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _
  unfold truncVec
  ring

/-- `x ⬝ z = ∑_{n<K+1} v n * w n`。 -/
lemma truncVec_dot (v w : ℕ → ℝ) (K : ℕ) :
    truncVec v K ⬝ᵥ truncVec w K = ∑ n ∈ Finset.range (K+1), v n * w n := by
  rw [dotProduct, ← Fin.sum_univ_eq_sum_range (fun n => v n * w n) (K+1)]
  apply Finset.sum_congr rfl; intro i _
  unfold truncVec; ring

lemma PN_inner_eq {v w : ℕ → ℝ} (N : ℕ) :
    inner ℝ (PN v N) (PN w N) = ∑ n ∈ Finset.range N, v n * w n := by
  rw [H_inner, tsum_eq_sum (s := Finset.range N)]
  · apply Finset.sum_congr rfl; intro n hn
    rw [Finset.mem_range] at hn
    rw [PN_apply_of_lt v N n hn, PN_apply_of_lt w N n hn]
  · intro n hn
    rw [Finset.mem_range, not_lt] at hn
    rw [PN_apply_of_ge v N n hn]; ring

/-- `bilinForm f v w (N) → ⟨O[f]v, w⟩`。 -/
lemma bilinForm_tendsto {f : ℕ → ℝ} (hf : L1 f) (x y : H) :
    Tendsto (fun N => bilinForm f (x : ℕ → ℝ) (y : ℕ → ℝ) N) atTop
      (𝓝 (inner ℝ (Op hf x) y)) := by
  have h : Tendsto (fun N => inner ℝ (Op hf (PN (x : ℕ → ℝ) N)) (PN (y : ℕ → ℝ) N)) atTop
      (𝓝 (inner ℝ (Op hf x) y)) :=
    (((Op hf).continuous.tendsto x).comp (PN_tendsto x)).inner (PN_tendsto y)
  apply h.congr
  intro N
  rw [inner_Op_PN_bilin hf, bilinForm_symm]

/-- `∑_{n<N} x_n y_n → ⟨x,y⟩`。 -/
lemma dot_partial_tendsto (x y : H) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, (x : ℕ → ℝ) n * (y : ℕ → ℝ) n) atTop
      (𝓝 (inner ℝ x y)) := by
  have h : Tendsto (fun N => inner ℝ (PN (x : ℕ → ℝ) N) (PN (y : ℕ → ℝ) N)) atTop
      (𝓝 (inner ℝ x y)) := (PN_tendsto x).inner (PN_tendsto y)
  apply h.congr
  intro N
  exact PN_inner_eq N

/-! ### 一‴、二次型在线性组合下的展开 -/

/-- `quadForm f (a v + b w) = a²Q(v) + 2ab·B(v,w) + b²Q(w)`。 -/
lemma quadForm_add_smul (f : ℕ → ℝ) (v w : ℕ → ℝ) (a b : ℝ) (N : ℕ) :
    quadForm f (fun n => a * v n + b * w n) N
      = a ^ 2 * quadForm f v N + 2 * a * b * bilinForm f v w N + b ^ 2 * quadForm f w N := by
  have key : quadForm f (fun n => a * v n + b * w n) N
      = a ^ 2 * quadForm f v N + a * b * bilinForm f v w N + a * b * bilinForm f w v N
        + b ^ 2 * quadForm f w N := by
    unfold quadForm bilinForm
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro n _
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro m _
    ring
  rw [key, bilinForm_symm f w v]
  ring

/-- `∑ (a v + b w)² = a²∑v² + 2ab∑vw + b²∑w²`。 -/
lemma sumSq_add_smul (v w : ℕ → ℝ) (a b : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, (a * v n + b * w n) ^ 2
      = a ^ 2 * (∑ n ∈ Finset.range N, v n ^ 2) + 2 * a * b * (∑ n ∈ Finset.range N, v n * w n)
        + b ^ 2 * (∑ n ∈ Finset.range N, w n ^ 2) := by
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro n _
  ring

/-- 给定两个实数，总能取单位系数对 `(a,b)` 把线性组合的某个坐标消掉。 -/
lemma exists_unit_pair_orth (α γ : ℝ) : ∃ a b : ℝ, a ^ 2 + b ^ 2 = 1 ∧ a * α + b * γ = 0 := by
  by_cases h : α = 0 ∧ γ = 0
  · exact ⟨1, 0, by norm_num, by rw [h.1, h.2]; ring⟩
  · have hpos : 0 < γ ^ 2 + α ^ 2 := by
      rcases not_and_or.mp h with h' | h'
      · have hα : 0 < α ^ 2 := by positivity
        linarith [sq_nonneg γ]
      · have hγ : 0 < γ ^ 2 := by positivity
        linarith [sq_nonneg α]
    have hr : 0 < Real.sqrt (γ ^ 2 + α ^ 2) := Real.sqrt_pos.mpr hpos
    have hr2 : Real.sqrt (γ ^ 2 + α ^ 2) ^ 2 = γ ^ 2 + α ^ 2 := Real.sq_sqrt hpos.le
    refine ⟨γ / Real.sqrt (γ ^ 2 + α ^ 2), -α / Real.sqrt (γ ^ 2 + α ^ 2), ?_, ?_⟩
    · field_simp
      rw [hr2]
    · field_simp; ring

/-- 坐标泛函在线性组合上线性。 -/
lemma dot_truncVec_add (K : ℕ) (e : Fin (K+1) → ℝ) (v w : ℕ → ℝ) (a b : ℝ) :
    e ⬝ᵥ truncVec (fun n => a * v n + b * w n) K
      = a * (e ⬝ᵥ truncVec v K) + b * (e ⬝ᵥ truncVec w K) := by
  simp only [dotProduct, truncVec, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  ring

/-! ### 二、「至多一个特征值 `> β`」——`eigen_le_of_dominated` 论证的完整强度 -/

/-- **`A` 不能有两个不同下标的特征值都 `> β`**。

`TheoremA10.eigen_le_of_dominated` 的证明其实只用到 `i ≠ j₀`，所以它内在给出的是这条更强的
结论。单独提出来，是因为提升到 `ℓ²` 需要「顶特征值在 `> β` 的范围内单重」。

论证：在 `span(e_i, e_j)` 里取与 `B` 的顶特征向量 `e_{k₀}(B)` 正交的非零向量 `x`，
则 `β‖x‖² < ⟨x, Ax⟩ ≤ ⟨x, Bx⟩ ≤ β‖x‖²`。 -/
theorem not_two_eigen_gt {N : ℕ} {A B : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hAB : ∀ x : Fin N → ℝ, x ⬝ᵥ A *ᵥ x ≤ x ⬝ᵥ B *ᵥ x) (β : ℝ)
    (hBspec : ∃ k₀, ∀ k, k ≠ k₀ → hB.eigenvalues k ≤ β) {i j : Fin N} (hij : i ≠ j)
    (hi : β < hA.eigenvalues i) (hj : β < hA.eigenvalues j) : False := by
  obtain ⟨k₀, hk₀⟩ := hBspec
  have hquad : ∀ a b : ℝ, (a • evec hA i + b • evec hA j) ⬝ᵥ A *ᵥ (a • evec hA i + b • evec hA j)
      = a ^ 2 * hA.eigenvalues i + b ^ 2 * hA.eigenvalues j := by
    intro a b
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, mulVec_evec, mulVec_evec]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, evec_dot,
      smul_eq_mul, hij, hij.symm, ite_true, ite_false]
    ring
  have hnorm : ∀ a b : ℝ, (a • evec hA i + b • evec hA j) ⬝ᵥ (a • evec hA i + b • evec hA j)
      = a ^ 2 + b ^ 2 := by
    intro a b
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, evec_dot,
      smul_eq_mul, hij, hij.symm, ite_true, ite_false]
    ring
  have hBle : ∀ x : Fin N → ℝ, evec hB k₀ ⬝ᵥ x = 0 → x ⬝ᵥ B *ᵥ x ≤ β * (x ⬝ᵥ x) := by
    intro x hfx
    rw [dot_mulVec_eq hB, dot_self_eq hB, Finset.mul_sum]
    apply Finset.sum_le_sum; intro k _
    by_cases hk : k = k₀
    · subst hk
      have h : coeff hB x k = 0 := hfx
      rw [h]; simp
    · exact mul_le_mul_of_nonneg_right (hk₀ k hk) (sq_nonneg _)
  set α := evec hB k₀ ⬝ᵥ evec hA i with hα
  set γ := evec hB k₀ ⬝ᵥ evec hA j with hγ
  by_cases h0 : α = 0 ∧ γ = 0
  · have h1 := hAB (evec hA i)
    have h2 := hBle (evec hA i) h0.1
    have h3 : evec hA i ⬝ᵥ A *ᵥ evec hA i = hA.eigenvalues i := by
      have := hquad 1 0; simpa using this
    have h4 : evec hA i ⬝ᵥ evec hA i = 1 := by
      have := hnorm 1 0; simpa using this
    rw [h3] at h1; rw [h4, mul_one] at h2
    linarith
  · have hfx : evec hB k₀ ⬝ᵥ (γ • evec hA i + (-α) • evec hA j) = 0 := by
      simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, ← hα, ← hγ]; ring
    have h1 := hAB (γ • evec hA i + (-α) • evec hA j)
    have h2 := hBle _ hfx
    rw [hquad] at h1; rw [hnorm] at h2
    rcases not_and_or.mp h0 with h | h
    · have hα2 : 0 < α ^ 2 := by positivity
      nlinarith [mul_pos hα2 (sub_pos.mpr hj), mul_nonneg (sq_nonneg γ) (sub_pos.mpr hi).le]
    · have hγ2 : 0 < γ ^ 2 := by positivity
      nlinarith [mul_pos hγ2 (sub_pos.mpr hi), mul_nonneg (sq_nonneg α) (sub_pos.mpr hj).le]

/-- **截断的强化谱分离**：`∃ j₀`，`A_{K+1}` 除下标 `j₀` 外的特征值都 `≤ 13/25`。

比 `AN_spec_le`（「除**取值** `= top` 者外」）强：这里排除的是**单个下标**，
所以 `> 13/25` 的特征值至多一个。 -/
theorem AN_at_most_one_gt (K : ℕ) :
    ∃ j₀, ∀ i, i ≠ j₀ →
      (ON_isHermitian (N := K+1) (fun k => 1 / (k:ℝ) ^ 2)).eigenvalues i ≤ 13/25 := by
  set hA := ON_isHermitian (N := K+1) (fun k => 1 / (k:ℝ) ^ 2) with hAdef
  obtain ⟨j₀, hj₀⟩ := exists_eigenvalues_eq_top hA
  refine ⟨j₀, fun i hij => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  have hj₀β : (13/25 : ℝ) < hA.eigenvalues j₀ := by
    rw [hj₀]; exact lt_of_lt_of_le hlt (eigenvalues_le_top hA i)
  refine not_two_eigen_gt hA (BN_isHermitian (K+1)) (fun x => ?_) (13/25) ?_ hij hlt hj₀β
  · rw [quadForm_eq_dot, dot_BN]
    exact quadForm_le_B _ _
  · obtain ⟨k₀, hk₀⟩ := nontop_le_trace_sub (BN_isHermitian (K+1)) (BN_eigen_nonneg (K+1)) 0
    exact ⟨k₀, fun k hk => (hk₀ k hk).trans (BN_trace_sub_le K)⟩

/-! ### 三、每个截断给出一个单位系数对 -/

/-- 对每个 `K`，存在单位系数对 `(a,b)`，使 `a v + b w` 的截断 Rayleigh 商被 `13/25` 控制。 -/
lemma exists_unit_pair_le (v w : ℕ → ℝ) (K : ℕ) :
    ∃ a b : ℝ, a ^ 2 + b ^ 2 = 1 ∧
      a ^ 2 * quadForm (fun k : ℕ => 1 / (k:ℝ) ^ 2) v (K+1)
        + 2 * a * b * bilinForm (fun k : ℕ => 1 / (k:ℝ) ^ 2) v w (K+1)
        + b ^ 2 * quadForm (fun k : ℕ => 1 / (k:ℝ) ^ 2) w (K+1)
      ≤ 13/25 * (a ^ 2 * (∑ n ∈ Finset.range (K+1), v n ^ 2)
          + 2 * a * b * (∑ n ∈ Finset.range (K+1), v n * w n)
          + b ^ 2 * (∑ n ∈ Finset.range (K+1), w n ^ 2)) := by
  obtain ⟨j₀, hj⟩ := AN_at_most_one_gt K
  obtain ⟨a, b, hab, horth⟩ := exists_unit_pair_orth
    (coeff (ON_isHermitian (N := K+1) (fun k => 1 / (k:ℝ) ^ 2)) (truncVec v K) j₀)
    (coeff (ON_isHermitian (N := K+1) (fun k => 1 / (k:ℝ) ^ 2)) (truncVec w K) j₀)
  refine ⟨a, b, hab, ?_⟩
  have hy : coeff (ON_isHermitian (N := K+1) (fun k => 1 / (k:ℝ) ^ 2))
      (truncVec (fun n => a * v n + b * w n) K) j₀ = 0 := by
    unfold coeff
    rw [dot_truncVec_add]
    exact horth
  have h := dot_le_of_orth_index K hj hy
  rw [truncVec_dot_ON, truncVec_dot_self, quadForm_add_smul, sumSq_add_smul] at h
  exact h

/-! ### 四、`ℓ²` 上的谱分离 -/

/-- **`Aop = O[k⁻²]` 至多有一个特征值 `> 13/25`**。

论文 Cor A.6 用「紧算子谱投影有限秩」得这条；mathlib 没有。这里的证明是把
`AN_at_most_one_gt`（截断层，`not_two_eigen_gt` 的完整强度）传到 `ℓ²`：

设 `v ⟂ w` 是两个单位特征向量，特征值 `μ, ν > 13/25`。每个截断 `K` 给出单位系数对
`(a_K, b_K)`（`exists_unit_pair_le`），使
`a²Q_K(v) + 2ab·B_K(v,w) + b²Q_K(w) ≤ (13/25)(a²S_K(v) + 2ab·D_K + b²S_K(w))`。
`K → ∞` 时 `Q_K(v) → μ`、`Q_K(w) → ν`、`B_K(v,w) → μ⟪v,w⟫ = 0`、`S_K → 1`、`D_K → 0`，
而不等式对 `(a,b)` **齐次**且 `a² + b² = 1`，`|2ab| ≤ 1`，所以系数序列不必收敛：
取 `K` 使五个量都落在 `δ` 邻域即得 `min(μ,ν) - 2δ ≤ (13/25)(1 + 2δ)`，`δ` 足够小时矛盾。 -/
theorem Aop_at_most_one_eigen_gt {μ ν : ℝ} {v w : H}
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hvw : inner ℝ v w = (0:ℝ))
    (hev : Aop v = μ • v) (hew : Aop w = ν • w)
    (hμ : 13/25 < μ) (hν : 13/25 < ν) : False := by
  set f : ℕ → ℝ := fun k => 1 / (k:ℝ) ^ 2 with hfdef
  set β : ℝ := 13/25 with hβ
  -- 五个极限
  have hQv : Tendsto (fun N => quadForm f (v : ℕ → ℝ) N) atTop (𝓝 μ) := by
    have hev' : Op invSq_L1 v = μ • v := hev
    have h := bilinForm_tendsto invSq_L1 v v
    rw [hev'] at h
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq, hv] at h
    simp only [one_pow, mul_one] at h
    exact h.congr fun N => bilinForm_self _ _ _
  have hQw : Tendsto (fun N => quadForm f (w : ℕ → ℝ) N) atTop (𝓝 ν) := by
    have hew' : Op invSq_L1 w = ν • w := hew
    have h := bilinForm_tendsto invSq_L1 w w
    rw [hew'] at h
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq, hw] at h
    simp only [one_pow, mul_one] at h
    exact h.congr fun N => bilinForm_self _ _ _
  have hB : Tendsto (fun N => bilinForm f (v : ℕ → ℝ) (w : ℕ → ℝ) N) atTop (𝓝 0) := by
    have hev' : Op invSq_L1 v = μ • v := hev
    have h := bilinForm_tendsto invSq_L1 v w
    rw [hev', real_inner_smul_left, hvw, mul_zero] at h
    exact h
  have hSv : Tendsto (fun N => ∑ n ∈ Finset.range N, (v : ℕ → ℝ) n ^ 2) atTop (𝓝 1) := by
    have h := dot_partial_tendsto v v
    rw [real_inner_self_eq_norm_sq, hv] at h
    simpa [sq] using h
  have hSw : Tendsto (fun N => ∑ n ∈ Finset.range N, (w : ℕ → ℝ) n ^ 2) atTop (𝓝 1) := by
    have h := dot_partial_tendsto w w
    rw [real_inner_self_eq_norm_sq, hw] at h
    simpa [sq] using h
  have hD : Tendsto (fun N => ∑ n ∈ Finset.range N, (v : ℕ → ℝ) n * (w : ℕ → ℝ) n) atTop
      (𝓝 0) := by
    have h := dot_partial_tendsto v w
    rwa [hvw] at h
  -- 取 δ
  set m : ℝ := min μ ν with hm
  have hmβ : β < m := lt_min hμ hν
  obtain ⟨δ, hδpos, hδle⟩ : ∃ d : ℝ, 0 < d ∧ 8 * d ≤ m - β :=
    ⟨(m - β) / 8, div_pos (by linarith) (by norm_num), le_of_eq (by ring)⟩
  have habs0 : ∀ᶠ y in 𝓝 (0:ℝ), |y| ≤ δ := by
    filter_upwards [Ioo_mem_nhds (by linarith : -δ < 0) hδpos] with y hy
    exact abs_le.mpr ⟨hy.1.le, hy.2.le⟩
  -- 五个量同时落进 δ 邻域
  have hev5 : ∀ᶠ N in atTop,
      μ - δ ≤ quadForm f (v : ℕ → ℝ) N ∧ ν - δ ≤ quadForm f (w : ℕ → ℝ) N ∧
      |bilinForm f (v : ℕ → ℝ) (w : ℕ → ℝ) N| ≤ δ ∧
      (∑ n ∈ Finset.range N, (v : ℕ → ℝ) n ^ 2) ≤ 1 + δ ∧
      (∑ n ∈ Finset.range N, (w : ℕ → ℝ) n ^ 2) ≤ 1 + δ ∧
      |∑ n ∈ Finset.range N, (v : ℕ → ℝ) n * (w : ℕ → ℝ) n| ≤ δ := by
    filter_upwards [hQv.eventually (eventually_ge_nhds (by linarith : μ - δ < μ)),
      hQw.eventually (eventually_ge_nhds (by linarith : ν - δ < ν)),
      hB.eventually habs0,
      hSv.eventually (eventually_le_nhds (by linarith : (1:ℝ) < 1 + δ)),
      hSw.eventually (eventually_le_nhds (by linarith : (1:ℝ) < 1 + δ)),
      hD.eventually habs0] with N h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hev5
  obtain ⟨hq1, hq2, hb, hs1, hs2, hd⟩ := hN₀ (N₀ + 1) (by omega)
  -- 该 N 的 K
  obtain ⟨a, b, hab, hle⟩ := exists_unit_pair_le (v : ℕ → ℝ) (w : ℕ → ℝ) N₀
  have hKN : N₀ + 1 = N₀ + 1 := rfl
  -- 系数界
  have ha2 : a ^ 2 ≤ 1 := by nlinarith [sq_nonneg b]
  have hb2 : b ^ 2 ≤ 1 := by nlinarith [sq_nonneg a]
  have hcross : |2 * a * b| ≤ 1 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (a + b), sq_nonneg (a - b)]
  -- 下界：LHS ≥ m - 2δ
  have hlow : m - 2 * δ ≤ a ^ 2 * quadForm f (v : ℕ → ℝ) (N₀+1)
      + 2 * a * b * bilinForm f (v : ℕ → ℝ) (w : ℕ → ℝ) (N₀+1)
      + b ^ 2 * quadForm f (w : ℕ → ℝ) (N₀+1) := by
    have h1 : m - δ ≤ quadForm f (v : ℕ → ℝ) (N₀+1) := le_trans (by
      rw [hm]; simp only [tsub_le_iff_right]; linarith [min_le_left μ ν]) hq1
    have h2 : m - δ ≤ quadForm f (w : ℕ → ℝ) (N₀+1) := le_trans (by
      rw [hm]; simp only [tsub_le_iff_right]; linarith [min_le_right μ ν]) hq2
    have hmain : (m - δ) * (a ^ 2 + b ^ 2)
        ≤ a ^ 2 * quadForm f (v : ℕ → ℝ) (N₀+1) + b ^ 2 * quadForm f (w : ℕ → ℝ) (N₀+1) := by
      rw [mul_add]
      exact add_le_add (by nlinarith [sq_nonneg a]) (by nlinarith [sq_nonneg b])
    rw [hab, mul_one] at hmain
    have hcr : -δ ≤ 2 * a * b * bilinForm f (v : ℕ → ℝ) (w : ℕ → ℝ) (N₀+1) := by
      have := abs_mul (2 * a * b) (bilinForm f (v : ℕ → ℝ) (w : ℕ → ℝ) (N₀+1))
      have hprod : |2 * a * b * bilinForm f (v : ℕ → ℝ) (w : ℕ → ℝ) (N₀+1)| ≤ 1 * δ := by
        rw [this]
        exact mul_le_mul hcross hb (abs_nonneg _) zero_le_one
      rw [one_mul] at hprod
      linarith [neg_abs_le (2 * a * b * bilinForm f (v : ℕ → ℝ) (w : ℕ → ℝ) (N₀+1)),
        (abs_le.mp hprod).1]
    linarith
  -- 上界：RHS ≤ β(1 + 2δ)
  have hhigh : 13/25 * (a ^ 2 * (∑ n ∈ Finset.range (N₀+1), (v : ℕ → ℝ) n ^ 2)
      + 2 * a * b * (∑ n ∈ Finset.range (N₀+1), (v : ℕ → ℝ) n * (w : ℕ → ℝ) n)
      + b ^ 2 * (∑ n ∈ Finset.range (N₀+1), (w : ℕ → ℝ) n ^ 2)) ≤ β * (1 + 2 * δ) := by
    have hsum : a ^ 2 * (∑ n ∈ Finset.range (N₀+1), (v : ℕ → ℝ) n ^ 2)
        + 2 * a * b * (∑ n ∈ Finset.range (N₀+1), (v : ℕ → ℝ) n * (w : ℕ → ℝ) n)
        + b ^ 2 * (∑ n ∈ Finset.range (N₀+1), (w : ℕ → ℝ) n ^ 2) ≤ 1 + 2 * δ := by
      have h1 : a ^ 2 * (∑ n ∈ Finset.range (N₀+1), (v : ℕ → ℝ) n ^ 2) ≤ a ^ 2 * (1 + δ) :=
        mul_le_mul_of_nonneg_left hs1 (sq_nonneg a)
      have h2 : b ^ 2 * (∑ n ∈ Finset.range (N₀+1), (w : ℕ → ℝ) n ^ 2) ≤ b ^ 2 * (1 + δ) :=
        mul_le_mul_of_nonneg_left hs2 (sq_nonneg b)
      have h3 : 2 * a * b * (∑ n ∈ Finset.range (N₀+1), (v : ℕ → ℝ) n * (w : ℕ → ℝ) n) ≤ δ := by
        have hprod : |2 * a * b * (∑ n ∈ Finset.range (N₀+1),
            (v : ℕ → ℝ) n * (w : ℕ → ℝ) n)| ≤ 1 * δ := by
          rw [abs_mul]
          exact mul_le_mul hcross hd (abs_nonneg _) zero_le_one
        rw [one_mul] at hprod
        exact (abs_le.mp hprod).2
      have hab' : a ^ 2 * (1 + δ) + b ^ 2 * (1 + δ) = 1 + δ := by
        rw [← add_mul, hab, one_mul]
      linarith
    calc 13/25 * (a ^ 2 * (∑ n ∈ Finset.range (N₀+1), (v : ℕ → ℝ) n ^ 2)
          + 2 * a * b * (∑ n ∈ Finset.range (N₀+1), (v : ℕ → ℝ) n * (w : ℕ → ℝ) n)
          + b ^ 2 * (∑ n ∈ Finset.range (N₀+1), (w : ℕ → ℝ) n ^ 2))
        ≤ 13/25 * (1 + 2 * δ) := by
          apply mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = β * (1 + 2 * δ) := by rw [hβ]
  -- 合并
  have hfinal : m - 2 * δ ≤ β * (1 + 2 * δ) := le_trans hlow (le_trans hle hhigh)
  have hs' : 25 * m - 50 * δ ≤ 13 + 26 * δ := by
    calc 25 * m - 50 * δ = 25 * (m - 2 * δ) := by ring
      _ ≤ 25 * (β * (1 + 2 * δ)) := mul_le_mul_of_nonneg_left hfinal (by norm_num)
      _ = 13 + 26 * δ := by rw [hβ]; ring
  have hd2 : 200 * δ ≤ 25 * m - 13 := by
    calc 200 * δ = 25 * (8 * δ) := by ring
      _ ≤ 25 * (m - β) := mul_le_mul_of_nonneg_left hδle (by norm_num)
      _ = 25 * m - 13 := by rw [hβ]; ring
  linarith

/-! ### 五、Corollary A.6 -/

/-- `13/25 < g(2)`（由 `1 ≤ g(2)`，即 `f(1) ≤ λ₁`）。 -/
lemma g2_gt_beta : (13:ℝ)/25 < g2 :=
  lt_of_lt_of_le (by norm_num) one_le_g2

/-- **`spec(A)` 中除 `g(2)` 外都 `≤ 13/25`**。 -/
theorem Aop_spectrum_le_of_ne {μ : ℝ} (hmem : μ ∈ spectrum ℝ Aop) (hne : μ ≠ g2) :
    μ ≤ 13/25 := by
  by_contra hlt
  rw [not_le] at hlt
  have hμ0 : μ ≠ 0 := by
    intro h; rw [h] at hlt; norm_num at hlt
  obtain ⟨v, hv, hev⟩ := exists_unit_eigenvector_of_mem_spectrum invSq_L1 hμ0 hmem
  obtain ⟨w, hw, hew⟩ := exists_unit_eigenvector_g2
  have ho := inner_eq_zero_of_eigen_ne Aop_isSelfAdjoint hev hew hne
  exact Aop_at_most_one_eigen_gt hv hw ho hev hew hlt g2_gt_beta

/-- **Corollary A.6 第一句**：`spec(A) ∩ (13/25, ∞) = {g(2)}`。 -/
theorem Aop_spectrum_inter_eq :
    spectrum ℝ Aop ∩ Set.Ioi (13/25 : ℝ) = {g2} := by
  apply Set.eq_singleton_iff_unique_mem.mpr
  refine ⟨⟨isGreatest_spectrum_Aop.1, Set.mem_Ioi.mpr g2_gt_beta⟩, ?_⟩
  intro μ hμ
  by_contra hne
  exact absurd (Aop_spectrum_le_of_ne hμ.1 hne) (not_le.mpr (Set.mem_Ioi.mp hμ.2))

/-- **Corollary A.6 第二句**：`g(2)` 的特征空间**一维**（单重）。

两个 `g(2)` 的特征向量若线性无关，可 Gram–Schmidt 出正交单位对，
再对 `μ = ν = g(2) > 13/25` 用 `Aop_at_most_one_eigen_gt`。 -/
theorem g2_eigenspace_dim_one :
    ∀ v w : H, Aop v = g2 • v → Aop w = g2 • w → ∃ c : ℝ, w = c • v ∨ v = c • w := by
  intro v w hv hw
  by_cases hv0 : v = 0
  · exact ⟨0, Or.inr (by rw [hv0, zero_smul])⟩
  -- Gram–Schmidt：w' := w − (⟪v,w⟫/‖v‖²) v
  set c : ℝ := inner ℝ v w / ‖v‖ ^ 2 with hc
  set w' : H := w - c • v with hw'
  have hnv : (0:ℝ) < ‖v‖ ^ 2 := by
    have : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
    positivity
  have horth : inner ℝ v w' = (0:ℝ) := by
    rw [hw', inner_sub_right, real_inner_smul_right, hc, real_inner_self_eq_norm_sq]
    field_simp
    ring
  have hew' : Aop w' = g2 • w' := by
    rw [hw', map_sub, map_smul, hv, hw, smul_comm, smul_sub]
  by_cases hz : w' = 0
  · refine ⟨c, Or.inl ?_⟩
    have : w - c • v = 0 := by rw [← hw']; exact hz
    rw [← sub_eq_zero]; exact this
  · exfalso
    have hnw' : ‖w'‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    have hnv' : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
    refine Aop_at_most_one_eigen_gt (v := ‖v‖⁻¹ • v) (w := ‖w'‖⁻¹ • w')
      (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnv'])
      (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnw'])
      ?_ ?_ ?_ g2_gt_beta g2_gt_beta
    · rw [real_inner_smul_left, real_inner_smul_right, horth]; ring
    · rw [map_smul, hv, smul_comm]
    · rw [map_smul, hew', smul_comm]

end

end Eliashberg
