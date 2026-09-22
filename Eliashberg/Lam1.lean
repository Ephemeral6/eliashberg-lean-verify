import Eliashberg.L2Bounds
import Eliashberg.LemmaM

/-!
# `ℓ²` 上的 `λ₁`：有限 Rayleigh 商的上确界（论文 Remark 1.2(b) 的定义）

论文 Remark 1.2(b)：
> read `k(P,T) := sup{⟨v, O[F]v⟩ : ‖v‖ = 1, v finitely supported} ∈ [0,+∞]`,
> a supremum of finite sums, always defined, agreeing with `λ₁(K(P,T))` whenever the operator is bounded.

本文件采用这一定义：对一般的对称核 `M : ℕ → ℕ → ℝ`，
`lamM M := sup { ∑_{n,m<N} v_n M_{nm} v_m : ∑_{n<N} v_n² = 1 }`，
`lam1 f := lamM (O[f])`。由 Lemma 0.2.1 的 Rayleigh 界（`rayleigh_abs_le`），`f ∈ ℓ¹` 时该上确界有限。

## 性质

* `f1_le_lam1`：`λ₁(O[f]) ≥ f(1)`（Prop 1.12(1)）；`lam1_le_five_l1`：`≤ 5‖f‖_ℓ¹`
* `lamN_le_lam1`、`lam1_eq_iSup_lamN`、`lamN_tendsto`：压缩单调性 `λ₁^{(N)} ↑ λ₁`（Thm 1.1 步骤 (i)、Cor 2.4(iv)）
* **`lam1_mono`**：Lemma M（Lemma 1.13）非严格版——由有限维版 `top_ON_le` 取上确界
* **`lam1_sub_le`、`abs_lam1_sub_le`**：`|λ₁(O[F]) − λ₁(O[G])| ≤ 5‖F−G‖_ℓ¹`（Remark 1.16 的 5-Lipschitz）
* `lam1_smul`：`λ₁(O[cf]) = c λ₁(O[f])`（`c > 0`，Lemma 2.2 证明第一句）
* `lam1_convex`：`f ↦ λ₁(O[f])` 凸（Remark 1.16）
* `lamM_sub_le`：`λ₁(M − μ K_c) ≤ λ₁(M)` 若 `K_c ⪰ 0`（Cor 2.4(v)）

## 未形式化

`lam1 f` 与 mathlib 的 `ℓ²` 空间上的算子 `O[f]` 的 `sSup (spectrum)` 相等这一点没有做：
那需要先把 `O[f]` 构造成 `lp 2` 上的有界算子。论文自己说两者"agree whenever the operator is
bounded"，并把此作为 Remark 1.2(b) 的等价读法；本库的全部主定理都以 `lam1` 陈述。
-/

namespace Eliashberg

open scoped BigOperators
open Filter Topology

/-! ### 一般对称核的 Rayleigh 上确界 -/

/-- 有限截断上的二次型 `∑_{n,m<N} v_n M_{nm} v_m`。 -/
noncomputable def rayM (M : ℕ → ℕ → ℝ) (v : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, v n * M n m * v m

/-- 有限支撑单位向量上的 Rayleigh 商集合。 -/
def raySetM (M : ℕ → ℕ → ℝ) : Set ℝ :=
  {q | ∃ N : ℕ, ∃ v : ℕ → ℝ, (∑ n ∈ Finset.range N, v n ^ 2 = 1) ∧ q = rayM M v N}

/-- `λ₁(M) := sup` 有限 Rayleigh 商。 -/
noncomputable def lamM (M : ℕ → ℕ → ℝ) : ℝ := sSup (raySetM M)

lemma rayM_Of (f : ℕ → ℝ) (v : ℕ → ℝ) (N : ℕ) : rayM (Of f) v N = quadForm f v N := rfl

/-- `λ₁(O[f])`。 -/
noncomputable def lam1 (f : ℕ → ℝ) : ℝ := lamM (Of f)

/-- 单位向量 `e_0`。 -/
def e0 : ℕ → ℝ := fun n => if n = 0 then 1 else 0

lemma sum_e0_sq (N : ℕ) (hN : 1 ≤ N) : ∑ n ∈ Finset.range N, e0 n ^ 2 = 1 := by
  unfold e0
  have : ∀ n, (if n = 0 then (1:ℝ) else 0) ^ 2 = if n = 0 then 1 else 0 := by
    intro n; split_ifs <;> simp
  simp only [this]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_range]
  rw [ite_eq_left (by omega)]

lemma rayM_e0 (M : ℕ → ℕ → ℝ) (N : ℕ) (hN : 1 ≤ N) : rayM M e0 N = M 0 0 := by
  unfold rayM e0
  have h1 : ∀ n m, (if n = 0 then (1:ℝ) else 0) * M n m * (if m = 0 then 1 else 0)
      = if n = 0 then (if m = 0 then M 0 0 else 0) else 0 := by
    intro n m
    by_cases hn : n = 0 <;> by_cases hm : m = 0 <;> simp [hn, hm]
  have h2 : ∀ n, ∑ m ∈ Finset.range N, (if n = 0 then (if m = 0 then M 0 0 else 0) else 0)
      = if n = 0 then M 0 0 else 0 := by
    intro n
    by_cases hn : n = 0
    · simp only [hn, ite_true]
      rw [Finset.sum_ite_eq']
      simp only [Finset.mem_range]
      rw [ite_eq_left (by omega)]
    · simp [hn]
  simp only [h1, h2]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_range]
  rw [ite_eq_left (by omega)]

lemma raySetM_nonempty (M : ℕ → ℕ → ℝ) : (raySetM M).Nonempty :=
  ⟨M 0 0, 1, e0, sum_e0_sq 1 le_rfl, (rayM_e0 M 1 le_rfl).symm⟩

/-- 若二次型有界 `|rayM M v N| ≤ C ∑ v²`，则 Rayleigh 集有上界 `C`。 -/
lemma raySetM_bddAbove (M : ℕ → ℕ → ℝ) (C : ℝ)
    (hC : ∀ v N, |rayM M v N| ≤ C * ∑ n ∈ Finset.range N, v n ^ 2) : BddAbove (raySetM M) := by
  refine ⟨C, ?_⟩
  rintro q ⟨N, v, hv, rfl⟩
  have := hC v N
  rw [hv, mul_one] at this
  exact (le_abs_self _).trans this

lemma le_lamM (M : ℕ → ℕ → ℝ) (hbdd : BddAbove (raySetM M)) (v : ℕ → ℝ) (N : ℕ)
    (hv : ∑ n ∈ Finset.range N, v n ^ 2 = 1) : rayM M v N ≤ lamM M :=
  le_csSup hbdd ⟨N, v, hv, rfl⟩

lemma lamM_le (M : ℕ → ℕ → ℝ) (c : ℝ)
    (h : ∀ v N, ∑ n ∈ Finset.range N, v n ^ 2 = 1 → rayM M v N ≤ c) : lamM M ≤ c := by
  apply csSup_le (raySetM_nonempty M)
  rintro q ⟨N, v, hv, rfl⟩
  exact h v N hv

/-- **Cor 2.4(v)**：若 `K` 的二次型非负，`μ ≥ 0`，则 `λ₁(M − μK) ≤ λ₁(M)`。 -/
theorem lamM_sub_le (M K : ℕ → ℕ → ℝ) (μ : ℝ) (hμ : 0 ≤ μ) (hbdd : BddAbove (raySetM M))
    (hK : ∀ v N, 0 ≤ rayM K v N) :
    lamM (fun n m => M n m - μ * K n m) ≤ lamM M := by
  apply lamM_le
  intro v N hv
  have e : rayM (fun n m => M n m - μ * K n m) v N = rayM M v N - μ * rayM K v N := by
    unfold rayM
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro n _
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro m _
    ring
  rw [e]
  have := le_lamM M hbdd v N hv
  have := mul_nonneg hμ (hK v N)
  linarith

/-! ### `lam1` 的基本性质 -/

lemma raySet_bddAbove {f : ℕ → ℝ} (hf : L1 f) : BddAbove (raySetM (Of f)) :=
  raySetM_bddAbove (Of f) (5 * l1 f) (fun v N => rayleigh_abs_le hf v N)

lemma quadForm_le_lam1 {f : ℕ → ℝ} (hf : L1 f) (v : ℕ → ℝ) (N : ℕ)
    (hv : ∑ n ∈ Finset.range N, v n ^ 2 = 1) : quadForm f v N ≤ lam1 f :=
  le_lamM (Of f) (raySet_bddAbove hf) v N hv

lemma lam1_le {f : ℕ → ℝ} (c : ℝ)
    (h : ∀ v N, ∑ n ∈ Finset.range N, v n ^ 2 = 1 → quadForm f v N ≤ c) : lam1 f ≤ c :=
  lamM_le (Of f) c h

lemma Of_zero_zero (f : ℕ → ℝ) : Of f 0 0 = f 1 := by
  unfold Of
  simp [u_zero]

/-- **Prop 1.12(1)**：`λ₁(O[f]) ≥ ⟨e_0, O[f] e_0⟩ = f(1)`。 -/
theorem f1_le_lam1 {f : ℕ → ℝ} (hf : L1 f) : f 1 ≤ lam1 f := by
  have := quadForm_le_lam1 hf e0 1 (sum_e0_sq 1 le_rfl)
  rwa [← rayM_Of, rayM_e0 (Of f) 1 le_rfl, Of_zero_zero] at this

/-- `λ₁(O[f]) ≤ 5‖f‖_ℓ¹`（Lemma 0.2.1）。 -/
theorem lam1_le_five_l1 {f : ℕ → ℝ} (hf : L1 f) : lam1 f ≤ 5 * l1 f := by
  apply lam1_le
  intro v N hv
  have := rayleigh_abs_le hf v N
  rw [hv, mul_one] at this
  exact (le_abs_self _).trans this

/-! ### 与有限维顶特征值的桥 -/

/-- `λ₁^{(N+1)}(f) := λ₁(P_{N+1} O[f] P_{N+1})`（用 `N+1` 避开 `NeZero`）。 -/
noncomputable def lamN (f : ℕ → ℝ) (N : ℕ) : ℝ := top (ON_isHermitian (N := N+1) f)

lemma sum_extN_sq {N : ℕ} (x : Fin N → ℝ) : ∑ n ∈ Finset.range N, extN x n ^ 2 = x ⬝ᵥ x := by
  rw [← Fin.sum_univ_eq_sum_range (fun n => extN x n ^ 2) N]
  simp only [dotProduct]
  apply Finset.sum_congr rfl; intro i _
  rw [extN_fin]; ring

/-- `quadForm` 只依赖 `v` 在 `[0,N)` 上的值。 -/
lemma quadForm_congr (f : ℕ → ℝ) {v w : ℕ → ℝ} (N : ℕ) (h : ∀ n < N, v n = w n) :
    quadForm f v N = quadForm f w N := by
  unfold quadForm
  apply Finset.sum_congr rfl; intro n hn
  apply Finset.sum_congr rfl; intro m hm
  rw [Finset.mem_range] at hn hm
  rw [h n hn, h m hm]

/-- `v_N = 0` 时 `quadForm f v (N+1) = quadForm f v N`。 -/
lemma quadForm_succ_of_zero (f : ℕ → ℝ) (v : ℕ → ℝ) (N : ℕ) (h : v N = 0) :
    quadForm f v (N+1) = quadForm f v N := by
  unfold quadForm
  rw [Finset.sum_range_succ]
  simp only [h, zero_mul]
  rw [Finset.sum_const_zero, add_zero]
  apply Finset.sum_congr rfl; intro n _
  rw [Finset.sum_range_succ]
  simp [h]

lemma quadForm_le_lamN (f : ℕ → ℝ) (N : ℕ) (v : ℕ → ℝ)
    (hv : ∑ n ∈ Finset.range (N+1), v n ^ 2 = 1) : quadForm f v (N+1) ≤ lamN f N := by
  let x : Fin (N+1) → ℝ := fun i => v i.val
  have hext : ∀ n < N+1, extN x n = v n := by
    intro n hn
    unfold extN; rw [dite_eq_left hn]
  have h1 : quadForm f v (N+1) = quadForm f (extN x) (N+1) :=
    quadForm_congr f (N+1) (fun n hn => (hext n hn).symm)
  have h2 : x ⬝ᵥ x = 1 := by
    rw [← sum_extN_sq, ← hv]
    apply Finset.sum_congr rfl; intro n hn
    rw [Finset.mem_range] at hn
    rw [hext n hn]
  rw [h1, ← quadForm_eq_dot]
  exact dot_mulVec_le_top (ON_isHermitian f) x h2

lemma lamN_le_lam1 {f : ℕ → ℝ} (hf : L1 f) (N : ℕ) : lamN f N ≤ lam1 f := by
  obtain ⟨x, hx, hq⟩ := (top_isGreatest (ON_isHermitian (N := N+1) f)).1
  unfold lamN
  rw [hq, quadForm_eq_dot]
  exact quadForm_le_lam1 hf _ _ (by rw [sum_extN_sq]; exact hx)

lemma lamN_bddAbove {f : ℕ → ℝ} (hf : L1 f) : BddAbove (Set.range (lamN f)) :=
  ⟨lam1 f, by rintro _ ⟨N, rfl⟩; exact lamN_le_lam1 hf N⟩

/-- 压缩单调性：`λ₁^{(N+1)} ≤ λ₁^{(N+2)}`（Thm 1.1 步骤 (i) 的有限层版本）。 -/
lemma lamN_mono (f : ℕ → ℝ) : Monotone (lamN f) := by
  apply monotone_nat_of_le_succ
  intro N
  obtain ⟨x, hx, hq⟩ := (top_isGreatest (ON_isHermitian (N := N+1) f)).1
  have hz : extN x (N+1) = 0 := by unfold extN; rw [dite_eq_right (lt_irrefl _)]
  have hsum : ∑ n ∈ Finset.range (N+1+1), extN x n ^ 2 = 1 := by
    rw [Finset.sum_range_succ, hz, sum_extN_sq, hx]; simp
  calc lamN f N = quadForm f (extN x) (N+1) := by unfold lamN; rw [hq, quadForm_eq_dot]
    _ = quadForm f (extN x) (N+1+1) := (quadForm_succ_of_zero f _ _ hz).symm
    _ ≤ lamN f (N+1) := quadForm_le_lamN f (N+1) _ hsum

/-- `λ₁(O[f]) = sup_N λ₁^{(N+1)}(f)`。 -/
theorem lam1_eq_iSup_lamN {f : ℕ → ℝ} (hf : L1 f) : lam1 f = ⨆ N, lamN f N := by
  apply le_antisymm
  · apply lam1_le
    intro v N hv
    rcases N with _ | N
    · simp at hv
    · exact (quadForm_le_lamN f N v hv).trans (le_ciSup (lamN_bddAbove hf) N)
  · exact ciSup_le (fun N => lamN_le_lam1 hf N)

/-- **Cor 2.4(iv)**：`λ₁^{(N)} ↑ λ₁`。 -/
theorem lamN_tendsto {f : ℕ → ℝ} (hf : L1 f) : Tendsto (lamN f) atTop (𝓝 (lam1 f)) := by
  rw [lam1_eq_iSup_lamN hf]
  exact tendsto_atTop_ciSup (lamN_mono f) (lamN_bddAbove hf)

/-! ### Lemma M（非严格）、Lipschitz、缩放、凸性 -/

/-- **Lemma M（Lemma 1.13），非严格，`ℓ²` 版**：`F` 在 `k ≥ 1` 上非增非负、`F ≤ G`、
`G ∈ ℓ¹` ⇒ `λ₁(O[F]) ≤ λ₁(O[G])`。 -/
theorem lam1_mono {F G : ℕ → ℝ} (hF : ∀ k, 1 ≤ k → F (k+1) ≤ F k) (hFpos : ∀ k, 1 ≤ k → 0 ≤ F k)
    (hFG : ∀ k, 1 ≤ k → F k ≤ G k) (hG : L1 G) : lam1 F ≤ lam1 G := by
  apply lam1_le
  intro v N hv
  rcases N with _ | N
  · simp at hv
  · calc quadForm F v (N+1) ≤ lamN F N := quadForm_le_lamN F N v hv
      _ ≤ lamN G N := top_ON_le F G hF hFpos hFG
      _ ≤ lam1 G := lamN_le_lam1 hG N

lemma Of_add (F G : ℕ → ℝ) (n m : ℕ) : Of (fun k => F k + G k) n m = Of F n m + Of G n m := by
  unfold Of
  rw [Finset.sum_add_distrib]
  split_ifs <;> ring

lemma quadForm_add (F G : ℕ → ℝ) (v : ℕ → ℝ) (N : ℕ) :
    quadForm (fun k => F k + G k) v N = quadForm F v N + quadForm G v N := by
  unfold quadForm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro n _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro m _
  rw [Of_add]; ring

lemma quadForm_sub (F G : ℕ → ℝ) (v : ℕ → ℝ) (N : ℕ) :
    quadForm (fun k => G k - F k) v N = quadForm G v N - quadForm F v N := by
  unfold quadForm
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro n _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro m _
  rw [Of_sub]; ring

lemma quadForm_smul (c : ℝ) (f : ℕ → ℝ) (v : ℕ → ℝ) (N : ℕ) :
    quadForm (fun k => c * f k) v N = c * quadForm f v N := by
  unfold quadForm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro n _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro m _
  rw [Of_smul]; ring

lemma L1_sub {F G : ℕ → ℝ} (hF : L1 F) (hG : L1 G) : L1 (fun k => F k - G k) := by
  unfold L1 at *
  apply Summable.of_nonneg_of_le (fun k => abs_nonneg _) _ (hF.add hG)
  intro k
  exact abs_sub _ _

lemma L1_add {F G : ℕ → ℝ} (hF : L1 F) (hG : L1 G) : L1 (fun k => F k + G k) := by
  unfold L1 at *
  apply Summable.of_nonneg_of_le (fun k => abs_nonneg _) _ (hF.add hG)
  intro k
  exact abs_add_le _ _

lemma L1_smul {F : ℕ → ℝ} (hF : L1 F) (c : ℝ) : L1 (fun k => c * F k) := by
  unfold L1 at *
  have := hF.mul_left |c|
  convert this using 2 with k
  rw [abs_mul]

lemma l1_sub_comm (F G : ℕ → ℝ) : l1 (fun k => F k - G k) = l1 (fun k => G k - F k) := by
  unfold l1
  congr 1; funext k; rw [abs_sub_comm]

/-- **5-Lipschitz（Remark 1.16）**：`λ₁(O[F]) ≤ λ₁(O[G]) + 5‖F − G‖_ℓ¹`。 -/
theorem lam1_sub_le {F G : ℕ → ℝ} (hF : L1 F) (hG : L1 G) :
    lam1 F ≤ lam1 G + 5 * l1 (fun k => F k - G k) := by
  apply lam1_le
  intro v N hv
  have h1 : quadForm F v N = quadForm G v N + quadForm (fun k => F k - G k) v N := by
    rw [quadForm_sub G F v N]; ring
  have h2 := rayleigh_abs_le (L1_sub hF hG) v N
  rw [hv, mul_one] at h2
  have h3 := quadForm_le_lam1 hG v N hv
  have h4 := (le_abs_self _).trans h2
  linarith

theorem abs_lam1_sub_le {F G : ℕ → ℝ} (hF : L1 F) (hG : L1 G) :
    |lam1 F - lam1 G| ≤ 5 * l1 (fun k => F k - G k) := by
  rw [abs_le]
  constructor
  · have := lam1_sub_le hG hF
    rw [l1_sub_comm] at this
    linarith
  · have := lam1_sub_le hF hG
    linarith

/-- **缩放**：`c > 0` ⇒ `λ₁(O[cf]) = c λ₁(O[f])`。 -/
theorem lam1_smul {f : ℕ → ℝ} (hf : L1 f) (c : ℝ) (hc : 0 < c) :
    lam1 (fun k => c * f k) = c * lam1 f := by
  apply le_antisymm
  · apply lam1_le
    intro v N hv
    rw [quadForm_smul]
    exact mul_le_mul_of_nonneg_left (quadForm_le_lam1 hf v N hv) (le_of_lt hc)
  · have : lam1 f ≤ lam1 (fun k => c * f k) / c := by
      apply lam1_le
      intro v N hv
      rw [le_div_iff₀ hc, mul_comm, ← quadForm_smul]
      exact quadForm_le_lam1 (L1_smul hf c) v N hv
    rwa [le_div_iff₀ hc, mul_comm] at this

/-- **Remark 1.16（凸性）**：`a, b ≥ 0`, `a + b = 1` ⇒ `λ₁(O[aF + bG]) ≤ a λ₁(O[F]) + b λ₁(O[G])`。 -/
theorem lam1_convex {F G : ℕ → ℝ} (hF : L1 F) (hG : L1 G) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    lam1 (fun k => a * F k + b * G k) ≤ a * lam1 F + b * lam1 G := by
  apply lam1_le
  intro v N hv
  rw [quadForm_add, quadForm_smul, quadForm_smul]
  have h1 := quadForm_le_lam1 hF v N hv
  have h2 := quadForm_le_lam1 hG v N hv
  nlinarith

end Eliashberg
