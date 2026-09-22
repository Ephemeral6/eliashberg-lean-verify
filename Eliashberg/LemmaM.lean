import Eliashberg.Spectral
import Eliashberg.AveragedKernel

/-!
# Lemma M（Lemma 1.13）及其推论的有限维版本

论文 §1.3–§2 在 `N × N` 截断 `O^{(N)}[F] := P_N O[F] P_N` 上的版本。记
`λ₁^{(N)}(F) := λ₁(O^{(N)}[F])`（`top (ON_isHermitian F)`），论文的 `k^{(N)}(P,T) = λ₁^{(N)}(F_{P,T})`。

* `Of_symm`、`ON_isHermitian`：`O[f]` 对称
* `trunc`、`ON_eq_trunc`：`N × N` 块只依赖 `f(1), …, f(2N−1)`，故可把 `f` 截断成最终为零的函数
* `exp_ON_preserves_cone'`：Proposition 1.11 的有限维部分，对**任意**非增非负 `F`（不必最终为零）
* `extN`、`quadForm_eq_dot`：`Fin N → ℝ` 与 `ℕ → ℝ` 两种二次型写法的桥
* **`top_ON_le`、`top_ON_lt`**：Lemma M 的有限维版本——`F` 非增非负、`F ≤ G` ⇒ `λ₁^{(N)}(F) ≤ λ₁^{(N)}(G)`，
  `G(1) > F(1)` 时严格
* **`kN_strictAnti`**：Theorem 1.14 的有限维版本——`T ↦ k^{(N)}(P,T)` 严格递减
* **`kN_le_hN_rms`、`kN_ae_const_or_lt`**：Theorem B 的有限维版本——`k^{(N)}(P,T) ≤ h^{(N)}(ϖ_rms)`，
  `P` 非点质量时严格
* **`top_smul`、`rN_strictAnti`、`hN_lt_gN`**：Lemma 2.2 的有限维版本——
  `r^{(N)}(ϖ) := h^{(N)}(ϖ)/ϖ²` 严格递减且 `< g^{(N)}(2)`

## 与论文的关系

论文的这些结论都在 `ℓ²` 上（`λ₁` 是紧自伴算子的顶谱点）。这里只做 `N × N` 截断；
`N → ∞` 的过渡（压缩单调性 `k ≥ k^{(N)}`、`k^{(N)} → k`，Corollary 2.4(iv)）属于第三层。
论文自己也强调（Remark 1.16）"at level N convexity is unconditional"——有限截断层面的论证
不需要任何可积性假设，这正是本文件的范围。
-/

namespace Eliashberg

open scoped Matrix
open NormedSpace Filter Topology MeasureTheory

/-! ### 对称性 -/

lemma Of_symm (f : ℕ → ℝ) (n m : ℕ) : Of f n m = Of f m n := by
  unfold Of
  rw [Nat.dist_comm]
  by_cases h : n = m
  · subst h; rfl
  · have h' : m ≠ n := Ne.symm h
    simp only [h, h', ite_false, ne_eq, not_false_eq_true, ite_true, zero_add]
    rw [show n + m + 1 = m + n + 1 by ring, mul_comm (u n) (u m)]

lemma ON_isHermitian {N : ℕ} (f : ℕ → ℝ) : (ON f : Matrix (Fin N) (Fin N) ℝ).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  apply Matrix.IsSymm.ext
  intro i j
  simp only [ON, Matrix.of_apply]
  exact Of_symm f j.val i.val

/-! ### 截断 -/

/-- `trunc f M j := f(j) 1_{1 ≤ j < M}`。 -/
def trunc (f : ℕ → ℝ) (M : ℕ) : ℕ → ℝ := fun j => if 1 ≤ j ∧ j < M then f j else 0

lemma trunc_eq_sum (f : ℕ → ℝ) (M j : ℕ) :
    (∑ k ∈ Finset.Ico 1 M, f k * delta k j) = trunc f M j := by
  unfold trunc delta
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_Ico]

lemma trunc_zero (f : ℕ → ℝ) (M k : ℕ) (h : M < k) : trunc f M k = 0 := by
  unfold trunc
  rw [ite_eq_right]
  omega

/-- 截断保持「在 `k ≥ 1` 上非增」，前提 `f ≥ 0`。 -/
lemma trunc_anti (f : ℕ → ℝ) (hf : ∀ k, 1 ≤ k → f (k+1) ≤ f k) (hpos : ∀ k, 1 ≤ k → 0 ≤ f k)
    (M : ℕ) : ∀ k, 1 ≤ k → trunc f M (k+1) ≤ trunc f M k := by
  intro k hk
  unfold trunc
  by_cases h1 : k + 1 < M
  · have h2 : k < M := by omega
    simp only [hk, h1, h2, and_true, ite_true, le_add_iff_nonneg_left, zero_le]
    exact hf k hk
  · by_cases h2 : k < M
    · simp only [h1, h2, hk, and_false, true_and, ite_false, ite_true]
      exact hpos k hk
    · simp [h1, h2]

lemma Of_eq_trunc (f : ℕ → ℝ) (L Lp n m : ℕ) (hn : n < L) (hm : m < Lp) :
    Of f n m = Of (trunc f (L + Lp)) n m := by
  rw [Of_truncate f L Lp n m hn hm]
  congr 1
  funext j
  exact trunc_eq_sum f (L + Lp) j

/-- `N × N` 块只看 `f(1), …, f(2N−1)`。 -/
lemma ON_eq_trunc {N : ℕ} (f : ℕ → ℝ) :
    (ON f : Matrix (Fin N) (Fin N) ℝ) = ON (trunc f (N + N)) := by
  ext i j
  simp only [ON, Matrix.of_apply]
  exact Of_eq_trunc f N N i.val j.val i.isLt j.isLt

/-- **Proposition 1.11 的有限维部分，一般形式**：`F` 在 `k ≥ 1` 上非增非负（不必最终为零）
⇒ `e^{tO^{(N)}[F]}` 保持 `C_N`。 -/
theorem exp_ON_preserves_cone' {N : ℕ} (F : ℕ → ℝ) (hF : ∀ k, 1 ≤ k → F (k+1) ≤ F k)
    (hpos : ∀ k, 1 ≤ k → 0 ≤ F k) (v : Fin N → ℝ) (hv : InConeN v) (t : ℝ) (ht : 0 ≤ t) :
    InConeN ((exp (t • (ON F : Matrix (Fin N) (Fin N) ℝ))).mulVec v) := by
  rw [ON_eq_trunc F]
  exact exp_ON_preserves_cone (trunc F (N + N)) (trunc_anti F hF hpos _) (N + N)
    (trunc_zero F _) v hv t ht

/-! ### `Fin N → ℝ` 与 `ℕ → ℝ` 的桥 -/

/-- 零延拓。 -/
def extN {N : ℕ} (v : Fin N → ℝ) : ℕ → ℝ := fun n => if h : n < N then v ⟨n, h⟩ else 0

lemma extN_fin {N : ℕ} (v : Fin N → ℝ) (i : Fin N) : extN v i.val = v i := by
  unfold extN; rw [dite_eq_left i.isLt]

lemma extN_anti {N : ℕ} (v : Fin N → ℝ) (hv : InConeN v) : Antitone (extN v) := by
  intro a b hab
  unfold extN
  by_cases hb : b < N
  · have ha : a < N := lt_of_le_of_lt hab hb
    rw [dite_eq_left ha, dite_eq_left hb]
    exact hv.1 ⟨a, ha⟩ ⟨b, hb⟩ (by rw [Fin.le_def]; exact hab)
  · rw [dite_eq_right hb]
    by_cases ha : a < N
    · rw [dite_eq_left ha]; exact hv.2 _
    · rw [dite_eq_right ha]

lemma extN_nonneg {N : ℕ} (v : Fin N → ℝ) (hv : InConeN v) : ∀ n, 0 ≤ extN v n := by
  intro n
  unfold extN
  split_ifs
  · exact hv.2 _
  · exact le_refl _

/-- `⟨v, O^{(N)}[f] v⟩`（`Fin N`）`= quadForm f (extN v) N`（`ℕ`）。 -/
lemma quadForm_eq_dot {N : ℕ} (f : ℕ → ℝ) (v : Fin N → ℝ) :
    v ⬝ᵥ (ON f : Matrix (Fin N) (Fin N) ℝ) *ᵥ v = quadForm f (extN v) N := by
  unfold quadForm
  simp only [dotProduct, Matrix.mulVec, ON, Matrix.of_apply]
  have inner : ∀ i : Fin N, ∑ j : Fin N, Of f i.val j.val * v j
      = ∑ m ∈ Finset.range N, Of f i.val m * extN v m := by
    intro i
    rw [← Fin.sum_univ_eq_sum_range (fun m => Of f i.val m * extN v m) N]
    apply Finset.sum_congr rfl; intro j _
    rw [extN_fin]
  simp only [inner]
  rw [← Fin.sum_univ_eq_sum_range (fun n => ∑ m ∈ Finset.range N, extN v n * Of f n m * extN v m) N]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro m _
  rw [extN_fin]; ring

lemma dot_self_pos {N : ℕ} (v : Fin N → ℝ) (hv : v ≠ 0) : 0 < v ⬝ᵥ v := by
  have h0 : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))
  rcases lt_or_eq_of_le h0 with h | h
  · exact h
  · exfalso; exact hv (dotProduct_self_eq_zero.mp h.symm)

/-- `v ∈ C_N`、`v ≠ 0` ⇒ 某个 Abel 系数严格正（Lemma 0.3.2 的有限维形式）。 -/
lemma exists_abelCoeff_pos {N : ℕ} [NeZero N] (v : Fin N → ℝ) (hv : InConeN v) (hv0 : v ≠ 0) :
    ∃ L₀ ∈ Finset.Icc 1 N, 0 < abelCoeff (extN v) N L₀ := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  -- `v_0 > 0`
  have hv0' : 0 < extN v 0 := by
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra h; push Not at h; exact hv0 (funext h)
    have hipos : 0 < v i := lt_of_le_of_ne (hv.2 i) (Ne.symm hi)
    have h0i : v i ≤ v ⟨0, hN⟩ := hv.1 ⟨0, hN⟩ i (by rw [Fin.le_def]; exact Nat.zero_le _)
    have : extN v 0 = v ⟨0, hN⟩ := extN_fin v ⟨0, hN⟩
    rw [this]; linarith
  -- `v_0 = ∑_{L=1}^N a_L`
  have hdec := abel_decomp (extN v) N 0 hN
  have he : ∀ L ∈ Finset.Icc 1 N, e L 0 = 1 := by
    intro L hL; rw [Finset.mem_Icc] at hL; unfold e; rw [ite_eq_left (by omega)]
  rw [Finset.sum_congr rfl (fun L hL => by rw [he L hL, mul_one])] at hdec
  by_contra hcon
  push Not at hcon
  have : ∑ L ∈ Finset.Icc 1 N, abelCoeff (extN v) N L ≤ 0 :=
    Finset.sum_nonpos (fun L hL => hcon L hL)
  linarith

/-! ### Lemma M 的有限维版本 -/

lemma Of_sub (F G : ℕ → ℝ) (n m : ℕ) :
    Of (fun k => G k - F k) n m = Of G n m - Of F n m := by
  unfold Of
  rw [Finset.sum_sub_distrib]
  split_ifs <;> ring

lemma ON_sub {N : ℕ} (F G : ℕ → ℝ) :
    (ON (fun k => G k - F k) : Matrix (Fin N) (Fin N) ℝ) = ON G - ON F := by
  ext i j
  simp only [ON, Matrix.of_apply, Matrix.sub_apply]
  exact Of_sub F G _ _

/-- **Lemma M（Lemma 1.13）的有限维版本，非严格**：`F` 在 `k ≥ 1` 上非增非负，
`F ≤ G`（`k ≥ 1`）⇒ `λ₁^{(N)}(F) ≤ λ₁^{(N)}(G)`。`G` 只需是任意函数。 -/
theorem top_ON_le {N : ℕ} [NeZero N] (F G : ℕ → ℝ) (hF : ∀ k, 1 ≤ k → F (k+1) ≤ F k)
    (hFpos : ∀ k, 1 ≤ k → 0 ≤ F k) (hFG : ∀ k, 1 ≤ k → F k ≤ G k) :
    top (ON_isHermitian (N := N) F) ≤ top (ON_isHermitian (N := N) G) := by
  obtain ⟨v, hv, hv0, hev⟩ := exists_cone_eigenvector (ON_isHermitian (N := N) F)
    (fun t ht w hw => exp_ON_preserves_cone' F hF hFpos w hw t ht)
  have hvv : 0 < v ⬝ᵥ v := dot_self_pos v hv0
  have h1 : v ⬝ᵥ (ON F : Matrix (Fin N) (Fin N) ℝ) *ᵥ v
      = top (ON_isHermitian (N := N) F) * (v ⬝ᵥ v) := by
    rw [hev, dotProduct_smul, smul_eq_mul]
  have h2 : v ⬝ᵥ (ON G : Matrix (Fin N) (Fin N) ℝ) *ᵥ v
      = v ⬝ᵥ (ON F : Matrix (Fin N) (Fin N) ℝ) *ᵥ v
        + v ⬝ᵥ (ON (fun k => G k - F k) : Matrix (Fin N) (Fin N) ℝ) *ᵥ v := by
    rw [ON_sub, Matrix.sub_mulVec, dotProduct_sub]; ring
  have h3 : 0 ≤ v ⬝ᵥ (ON (fun k => G k - F k) : Matrix (Fin N) (Fin N) ℝ) *ᵥ v := by
    rw [quadForm_eq_dot]
    exact quad_form_nonneg _ (fun k hk => sub_nonneg.mpr (hFG k hk)) _ (extN_anti v hv)
      (extN_nonneg v hv) N
  have h4 := dot_mulVec_le (ON_isHermitian (N := N) G) v
  have h5 : top (ON_isHermitian (N := N) F) * (v ⬝ᵥ v)
      ≤ top (ON_isHermitian (N := N) G) * (v ⬝ᵥ v) := by
    linarith
  exact le_of_mul_le_mul_right h5 hvv

/-- **Lemma M 的有限维版本，严格**：此外若 `F(1) < G(1)`，则 `λ₁^{(N)}(F) < λ₁^{(N)}(G)`。 -/
theorem top_ON_lt {N : ℕ} [NeZero N] (F G : ℕ → ℝ) (hF : ∀ k, 1 ≤ k → F (k+1) ≤ F k)
    (hFpos : ∀ k, 1 ≤ k → 0 ≤ F k) (hFG : ∀ k, 1 ≤ k → F k ≤ G k) (h1 : F 1 < G 1) :
    top (ON_isHermitian (N := N) F) < top (ON_isHermitian (N := N) G) := by
  obtain ⟨v, hv, hv0, hev⟩ := exists_cone_eigenvector (ON_isHermitian (N := N) F)
    (fun t ht w hw => exp_ON_preserves_cone' F hF hFpos w hw t ht)
  have hvv : 0 < v ⬝ᵥ v := dot_self_pos v hv0
  have e1 : v ⬝ᵥ (ON F : Matrix (Fin N) (Fin N) ℝ) *ᵥ v
      = top (ON_isHermitian (N := N) F) * (v ⬝ᵥ v) := by
    rw [hev, dotProduct_smul, smul_eq_mul]
  have e2 : v ⬝ᵥ (ON G : Matrix (Fin N) (Fin N) ℝ) *ᵥ v
      = v ⬝ᵥ (ON F : Matrix (Fin N) (Fin N) ℝ) *ᵥ v
        + v ⬝ᵥ (ON (fun k => G k - F k) : Matrix (Fin N) (Fin N) ℝ) *ᵥ v := by
    rw [ON_sub, Matrix.sub_mulVec, dotProduct_sub]; ring
  -- 严格正：Corollary 1.6(3) 有限版
  obtain ⟨L₀, hL₀, ha⟩ := exists_abelCoeff_pos v hv hv0
  rw [Finset.mem_Icc] at hL₀
  have h3 : 0 < v ⬝ᵥ (ON (fun k => G k - F k) : Matrix (Fin N) (Fin N) ℝ) *ᵥ v := by
    rw [quadForm_eq_dot]
    have hlow := quad_form_lower (fun k => G k - F k) (fun k hk => sub_nonneg.mpr (hFG k hk))
      (extN v) (extN_anti v hv) (extN_nonneg v hv) N L₀ hL₀.1 hL₀.2
    have : 0 < abelCoeff (extN v) N L₀ ^ 2 * (G 1 - F 1) :=
      mul_pos (pow_pos ha 2) (sub_pos.mpr h1)
    linarith
  have h4 := dot_mulVec_le (ON_isHermitian (N := N) G) v
  have h5 : top (ON_isHermitian (N := N) F) * (v ⬝ᵥ v)
      < top (ON_isHermitian (N := N) G) * (v ⬝ᵥ v) := by
    linarith
  exact lt_of_mul_lt_mul_right h5 (le_of_lt hvv)

/-! ### Theorem 1.14 的有限维版本 -/

/-- `k^{(N)}(P,T) := λ₁(P_N K(P,T) P_N)`。 -/
noncomputable def kN (P : Measure ℝ) (T : ℝ) (N : ℕ) [NeZero N] : ℝ :=
  top (ON_isHermitian (N := N) (FT P T))

/-- **Theorem 1.14 的有限维版本**：`T ↦ k^{(N)}(P,T)` 在 `(0,∞)` 严格递减。 -/
theorem kN_strictAnti (P : Measure ℝ) [IsProbabilityMeasure P] (hP : ∀ᵐ ω ∂P, 0 < ω)
    {N : ℕ} [NeZero N] (T T' : ℝ) (hT : 0 < T) (hTT : T < T') : kN P T' N < kN P T N := by
  unfold kN
  have hT' : 0 < T' := lt_trans hT hTT
  apply top_ON_lt
  · intro k hk; exact le_of_lt (FT_strictAnti_k P hP T' hT' k (k+1) hk (Nat.lt_succ_self k))
  · intro k _; exact FT_nonneg P T' k
  · intro k hk; exact le_of_lt (FT_strictAnti_T P hP k hk T T' hT hTT)
  · exact FT_strictAnti_T P hP 1 le_rfl T T' hT hTT

/-! ### Theorem B 的有限维版本 -/

/-- `h^{(N)}(ϖ) := λ₁(P_N H(ϖ) P_N)`。 -/
noncomputable def hN (ϖ : ℝ) (N : ℕ) [NeZero N] : ℝ :=
  top (ON_isHermitian (N := N) (fun k => kern k ϖ))

/-- **Theorem B 的有限维版本，不等式**：`k^{(N)}(P,T) ≤ h^{(N)}(ϖ_rms)`。 -/
theorem kN_le_hN_rms (P : Measure ℝ) [IsProbabilityMeasure P] (hP : ∀ᵐ ω ∂P, 0 < ω)
    (hm : Integrable (fun ω => ω ^ 2) P) {N : ℕ} [NeZero N] (T : ℝ) (hT : 0 < T) :
    kN P T N ≤ hN (varpiRms P T) N := by
  unfold kN hN
  apply top_ON_le
  · intro k hk; exact le_of_lt (FT_strictAnti_k P hP T hT k (k+1) hk (Nat.lt_succ_self k))
  · intro k _; exact FT_nonneg P T k
  · intro k hk; exact FT_le_kern_rms P hm k hk T hT

/-- **Theorem B 的有限维版本，等号情形**：或者 `ω²` 几乎处处为常数（`P` 是点质量），
或者 `k^{(N)}(P,T) < h^{(N)}(ϖ_rms)`。 -/
theorem kN_ae_const_or_lt (P : Measure ℝ) [IsProbabilityMeasure P] (hP : ∀ᵐ ω ∂P, 0 < ω)
    (hm : Integrable (fun ω => ω ^ 2) P) {N : ℕ} [NeZero N] (T : ℝ) (hT : 0 < T) :
    (fun ω : ℝ => ω ^ 2) =ᵐ[P] (fun _ => moment2 P) ∨ kN P T N < hN (varpiRms P T) N := by
  rcases FT_ae_const_or_lt_kern_rms P hm 1 le_rfl T hT with h | h
  · left; exact h
  · right
    unfold kN hN
    apply top_ON_lt
    · intro k hk; exact le_of_lt (FT_strictAnti_k P hP T hT k (k+1) hk (Nat.lt_succ_self k))
    · intro k _; exact FT_nonneg P T k
    · intro k hk; exact FT_le_kern_rms P hm k hk T hT
    · exact h

/-- 点质量 `P = δ_{ω_E}` 时 `k^{(N)}(P,T) = h^{(N)}(ϖ_rms)`。 -/
theorem kN_dirac (ωE : ℝ) (hω : 0 ≤ ωE) {N : ℕ} [NeZero N] (T : ℝ) :
    kN (Measure.dirac ωE) T N = hN (varpiRms (Measure.dirac ωE) T) N := by
  unfold kN hN
  have e : FT (Measure.dirac ωE) T = fun k => kern k (varpiRms (Measure.dirac ωE) T) := by
    funext k; exact FT_dirac_eq_kern_rms ωE T hω k
  simp only [e]

/-! ### Lemma 2.2 的有限维版本 -/

lemma ON_smul {N : ℕ} (c : ℝ) (f : ℕ → ℝ) :
    (ON (fun k => c * f k) : Matrix (Fin N) (Fin N) ℝ) = c • ON f := by
  ext i j
  simp only [ON, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  exact Of_smul c f _ _

/-- `λ₁(cA) = c λ₁(A)`（`c > 0`），由 Rayleigh 刻画。 -/
theorem top_smul {N : ℕ} [NeZero N] {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) (c : ℝ)
    (hc : 0 < c) (hcA : (c • A).IsHermitian) : top hcA = c * top hA := by
  apply le_antisymm
  · obtain ⟨x, hx, hq⟩ := (top_isGreatest hcA).1
    rw [hq, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (dot_mulVec_le_top hA x hx) (le_of_lt hc)
  · obtain ⟨x, hx, hq⟩ := (top_isGreatest hA).1
    rw [hq, ← smul_eq_mul, ← dotProduct_smul, ← Matrix.smul_mulVec]
    exact dot_mulVec_le_top hcA x hx

/-- `r^{(N)}(ϖ) := λ₁^{(N)}(k ↦ (k²+ϖ²)⁻¹)`。 -/
noncomputable def rN (ϖ : ℝ) (N : ℕ) [NeZero N] : ℝ :=
  top (ON_isHermitian (N := N) (fun k => 1 / ((k:ℝ) ^ 2 + ϖ ^ 2)))

/-- `g^{(N)}(2) := λ₁^{(N)}(k ↦ k⁻²)`。 -/
noncomputable def gN2 (N : ℕ) [NeZero N] : ℝ :=
  top (ON_isHermitian (N := N) (fun k => 1 / (k:ℝ) ^ 2))

/-- `h^{(N)}(ϖ) = ϖ² r^{(N)}(ϖ)`（`ϖ ≠ 0`）。 -/
theorem hN_eq_sq_mul_rN (ϖ : ℝ) (hϖ : ϖ ≠ 0) (N : ℕ) [NeZero N] : hN ϖ N = ϖ ^ 2 * rN ϖ N := by
  unfold hN rN
  have hpos : 0 < ϖ ^ 2 := by positivity
  have e : (fun k : ℕ => kern k ϖ) = fun k : ℕ => ϖ ^ 2 * (1 / ((k:ℝ) ^ 2 + ϖ ^ 2)) := by
    funext k; unfold kern; ring
  have hH : (ϖ ^ 2 • (ON (fun k => 1 / ((k:ℝ) ^ 2 + ϖ ^ 2)) : Matrix (Fin N) (Fin N) ℝ)).IsHermitian := by
    rw [← ON_smul]; exact ON_isHermitian _
  have : top (ON_isHermitian (N := N) (fun k => kern k ϖ)) = top hH := by
    congr 1
    rw [e, ON_smul]
  rw [this, top_smul (ON_isHermitian _) (ϖ ^ 2) hpos hH]

lemma inv_sq_add_anti (ϖ : ℝ) : ∀ k : ℕ, 1 ≤ k →
    (1:ℝ) / (((k+1:ℕ):ℝ) ^ 2 + ϖ ^ 2) ≤ 1 / ((k:ℝ) ^ 2 + ϖ ^ 2) := by
  intro k hk
  have hk' : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  apply one_div_le_one_div_of_le (by positivity)
  push_cast
  nlinarith

lemma inv_sq_add_pos (ϖ : ℝ) : ∀ k : ℕ, 1 ≤ k → (0:ℝ) ≤ 1 / ((k:ℝ) ^ 2 + ϖ ^ 2) := by
  intro k hk
  have hk' : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  positivity

/-- **Lemma 2.2 的有限维版本，单调性**：`0 < ϖ < ϖ'` ⇒ `r^{(N)}(ϖ') < r^{(N)}(ϖ)`。 -/
theorem rN_strictAnti (ϖ ϖ' : ℝ) (hϖ : 0 < ϖ) (hϖϖ : ϖ < ϖ') (N : ℕ) [NeZero N] :
    rN ϖ' N < rN ϖ N := by
  unfold rN
  have hsq : ϖ ^ 2 < ϖ' ^ 2 := by nlinarith
  apply top_ON_lt
  · exact inv_sq_add_anti ϖ'
  · exact inv_sq_add_pos ϖ'
  · intro k hk
    have hk' : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  · apply one_div_lt_one_div_of_lt (by positivity)
    push_cast; linarith

/-- **Lemma 2.2 的有限维版本，上界**：`ϖ > 0` ⇒ `r^{(N)}(ϖ) < g^{(N)}(2)`，即 `h^{(N)}(ϖ) < g^{(N)}(2) ϖ²`。 -/
theorem rN_lt_gN2 (ϖ : ℝ) (hϖ : 0 < ϖ) (N : ℕ) [NeZero N] : rN ϖ N < gN2 N := by
  unfold rN gN2
  have hsq : 0 < ϖ ^ 2 := by positivity
  apply top_ON_lt
  · exact inv_sq_add_anti ϖ
  · exact inv_sq_add_pos ϖ
  · intro k hk
    have hk' : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  · apply one_div_lt_one_div_of_lt (by positivity)
    push_cast; linarith

theorem hN_lt_gN2_mul (ϖ : ℝ) (hϖ : 0 < ϖ) (N : ℕ) [NeZero N] : hN ϖ N < gN2 N * ϖ ^ 2 := by
  rw [hN_eq_sq_mul_rN ϖ (ne_of_gt hϖ) N, mul_comm]
  have hsq : 0 < ϖ ^ 2 := by positivity
  exact mul_lt_mul_of_pos_right (rN_lt_gN2 ϖ hϖ N) hsq

/-- **Theorem 2.3（Theorem A(c)）的有限维版本**：`k^{(N)}(P,T) < g^{(N)}(2) ⟨ω²⟩/(2πT)²`。
（`⟨ω²⟩ > 0` 由 `P((0,∞)) = 1` 保证。） -/
theorem kN_lt_gN2_mul_varpiSq (P : Measure ℝ) [IsProbabilityMeasure P] (hP : ∀ᵐ ω ∂P, 0 < ω)
    (hm : Integrable (fun ω => ω ^ 2) P) (hm0 : 0 < moment2 P) {N : ℕ} [NeZero N] (T : ℝ)
    (hT : 0 < T) : kN P T N < gN2 N * varpiSq P T := by
  have hrms : 0 < varpiRms P T := by
    unfold varpiRms
    exact div_pos (Real.sqrt_pos.mpr hm0) (two_pi_T_pos T hT)
  have h1 := kN_le_hN_rms P hP hm (N := N) T hT
  have h2 := hN_lt_gN2_mul (varpiRms P T) hrms N
  have e : varpiRms P T ^ 2 = varpiSq P T := by
    unfold varpiRms varpiSq
    rw [div_pow, Real.sq_sqrt (le_of_lt hm0)]
  rw [e] at h2
  linarith

end Eliashberg
