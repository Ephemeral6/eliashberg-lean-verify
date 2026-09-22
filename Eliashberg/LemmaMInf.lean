import Eliashberg.Lam1

/-!
# Lemma M（Lemma 1.13）的严格版，`ℓ²` 层

论文的证明：取 `O[F]` 的锥内单位特征向量 `v ∈ C`（Prop 1.12，需要紧算子谱定理、谱投影
(F3)、半群 (F5)），再 `λ₁(O[G]) ≥ ⟨v, O[G]v⟩ = λ₁(O[F]) + ⟨v, O[G−F]v⟩ ≥ λ₁(O[F]) + a_{L₀}² f(1)`。

这里给出一个**只用有限维对象**的证明，绕开 mathlib 缺失的无穷维谱论：

假设 `λ₁(O[G]) ≤ λ₁(O[F]) =: Λ`（要证矛盾；`≥` 已由 `lam1_mono` 得到）。
对每个 `N`，取 `P_{N+1} O[F] P_{N+1}` 的锥内单位特征向量 `w_N`（`exists_cone_eigenvector`，
特征值 `λ_N := λ₁^{(N+1)}(F) ↑ Λ`）。

1. **`A_N → 0`**：`Λ ≥ λ₁^{(N+1)}(G) ≥ ⟨w_N, O[G] w_N⟩ = λ_N + ⟨w_N, O[G−F] w_N⟩ ≥ λ_N + f(1) A_N`，
   其中 `A_N := ∑_L a_L(w_N)²`（Abel 系数平方和，Cor 1.6 有限版），而 `λ_N → Λ`。
2. **尾部界**（用 HS 可和性）：由特征方程 `λ_N w_N(n) = ∑_m O_{nm} w_N(m)` 与 Cauchy–Schwarz，
   `λ_N² ∑_{M≤n≤N} w_N(n)² ≤ ∑_{M≤n≤N}∑_m O_{nm}² ≤ ‖O[F]‖_HS² − hs(M) =: τ_M`，
   且 `λ_N ≥ F(1) > 0`，故 `∑_{n≥M} w_N(n)² ≤ τ_M/F(1)² =: ε_M → 0`，**对 `N` 一致**。
3. **平坦化矛盾**：`w_N` 递减非负、`‖w_N‖ = 1`，于是 `w_N(0)² ≥ (1−ε_M)/M`；
   而 `w_N(0) − w_N(n) = ∑_{L≤n} a_L ≤ √(n A_N)`（Cauchy–Schwarz）。`N` 大时 `A_N` 很小，
   `w_N(n) ≥ w_N(0)/2` 对所有 `n < 2M` 成立，于是 `∑_{M≤n<2M} w_N(n)² ≥ M · w_N(0)²/4 ≥ (1−ε_M)/4`，
   与尾部界 `≤ ε_M` 矛盾（取 `ε_M < 1/8`）。

数学上这就是"锥内极大化序列不会把质量推向无穷远"，即紧性论证的有限化。
-/

namespace Eliashberg

open scoped BigOperators Matrix
open Filter Topology

/-! ### 锥内单位特征向量（零延拓到 `ℕ → ℝ`） -/

/-- 特征向量的数据：`w : ℕ → ℝ`，支撑在 `[0, N+1)`，在锥内，单位，满足特征方程。 -/
structure ConeEigen (F : ℕ → ℝ) (N : ℕ) where
  w : ℕ → ℝ
  supp : ∀ n, N + 1 ≤ n → w n = 0
  anti : ∀ i j, i ≤ j → w j ≤ w i
  nonneg : ∀ n, 0 ≤ w n
  unit : ∑ n ∈ Finset.range (N+1), w n ^ 2 = 1
  eigen : ∀ n, n < N + 1 → lamN F N * w n = ∑ m ∈ Finset.range (N+1), Of F n m * w m

/-- 由 `exists_cone_eigenvector` 造出归一化的锥内特征向量。 -/
lemma exists_coneEigen (F : ℕ → ℝ) (hF : ∀ k, 1 ≤ k → F (k+1) ≤ F k)
    (hFpos : ∀ k, 1 ≤ k → 0 ≤ F k) (N : ℕ) : Nonempty (ConeEigen F N) := by
  obtain ⟨v, hv, hv0, hev⟩ := exists_cone_eigenvector (ON_isHermitian (N := N+1) F)
    (fun t ht w hw => exp_ON_preserves_cone' F hF hFpos w hw t ht)
  have hvv : 0 < v ⬝ᵥ v := dot_self_pos v hv0
  set c : ℝ := (Real.sqrt (v ⬝ᵥ v))⁻¹ with hc
  have hsq : 0 < Real.sqrt (v ⬝ᵥ v) := Real.sqrt_pos.mpr hvv
  have hcpos : 0 < c := inv_pos.mpr hsq
  refine ⟨⟨fun n => c * extN v n, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro n hn
    unfold extN
    rw [dite_eq_right (by omega), mul_zero]
  · intro i j hij
    have := extN_anti v hv hij
    exact mul_le_mul_of_nonneg_left this (le_of_lt hcpos)
  · intro n
    exact mul_nonneg (le_of_lt hcpos) (extN_nonneg v hv n)
  · have : ∑ n ∈ Finset.range (N+1), (c * extN v n) ^ 2 = c ^ 2 * (v ⬝ᵥ v) := by
      rw [← sum_extN_sq, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro n _; ring
    rw [this, hc, inv_pow, Real.sq_sqrt (le_of_lt hvv)]
    exact inv_mul_cancel₀ (ne_of_gt hvv)
  · intro n hn
    -- 特征方程的第 `n` 个坐标
    have h := congrFun hev ⟨n, hn⟩
    simp only [Matrix.mulVec, dotProduct, ON, Matrix.of_apply, Pi.smul_apply, smul_eq_mul] at h
    have e1 : ∑ m ∈ Finset.range (N+1), Of F n m * (c * extN v m)
        = c * ∑ j : Fin (N+1), Of F n j.val * v j := by
      rw [Finset.mul_sum, ← Fin.sum_univ_eq_sum_range (fun m => Of F n m * (c * extN v m)) (N+1)]
      apply Finset.sum_congr rfl; intro j _
      rw [extN_fin]; ring
    have e2 : extN v n = v ⟨n, hn⟩ := by unfold extN; rw [dite_eq_left hn]
    rw [e1, h, e2]
    show lamN F N * (c * v ⟨n, hn⟩) = c * (lamN F N * v ⟨n, hn⟩)
    ring

/-! ### 步骤 2：一致尾部界 -/

/-- `λ₁^{(N+1)}(F) ≥ F(1)`（Prop 1.12(1) 的有限维形式）。 -/
lemma f1_le_lamN (F : ℕ → ℝ) (N : ℕ) : F 1 ≤ lamN F N := by
  have h := quadForm_le_lamN F N e0 (sum_e0_sq (N+1) (by omega))
  rwa [← rayM_Of, rayM_e0 (Of F) (N+1) (by omega), Of_zero_zero] at h

/-- **一致尾部界**：`F(1) > 0`、`M ≤ N+1` ⇒
`∑_{M≤n<N+1} w_N(n)² ≤ (‖O[F]‖_HS² − hs F M)/F(1)²`。 -/
lemma coneEigen_tail_le {F : ℕ → ℝ} (hF : L1 F) (hF1 : 0 < F 1) {N : ℕ} (E : ConeEigen F N)
    (M : ℕ) (hM : M ≤ N + 1) :
    ∑ n ∈ Finset.Ico M (N+1), E.w n ^ 2 ≤ (hsSup F - hs F M) / F 1 ^ 2 := by
  have hlam : F 1 ≤ lamN F N := f1_le_lamN F N
  have hlam0 : 0 < lamN F N := lt_of_lt_of_le hF1 hlam
  -- 逐坐标：`λ_N² w(n)² ≤ ∑_m O_{nm}²`
  have hcoord : ∀ n, n < N + 1 → lamN F N ^ 2 * E.w n ^ 2
      ≤ ∑ m ∈ Finset.range (N+1), Of F n m ^ 2 := by
    intro n hn
    have h := E.eigen n hn
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (N+1)) (fun m => Of F n m) E.w
    rw [E.unit, mul_one] at hcs
    calc lamN F N ^ 2 * E.w n ^ 2 = (lamN F N * E.w n) ^ 2 := by ring
      _ = (∑ m ∈ Finset.range (N+1), Of F n m * E.w m) ^ 2 := by rw [h]
      _ ≤ _ := hcs
  have hsum : lamN F N ^ 2 * ∑ n ∈ Finset.Ico M (N+1), E.w n ^ 2
      ≤ ∑ n ∈ Finset.Ico M (N+1), ∑ m ∈ Finset.range (N+1), Of F n m ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro n hn
    rw [Finset.mem_Ico] at hn
    exact hcoord n hn.2
  have hbox := hs_tail_box_le hF M (N+1) hM
  have hF1sq : 0 < F 1 ^ 2 := by positivity
  have hlamsq : F 1 ^ 2 ≤ lamN F N ^ 2 := by nlinarith
  have htail0 : 0 ≤ ∑ n ∈ Finset.Ico M (N+1), E.w n ^ 2 := Finset.sum_nonneg (fun n _ => sq_nonneg _)
  rw [le_div_iff₀ hF1sq]
  calc (∑ n ∈ Finset.Ico M (N+1), E.w n ^ 2) * F 1 ^ 2
      ≤ (∑ n ∈ Finset.Ico M (N+1), E.w n ^ 2) * lamN F N ^ 2 :=
        mul_le_mul_of_nonneg_left hlamsq htail0
    _ = lamN F N ^ 2 * ∑ n ∈ Finset.Ico M (N+1), E.w n ^ 2 := by ring
    _ ≤ _ := hsum
    _ ≤ hsSup F - hs F M := hbox

/-! ### 步骤 1：Abel 系数平方和趋于零 -/

/-- Abel 系数平方和 `A(w) := ∑_{L=1}^{N+1} a_L(w)²`（`a_L = w_{L−1} − w_L`，含 `w_{N+1} = 0`）。 -/
noncomputable def abelSq {F : ℕ → ℝ} {N : ℕ} (E : ConeEigen F N) : ℝ :=
  ∑ L ∈ Finset.Icc 1 (N+1), (E.w (L - 1) - E.w L) ^ 2

/-- 零延拓下 `abelCoeff w (N+1) L = w(L−1) − w(L)` 对 `L ∈ [1, N+1]`。 -/
lemma abelCoeff_eq {F : ℕ → ℝ} {N : ℕ} (E : ConeEigen F N) (L : ℕ) (hL : 1 ≤ L) (hL2 : L ≤ N + 1) :
    abelCoeff E.w (N+1) L = E.w (L - 1) - E.w L := by
  unfold abelCoeff
  split_ifs with h
  · rfl
  · have : L = N + 1 := by omega
    rw [this, E.supp (N+1) le_rfl, sub_zero]

/-- Cor 1.6 的有限版，求和形式：`⟨w, O[f] w⟩ ≥ f(1) ∑_L a_L²`（`f ≥ 0` 于 `k ≥ 1`）。 -/
lemma quadForm_ge_f1_abelSq {F : ℕ → ℝ} {N : ℕ} (E : ConeEigen F N) (f : ℕ → ℝ)
    (hf : ∀ k, 1 ≤ k → 0 ≤ f k) : f 1 * abelSq E ≤ quadForm f E.w (N+1) := by
  rw [quad_form_eq]
  have hanti : Antitone E.w := fun i j h => E.anti i j h
  have hnn : ∀ n, 0 ≤ E.w n := E.nonneg
  -- 丢掉 `L ≠ L'` 的项（非负），对角项 `≥ f(1) a_L²`
  have hdiag : ∀ L ∈ Finset.Icc 1 (N+1),
      f 1 * (E.w (L - 1) - E.w L) ^ 2
        ≤ ∑ Lp ∈ Finset.Icc 1 (N+1), abelCoeff E.w (N+1) L * abelCoeff E.w (N+1) Lp * Qf f L Lp := by
    intro L hL
    rw [Finset.mem_Icc] at hL
    have hmem : L ∈ Finset.Icc 1 (N+1) := Finset.mem_Icc.mpr hL
    have hterm : ∀ Lp ∈ Finset.Icc 1 (N+1),
        0 ≤ abelCoeff E.w (N+1) L * abelCoeff E.w (N+1) Lp * Qf f L Lp := fun Lp _ =>
      mul_nonneg (mul_nonneg (abel_coeff_nonneg _ hanti hnn _ _) (abel_coeff_nonneg _ hanti hnn _ _))
        (Qf_nonneg f hf L Lp)
    have h1 := Finset.single_le_sum hterm hmem
    have h2 : f 1 * (E.w (L - 1) - E.w L) ^ 2
        ≤ abelCoeff E.w (N+1) L * abelCoeff E.w (N+1) L * Qf f L L := by
      rw [abelCoeff_eq E L hL.1 hL.2, ← sq]
      rw [mul_comm]
      apply mul_le_mul_of_nonneg_left (Qf_LL_lower f hf L hL.1) (sq_nonneg _)
    linarith
  unfold abelSq
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum hdiag

/-- 步骤 1：若 `λ₁(O[G]) ≤ λ₁(O[F])`，则 `f(1) A_N ≤ Λ − λ_N`。 -/
lemma f1_abelSq_le {F G : ℕ → ℝ} (hG : L1 G) (hFG : ∀ k, 1 ≤ k → F k ≤ G k)
    (hle : lam1 G ≤ lam1 F) {N : ℕ} (E : ConeEigen F N) :
    (G 1 - F 1) * abelSq E ≤ lam1 F - lamN F N := by
  have hq : quadForm G E.w (N+1) = quadForm F E.w (N+1) + quadForm (fun k => G k - F k) E.w (N+1) := by
    rw [quadForm_sub]; ring
  -- `⟨w, O[F] w⟩ = λ_N`
  have hF : quadForm F E.w (N+1) = lamN F N := by
    unfold quadForm
    have : ∀ n ∈ Finset.range (N+1), ∑ m ∈ Finset.range (N+1), E.w n * Of F n m * E.w m
        = E.w n * (lamN F N * E.w n) := by
      intro n hn
      rw [Finset.mem_range] at hn
      rw [E.eigen n hn, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro m _; ring
    rw [Finset.sum_congr rfl this]
    have e : ∑ n ∈ Finset.range (N+1), E.w n * (lamN F N * E.w n)
        = lamN F N * ∑ n ∈ Finset.range (N+1), E.w n ^ 2 := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro n _; ring
    rw [e, E.unit, mul_one]
  have hG' := quadForm_le_lam1 hG E.w (N+1) E.unit
  have hlow := quadForm_ge_f1_abelSq E (fun k => G k - F k) (fun k hk => sub_nonneg.mpr (hFG k hk))
  linarith

/-! ### 步骤 3：平坦化矛盾 -/

/-- `w(0) − w(n) = ∑_{L=1}^{n} a_L`（望远镜）。 -/
lemma w_zero_sub_eq {F : ℕ → ℝ} {N : ℕ} (E : ConeEigen F N) (n : ℕ) :
    E.w 0 - E.w n = ∑ L ∈ Finset.Icc 1 n, (E.w (L - 1) - E.w L) := by
  have e : Finset.Icc 1 n = Finset.Ico 1 (n+1) := rfl
  rw [e, Finset.sum_Ico_eq_sum_range]
  have : ∀ i, E.w (1 + i - 1) - E.w (1 + i) = E.w i - E.w (i + 1) := by
    intro i; congr 2 <;> omega
  simp only [this]
  rw [Finset.sum_range_sub' E.w]
  have : n + 1 - 1 = n := by omega
  rw [this]

/-- Cauchy–Schwarz：`(w(0) − w(n))² ≤ n · A`（`n ≤ N+1`）。 -/
lemma w_zero_sub_sq_le {F : ℕ → ℝ} {N : ℕ} (E : ConeEigen F N) (n : ℕ) (hn : n ≤ N + 1) :
    (E.w 0 - E.w n) ^ 2 ≤ (n:ℝ) * abelSq E := by
  rw [w_zero_sub_eq]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 1 n) (fun _ => (1:ℝ))
    (fun L => E.w (L - 1) - E.w L)
  simp only [one_mul, one_pow, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul,
    mul_one] at hcs
  refine hcs.trans ?_
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
  unfold abelSq
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro L hL; simp only [Finset.mem_Icc] at hL ⊢; omega
  · intro L _ _; exact sq_nonneg _

/-- `w(0)² · M ≥ ∑_{n<M} w(n)²`（`w` 递减）。 -/
lemma sum_sq_le_M_w0_sq {F : ℕ → ℝ} {N : ℕ} (E : ConeEigen F N) (M : ℕ) :
    ∑ n ∈ Finset.range M, E.w n ^ 2 ≤ (M:ℝ) * E.w 0 ^ 2 := by
  have : ∀ n ∈ Finset.range M, E.w n ^ 2 ≤ E.w 0 ^ 2 := by
    intro n _
    have h1 := E.anti 0 n (Nat.zero_le n)
    have h2 := E.nonneg n
    nlinarith
  calc ∑ n ∈ Finset.range M, E.w n ^ 2 ≤ ∑ _n ∈ Finset.range M, E.w 0 ^ 2 := Finset.sum_le_sum this
    _ = (M:ℝ) * E.w 0 ^ 2 := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **平坦化矛盾**：若 `0 < ε < 1/8`、`M ≥ 1`、`2M ≤ N+1`，`∑_{M≤n<N+1} w² ≤ ε`，
`∑_{n<M} w² ≥ 1 − ε`，且 `A ≤ (1−ε)/(32 M²)`，则矛盾。 -/
lemma flatness_contra {F : ℕ → ℝ} {N : ℕ} (E : ConeEigen F N) (M : ℕ) (hM : 1 ≤ M)
    (hMN : 2 * M ≤ N + 1) (ε : ℝ) (hε : ε < 1 / 8)
    (htail : ∑ n ∈ Finset.Ico M (N+1), E.w n ^ 2 ≤ ε)
    (hA : abelSq E ≤ (1 - ε) / (32 * (M:ℝ) ^ 2)) : False := by
  have hMpos : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM
  have hε0 : 0 ≤ ε := le_trans (Finset.sum_nonneg (fun n _ => sq_nonneg _)) htail
  -- 头部质量 `≥ 1 − ε`
  have hhead : 1 - ε ≤ ∑ n ∈ Finset.range M, E.w n ^ 2 := by
    have := E.unit
    rw [← Finset.sum_range_add_sum_Ico _ (by omega : M ≤ N + 1)] at this
    linarith
  -- `w(0)² ≥ (1−ε)/M`
  have hw0 : (1 - ε) / (M:ℝ) ≤ E.w 0 ^ 2 := by
    rw [div_le_iff₀ hMpos]
    have := sum_sq_le_M_w0_sq E M
    linarith
  have hw0pos : 0 < E.w 0 := by
    have h1 : 0 < (1 - ε) / (M:ℝ) := div_pos (by linarith) hMpos
    have h2 : 0 < E.w 0 ^ 2 := lt_of_lt_of_le h1 hw0
    have h3 := E.nonneg 0
    rcases lt_or_eq_of_le h3 with h | h
    · exact h
    · rw [← h] at h2; simp at h2
  -- 对 `n < 2M`：`(w(0) − w(n))² ≤ 2M · A ≤ (1−ε)/(16M) ≤ w(0)²/16`，故 `w(n) ≥ w(0) − w(0)/4`
  have hn_lower : ∀ n, n < 2 * M → E.w 0 / 2 ≤ E.w n := by
    intro n hn
    have h1 := w_zero_sub_sq_le E n (by omega)
    have hn' : (n:ℝ) ≤ 2 * (M:ℝ) := by exact_mod_cast (le_of_lt hn)
    have hA0 : 0 ≤ abelSq E := Finset.sum_nonneg (fun L _ => sq_nonneg _)
    have h2 : (E.w 0 - E.w n) ^ 2 ≤ 2 * (M:ℝ) * ((1 - ε) / (32 * (M:ℝ) ^ 2)) := by
      calc (E.w 0 - E.w n) ^ 2 ≤ (n:ℝ) * abelSq E := h1
        _ ≤ 2 * (M:ℝ) * abelSq E := mul_le_mul_of_nonneg_right hn' hA0
        _ ≤ 2 * (M:ℝ) * ((1 - ε) / (32 * (M:ℝ) ^ 2)) := mul_le_mul_of_nonneg_left hA (by positivity)
    have h3 : 2 * (M:ℝ) * ((1 - ε) / (32 * (M:ℝ) ^ 2)) = ((1 - ε) / (M:ℝ)) / 16 := by
      field_simp; ring
    rw [h3] at h2
    have h4 : (E.w 0 - E.w n) ^ 2 ≤ E.w 0 ^ 2 / 16 := by linarith
    have h5 : E.w 0 - E.w n ≤ E.w 0 / 4 := by
      have : (E.w 0 - E.w n) ^ 2 ≤ (E.w 0 / 4) ^ 2 := by linarith
      have hpos : 0 ≤ E.w 0 / 4 := by linarith
      exact abs_le_of_sq_le_sq' this hpos |>.2
    linarith
  -- 于是 `∑_{M≤n<2M} w(n)² ≥ M · w(0)²/4 ≥ (1−ε)/4 > ε`
  have hmid : (M:ℝ) * (E.w 0 ^ 2 / 4) ≤ ∑ n ∈ Finset.Ico M (2 * M), E.w n ^ 2 := by
    have : ∀ n ∈ Finset.Ico M (2 * M), E.w 0 ^ 2 / 4 ≤ E.w n ^ 2 := by
      intro n hn
      rw [Finset.mem_Ico] at hn
      have := hn_lower n hn.2
      have h0 : 0 ≤ E.w 0 / 2 := by linarith
      calc E.w 0 ^ 2 / 4 = (E.w 0 / 2) ^ 2 := by ring
        _ ≤ E.w n ^ 2 := pow_le_pow_left₀ h0 this 2
    calc (M:ℝ) * (E.w 0 ^ 2 / 4) = ∑ _n ∈ Finset.Ico M (2 * M), E.w 0 ^ 2 / 4 := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
          have : 2 * M - M = M := by omega
          rw [this]
      _ ≤ _ := Finset.sum_le_sum this
  have hsub : ∑ n ∈ Finset.Ico M (2 * M), E.w n ^ 2 ≤ ∑ n ∈ Finset.Ico M (N+1), E.w n ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico le_rfl hMN)
      (fun n _ _ => sq_nonneg _)
  have h6 : (1 - ε) / 4 ≤ (M:ℝ) * (E.w 0 ^ 2 / 4) := by
    have := mul_le_mul_of_nonneg_left hw0 (le_of_lt hMpos)
    rw [mul_div_assoc', mul_div_cancel_left₀ _ (ne_of_gt hMpos)] at this
    linarith
  linarith

/-! ### 组装 -/

/-- **Lemma M（Lemma 1.13），严格版，`ℓ²` 层**：`F` 在 `k ≥ 1` 上非增非负、`F ∈ ℓ¹`、`F(1) > 0`，
`G ∈ ℓ¹`、`F ≤ G`（`k ≥ 1`）、`F(1) < G(1)` ⇒ `λ₁(O[F]) < λ₁(O[G])`。 -/
theorem lam1_lt {F G : ℕ → ℝ} (hFl1 : L1 F) (hF : ∀ k, 1 ≤ k → F (k+1) ≤ F k)
    (hFpos : ∀ k, 1 ≤ k → 0 ≤ F k) (hF1 : 0 < F 1) (hG : L1 G)
    (hFG : ∀ k, 1 ≤ k → F k ≤ G k) (h1 : F 1 < G 1) : lam1 F < lam1 G := by
  rcases lt_or_ge (lam1 F) (lam1 G) with h | hle
  · exact h
  exfalso
  -- 特征向量族
  have hE : ∀ N, Nonempty (ConeEigen F N) := exists_coneEigen F hF hFpos
  let E : ∀ N, ConeEigen F N := fun N => Classical.choice (hE N)
  -- 步骤 1：`A_N → 0`
  have hA_tend : Tendsto (fun N => abelSq (E N)) atTop (𝓝 0) := by
    have hlam := lamN_tendsto hFl1
    have hd : Tendsto (fun N => (lam1 F - lamN F N) / (G 1 - F 1)) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := lam1 F)).sub hlam
      rw [sub_self] at this
      have := this.div_const (G 1 - F 1)
      rwa [zero_div] at this
    apply squeeze_zero (fun N => Finset.sum_nonneg (fun L _ => sq_nonneg _)) _ hd
    intro N
    have := f1_abelSq_le hG hFG hle (E N)
    rw [le_div_iff₀ (sub_pos.mpr h1), mul_comm]
    exact this
  -- 步骤 2：尾部 `ε_M → 0`
  have hε_tend : Tendsto (fun M => (hsSup F - hs F M) / F 1 ^ 2) atTop (𝓝 0) := by
    have := (hs_tail_tendsto_zero hFl1).div_const (F 1 ^ 2)
    rwa [zero_div] at this
  -- 取 `M ≥ 1` 使 `ε_M < 1/8`
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp (hε_tend.eventually_lt_const (by norm_num : (0:ℝ) < 1/8))
  set M := max M₀ 1 with hMdef
  have hM1 : 1 ≤ M := le_max_right _ _
  have hεM : (hsSup F - hs F M) / F 1 ^ 2 < 1 / 8 := hM₀ M (le_max_left _ _)
  set ε := (hsSup F - hs F M) / F 1 ^ 2 with hε
  -- 取 `N` 使 `A_N ≤ (1−ε)/(32M²)` 且 `2M ≤ N+1`
  have hεnn : 0 ≤ ε := by
    have h1 := coneEigen_tail_le hFl1 hF1 (E (2 * M)) M (by omega)
    exact le_trans (Finset.sum_nonneg (fun n _ => sq_nonneg _)) h1
  have hbound_pos : 0 < (1 - ε) / (32 * (M:ℝ) ^ 2) := by
    have : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM1
    apply div_pos (by linarith) (by positivity)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hA_tend.eventually_le_const hbound_pos)
  set N := max N₀ (2 * M) with hNdef
  have hN1 : N₀ ≤ N := le_max_left _ _
  have hN2 : 2 * M ≤ N + 1 := by have := le_max_right N₀ (2 * M); omega
  have htail := coneEigen_tail_le hFl1 hF1 (E N) M (by omega)
  exact flatness_contra (E N) M hM1 hN2 ε hεM htail (hN₀ N hN1)

end Eliashberg
