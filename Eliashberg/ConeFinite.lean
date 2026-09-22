import Eliashberg.Corollaries

/-!
# Proposition 1.11 的有限维部分：(F4) 与阶梯基下的 Metzler 矩阵

论文 §1.3。Proposition 1.11 说 `e^{tO[F]} C ⊂ C`。其证明的**有限维核心**是：

1. **(F4)** Metzler 矩阵（非对角元 `≥ 0`）的指数 `e^{tB}` 逐元非负（`t ≥ 0`），
   故保持非负卦限。
2. 在阶梯基 `{e_1, …, e_N}` 下，`O^{(N)} := P_N O[F] P_N` 的矩阵 `B` 满足
   `B_{LL'} = W_{L,L'}(F)`（`L ≤ N-1`）、`B_{NL'} = (O[F] e_{L'})_{N-1}`，
   由 Corollary 1.10 两者在 `L ≠ L'` 时非负，故 `B` 是 Metzler 的。
3. 于是 `e^{tO^{(N)}}` 保持 `C_N = C ∩ ran P_N`（坐标非负卦限）。

本文件把这三步全部形式化（`N × N` 实矩阵，`Fin N` 索引）：

* `EntryNonneg`、`exp_entryNonneg`：逐元非负矩阵的指数逐元非负（级数部分和的极限）
* `Metzler`、**`exp_smul_entryNonneg_of_metzler`**：(F4)
* `E`、`D`：阶梯基矩阵与其逆（`D * E = 1`，`E * D = 1`）；`D.mulVec v` 是 Abel 坐标
* `inConeN_iff`：`v ∈ C_N ⟺ D v ≥ 0`（Lemma 0.3.1 的「`C_N` 是坐标非负卦限」）
* `B`、`B_apply`、**`B_metzler`**：阶梯基下的矩阵是 Metzler 的
* **`exp_ON_preserves_cone`**：`v ∈ C_N`、`t ≥ 0` ⇒ `e^{tO^{(N)}} v ∈ C_N`

论文 Proposition 1.11 的最后一段（`N → ∞`、`O^{(N)} → O[F]` 强收敛、(F5)、`C` 闭）
需要 `ℓ²` 上的算子理论，属于第三层。

## 与论文的一处小偏离

(F4) 的证明中论文取 `c := max_L (−B_{LL})^+`；这里取 `c := ∑_L |B_{LL}|`，同样使 `B + cI`
逐元非负，且避免了 `Finset.sup'` 的非空性讨论。
-/

namespace Eliashberg

open scoped Matrix
open NormedSpace

section Metzler

variable {N : ℕ}

/-- 逐元非负。 -/
def EntryNonneg (A : Matrix (Fin N) (Fin N) ℝ) : Prop := ∀ i j, 0 ≤ A i j

/-- Metzler：非对角元非负。 -/
def Metzler (A : Matrix (Fin N) (Fin N) ℝ) : Prop := ∀ i j, i ≠ j → 0 ≤ A i j

lemma EntryNonneg.mul {A B : Matrix (Fin N) (Fin N) ℝ} (hA : EntryNonneg A) (hB : EntryNonneg B) :
    EntryNonneg (A * B) := by
  intro i j
  rw [Matrix.mul_apply]
  exact Finset.sum_nonneg (fun k _ => mul_nonneg (hA i k) (hB k j))

lemma EntryNonneg.pow {A : Matrix (Fin N) (Fin N) ℝ} (hA : EntryNonneg A) (n : ℕ) :
    EntryNonneg (A ^ n) := by
  induction n with
  | zero => intro i j; rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ n ih => rw [pow_succ]; exact ih.mul hA

lemma EntryNonneg.smul {A : Matrix (Fin N) (Fin N) ℝ} (hA : EntryNonneg A) {c : ℝ} (hc : 0 ≤ c) :
    EntryNonneg (c • A) := by
  intro i j; rw [Matrix.smul_apply, smul_eq_mul]; exact mul_nonneg hc (hA i j)

lemma EntryNonneg.sum {ι : Type*} (s : Finset ι) (f : ι → Matrix (Fin N) (Fin N) ℝ)
    (h : ∀ i ∈ s, EntryNonneg (f i)) : EntryNonneg (∑ i ∈ s, f i) := by
  intro a b
  rw [Matrix.sum_apply]
  exact Finset.sum_nonneg (fun i hi => h i hi a b)

open scoped Matrix.Norms.Operator in
/-- 逐元非负矩阵的指数逐元非负：`exp A = ∑ A^n/n!` 是逐元非负矩阵的极限，`[0,∞)` 闭。 -/
lemma exp_entryNonneg {A : Matrix (Fin N) (Fin N) ℝ} (hA : EntryNonneg A) :
    EntryNonneg (exp A) := by
  intro i j
  have hs : HasSum (fun n : ℕ => ((n.factorial : ℝ)⁻¹) • A ^ n) (exp A) :=
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A
  have ht := hs.tendsto_sum_nat
  have hcont : Continuous (fun M : Matrix (Fin N) (Fin N) ℝ => M i j) :=
    Continuous.matrix_elem continuous_id i j
  have ht' := (hcont.tendsto _).comp ht
  apply ge_of_tendsto' ht'
  intro n
  simp only [Function.comp]
  have : EntryNonneg (∑ k ∈ Finset.range n, ((k.factorial : ℝ)⁻¹) • A ^ k) := by
    apply EntryNonneg.sum
    intro k _
    exact (hA.pow k).smul (by positivity)
  exact this i j

open scoped Matrix.Norms.Operator in
/-- `exp (r • 1) = e^r • 1`。 -/
lemma exp_smul_one (r : ℝ) :
    exp ((r • (1 : Matrix (Fin N) (Fin N) ℝ))) = Real.exp r • (1 : Matrix (Fin N) (Fin N) ℝ) := by
  have h := NormedSpace.algebraMap_exp_comm (𝕂 := ℝ) (𝔸 := Matrix (Fin N) (Fin N) ℝ) r
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one] at h
  rw [Real.exp_eq_exp_ℝ]
  exact h.symm

/-- **(F4)**：`B` Metzler、`t ≥ 0` ⇒ `e^{tB}` 逐元非负。 -/
theorem exp_smul_entryNonneg_of_metzler {B : Matrix (Fin N) (Fin N) ℝ} (hB : Metzler B)
    (t : ℝ) (ht : 0 ≤ t) : EntryNonneg (exp (t • B)) := by
  -- `c := ∑ |B_ii|`，则 `B + c•1` 逐元非负
  set c : ℝ := ∑ i, |B i i| with hc
  have hc0 : 0 ≤ c := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hBc : EntryNonneg (B + c • (1 : Matrix (Fin N) (Fin N) ℝ)) := by
    intro i j
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases h : i = j
    · subst h
      simp only [ite_true, mul_one]
      have h1 : |B i i| ≤ c := Finset.single_le_sum (fun k _ => abs_nonneg (B k k)) (Finset.mem_univ i)
      linarith [neg_abs_le (B i i)]
    · simp only [h, ite_false, mul_zero, add_zero]
      exact hB i j h
  -- `t•B = t•(B + c•1) + (-(t c))•1`，两项交换
  have hsplit : t • B = t • (B + c • (1 : Matrix (Fin N) (Fin N) ℝ))
      + (-(t * c)) • (1 : Matrix (Fin N) (Fin N) ℝ) := by
    rw [smul_add, smul_smul, add_assoc, ← add_smul]
    simp
  have hcomm : Commute (t • (B + c • (1 : Matrix (Fin N) (Fin N) ℝ)))
      ((-(t * c)) • (1 : Matrix (Fin N) (Fin N) ℝ)) :=
    ((Commute.one_right _).smul_right _).smul_left _
  rw [hsplit, Matrix.exp_add_of_commute _ _ hcomm, exp_smul_one]
  have h1 : EntryNonneg (exp (t • (B + c • (1 : Matrix (Fin N) (Fin N) ℝ)))) :=
    exp_entryNonneg (hBc.smul ht)
  intro i j
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_apply, smul_eq_mul]
  exact mul_nonneg (le_of_lt (Real.exp_pos _)) (h1 i j)

end Metzler

/-! ### 阶梯基 -/

section Ladder

variable {N : ℕ}

/-- 阶梯基矩阵：第 `i` 列是 `e_{i+1} = 1_{[0, i]}`，即 `E_{n i} = 1_{n ≤ i}`。 -/
def E : Matrix (Fin N) (Fin N) ℝ := Matrix.of fun n i => if n.val ≤ i.val then 1 else 0

/-- 上移矩阵 `S_{i n} = 1_{n = i+1}`。 -/
def Sh : Matrix (Fin N) (Fin N) ℝ := Matrix.of fun i n => if i.val + 1 = n.val then 1 else 0

/-- `D := 1 − S`：`(Dv)_i = v_i − v_{i+1}`（`i < N−1`），`(Dv)_{N-1} = v_{N-1}`，即 Abel 坐标。 -/
def D : Matrix (Fin N) (Fin N) ℝ := 1 - Sh

lemma Sh_mul_apply (M : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) :
    ((Sh : Matrix (Fin N) (Fin N) ℝ) * M) i j = if h : i.val + 1 < N then M ⟨i.val + 1, h⟩ j else 0 := by
  rw [Matrix.mul_apply]
  simp only [Sh, Matrix.of_apply, ite_mul, one_mul, zero_mul]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨i.val + 1, h⟩]
    · simp
    · intro n _ hn
      have : ¬ (i.val + 1 = n.val) := by
        intro heq; apply hn; ext; simp [heq]
      simp [this]
    · intro habs; exact absurd (Finset.mem_univ _) habs
  · apply Finset.sum_eq_zero
    intro n _
    have : ¬ (i.val + 1 = n.val) := by have := n.isLt; omega
    simp [this]

lemma Sh_mulVec_apply (v : Fin N → ℝ) (i : Fin N) :
    (Sh.mulVec v) i = if h : i.val + 1 < N then v ⟨i.val + 1, h⟩ else 0 := by
  simp only [Matrix.mulVec, dotProduct, Sh, Matrix.of_apply, ite_mul, one_mul, zero_mul]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨i.val + 1, h⟩]
    · simp
    · intro n _ hn
      have : ¬ (i.val + 1 = n.val) := by
        intro heq; apply hn; ext; simp [heq]
      simp [this]
    · intro habs; exact absurd (Finset.mem_univ _) habs
  · apply Finset.sum_eq_zero
    intro n _
    have : ¬ (i.val + 1 = n.val) := by have := n.isLt; omega
    simp [this]

lemma D_mulVec_apply (v : Fin N → ℝ) (i : Fin N) :
    (D.mulVec v) i = v i - (if h : i.val + 1 < N then v ⟨i.val + 1, h⟩ else 0) := by
  unfold D
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, Sh_mulVec_apply]

lemma D_mul_apply (M : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) :
    ((D : Matrix (Fin N) (Fin N) ℝ) * M) i j = M i j - (if h : i.val + 1 < N then M ⟨i.val + 1, h⟩ j else 0) := by
  unfold D
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, Sh_mul_apply]

/-- `D * E = 1`。 -/
lemma D_mul_E : (D : Matrix (Fin N) (Fin N) ℝ) * E = 1 := by
  ext i j
  rw [D_mul_apply, Matrix.one_apply]
  simp only [E, Matrix.of_apply]
  have hij : (i = j) ↔ (i.val = j.val) := Fin.ext_iff
  have hj := j.isLt
  split_ifs <;> simp_all <;> omega

lemma isUnit_E : IsUnit (E : Matrix (Fin N) (Fin N) ℝ) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_left_inverse D_mul_E)

lemma E_inv : (E : Matrix (Fin N) (Fin N) ℝ)⁻¹ = D := Matrix.inv_eq_left_inv D_mul_E

/-- `E * D = 1`。 -/
lemma E_mul_D : (E : Matrix (Fin N) (Fin N) ℝ) * D = 1 := by
  rw [← E_inv]
  exact Matrix.mul_nonsing_inv _ (Matrix.isUnit_det_of_left_inverse D_mul_E)

/-- `C_N`：`v_0 ≥ v_1 ≥ ⋯ ≥ v_{N-1} ≥ 0`。 -/
def InConeN (v : Fin N → ℝ) : Prop := (∀ i j : Fin N, i ≤ j → v j ≤ v i) ∧ (∀ i, 0 ≤ v i)

/-- Lemma 0.3.1 的有限维形式：`v ∈ C_N ⟺` Abel 坐标 `Dv ≥ 0`。 -/
theorem inConeN_iff (v : Fin N → ℝ) : InConeN v ↔ ∀ i, 0 ≤ (D.mulVec v) i := by
  constructor
  · rintro ⟨hanti, hpos⟩ i
    rw [D_mulVec_apply]
    split_ifs with h
    · exact sub_nonneg.mpr (hanti i ⟨i.val + 1, h⟩ (by simp [Fin.le_def]))
    · simpa using hpos i
  · intro hD
    have hstep : ∀ i : Fin N, ∀ h : i.val + 1 < N, v ⟨i.val + 1, h⟩ ≤ v i := by
      intro i h
      have := hD i
      rw [D_mulVec_apply, dite_eq_left h] at this
      linarith
    have hchain : ∀ n : ℕ, ∀ i : Fin N, ∀ h : i.val + n < N, v ⟨i.val + n, h⟩ ≤ v i := by
      intro n
      induction n with
      | zero => intro i h; simp
      | succ n ih =>
        intro i h
        have h1 : i.val + n < N := by omega
        have h2 := hstep ⟨i.val + n, h1⟩ (by simp; omega)
        have h3 := ih i h1
        simp only at h2
        calc v ⟨i.val + (n + 1), h⟩ = v ⟨i.val + n + 1, by omega⟩ := by congr 1
          _ ≤ v ⟨i.val + n, h1⟩ := h2
          _ ≤ v i := h3
    have hanti : ∀ i j : Fin N, i ≤ j → v j ≤ v i := by
      intro i j hij
      rw [Fin.le_def] at hij
      have := hchain (j.val - i.val) i (by omega)
      convert this using 2
      ext; simp; omega
    refine ⟨hanti, ?_⟩
    intro i
    -- `v_{N-1} = (Dv)_{N-1} ≥ 0`，再由单调性
    have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) i.isLt
    have hlast : 0 ≤ v ⟨N - 1, by omega⟩ := by
      have := hD ⟨N - 1, by omega⟩
      rw [D_mulVec_apply] at this
      have hno : ¬ ((⟨N - 1, by omega⟩ : Fin N).val + 1 < N) := by simp; omega
      rw [dite_eq_right hno, sub_zero] at this
      exact this
    exact le_trans hlast (hanti i ⟨N - 1, by omega⟩ (by rw [Fin.le_def]; simp; omega))

end Ladder

/-! ### 阶梯基下的矩阵 `B` 与 Proposition 1.11 的有限维部分 -/

section Prop111

variable {N : ℕ} (F : ℕ → ℝ)

/-- `O^{(N)} := P_N O[F] P_N`，作为 `N × N` 矩阵。 -/
noncomputable def ON : Matrix (Fin N) (Fin N) ℝ := Matrix.of fun n m => Of F n.val m.val

/-- 阶梯基下 `O^{(N)}` 的矩阵：`B := E⁻¹ O^{(N)} E = D O^{(N)} E`。 -/
noncomputable def B : Matrix (Fin N) (Fin N) ℝ := D * ON F * E

lemma ON_eq : (ON F : Matrix (Fin N) (Fin N) ℝ) = E * B F * D := by
  unfold B
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, E_mul_D, Matrix.one_mul, Matrix.mul_assoc, E_mul_D,
    Matrix.mul_one]

/-- 行和 `g_F(L', n) := ∑_{m<L'} O[F]_{nm} = (O[F] e_{L'})_n`。 -/
noncomputable def gF (Lp n : ℕ) : ℝ := ∑ m ∈ Finset.range Lp, Of F n m

/-- `∑_{m : Fin N} 1_{m ≤ j} f(m) = ∑_{m < j+1} f(m)`。 -/
lemma sum_fin_le (j : Fin N) (f : ℕ → ℝ) :
    ∑ m : Fin N, (if m.val ≤ j.val then f m.val else 0) = ∑ m ∈ Finset.range (j.val + 1), f m := by
  rw [Fin.sum_univ_eq_sum_range (fun m => if m ≤ j.val then f m else 0) N]
  have e : ∀ m, (m ≤ j.val) ↔ (m < j.val + 1) := fun m => by omega
  simp only [e]
  rw [sum_range_ite_lt]
  have : min N (j.val + 1) = j.val + 1 := by have := j.isLt; omega
  rw [this]

lemma ON_mul_E_apply (i j : Fin N) :
    ((ON F : Matrix (Fin N) (Fin N) ℝ) * (E : Matrix (Fin N) (Fin N) ℝ)) i j
      = gF F (j.val + 1) i.val := by
  rw [Matrix.mul_apply]
  simp only [ON, E, Matrix.of_apply, mul_ite, mul_one, mul_zero]
  exact sum_fin_le j (fun m => Of F i.val m)

/-- `B_{ij} = g_F(j+1, i) − g_F(j+1, i+1)`（`i+1 < N`）`= W_{i+1,j+1}(F)`；`B_{N-1,j} = g_F(j+1, N−1)`。 -/
lemma B_apply (i j : Fin N) :
    B F i j = gF F (j.val + 1) i.val
      - (if h : i.val + 1 < N then gF F (j.val + 1) (i.val + 1) else 0) := by
  unfold B
  rw [Matrix.mul_assoc, D_mul_apply, ON_mul_E_apply]
  split_ifs with h
  · rw [ON_mul_E_apply]
  · rfl

lemma B_apply_of_lt (i j : Fin N) (h : i.val + 1 < N) : B F i j = WF F (i.val + 1) (j.val + 1) := by
  rw [B_apply, dite_eq_left h]
  unfold WF gF
  simp

lemma B_apply_last (i j : Fin N) (h : ¬ i.val + 1 < N) : B F i j = gF F (j.val + 1) i.val := by
  rw [B_apply, dite_eq_right h, sub_zero]

/-- **阶梯基下的矩阵是 Metzler 的**（Proposition 1.11 证明的核心）。 -/
theorem B_metzler (hF : ∀ k, 1 ≤ k → F (k + 1) ≤ F k) (K₀ : ℕ) (hzero : ∀ k, K₀ < k → F k = 0) :
    Metzler (B F : Matrix (Fin N) (Fin N) ℝ) := by
  intro i j hij
  have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
  by_cases h : i.val + 1 < N
  · rw [B_apply_of_lt F i j h]
    exact WF_nonneg F hF K₀ hzero (i.val + 1) (j.val + 1) (by omega) (by omega) (by omega)
  · rw [B_apply_last F i j h]
    unfold gF
    have hj := j.isLt
    exact gF_nonneg_of_ge F hF K₀ hzero (j.val + 1) i.val (by omega)

/-- `e^{tO^{(N)}} = E e^{tB} D`。 -/
lemma exp_ON (t : ℝ) :
    exp (t • (ON F : Matrix (Fin N) (Fin N) ℝ)) = E * exp (t • B F) * D := by
  rw [ON_eq, ← E_inv]
  have e : t • ((E : Matrix (Fin N) (Fin N) ℝ) * B F * E⁻¹) = E * (t • B F) * E⁻¹ := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [e]
  exact Matrix.exp_conj _ _ isUnit_E

/-- **Proposition 1.11 的有限维部分**：`F` 非增、最终为零，`v ∈ C_N`、`t ≥ 0` ⇒
`e^{tO^{(N)}} v ∈ C_N`。 -/
theorem exp_ON_preserves_cone (hF : ∀ k, 1 ≤ k → F (k + 1) ≤ F k) (K₀ : ℕ)
    (hzero : ∀ k, K₀ < k → F k = 0)
    (v : Fin N → ℝ) (hv : InConeN v) (t : ℝ) (ht : 0 ≤ t) :
    InConeN ((exp (t • (ON F : Matrix (Fin N) (Fin N) ℝ))).mulVec v) := by
  rw [inConeN_iff] at hv ⊢
  intro i
  rw [exp_ON, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, D_mul_E,
    Matrix.one_mul, ← Matrix.mulVec_mulVec]
  have hexp := exp_smul_entryNonneg_of_metzler (B_metzler (N := N) F hF K₀ hzero) t ht
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (hexp i j) (hv j))

end Prop111

end Eliashberg
