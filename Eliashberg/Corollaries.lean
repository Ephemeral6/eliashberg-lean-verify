import Eliashberg.Lemma18

/-!
# §0.3–§1.2 的有限维推论：(S1)、Corollary 1.6、Lemma 0.3(1)、Corollary 1.10

这些是论文里 Lemma 1.4 / Lemma 1.8 的直接推论，全部在**有限截断**层面陈述
（矩阵元与有限和），不涉及 `ℓ²` 上的算子。这是论文自己的做法：(S1) "is stated — and is
used only — as an identity of finite compressions"，Corollary 1.6(1) 是 "a finite sum"，
Remark 1.7 强调 "The passage from Σ_{n,m} to Σ_{L,L'} must be made through the finite
truncation (0.4)"。

## 内容

* **(S1)**：`O[1]_{nm} = 2 u_n u_m - δ_{nm}`（`Of_one`）。
* **Lemma 0.3(1)，Abel 分解**：`(P_N v)_n = ∑_{L=1}^{N} a_L^{(N)} (e_L)_n`（`abel_decomp`），
  `v ∈ C` 时系数 `a_L ≥ 0`（`abel_coeff_nonneg`）。
* **Corollary 1.6(1)**：`f ≥ 0` 时 `Q_{LL'}(f) = ∑_{k<L+L'} f(k) Q_{LL'}(δ_k) ≥ 0`
  （`Qf_eq_sum`、`Qf_nonneg`）。这里 `f` 是任意函数：有限矩形上的和只涉及有限多个 `f(k)`，
  论文中的 `‖f‖_{ℓ¹} < ∞` 只是为了 `O[f]` 有界，有限层面不需要。
* **Corollary 1.6(2)–(3) 的有限版本**：`v` 非增非负、支撑在 `[0,N)` 内时
  `⟨v, O[f] v⟩ = ∑_{L,L'} a_L a_{L'} Q_{LL'}(f) ≥ 0`（`quad_form_eq`、`quad_form_nonneg`），
  且 `f(1) > 0`、`a_{L₀} > 0` 时 `⟨v, O[f] v⟩ ≥ a_{L₀}² f(1)`（`quad_form_lower`）。
  论文的 (2)–(3) 再由 `N → ∞` 的连续性过渡到 `ℓ²`，那一步属于第三层。
* **Corollary 1.10 的有限版本**：`F` 非增且在 `K₀` 之后为零时，
  `W_{L,L'}(F) ≥ 0`（`WF_nonneg`）。论文的一般情形（`F ∈ ℓ¹`，`F(k) → 0`）
  需要无穷 Abel 级数与 `O[·]` 的 `ℓ¹ → B(ℓ²)` 连续性，属于第三层。
-/

namespace Eliashberg

open scoped BigOperators

/-! ### 求和次序交换的两个小工具（避免 `rw [Finset.sum_comm]` 匹配到错误的一对） -/

lemma sum3_comm {α : Type*} [AddCommMonoid α] (s t r : Finset ℕ) (h : ℕ → ℕ → ℕ → α) :
    ∑ n ∈ s, ∑ m ∈ t, ∑ k ∈ r, h k n m = ∑ k ∈ r, ∑ n ∈ s, ∑ m ∈ t, h k n m :=
  calc ∑ n ∈ s, ∑ m ∈ t, ∑ k ∈ r, h k n m
      = ∑ n ∈ s, ∑ k ∈ r, ∑ m ∈ t, h k n m := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ k ∈ r, ∑ n ∈ s, ∑ m ∈ t, h k n m := Finset.sum_comm

lemma sum4_comm {α : Type*} [AddCommMonoid α] (s t : Finset ℕ) (A : ℕ → ℕ → ℕ → ℕ → α) :
    ∑ n ∈ s, ∑ m ∈ s, ∑ L ∈ t, ∑ Lp ∈ t, A n m L Lp
      = ∑ L ∈ t, ∑ Lp ∈ t, ∑ n ∈ s, ∑ m ∈ s, A n m L Lp :=
  calc ∑ n ∈ s, ∑ m ∈ s, ∑ L ∈ t, ∑ Lp ∈ t, A n m L Lp
      = ∑ n ∈ s, ∑ L ∈ t, ∑ m ∈ s, ∑ Lp ∈ t, A n m L Lp :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ n ∈ s, ∑ L ∈ t, ∑ Lp ∈ t, ∑ m ∈ s, A n m L Lp :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ L ∈ t, ∑ n ∈ s, ∑ Lp ∈ t, ∑ m ∈ s, A n m L Lp := Finset.sum_comm
    _ = ∑ L ∈ t, ∑ Lp ∈ t, ∑ n ∈ s, ∑ m ∈ s, A n m L Lp :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-! ### (S1) -/

/-- **(S1)**：`O[1]_{nm} = 2 u_n u_m - δ_{nm}`。对角上用 `-2n u_n² + u_n² = u_n²(1-2n) = 2u_n² - 1`。 -/
theorem Of_one (n m : ℕ) :
    Of (fun _ => (1:ℝ)) n m = 2 * u n * u m - (if n = m then 1 else 0) := by
  unfold Of
  simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
  by_cases h : n = m
  · subst h
    simp only [ite_true, ne_eq, not_true_eq_false, ite_false, add_zero]
    have := u_sq_mul n
    nlinarith [this]
  · simp only [h, ite_false, ne_eq, not_false_eq_true, ite_true, zero_add, sub_zero]
    ring

/-! ### Lemma 0.3(1)：Abel 分解 -/

/-- `e_L := 1_{[0,L)}` 的第 `n` 个分量。 -/
def e (L n : ℕ) : ℝ := if n < L then 1 else 0

/-- (0.4) 的系数：`a_L^{(N)} := v_{L-1} - v_L`（`1 ≤ L < N`），`a_N^{(N)} := v_{N-1}`。 -/
noncomputable def abelCoeff (v : ℕ → ℝ) (N L : ℕ) : ℝ :=
  if L < N then v (L - 1) - v L else v (L - 1)

/-- **Lemma 0.3(1)**：`n < N` 时 `v_n = ∑_{L=1}^{N} a_L^{(N)} (e_L)_n`。 -/
theorem abel_decomp (v : ℕ → ℝ) (N n : ℕ) (hn : n < N) :
    v n = ∑ L ∈ Finset.Icc 1 N, abelCoeff v N L * e L n := by
  -- 只有 `L > n` 的项非零；它们望远镜地求和成 `v_n`
  have hsplit : Finset.Icc 1 N = Finset.Icc 1 n ∪ Finset.Ico (n+1) (N+1) := by
    ext L; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ico]; omega
  have hdisj : Disjoint (Finset.Icc 1 n) (Finset.Ico (n+1) (N+1)) := by
    rw [Finset.disjoint_left]; intro L h1 h2
    simp only [Finset.mem_Icc, Finset.mem_Ico] at h1 h2; omega
  rw [hsplit, Finset.sum_union hdisj]
  have h0 : ∑ L ∈ Finset.Icc 1 n, abelCoeff v N L * e L n = 0 := by
    apply Finset.sum_eq_zero; intro L hL
    rw [Finset.mem_Icc] at hL
    unfold e; rw [ite_eq_right (by omega)]; ring
  rw [h0, zero_add]
  have h1 : ∀ L ∈ Finset.Ico (n+1) (N+1), abelCoeff v N L * e L n
      = (if L < N then v (L - 1) - v L else v (L - 1)) := by
    intro L hL
    rw [Finset.mem_Ico] at hL
    unfold e; rw [ite_eq_left (by omega), mul_one]; rfl
  rw [Finset.sum_congr rfl h1]
  -- 望远镜：`∑_{L=n+1}^{N} (v_{L-1} - v_L) + v_{N-1}`，其中末项 `L = N` 单独
  have hN : n + 1 ≤ N := hn
  rw [Finset.sum_Ico_succ_top hN]
  rw [ite_eq_right (lt_irrefl N)]
  have h2 : ∀ L ∈ Finset.Ico (n+1) N, (if L < N then v (L - 1) - v L else v (L - 1))
      = v (L - 1) - v L := by
    intro L hL; rw [Finset.mem_Ico] at hL; rw [ite_eq_left hL.2]
  rw [Finset.sum_congr rfl h2]
  rw [Finset.sum_Ico_eq_sum_range]
  have h3 : ∀ i, v (n + 1 + i - 1) - v (n + 1 + i) = v (n + i) - v (n + (i + 1)) := by
    intro i
    have e1 : n + 1 + i - 1 = n + i := by omega
    have e2 : n + 1 + i = n + (i + 1) := by omega
    rw [e1, e2]
  simp only [h3]
  rw [Finset.sum_range_sub' (fun i => v (n + i))]
  simp only [add_zero]
  have e4 : n + (N - (n + 1)) = N - 1 := by omega
  rw [e4]
  ring

/-- `v` 非增、非负 ⇒ 所有 Abel 系数非负。 -/
lemma abel_coeff_nonneg (v : ℕ → ℝ) (hv : Antitone v) (hpos : ∀ n, 0 ≤ v n) (N L : ℕ) :
    0 ≤ abelCoeff v N L := by
  unfold abelCoeff
  split_ifs
  · exact sub_nonneg.mpr (hv (Nat.sub_le L 1))
  · exact hpos _

/-! ### Corollary 1.6(1) -/

/-- `Q_{LL'}(f) := ∑_{n<L} ∑_{m<L'} O[f]_{nm}`。 -/
noncomputable def Qf (f : ℕ → ℝ) (L Lp : ℕ) : ℝ :=
  ∑ n ∈ Finset.range L, ∑ m ∈ Finset.range Lp, Of f n m

/-- `Q_{LL'}(δ_k) = Q2 k L L'`（`k ≥ 1`）。 -/
lemma Qf_delta (k L Lp : ℕ) (hk : 1 ≤ k) : Qf (delta k) L Lp = Q2 k L Lp := by
  unfold Qf Q2
  apply Finset.sum_congr rfl; intro n _
  apply Finset.sum_congr rfl; intro m _
  exact Of_delta k n m hk

/-- 在 `L × L'` 矩形内，`O[f]_{nm}` 只依赖 `f(1), …, f(L+L'-1)`：
把 `f` 写成 `∑_{k=1}^{L+L'-1} f(k) δ_k` 在该矩形上不改变矩阵元。 -/
lemma Of_truncate (f : ℕ → ℝ) (L Lp n m : ℕ) (hn : n < L) (hm : m < Lp) :
    Of f n m = Of (fun j => ∑ k ∈ Finset.Ico 1 (L + Lp), f k * delta k j) n m := by
  have hfj : ∀ j, 1 ≤ j → j < L + Lp → (∑ k ∈ Finset.Ico 1 (L + Lp), f k * delta k j) = f j := by
    intro j hj1 hj2
    unfold delta
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    rw [ite_eq_left (Finset.mem_Ico.mpr ⟨hj1, hj2⟩)]
  unfold Of
  beta_reduce
  have hsum : ∑ k ∈ Finset.Icc 1 n, (∑ k' ∈ Finset.Ico 1 (L + Lp), f k' * delta k' k)
      = ∑ k ∈ Finset.Icc 1 n, f k := by
    apply Finset.sum_congr rfl; intro k hk
    rw [Finset.mem_Icc] at hk
    exact hfj k hk.1 (by omega)
  rw [hsum, hfj (n + m + 1) (by omega) (by omega)]
  by_cases hne : n = m
  · simp [hne]
  · rw [hfj (Nat.dist n m) (by unfold Nat.dist; omega) (by unfold Nat.dist; omega)]

/-- `Of` 对 `f` 的标量倍数线性。 -/
lemma Of_smul (a : ℝ) (f : ℕ → ℝ) (n m : ℕ) : Of (fun j => a * f j) n m = a * Of f n m := by
  unfold Of
  rw [← Finset.mul_sum]
  split_ifs <;> ring

/-- **Corollary 1.6(1)，恒等式**：`Q_{LL'}(f) = ∑_{k=1}^{L+L'-1} f(k) Q_{LL'}(δ_k)`。
论文写 `∑_{k<L+L'}`；`k = 0` 项不出现在 (0.1) 中（`f` 定义在 `N = {1,2,…}` 上），
且 `L + L' ≤ k` 时 `Q_{LL'}(δ_k) = 0`（`Q2_eq_zero_of_le`），故求和上限取 `L+L'-1` 即可。 -/
theorem Qf_eq_sum (f : ℕ → ℝ) (L Lp : ℕ) :
    Qf f L Lp = ∑ k ∈ Finset.Ico 1 (L + Lp), f k * Q2 k L Lp := by
  unfold Qf
  have h1 : ∀ n ∈ Finset.range L, ∀ m ∈ Finset.range Lp,
      Of f n m = ∑ k ∈ Finset.Ico 1 (L + Lp), f k * Ok k n m := by
    intro n hn m hm
    rw [Finset.mem_range] at hn hm
    rw [Of_truncate f L Lp n m hn hm, Of_sum]
    apply Finset.sum_congr rfl; intro k hk
    rw [Finset.mem_Ico] at hk
    rw [Of_smul, Of_delta k n m hk.1]
  rw [Finset.sum_congr rfl (fun n hn => Finset.sum_congr rfl (fun m hm => h1 n hn m hm))]
  unfold Q2
  rw [sum3_comm]
  apply Finset.sum_congr rfl; intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro n _
  rw [Finset.mul_sum]

/-- **Corollary 1.6(1)，非负性**：`f ≥ 0` ⇒ `Q_{LL'}(f) ≥ 0`。 -/
theorem Qf_nonneg (f : ℕ → ℝ) (hf : ∀ k, 1 ≤ k → 0 ≤ f k) (L Lp : ℕ) : 0 ≤ Qf f L Lp := by
  rw [Qf_eq_sum]
  apply Finset.sum_nonneg; intro k hk
  rw [Finset.mem_Ico] at hk
  exact mul_nonneg (hf k hk.1) (Q2_nonneg k L Lp hk.1)

/-- `f(1) > 0`、`L ≥ 1` 时 `Q_{LL}(f) ≥ f(1) Q_{LL}(δ_1) ≥ f(1)`。 -/
theorem Qf_LL_lower (f : ℕ → ℝ) (hf : ∀ k, 1 ≤ k → 0 ≤ f k) (L : ℕ) (hL : 1 ≤ L) :
    f 1 ≤ Qf f L L := by
  rw [Qf_eq_sum]
  have hmem : 1 ∈ Finset.Ico 1 (L + L) := Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
  have h1 : f 1 * Q2 1 L L ≤ ∑ k ∈ Finset.Ico 1 (L + L), f k * Q2 k L L :=
    Finset.single_le_sum (fun k hk => mul_nonneg (hf k (Finset.mem_Ico.mp hk).1)
      (Q2_nonneg k L L (Finset.mem_Ico.mp hk).1)) hmem
  have h2 : f 1 ≤ f 1 * Q2 1 L L := le_mul_of_one_le_right (hf 1 le_rfl) (Q2_LL_one L hL)
  linarith

/-! ### Corollary 1.6(2)–(3) 的有限版本：二次型 -/

/-- 有限二次型 `⟨P_N v, O[f] P_N v⟩ = ∑_{n<N} ∑_{m<N} v_n O[f]_{nm} v_m`。 -/
noncomputable def quadForm (f : ℕ → ℝ) (v : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, v n * Of f n m * v m

/-- `∑_{n<N} e_L(n) φ(n) = ∑_{n<L} φ(n)`（`L ≤ N`）。 -/
lemma sum_e_mul (L N : ℕ) (hL : L ≤ N) (φ : ℕ → ℝ) :
    ∑ n ∈ Finset.range N, e L n * φ n = ∑ n ∈ Finset.range L, φ n := by
  unfold e
  simp only [ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  congr 1
  ext n; simp only [Finset.mem_filter, Finset.mem_range]; omega

/-- **二次型的 Abel 展开**（论文 Corollary 1.6 证明中的第一行）：
`⟨P_N v, O[f] P_N v⟩ = ∑_{L,L'=1}^{N} a_L a_{L'} Q_{LL'}(f)`。 -/
theorem quad_form_eq (f : ℕ → ℝ) (v : ℕ → ℝ) (N : ℕ) :
    quadForm f v N
      = ∑ L ∈ Finset.Icc 1 N, ∑ Lp ∈ Finset.Icc 1 N,
          abelCoeff v N L * abelCoeff v N Lp * Qf f L Lp := by
  unfold quadForm
  have hv : ∀ n ∈ Finset.range N, v n = ∑ L ∈ Finset.Icc 1 N, abelCoeff v N L * e L n := by
    intro n hn; rw [Finset.mem_range] at hn; exact abel_decomp v N n hn
  calc ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, v n * Of f n m * v m
      = ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
          (∑ L ∈ Finset.Icc 1 N, abelCoeff v N L * e L n) * Of f n m
            * (∑ Lp ∈ Finset.Icc 1 N, abelCoeff v N Lp * e Lp m) := by
        apply Finset.sum_congr rfl; intro n hn
        apply Finset.sum_congr rfl; intro m hm
        rw [← hv n hn, ← hv m hm]
    _ = ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, ∑ L ∈ Finset.Icc 1 N, ∑ Lp ∈ Finset.Icc 1 N,
          abelCoeff v N L * abelCoeff v N Lp * (e L n * Of f n m * e Lp m) := by
        apply Finset.sum_congr rfl; intro n _
        apply Finset.sum_congr rfl; intro m _
        rw [Finset.sum_mul, Finset.sum_mul]
        apply Finset.sum_congr rfl; intro L _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro Lp _
        ring
    _ = ∑ L ∈ Finset.Icc 1 N, ∑ Lp ∈ Finset.Icc 1 N, ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
          abelCoeff v N L * abelCoeff v N Lp * (e L n * Of f n m * e Lp m) := by
        exact sum4_comm (Finset.range N) (Finset.Icc 1 N)
          (fun n m L Lp => abelCoeff v N L * abelCoeff v N Lp * (e L n * Of f n m * e Lp m))
    _ = ∑ L ∈ Finset.Icc 1 N, ∑ Lp ∈ Finset.Icc 1 N,
          abelCoeff v N L * abelCoeff v N Lp * Qf f L Lp := by
        apply Finset.sum_congr rfl; intro L hL
        apply Finset.sum_congr rfl; intro Lp hLp
        rw [Finset.mem_Icc] at hL hLp
        simp only [← Finset.mul_sum]
        congr 1
        unfold Qf
        rw [← sum_e_mul L N hL.2]
        apply Finset.sum_congr rfl; intro n _
        rw [← sum_e_mul Lp N hLp.2 (fun m => Of f n m)]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro m _
        ring

/-- **Corollary 1.6(2) 的有限版本**：`v` 非增非负、`f ≥ 0` ⇒ `⟨P_N v, O[f] P_N v⟩ ≥ 0`。 -/
theorem quad_form_nonneg (f : ℕ → ℝ) (hf : ∀ k, 1 ≤ k → 0 ≤ f k) (v : ℕ → ℝ) (hv : Antitone v)
    (hpos : ∀ n, 0 ≤ v n) (N : ℕ) : 0 ≤ quadForm f v N := by
  rw [quad_form_eq]
  apply Finset.sum_nonneg; intro L _
  apply Finset.sum_nonneg; intro Lp _
  exact mul_nonneg (mul_nonneg (abel_coeff_nonneg v hv hpos N L) (abel_coeff_nonneg v hv hpos N Lp))
    (Qf_nonneg f hf L Lp)

/-- **Corollary 1.6(3) 的有限版本**：此外若 `1 ≤ L₀ ≤ N`，则
`⟨P_N v, O[f] P_N v⟩ ≥ a_{L₀}² Q_{L₀L₀}(f) ≥ a_{L₀}² f(1)`。 -/
theorem quad_form_lower (f : ℕ → ℝ) (hf : ∀ k, 1 ≤ k → 0 ≤ f k) (v : ℕ → ℝ) (hv : Antitone v)
    (hpos : ∀ n, 0 ≤ v n) (N L₀ : ℕ) (hL₀ : 1 ≤ L₀) (hL₀N : L₀ ≤ N) :
    abelCoeff v N L₀ ^ 2 * f 1 ≤ quadForm f v N := by
  rw [quad_form_eq]
  have hmem : L₀ ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨hL₀, hL₀N⟩
  have hterm : ∀ L ∈ Finset.Icc 1 N, 0 ≤ ∑ Lp ∈ Finset.Icc 1 N,
      abelCoeff v N L * abelCoeff v N Lp * Qf f L Lp := by
    intro L _
    apply Finset.sum_nonneg; intro Lp _
    exact mul_nonneg (mul_nonneg (abel_coeff_nonneg v hv hpos N L)
      (abel_coeff_nonneg v hv hpos N Lp)) (Qf_nonneg f hf L Lp)
  have h1 := Finset.single_le_sum hterm hmem
  have hinner : ∀ Lp ∈ Finset.Icc 1 N, 0 ≤ abelCoeff v N L₀ * abelCoeff v N Lp * Qf f L₀ Lp := by
    intro Lp _
    exact mul_nonneg (mul_nonneg (abel_coeff_nonneg v hv hpos N L₀)
      (abel_coeff_nonneg v hv hpos N Lp)) (Qf_nonneg f hf L₀ Lp)
  have h2 := Finset.single_le_sum hinner hmem
  have h3 : abelCoeff v N L₀ ^ 2 * f 1 ≤ abelCoeff v N L₀ * abelCoeff v N L₀ * Qf f L₀ L₀ := by
    rw [sq]
    apply mul_le_mul_of_nonneg_left (Qf_LL_lower f hf L₀ hL₀)
    exact mul_nonneg (abel_coeff_nonneg v hv hpos N L₀) (abel_coeff_nonneg v hv hpos N L₀)
  linarith

/-! ### Corollary 1.10 的有限版本 -/

/-- 阶梯核 `F` 的非对角系数 `W_{L,L'}(F) := (O[F] e_{L'})_{L-1} - (O[F] e_{L'})_L`。 -/
noncomputable def WF (F : ℕ → ℝ) (L Lp : ℕ) : ℝ :=
  (∑ m ∈ Finset.range Lp, Of F (L - 1) m) - ∑ m ∈ Finset.range Lp, Of F L m

/-- Lemma 0.3(4) 的有限版本：`F` 在 `K₀` 之后为零时，`F(j) = ∑_{K=1}^{K₀} (F(K) - F(K+1)) 1_{j≤K}`
对 `j ≥ 1` 成立。 -/
lemma abel_step (F : ℕ → ℝ) (K₀ : ℕ) (hF : ∀ k, K₀ < k → F k = 0) (j : ℕ) (hj : 1 ≤ j) :
    F j = ∑ K ∈ Finset.Icc 1 K₀, (F K - F (K + 1)) * step K j := by
  unfold step
  simp only [mul_ite, mul_one, mul_zero]
  -- 只有 `K ≥ j` 的项非零
  have hfilt : ∑ K ∈ Finset.Icc 1 K₀, (if 1 ≤ j ∧ j ≤ K then F K - F (K + 1) else 0)
      = ∑ K ∈ Finset.Ico j (K₀ + 1), (F K - F (K + 1)) := by
    rw [← Finset.sum_filter]
    congr 1
    ext K; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hfilt]
  by_cases hjK : j ≤ K₀
  · rw [Finset.sum_Ico_eq_sum_range]
    have h3 : ∀ i, F (j + i) - F (j + i + 1) = F (j + i) - F (j + (i + 1)) := by
      intro i; rw [add_assoc]
    simp only [h3]
    rw [Finset.sum_range_sub' (fun i => F (j + i))]
    simp only [add_zero]
    have e : j + (K₀ + 1 - j) = K₀ + 1 := by omega
    rw [e, hF (K₀ + 1) (Nat.lt_succ_self K₀), sub_zero]
  · rw [Finset.Ico_eq_empty_of_le (by omega), Finset.sum_empty]
    exact hF j (by omega)

/-- **`O[F]` 的逐矩阵元 Abel 展开**（Corollary 1.10 证明的核心）：`F` 在 `K₀` 之后为零时
`O[F]_{nm} = ∑_{K=1}^{K₀} (F(K) − F(K+1)) M^{(K)}_{nm}`。 -/
lemma Of_abel (F : ℕ → ℝ) (K₀ : ℕ) (hzero : ∀ k, K₀ < k → F k = 0) (n m : ℕ) :
    Of F n m = ∑ K ∈ Finset.Icc 1 K₀, (F K - F (K + 1)) * Mk K n m := by
  have hFeq : ∀ j, 1 ≤ j → F j = ∑ K ∈ Finset.Icc 1 K₀, (F K - F (K + 1)) * step K j :=
    abel_step F K₀ hzero
  -- 在 `Of` 中出现的 `F` 的自变量全 `≥ 1`
  unfold Of
  have hsum : ∑ k ∈ Finset.Icc 1 n, F k
      = ∑ k ∈ Finset.Icc 1 n, ∑ K ∈ Finset.Icc 1 K₀, (F K - F (K + 1)) * step K k := by
    apply Finset.sum_congr rfl; intro k hk
    rw [Finset.mem_Icc] at hk; exact hFeq k hk.1
  have h3 : F (n + m + 1) = ∑ K ∈ Finset.Icc 1 K₀, (F K - F (K + 1)) * step K (n + m + 1) :=
    hFeq _ (by omega)
  rw [hsum, h3]
  unfold Mk
  by_cases hnm : n = m
  · subst hnm
    simp only [ite_true, ne_eq, not_true_eq_false, ite_false, add_zero]
    rw [Finset.sum_comm, Finset.mul_sum, ← Finset.sum_neg_distrib, Finset.sum_mul,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro K _
    rw [← Finset.mul_sum, sum_step]
    have hd : Nat.dist n n = 0 := Nat.dist_self n
    have e0 : ¬ (1 ≤ 0 ∧ 0 ≤ K) := by omega
    unfold step
    have e : (1 ≤ n + n + 1 ∧ n + n + 1 ≤ K) ↔ (n + n + 1 ≤ K) := by omega
    simp only [hd, e0, e, ite_false, zero_add]
    split_ifs <;> ring
  · have hne' : n ≠ m := hnm
    simp only [hnm, ite_false, ne_eq, not_false_eq_true, ite_true, zero_add, sub_zero]
    rw [hFeq (Nat.dist n m) (by unfold Nat.dist; omega)]
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro K _
    unfold step
    have e1 : (1 ≤ n + m + 1 ∧ n + m + 1 ≤ K) ↔ (n + m + 1 ≤ K) := by omega
    simp only [e1]
    split_ifs <;> ring

/-- **Corollary 1.10 的有限版本**：`F` 在 `k ≥ 1` 上非增、在 `K₀` 之后为零，则 `L ≠ L'`（`≥ 1`）时
`W_{L,L'}(F) ≥ 0`。证明：`O[F] = ∑_K a_K O[1_{k≤K}]`（`a_K ≥ 0`）逐矩阵元成立（`Of_abel`），
再对每个 `K` 用 Lemma 1.8。

论文另设 `F ≥ 0`；这里不需要，因为非增且最终为零已蕴含非负。单调性只要求在 `k ≥ 1` 上成立，
因为 (0.1) 从不取 `F(0)`。 -/
theorem WF_nonneg (F : ℕ → ℝ) (hF : ∀ k, 1 ≤ k → F (k + 1) ≤ F k) (K₀ : ℕ)
    (hzero : ∀ k, K₀ < k → F k = 0) (L Lp : ℕ) (hL : 1 ≤ L) (hLp : 1 ≤ Lp) (hne : L ≠ Lp) :
    0 ≤ WF F L Lp := by
  unfold WF
  simp only [Of_abel F K₀ hzero]
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.range Lp), ← Finset.sum_sub_distrib]
  apply Finset.sum_nonneg; intro K hK
  rw [Finset.mem_Icc] at hK
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_sub]
  apply mul_nonneg
  · exact sub_nonneg.mpr (hF K hK.1)
  · have := W_nonneg K L Lp hL hLp hne
    unfold W g at this
    exact this

/-- **Corollary 1.10 末句的有限版本**：`(O[F] e_{L'})_n ≥ 0`，`n ≥ L'`。 -/
theorem gF_nonneg_of_ge (F : ℕ → ℝ) (hF : ∀ k, 1 ≤ k → F (k + 1) ≤ F k) (K₀ : ℕ)
    (hzero : ∀ k, K₀ < k → F k = 0) (Lp n : ℕ) (h : Lp ≤ n) :
    0 ≤ ∑ m ∈ Finset.range Lp, Of F n m := by
  simp only [Of_abel F K₀ hzero]
  rw [Finset.sum_comm]
  apply Finset.sum_nonneg; intro K hK
  rw [Finset.mem_Icc] at hK
  rw [← Finset.mul_sum]
  apply mul_nonneg
  · exact sub_nonneg.mpr (hF K hK.1)
  · have := Mk_row_nonneg K Lp n h
    unfold g at this
    exact this

end Eliashberg
