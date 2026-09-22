import Eliashberg.MainB

/-!
# §3：`H` 的凹性猜想，以及其中真正是定理的部分

论文 §3 把 `H(x) := h(√x)` 的严格凹性列为 **Conjecture 3.1**（明确不是定理），
并按三个严格性层级说明现状。其中**第一层是定理，而且是一条否定性定理**（Remark 1.16(b)）：
「`λ₁` 在核上凸、核 `x ↦ x/(k²+x)` 在 `x` 上凹，两个效应反向，所以任何只看 (1.7) 变分包络的论证
都不能定出 `H` 的凹性」。本文件形式化这一层，外加 `H` 已证的全部性质。

**猜想本身不予证明**（论文自己不证），也不作为公理引入。本文件给出的是：
猜想的精确陈述 `ConjectureThreeOne`、它与已证 Lemma 2.2 的**单向**关系、以及反向不成立的显式反例。

| 定理 | 内容 |
|---|---|
| `HH`、`HH_eq_lam1` | `H(x) = λ₁(O[k ↦ x/(k²+x)])`，`x > 0` |
| `HH_div_eq_rr`、`HH_eq` | `H(x)/x = r(√x)`、`H(x) = x·r(√x)` |
| `HH_strictMonoOn` | `H` 在 `(0,∞)` 严格递增（Cor 2.4(i)） |
| `HH_div_strictAnti`、`HH_lt`、`HH_div_tendsto` | **Lemma 2.2 的 `H` 形式**：`H(x)/x` 严格递减、`H(x) < g(2)x`、`H(x)/x → g(2)`（`x ↓ 0`） |
| `kernel_strictConcaveOn` | 核 `x ↦ x/(k²+x)` 在 `[0,∞)` 严格凹 |
| `lam1_convexOn_pair` | `F ↦ λ₁(O[F])` 沿线段凸（即 (1.7) 的凸包络，`lam1_convex` 的重述） |
| **`div_antitone_of_concaveOn`** | **凹 ⇒ `H(x)/x` 递减**：猜想蕴含 Lemma 2.2，方向一致 |
| **`not_concaveOn_of_div_strictAnti`** | **反向不成立**：`x/(1+x²)` 的商严格递减但函数不凹 ⇒ Lemma 2.2 推不出猜想 |
| **`comp_convex_concave_no_sign`** | **Remark 1.16(b) 的结构障碍**：单调凸 ∘ 凹 的凹性无定号（两个显式实例） |

**未做**：猜想本身；论文 §3 的 `H′ = E − |C|` 分解与 `ϖ ∈ (0,45]` 的区间算术证书
（论文把剩余范围明确标为「numerical evidence only」，不是定理）。
-/

namespace Eliashberg

open Filter Topology

noncomputable section

/-! ### 一、`H(x) := h(√x)` 及其已证性质 -/

/-- `H(x) := h(√x)`（论文 §3 开头）。 -/
def HH (x : ℝ) : ℝ := hh (Real.sqrt x)

/-- `x > 0`：`H(x) = λ₁(O[k ↦ x/(k²+x)])`。 -/
theorem HH_eq_lam1 (x : ℝ) (hx : 0 < x) :
    HH x = lam1 (fun k : ℕ => x / ((k:ℝ) ^ 2 + x)) := by
  unfold HH hh
  congr 1
  funext k
  unfold kern
  rw [Real.sq_sqrt (le_of_lt hx)]

/-- `H(x) = x · r(√x)`。 -/
theorem HH_eq (x : ℝ) (hx : 0 < x) : HH x = x * rr (Real.sqrt x) := by
  unfold HH
  rw [lemma_2_2_h_eq _ (ne_of_gt (Real.sqrt_pos.mpr hx)), Real.sq_sqrt (le_of_lt hx)]

/-- `H(x)/x = r(√x)`。 -/
theorem HH_div_eq_rr (x : ℝ) (hx : 0 < x) : HH x / x = rr (Real.sqrt x) := by
  rw [HH_eq x hx, mul_comm, mul_div_assoc, div_self (ne_of_gt hx), mul_one]

/-- **Cor 2.4(i) 的 `H` 形式**：`H` 在 `(0,∞)` 严格递增。 -/
theorem HH_strictMonoOn : StrictMonoOn HH (Set.Ioi 0) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ioi] at hx hy
  exact corollary_2_4_i _ _ (Real.sqrt_pos.mpr hx)
    (Real.sqrt_lt_sqrt (le_of_lt hx) hxy)

/-- **Lemma 2.2 的 `H` 形式**：`H(x)/x` 在 `(0,∞)` 严格递减。 -/
theorem HH_div_strictAnti (x y : ℝ) (hx : 0 < x) (hxy : x < y) : HH y / y < HH x / x := by
  have hy : 0 < y := lt_trans hx hxy
  rw [HH_div_eq_rr x hx, HH_div_eq_rr y hy]
  exact lemma_2_2_r_strictAnti _ _ (Real.sqrt_pos.mpr hx) (Real.sqrt_lt_sqrt (le_of_lt hx) hxy)

/-- **Lemma 2.2 的 `H` 形式**：`H(x) < g(2)·x`。 -/
theorem HH_lt (x : ℝ) (hx : 0 < x) : HH x < g2 * x := by
  unfold HH
  have h := lemma_2_2_h_lt (Real.sqrt x) (Real.sqrt_pos.mpr hx)
  rwa [Real.sq_sqrt (le_of_lt hx)] at h

/-- `√·` 把 `0⁺` 送到 `0⁺`。 -/
lemma sqrt_tendsto_nhdsGT : Tendsto Real.sqrt (𝓝[>] 0) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · have h : Tendsto Real.sqrt (𝓝 0) (𝓝 (Real.sqrt 0)) :=
      Real.continuous_sqrt.tendsto 0
    rw [Real.sqrt_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact Real.sqrt_pos.mpr hx

/-- **Lemma 2.2 的 `H` 形式**：`H(x)/x → g(2)`（`x ↓ 0`）。 -/
theorem HH_div_tendsto : Tendsto (fun x => HH x / x) (𝓝[>] 0) (𝓝 g2) := by
  have h : Tendsto (fun x => rr (Real.sqrt x)) (𝓝[>] 0) (𝓝 g2) :=
    lemma_2_2_r_tendsto.comp sqrt_tendsto_nhdsGT
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (HH_div_eq_rr x hx).symm

/-! ### 二、Conjecture 3.1 的陈述 -/

/-- **Conjecture 3.1**：`H` 在 `(0,∞)` 严格凹。**本库不证明、也不假设它。** -/
def ConjectureThreeOne : Prop := StrictConcaveOn ℝ (Set.Ioi 0) HH

/-! ### 三、Remark 1.16(b)：两个反向的效应 -/

/-- 核 `x ↦ x/(k²+x)` 在 `[0,∞)` **严格凹**（`k ≥ 1`）。 -/
theorem kernel_strictConcaveOn (k : ℕ) (hk : 1 ≤ k) :
    StrictConcaveOn ℝ (Set.Ici 0) (fun x : ℝ => x / ((k:ℝ) ^ 2 + x)) := by
  have hk2 : (0:ℝ) < (k:ℝ) ^ 2 := by
    have : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    positivity
  obtain ⟨hconv, hstr⟩ := chi_strictConcaveOn ((k:ℝ) ^ 2) hk2
  refine ⟨hconv, ?_⟩
  intro x hx z hz hxz a b ha hb hab
  simp only [Set.mem_Ici] at hx hz
  have hmem : (0:ℝ) ≤ a • x + b • z := by
    simp only [smul_eq_mul]
    have := mul_nonneg (le_of_lt ha) hx
    have := mul_nonneg (le_of_lt hb) hz
    linarith
  have h := hstr hx hz hxz ha hb hab
  rwa [chi_eq _ x hk2 hx, chi_eq _ z hk2 hz, chi_eq _ _ hk2 hmem] at h

/-- `F ↦ λ₁(O[F])` 沿线段凸（(1.7) 的凸包络；`lam1_convex` 的重述）。 -/
theorem lam1_convexOn_pair {F G : ℕ → ℝ} (hF : L1 F) (hG : L1 G) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    lam1 (fun k => a * F k + b * G k) ≤ a * lam1 F + b * lam1 G :=
  lam1_convex hF hG a b ha hb

/-! ### 四、猜想与 Lemma 2.2 的关系：单向蕴含，反向不成立 -/

/-- **凹 ⇒ 商递减**：若 `H` 在 `[0,∞)` 凹且 `H(0) ≥ 0`，则 `x ↦ H(x)/x` 在 `(0,∞)` 递减。

这说明 Conjecture 3.1 与已证的 Lemma 2.2 方向一致：猜想（加端点非负）蕴含 Lemma 2.2。
证明只用 `x = (x/y)·y + (1−x/y)·0`。 -/
theorem div_antitone_of_concaveOn {H : ℝ → ℝ} (hcon : ConcaveOn ℝ (Set.Ici 0) H)
    (h0 : 0 ≤ H 0) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : H y / y ≤ H x / x := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  set t : ℝ := x / y with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hy]; exact hxy
  have hcomb : t • y + (1 - t) • (0:ℝ) = x := by
    simp only [smul_eq_mul, mul_zero, add_zero, ht]
    field_simp
  have h := hcon.2 (Set.mem_Ici.mpr (le_of_lt hy)) (Set.mem_Ici.mpr le_rfl) ht0
    (by linarith : (0:ℝ) ≤ 1 - t) (by ring)
  rw [hcomb] at h
  simp only [smul_eq_mul] at h
  have h1 : t * H y ≤ H x := by nlinarith
  rw [div_le_div_iff₀ hy hx]
  rw [ht, div_mul_eq_mul_div, div_le_iff₀ hy] at h1
  nlinarith

/-! #### 反向不成立：`x/(1+x²)` -/

/-- 反例函数 `G(x) := x/(1+x²)`。 -/
def Gex (x : ℝ) : ℝ := x / (1 + x ^ 2)

/-- `G(x)/x = 1/(1+x²)` 在 `(0,∞)` 严格递减（和 Lemma 2.2 同形）。 -/
theorem Gex_div_strictAnti (x y : ℝ) (hx : 0 < x) (hxy : x < y) : Gex y / y < Gex x / x := by
  have hy : 0 < y := lt_trans hx hxy
  have e : ∀ z : ℝ, 0 < z → Gex z / z = 1 / (1 + z ^ 2) := by
    intro z hz
    unfold Gex
    rw [div_div, div_eq_div_iff (by positivity) (by positivity)]
    ring
  rw [e x hx, e y hy, div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- `G` 在 `(0,∞)` **不**凹（中点检验：`G(3) = 3/10 < 27/85 = (G(2)+G(4))/2`）。 -/
theorem Gex_not_concaveOn : ¬ ConcaveOn ℝ (Set.Ioi 0) Gex := by
  intro h
  have h2 : (2:ℝ) ∈ Set.Ioi (0:ℝ) := by norm_num
  have h4 : (4:ℝ) ∈ Set.Ioi (0:ℝ) := by norm_num
  have hc := h.2 h2 h4 (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  simp only [smul_eq_mul, Gex] at hc
  norm_num at hc

/-- **Lemma 2.2 推不出 Conjecture 3.1**：存在函数其商严格递减却不凹。 -/
theorem not_concaveOn_of_div_strictAnti :
    ∃ G : ℝ → ℝ, (∀ x y : ℝ, 0 < x → x < y → G y / y < G x / x) ∧
      ¬ ConcaveOn ℝ (Set.Ioi 0) G :=
  ⟨Gex, Gex_div_strictAnti, Gex_not_concaveOn⟩

/-! #### Remark 1.16(b) 的结构障碍：单调凸 ∘ 凹 无定号 -/

/-- `x ↦ (√x)⁴ = x²` 在 `[0,∞)` 不凹（中点检验：`4 < 5`）。 -/
lemma sq_not_concaveOn : ¬ ConcaveOn ℝ (Set.Ici 0) (fun x : ℝ => x ^ 2) := by
  intro h
  have h1 : (1:ℝ) ∈ Set.Ici (0:ℝ) := by norm_num
  have h3 : (3:ℝ) ∈ Set.Ici (0:ℝ) := by norm_num
  have hc := h.2 h1 h3 (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  simp only [smul_eq_mul] at hc
  norm_num at hc

/-- **Remark 1.16(b)**：「单调不减的凸函数 ∘ 凹映射」的凹性**无定号**——
两个实例，一个得到凹（`g = id`），一个得到不凹（`g = (·)⁴`，`φ = √·`，复合为 `x²`）。

这正是论文所说的结构障碍：只凭「`λ₁` 凸且序保持」＋「核在 `x` 上凹」推不出 `H` 的凹性，
无论哪个方向。 -/
theorem comp_convex_concave_no_sign :
    (∃ g φ : ℝ → ℝ, ConvexOn ℝ (Set.Ici 0) g ∧ MonotoneOn g (Set.Ici 0) ∧
        ConcaveOn ℝ (Set.Ici 0) φ ∧ Set.MapsTo φ (Set.Ici 0) (Set.Ici 0) ∧
        ¬ ConcaveOn ℝ (Set.Ici 0) (g ∘ φ)) ∧
      (∃ g φ : ℝ → ℝ, ConvexOn ℝ (Set.Ici 0) g ∧ MonotoneOn g (Set.Ici 0) ∧
        ConcaveOn ℝ (Set.Ici 0) φ ∧ Set.MapsTo φ (Set.Ici 0) (Set.Ici 0) ∧
        ConcaveOn ℝ (Set.Ici 0) (g ∘ φ)) := by
  constructor
  · refine ⟨fun t => t ^ 4, Real.sqrt, convexOn_pow 4, ?_,
      Real.strictConcaveOn_sqrt.concaveOn, ?_, ?_⟩
    · intro s hs t ht hst
      simp only [Set.mem_Ici] at hs
      exact pow_le_pow_left₀ hs hst 4
    · intro x _
      exact Set.mem_Ici.mpr (Real.sqrt_nonneg x)
    · intro h
      apply sq_not_concaveOn
      apply h.congr
      intro x hx
      simp only [Set.mem_Ici] at hx
      simp only [Function.comp_apply]
      rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hx]
  · refine ⟨id, Real.sqrt, (convexOn_pow 1).congr (fun x _ => by simp), ?_,
      Real.strictConcaveOn_sqrt.concaveOn, ?_, ?_⟩
    · exact fun s _ t _ hst => hst
    · intro x _
      exact Set.mem_Ici.mpr (Real.sqrt_nonneg x)
    · exact Real.strictConcaveOn_sqrt.concaveOn.congr (fun x _ => rfl)

end

end Eliashberg
