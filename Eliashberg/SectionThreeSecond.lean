import Eliashberg.SectionThree

/-!
# §3 补篇：二阶结构 —— 为什么凹性不能从变分包络得到

论文 §3 把 `H(x) := h(√x)` 的严格凹性列为 **Conjecture 3.1**，并分四个严格性层级。
第二层（「Analytic, partial」）说：

> A decomposition `H′(x) = E(x) − |C(x)|` into an explicitly positive principal term `E`
> and a commutator remainder `C`, with `E > 0` and `C ≤ 0`, is available in closed form;
> the reduction of Conjecture 3.1 to the single inequality `|C| < E` is analytic.

**论文全文没有印出 `E`、`C` 的公式**（只在 §3 这一句里出现）。所以这一层无法按论文原文核验，
本文件不猜它们的形式。可形式化的是**这条分解为什么必需**：第一层那条否定性结论的二阶版本。

## 本文件的内容

1. **核的二阶差分封闭形式**（`kernel_second_diff`）：`x ↦ x/(m+x)` 的二阶差分恰为
   `−2 m s²/((m+x−s)(m+x)(m+x+s))`。这是库里 `kernel_strictConcaveOn` 的定量版本，
   也是论文说核 `x ↦ x/(k²+x)` 严格凹的全部来源。

2. **凹性的来源只有 kernel 项**（`kernel_second_diff_neg`）：`m > 0`、`s ≠ 0`、
   `m+x±s > 0` 时该式严格为负，且与 `x` 无关。

3. **单调凸 ∘ 凹 在二阶上无定号**。`g(s) = s²` 在 `[0,∞)` 上凸且递增，
   `f(t) = t/(1+t)` 在 `[0,∞)` 上严格凹，而 `g ∘ f = (t/(1+t))²` 的二阶差分
   **在 `t = 1/10` 处严格为正、在 `t = 1` 处严格为负**（`comp_sq_div_second_diff_pos`、
   `comp_sq_div_second_diff_neg`）。三个断言都是精确有理数，`norm_num` 直接核。

   含义：`λ₁` 在核上凸且保序（(1.7)），kernel 在 `x` 上凹，而这个复合既不必凹也不必凸。
   这正是论文「两个效应反向、任何只用变分包络的论证都定不出 `H` 的二阶性态」的精确形式。

4. **二阶差分判据**（`concave_of_second_diff_nonpos`）：相邻斜率形式下的凹性判据，
   即论文所说「归约到单个不等式」的**形式**（具体的不等式内容本文件不涉及）。

**未做**：`E`、`C` 的具体形式（论文未印）；`ϖ ∈ (0,45]` 的区间算术证书；剩余范围的数值证据。
-/

namespace Eliashberg

open Filter Topology

noncomputable section

/-! ### 一、核的二阶差分封闭形式 -/

/-- **核的二阶差分**：`x ↦ x/(m+x)` 的对称二阶差分恰为 `−2 m s²/((m+x−s)(m+x)(m+x+s))`。 -/
theorem kernel_second_diff {m x s : ℝ} (h1 : m + x - s ≠ 0) (h2 : m + x ≠ 0)
    (h3 : m + x + s ≠ 0) :
    (x+s)/(m+(x+s)) + (x-s)/(m+(x-s)) - 2*(x/(m+x))
      = -2*m*s^2/((m+x-s)*(m+x)*(m+x+s)) := by
  have e1 : m + (x+s) = m+x+s := by ring
  have e2 : m + (x-s) = m+x-s := by ring
  rw [e1, e2]
  field_simp
  ring

/-- `m > 0`、`s ≠ 0`、`m+x±s > 0` ⇒ 核的二阶差分**严格为负**（与 `x` 无关）。 -/
theorem kernel_second_diff_neg {m x s : ℝ} (hm : 0 < m) (hs : s ≠ 0)
    (h1 : 0 < m + x - s) (h2 : 0 < m + x) (h3 : 0 < m + x + s) :
    (x+s)/(m+(x+s)) + (x-s)/(m+(x-s)) - 2*(x/(m+x)) < 0 := by
  rw [kernel_second_diff (ne_of_gt h1) (ne_of_gt h2) (ne_of_gt h3)]
  have hs2 : 0 < s^2 := by positivity
  have hden : 0 < (m+x-s)*(m+x)*(m+x+s) := by positivity
  have hnum : 0 < 2*m*s^2 := by positivity
  exact div_neg_of_neg_of_pos (by linarith) hden

/-! ### 二、二阶差分判据 -/

/-- 相邻斜率递减 ⇒ 凹（`ConcaveOn` 的斜率形式）。论文「归约到单个不等式」的形式。 -/
theorem concave_of_second_diff_nonpos {f : ℝ → ℝ}
    (h : ∀ x y z : ℝ, 0 < x → x < y → y < z →
      (f z - f y) / (z - y) ≤ (f y - f x) / (y - x)) :
    ConcaveOn ℝ (Set.Ioi 0) f := by
  rw [concaveOn_iff_slope_anti_adjacent]
  refine ⟨convex_Ioi 0, ?_⟩
  intro x y z hx hz hxy hyz
  simp only [Set.mem_Ioi] at hx hz
  exact h x y z hx hxy hyz

/-! ### 三、单调凸 ∘ 凹：二阶无定号

取 `g(s) = s²`（`[0,∞)` 上凸且递增）、`f(t) = t/(1+t)`（`[0,∞)` 上严格凹）。
复合是 `t ↦ (t/(1+t))²`。下面两个定理给出它在两个点的二阶差分（步长 `1/1000`），
一正一负，都是精确有理数。 -/

/-- `f(t) = t/(1+t)` 在 `t = 1` 处的二阶差分严格为负（`f` 严格凹）。
（注意分母里的 `1/1000` 必须写成 `(1:ℝ)/1000`：`1/1000` 会被解析成 `ℕ` 除法并截断为 `0`。） -/
theorem div_second_diff_neg :
    ((1:ℝ) + 1/1000)/(1 + (1 + 1/1000)) + (1 - 1/1000)/(1 + (1 - 1/1000))
      - 2*((1:ℝ)/(1+1)) < 0 := by
  norm_num

/-- 复合 `(t/(1+t))²` 在 `t = 1/10` 处二阶差分**严格为正**（复合不凹）。 -/
theorem comp_sq_div_second_diff_pos :
    (((1:ℝ)/10 + 1/1000)/(1 + ((1:ℝ)/10 + 1/1000)))^2
      + (((1:ℝ)/10 - 1/1000)/(1 + ((1:ℝ)/10 - 1/1000)))^2
      - 2*(((1:ℝ)/10)/(1 + (1:ℝ)/10))^2 > 0 := by
  norm_num

/-- 同一复合在 `t = 1` 处二阶差分**严格为负**（复合在该点凹）。 -/
theorem comp_sq_div_second_diff_neg :
    (((1:ℝ) + 1/1000)/(1 + ((1:ℝ) + 1/1000)))^2
      + (((1:ℝ) - 1/1000)/(1 + ((1:ℝ) - 1/1000)))^2
      - 2*(((1:ℝ))/(1 + (1:ℝ)))^2 < 0 := by
  norm_num


/-! ### 四、Hadamard 二阶结构：一阶项消失，曲率由 kernel 项单独承担

`H(x) = λ₁(O[F(x)])`，`F(x)(k) = x/(k²+x)`。沿 `x` 求二阶导时，一阶项是**线性**泛函
`F ↦ ⟨v, O[F]v⟩` 在方向 `F′(x)` 上的值（论文 (1.7) 的凸性就是它的上确界），
二阶项则来自**特征向量随 `x` 移动**。下面这条说：若 `x` 是单位特征向量、`y ⊥ x`，
则混合项 `x ⬝ᵥ A.mulVec y` 恒为零——于是沿 `x + t y` 的展开只剩
`λ + t² (y ⬝ᵥ A.mulVec y)`，二阶性态完全由**方向曲率**承担。

这正是论文说「`λ₁` 凸、kernel 凹、两个效应反向」的代数机制：凸性来自一阶项的线性性，
凹性只能来自方向曲率，而后者不受变分包络控制（第三节两个反例）。 -/

section Hadamard

variable {N : ℕ} [NeZero N]

/-- 点积交换。 -/
lemma dot_comm' (x y : Fin N → ℝ) : y ⬝ᵥ x = x ⬝ᵥ y := by
  simp only [dotProduct]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- 对称矩阵的二次型对称性：`y ⬝ᵥ A x = x ⬝ᵥ A y`（`A` 对称）。 -/
lemma dot_mulVec_comm' (A : Matrix (Fin N) (Fin N) ℝ) (hs : A.IsSymm) (x y : Fin N → ℝ) :
    y ⬝ᵥ A.mulVec x = x ⬝ᵥ A.mulVec y := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [hs.apply j i]; ring

/-- **Hadamard 二阶：混合项消失**。`A` 对称、`x` 是单位特征向量（`A x = λ x`）、`x ⊥ y`
⇒ `x ⬝ᵥ A.mulVec y = 0`。于是 `(x + t y)` 的 Rayleigh 商 = `λ + t² (y ⬝ᵥ A y)`。 -/
theorem hadamard_second_order_vanishes (A : Matrix (Fin N) (Fin N) ℝ) (hs : A.IsSymm)
    (x y : Fin N → ℝ) (lam : ℝ) (heig : A.mulVec x = lam • x) (horth : x ⬝ᵥ y = 0) :
    x ⬝ᵥ A.mulVec y = 0 := by
  rw [← dot_mulVec_comm' A hs, heig, dotProduct_smul, smul_eq_mul, ← dot_comm' y x, horth,
    mul_zero]

end Hadamard

end

end Eliashberg
