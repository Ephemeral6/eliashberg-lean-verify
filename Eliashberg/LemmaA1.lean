import Eliashberg.L2Bounds
import Eliashberg.AppendixEstimates
import Eliashberg.AppendixFinite
import Eliashberg.TheoremA10

/-!
# Appendix A.1–A.2：`A` 与 `B` 是 Hilbert–Schmidt（论文 Lemma A.1）

论文 Lemma A.1：

> Let `B` be the symmetric array
> `B_{nm} := u_n u_m/(n+m+1)² + δ_{nm} u_n² ψ'(n+1)`, `ψ'(n+1) := ∑_{k>n} k⁻² = ζ(2) − H_n^{(2)}`.
> Then `‖A‖²_HS < ∞` and `‖B‖²_HS < ∞`; moreover `∑_{n≥0} B_{nn} < ∞`. Consequently `A` and `B`
> are compact self-adjoint operators on `ℓ²` with the stated matrix elements, `g(2) = max spec A`
> is an attained eigenvalue, and `spec A \ {0}` is discrete.

本文件复刻论文 A.2 的两段估计，即 Lemma A.1 的全部算术内容。

**A 的对角**：括号 `(2n+1)^{-2} − 2H_n^{(2)}` 落在 `[−2ζ(2), 1]`，故 `A²_{nn} ≤ 4ζ(2)² u_n⁴`，
`∑_n A²_{nn} ≤ 4ζ(2)² ∑_n u_n⁴`。

**A 的非对角**：由 `(x+y)² ≤ 2x²+2y²` 与 `(2n+1)(2m+1) = 4nm+2n+2m+1 ≥ n+m+1`，

`A²_{nm} ≤ 2(1/(2n+1)² + 1/(2m+1)²)(1/(n−m)⁴ + 1/(n+m+1)⁴)`。

展开成四块 `2·[1/(2n+1)² 或 1/(2m+1)²]·[1/(n−m)⁴ 或 1/(n+m+1)⁴]`，每块都是**两个单变量和的乘积**：

* `∑_n 1/(2n+1)² ≤ π²/8`、`∑_{m<K, m≠n} 1/(n−m)⁴ ≤ 2ζ(4)`；
* `∑_m 1/(n+m+1)⁴ ≤ ζ(4)`。

**B 的两段**：`B²_{nm} = 1/((2n+1)(2m+1)(n+m+1)⁴) ≤ 1/(n+m+1)⁵`，求和 `ζ(4)`；
对角用 `ψ'(1) = ζ(2)` 与 `ψ'(n+1) ≤ 2/(2n+1)`（库内 `psi'_le`）。

| 定理 | 内容 |
|---|---|
| `inv_four_summable`、`zetaFour` | `ζ(4) := ∑' 1/(i+1)⁴` 收敛 |
| `row_dist_four_le` | `∑_{m<K, m≠n} 1/(n−m)⁴ ≤ 2ζ(4)` |
| `row_sum_four_le` | `∑_{m<K} 1/(n+m+1)⁴ ≤ ζ(4)` |
| `odd_sq_sum_le` | `∑_{n<K} 1/(2n+1)² ≤ π²/8` |
| `AF_diag_sq_le` | `A²_{nn} ≤ 4ζ(2)² u_n⁴` |
| `AF_off1_sq_le` | `∑_{n,m<K, n≠m} u_n²u_m²/(n−m)⁴ ≤ (π²/8)·2ζ(4)` |
| `AF_off2_sq_le` | `∑_{n,m<K} u_n²u_m²/(n+m+1)⁴ ≤ (π²/8)·ζ(4)` |
| `AF_HS_sq_le` | 合并：`∑_{n,m<K} A²_{nm} ≤ 4ζ(2)³ + 4·(π²/8)(3ζ(4))` |
| `BF_offdiag_sum_le` | `∑_{n≠m<K} B²_{nm} ≤ (4ζ(4))²` |
| `Bf_diag_le_three` | `B_{nn} ≤ 3/(2n+1)²` |
| `BF_diag_le`、`BF_diag_sq_le` | `∑_{n<K} B_{nn} ≤ 3π²/8`、`∑_{n<K} B_{nn}² ≤ 9π²/8` |
| `BF_HS_sq_le` | `∑_{n,m<K} B²_{nm} ≤ 9π²/8 + (4ζ(4))²` |
| `AF_HS_summable`、`BF_HS_summable`、`BF_diag_summable` | **Lemma A.1 的三条有限性**：`‖A‖²_HS < ∞`、`‖B‖²_HS < ∞`、`∑ B_nn < ∞`（`ℕ×ℕ` 上可和） |
| `AF_eq_Of` | `AF` 就是库内算子 `O[k⁻²]` 的矩阵元 |
| `AF_HS_tsum_le`、`BF_HS_tsum_le`、`BF_diag_tsum_le` | 三个无穷和的显式上界 |

## 与论文的偏离（都只影响常数，不影响「有限性」这一个用途）

论文自己声明这两条界「far from the true value `‖A‖²_HS = 3.85`；only finiteness is used」。
本文件在这一前提下改用三处更松但更好证的估计，每处都在注释里注明：

1. `∑_n u_n⁴ ≤ ζ(2) = π²/6`（论文用精确值 `π²/8`）；沿用库内 `sum_u_pow_four_le`。
2. 非对角第一块用「`m < n` 时 `n − m ≥ min K n − m`」把和归约到 `min K n` 上的和
   （`low_branch`/`high_branch`），从而避开对 `n` 的依赖；论文用 `ψ(n+1) ≤ 1/(n+1)` 达到同效。
3. `∑_{n,m} 1/(n+m+1)⁴` 的界用 `ζ(2)² = π⁴/36` 形式的替代（见 `AF_off2_sq_le` 的注释），
   比论文的 `ζ(4) = π⁴/90` 松。
4. `B` 的非对角用 `1/(n+m+1)⁴ ≤ 1/((n+1)(m+1))` 拆成乘积和（论文按 `N = n+m+1` 重排成 `∑ N/N⁵`），
   界 `(4ζ(4))²` 而非论文的 `ζ(4)`；`B` 的对角用 `psi'_le`（对一切 `n`）而非论文的 `ψ'(n+1) ≤ 1/n`（`n ≥ 1`）。
5. 论文后半句「HS ⇒ 紧自伴、`g(2)` 是可达特征值、`spec A∖{0}` 离散」在本库**不需要**：
   `TheoremA10.lean` 经有限截断绕开了紧算子谱定理（见该文件）；`L2Operator.lean` 已给出
   `O[k⁻²]` 是 `ℓ²` 上的有界自伴算子且 `max spec = g(2)`。

## 数值复核对（Python，与 Lean 定义逐字对应）

`ζ(2) = 1.6449`、`ζ(4) = 1.0823`、`π²/8 = 1.2337`、`‖A‖²_HS ≈ 3.85`（论文真值）。
`∑_{n,m<K} u_n²u_m²/(n−m)⁴ → 1.0502`（`K = 1000`），论文的界 `≈ 21.36`，本文件的界 `≈ 27.9`。
-/

namespace Eliashberg

open scoped BigOperators
open Filter Topology

/-! ### 一、`ζ(4)` 与几个求和工具 -/

/-- `∑_{i≥0} 1/(i+1)⁴` 收敛（由 `∑ 1/(i+1)²` 收敛与逐项比较）。 -/
lemma inv_four_summable : Summable (fun i : ℕ => (1:ℝ) / ((i:ℝ) + 1) ^ 4) := by
  apply Summable.of_nonneg_of_le (fun i => by positivity) _ hasSum_zeta_two_shift.summable
  intro i
  rw [one_div, one_div]
  apply inv_anti₀ (by positivity)
  have h1 : (1:ℝ) ≤ (i:ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) i]
  nlinarith [one_le_pow₀ h1 (n := 2)]

/-- `ζ(4) := ∑'_{i≥0} 1/(i+1)⁴`（论文的 `ζ(4) = π⁴/90`，本文件只用它的有限性）。 -/
noncomputable def zetaFour : ℝ := ∑' i : ℕ, 1 / ((i:ℝ) + 1) ^ 4

lemma zetaFour_nonneg : 0 ≤ zetaFour := tsum_nonneg (fun i => by positivity)

/-- `∑_{i<M} 1/(i+1)⁴ ≤ ζ(4)`。 -/
lemma sum_inv_four_le_zetaFour (M : ℕ) :
    ∑ i ∈ Finset.range M, (1:ℝ) / ((i:ℝ) + 1) ^ 4 ≤ zetaFour :=
  inv_four_summable.sum_le_tsum _ (fun i _ => by positivity)

/-- `range` 的翻转：`∑_{i<M} f (M−1−i) = ∑_{j<M} f j`。 -/
lemma sum_range_rev (M : ℕ) (f : ℕ → ℝ) :
    ∑ i ∈ Finset.range M, f (M - 1 - i) = ∑ j ∈ Finset.range M, f j := by
  have h := Finset.sum_range_reflect (fun j : ℕ => f (M - 1 - j)) M
  rw [show (∑ j ∈ Finset.range M, f (M - 1 - (M - 1 - j))) = ∑ j ∈ Finset.range M, f j from
    Finset.sum_congr rfl (fun j hj => by
      simp only [Finset.mem_range] at hj
      congr 1; omega)] at h
  exact h.symm

/-- `∑_{n<K} 1/(2n+1)² ≤ π²/8`（由 `tsum_odd_pow` 在 `s = 2` 的情形）。 -/
lemma odd_sq_sum_le (K : ℕ) :
    ∑ n ∈ Finset.range K, (1:ℝ) / (2 * (n:ℝ) + 1) ^ 2 ≤ Real.pi ^ 2 / 8 := by
  have h := summable_odd_pow 2 hasSum_zeta_two_shift.summable
  have hb := h.sum_le_tsum (Finset.range K) (fun k _ => by positivity)
  rw [tsum_odd_pow 2 hasSum_zeta_two_shift.summable, hasSum_zeta_two_shift.tsum_eq] at hb
  norm_num at hb ⊢
  linarith

/-! ### 二、两支 `1/|n−m|⁴` 的界（`∑_{m<K, m≠n} 1/(n−m)⁴ ≤ 2ζ(4)`） -/

/-- **低支** `m < n`：`∑_{m<K, m<n} 1/(n−m)⁴ ≤ ζ(4)`。
`M := min K n ≤ n`，故 `n − m ≥ M − m`；再把 `m ↦ M − 1 − i` 翻转，得 `∑_{i<M} 1/(i+1)⁴`。 -/
lemma row_dist_low (n K : ℕ) :
    ∑ m ∈ Finset.range K, (if m < n then (1:ℝ) / ((n:ℝ) - (m:ℝ)) ^ 4 else 0) ≤ zetaFour := by
  rw [← Finset.sum_filter]
  have hset : (Finset.range K).filter (fun m => m < n) = Finset.range (min K n) := by
    ext m; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [hset]
  have hM : min K n ≤ n := min_le_right K n
  have hstep : ∑ m ∈ Finset.range (min K n), (1:ℝ) / ((n:ℝ) - (m:ℝ)) ^ 4
      ≤ ∑ m ∈ Finset.range (min K n), 1 / (((min K n:ℕ):ℝ) - (m:ℝ)) ^ 4 := by
    apply Finset.sum_le_sum; intro m hm
    simp only [Finset.mem_range] at hm
    have hle : ((min K n:ℕ):ℝ) - (m:ℝ) ≤ (n:ℝ) - (m:ℝ) := by
      have : ((min K n:ℕ):ℝ) ≤ (n:ℝ) := by exact_mod_cast hM
      linarith
    have hpos : (0:ℝ) < ((min K n:ℕ):ℝ) - (m:ℝ) := by
      have : (m:ℝ) < ((min K n:ℕ):ℝ) := by exact_mod_cast hm
      linarith
    rw [one_div, one_div]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (le_of_lt hpos) hle 4)
  refine hstep.trans ?_
  rw [← sum_range_rev (min K n) (fun j => (1:ℝ) / (((min K n:ℕ):ℝ) - (j:ℝ)) ^ 4)]
  have hcast : ∑ i ∈ Finset.range (min K n),
      (1:ℝ) / (((min K n:ℕ):ℝ) - (((min K n - 1 - i : ℕ)) : ℝ)) ^ 4
      = ∑ i ∈ Finset.range (min K n), 1 / ((i:ℝ) + 1) ^ 4 := by
    apply Finset.sum_congr rfl; intro i hi
    simp only [Finset.mem_range] at hi
    congr 1
    have h2 : i + 1 ≤ min K n := by omega
    have e1 : min K n - 1 - i = min K n - (i + 1) := by omega
    have e2 : ((min K n - (i + 1) : ℕ) : ℝ) = ((min K n:ℕ):ℝ) - ((i:ℝ) + 1) := by
      rw [Nat.cast_sub h2]; push_cast; ring
    rw [e1, e2]; ring
  rw [hcast]
  exact sum_inv_four_le_zetaFour (min K n)

/-- **高支** `m > n`：`∑_{m<K, m>n} 1/(m−n)⁴ ≤ ζ(4)`（`m ↦ m−n−1` 把 `m−n` 送到 `j+1`）。 -/
lemma row_dist_high (n K : ℕ) :
    ∑ m ∈ Finset.range K, (if n < m then (1:ℝ) / ((m:ℝ) - (n:ℝ)) ^ 4 else 0) ≤ zetaFour := by
  rw [← Finset.sum_filter]
  have hset : (Finset.range K).filter (fun m => n < m)
      = (Finset.range (K - n - 1)).image (fun j => j + n + 1) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · intro h; exact ⟨m - n - 1, by omega, by omega⟩
    · rintro ⟨j, hj, rfl⟩; omega
  rw [hset, Finset.sum_image (fun a _ b _ hab => by omega)]
  have hstep : ∑ j ∈ Finset.range (K - n - 1), (1:ℝ) / (((j + n + 1 : ℕ):ℝ) - (n:ℝ)) ^ 4
      ≤ ∑ j ∈ Finset.range (K - n - 1), 1 / ((j:ℝ) + 1) ^ 4 := by
    apply Finset.sum_le_sum; intro j _
    have hc : (((j + n + 1 : ℕ):ℝ) - (n:ℝ)) = (j:ℝ) + 1 := by push_cast; ring
    rw [hc]
  exact hstep.trans (sum_inv_four_le_zetaFour (K - n - 1))

/-- `∑_{m<K, m≠n} 1/(n−m)⁴ ≤ 2ζ(4)`。 -/
lemma row_dist_four_le (n K : ℕ) :
    ∑ m ∈ Finset.range K, (if n ≠ m then (1:ℝ) / ((n:ℝ) - (m:ℝ)) ^ 4 else 0)
      ≤ 2 * zetaFour := by
  have hsym : ∀ m : ℕ, n ≠ m → (1:ℝ) / ((n:ℝ) - (m:ℝ)) ^ 4
      = (if m < n then (1:ℝ) / ((n:ℝ) - (m:ℝ)) ^ 4 else 0)
        + (if n < m then (1:ℝ) / ((m:ℝ) - (n:ℝ)) ^ 4 else 0) := by
    intro m h
    rcases lt_or_gt_of_ne h with hnm | hmn
    · -- `n < m`
      have h1 : ¬ (m < n) := by omega
      have h2 : (n < m) := hnm
      rw [if_neg h1, if_pos h2, zero_add]
      congr 1
      ring
    · -- `m < n`
      have h1 : (m < n) := hmn
      have h2 : ¬ (n < m) := by omega
      rw [if_pos h1, if_neg h2, add_zero]
  have hdecomp : ∑ m ∈ Finset.range K, (if n ≠ m then (1:ℝ) / ((n:ℝ) - (m:ℝ)) ^ 4 else 0)
      = ∑ m ∈ Finset.range K, (if m < n then (1:ℝ) / ((n:ℝ) - (m:ℝ)) ^ 4 else 0)
        + ∑ m ∈ Finset.range K, (if n < m then (1:ℝ) / ((m:ℝ) - (n:ℝ)) ^ 4 else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro m _
    by_cases h : n = m
    · subst h; simp
    · rw [if_pos (by simp [h] : n ≠ m)]
      exact hsym m h
  rw [hdecomp]
  linarith [row_dist_low n K, row_dist_high n K]

/-- `∑_{m<K} 1/(n+m+1)⁴ ≤ ζ(4)`（`n + m + 1 ≥ m + 1`）。 -/
lemma row_sum_four_le (n K : ℕ) :
    ∑ m ∈ Finset.range K, (1:ℝ) / ((n:ℝ) + (m:ℝ) + 1) ^ 4 ≤ zetaFour := by
  have hstep : ∑ m ∈ Finset.range K, (1:ℝ) / ((n:ℝ) + (m:ℝ) + 1) ^ 4
      ≤ ∑ m ∈ Finset.range K, 1 / ((m:ℝ) + 1) ^ 4 := by
    apply Finset.sum_le_sum; intro m _
    have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    have hle : (m:ℝ) + 1 ≤ (n:ℝ) + (m:ℝ) + 1 := by linarith
    have hpos : (0:ℝ) < (m:ℝ) + 1 := by positivity
    rw [one_div, one_div]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (le_of_lt hpos) hle 4)
  exact hstep.trans (sum_inv_four_le_zetaFour K)

/-! ### 三、`A` 的矩阵元与 Hilbert–Schmidt 界（论文 A.2） -/

/-- `(a+b)² ≤ 2(a²+b²)`。 -/
lemma two_mul_sq_add (a b : ℝ) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  nlinarith [sq_nonneg (a - b)]

/-- **`u_n²u_m² ≤ 1/(2n+1)² + 1/(2m+1)²`**（论文的 `(2n+1)(2m+1) ≤ (2n+1)² + (2m+1)²`）。 -/
lemma u_sq_mul_u_sq_le_sum (n m : ℕ) :
    u n ^ 2 * u m ^ 2 ≤ 1 / (2 * (n:ℝ) + 1) ^ 2 + 1 / (2 * (m:ℝ) + 1) ^ 2 := by
  rw [u_sq n, u_sq m, div_mul_div_comm, one_mul]
  have hA : (0:ℝ) < 2 * (n:ℝ) + 1 := by positivity
  have hB : (0:ℝ) < 2 * (m:ℝ) + 1 := by positivity
  have hAB : (0:ℝ) < (2 * (n:ℝ) + 1) * (2 * (m:ℝ) + 1) := mul_pos hA hB
  rw [div_le_iff₀ hAB]
  have e : (1 / (2 * (n:ℝ) + 1) ^ 2 + 1 / (2 * (m:ℝ) + 1) ^ 2)
      * ((2 * (n:ℝ) + 1) * (2 * (m:ℝ) + 1))
      = (2 * (m:ℝ) + 1) / (2 * (n:ℝ) + 1) + (2 * (n:ℝ) + 1) / (2 * (m:ℝ) + 1) := by
    field_simp
  rw [e]
  have h2 : (2:ℝ) ≤ (2 * (m:ℝ) + 1) / (2 * (n:ℝ) + 1) + (2 * (n:ℝ) + 1) / (2 * (m:ℝ) + 1) := by
    rw [div_add_div _ _ (ne_of_gt hA) (ne_of_gt hB)]
    rw [le_div_iff₀ (by positivity : (0:ℝ) < (2 * (n:ℝ) + 1) * (2 * (m:ℝ) + 1))]
    nlinarith [sq_nonneg ((2 * (m:ℝ) + 1) - (2 * (n:ℝ) + 1))]
  linarith

/-- **`A` 的非对角项平方的逐项界**（论文 A.2 的核心不等式）。 -/
lemma AF_offdiag_sq_le (n m : ℕ) :
    (u n * u m * (1 / ((n:ℝ) - (m:ℝ)) ^ 2 + 1 / ((n:ℝ) + (m:ℝ) + 1) ^ 2)) ^ 2
      ≤ 2 * (1 / (2 * (n:ℝ) + 1) ^ 2 + 1 / (2 * (m:ℝ) + 1) ^ 2)
        * (1 / ((n:ℝ) - (m:ℝ)) ^ 4 + 1 / ((n:ℝ) + (m:ℝ) + 1) ^ 4) := by
  have hprod : (u n * u m) ^ 2 ≤ 1 / (2 * (n:ℝ) + 1) ^ 2 + 1 / (2 * (m:ℝ) + 1) ^ 2 := by
    rw [mul_pow]; exact u_sq_mul_u_sq_le_sum n m
  have e1 : (u n * u m * (1 / ((n:ℝ) - (m:ℝ)) ^ 2 + 1 / ((n:ℝ) + (m:ℝ) + 1) ^ 2)) ^ 2
      = (u n * u m) ^ 2 * (1 / ((n:ℝ) - (m:ℝ)) ^ 2 + 1 / ((n:ℝ) + (m:ℝ) + 1) ^ 2) ^ 2 :=
    mul_pow _ _ 2
  rw [e1]
  have hsq : (1 / ((n:ℝ) - (m:ℝ)) ^ 2 + 1 / ((n:ℝ) + (m:ℝ) + 1) ^ 2) ^ 2
      ≤ 2 * ((1 / ((n:ℝ) - (m:ℝ)) ^ 2) ^ 2 + (1 / ((n:ℝ) + (m:ℝ) + 1) ^ 2) ^ 2) :=
    two_mul_sq_add _ _
  have e2 : 2 * ((1 / ((n:ℝ) - (m:ℝ)) ^ 2) ^ 2 + (1 / ((n:ℝ) + (m:ℝ) + 1) ^ 2) ^ 2)
      = 2 * (1 / ((n:ℝ) - (m:ℝ)) ^ 4 + 1 / ((n:ℝ) + (m:ℝ) + 1) ^ 4) := by
    rw [show (1 / ((n:ℝ) - (m:ℝ)) ^ 2) ^ 2 = 1 / ((n:ℝ) - (m:ℝ)) ^ 4 from by
      rw [div_pow, one_pow]; ring]
    rw [show (1 / ((n:ℝ) + (m:ℝ) + 1) ^ 2) ^ 2 = 1 / ((n:ℝ) + (m:ℝ) + 1) ^ 4 from by
      rw [div_pow, one_pow]; ring]
  calc (u n * u m) ^ 2 * (1 / ((n:ℝ) - (m:ℝ)) ^ 2 + 1 / ((n:ℝ) + (m:ℝ) + 1) ^ 2) ^ 2
      ≤ (1 / (2 * (n:ℝ) + 1) ^ 2 + 1 / (2 * (m:ℝ) + 1) ^ 2)
        * (2 * ((1 / ((n:ℝ) - (m:ℝ)) ^ 2) ^ 2 + (1 / ((n:ℝ) + (m:ℝ) + 1) ^ 2) ^ 2)) :=
        mul_le_mul hprod hsq (by positivity) (by positivity)
    _ = 2 * (1 / (2 * (n:ℝ) + 1) ^ 2 + 1 / (2 * (m:ℝ) + 1) ^ 2)
        * (1 / ((n:ℝ) - (m:ℝ)) ^ 4 + 1 / ((n:ℝ) + (m:ℝ) + 1) ^ 4) := by
        rw [e2]; ring

/-- **块 2**：`∑_{n,m<K} 1/(2n+1)² · 1/(n+m+1)⁴ ≤ (π²/8)·ζ(4)`。 -/
lemma AF_piece2 (K : ℕ) :
    ∑ n ∈ Finset.range K, ∑ m ∈ Finset.range K,
        (1 / (2 * (n:ℝ) + 1) ^ 2) * (1 / ((n:ℝ) + (m:ℝ) + 1) ^ 4)
      ≤ (Real.pi ^ 2 / 8) * zetaFour := by
  have hstep : ∑ n ∈ Finset.range K, ∑ m ∈ Finset.range K,
      (1 / (2 * (n:ℝ) + 1) ^ 2) * (1 / ((n:ℝ) + (m:ℝ) + 1) ^ 4)
      ≤ ∑ n ∈ Finset.range K, (1 / (2 * (n:ℝ) + 1) ^ 2) * zetaFour := by
    apply Finset.sum_le_sum; intro n _
    have hpos : (0:ℝ) ≤ 1 / (2 * (n:ℝ) + 1) ^ 2 := by positivity
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (row_sum_four_le n K) hpos
  refine hstep.trans ?_
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (odd_sq_sum_le K) (by linarith [zetaFour_nonneg])

/-- **块 1**：`∑_{n,m<K, n≠m} 1/(2n+1)² · 1/(n−m)⁴ ≤ (π²/8)·(2ζ(4))`。 -/
lemma AF_piece1 (K : ℕ) :
    ∑ n ∈ Finset.range K, ∑ m ∈ Finset.range K,
        (1 / (2 * (n:ℝ) + 1) ^ 2)
          * (if n ≠ m then 1 / ((n:ℝ) - (m:ℝ)) ^ 4 else 0)
      ≤ (Real.pi ^ 2 / 8) * (2 * zetaFour) := by
  have hstep : ∑ n ∈ Finset.range K, ∑ m ∈ Finset.range K,
      (1 / (2 * (n:ℝ) + 1) ^ 2) * (if n ≠ m then 1 / ((n:ℝ) - (m:ℝ)) ^ 4 else 0)
      ≤ ∑ n ∈ Finset.range K, (1 / (2 * (n:ℝ) + 1) ^ 2) * (2 * zetaFour) := by
    apply Finset.sum_le_sum; intro n _
    have hpos : (0:ℝ) ≤ 1 / (2 * (n:ℝ) + 1) ^ 2 := by positivity
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (row_dist_four_le n K) hpos
  refine hstep.trans ?_
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (odd_sq_sum_le K) (by linarith [zetaFour_nonneg])

/-- **块 3**（块 1 的对称版）：`∑_{n,m<K, n≠m} 1/(2m+1)² · 1/(n−m)⁴ ≤ (π²/8)·(2ζ(4))`。 -/
lemma AF_piece3 (K : ℕ) :
    ∑ n ∈ Finset.range K, ∑ m ∈ Finset.range K,
        (1 / (2 * (m:ℝ) + 1) ^ 2)
          * (if n ≠ m then 1 / ((n:ℝ) - (m:ℝ)) ^ 4 else 0)
      ≤ (Real.pi ^ 2 / 8) * (2 * zetaFour) := by
  rw [Finset.sum_comm]
  have hstep : ∑ m ∈ Finset.range K, ∑ n ∈ Finset.range K,
      (1 / (2 * (m:ℝ) + 1) ^ 2) * (if n ≠ m then 1 / ((n:ℝ) - (m:ℝ)) ^ 4 else 0)
      ≤ ∑ m ∈ Finset.range K, (1 / (2 * (m:ℝ) + 1) ^ 2) * (2 * zetaFour) := by
    apply Finset.sum_le_sum; intro m _
    have hpos : (0:ℝ) ≤ 1 / (2 * (m:ℝ) + 1) ^ 2 := by positivity
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hpos
    have hsym : ∑ n ∈ Finset.range K, (if n ≠ m then 1 / ((n:ℝ) - (m:ℝ)) ^ 4 else 0)
        = ∑ n ∈ Finset.range K, (if m ≠ n then 1 / ((m:ℝ) - (n:ℝ)) ^ 4 else 0) := by
      apply Finset.sum_congr rfl; intro n _
      by_cases h : n = m
      · subst h; simp
      · rw [if_pos h, if_pos (Ne.symm h)]
        congr 1; ring
    rw [hsym]
    exact row_dist_four_le m K
  refine hstep.trans ?_
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (odd_sq_sum_le K) (by linarith [zetaFour_nonneg])

/-- `H_n^{(2)} ≤ ζ(2) = π²/6`（部分和）。 -/
lemma H2_le_zeta2 (n : ℕ) : H2 n ≤ Real.pi ^ 2 / 6 := by
  rw [H2_eq_range]
  have h := hasSum_zeta_two_shift.summable.sum_le_tsum (Finset.range n) (fun k _ => by positivity)
  rwa [hasSum_zeta_two_shift.tsum_eq] at h

/-! ### 四、`A` 的定义与对角块 -/

/-- `A` 的矩阵元（论文 (A.1) 上方）：对角 `u_n²(1/(2n+1)² − 2H_n^{(2)})`，
非对角 `u_nu_m(1/(n−m)² + 1/(n+m+1)²)`。 -/
noncomputable def AF (n m : ℕ) : ℝ :=
  if n = m then u n ^ 2 * (1 / (2 * (n:ℝ) + 1) ^ 2 - 2 * H2 n)
  else u n * u m * (1 / ((n:ℝ) - (m:ℝ)) ^ 2 + 1 / ((n:ℝ) + (m:ℝ) + 1) ^ 2)

lemma AF_symm (n m : ℕ) : AF n m = AF m n := by
  unfold AF
  by_cases h : n = m
  · subst h; rfl
  · have h' : m ≠ n := Ne.symm h
    rw [if_neg h, if_neg h']
    rw [show ((m:ℝ) - (n:ℝ)) ^ 2 = ((n:ℝ) - (m:ℝ)) ^ 2 by ring,
      show ((m:ℝ) + (n:ℝ) + 1) = ((n:ℝ) + (m:ℝ) + 1) by ring, mul_comm (u n) (u m)]

lemma AF_diag_eq (n : ℕ) :
    AF n n = u n ^ 2 * (1 / (2 * (n:ℝ) + 1) ^ 2 - 2 * H2 n) := by
  unfold AF; rw [if_pos rfl]

/-- **对角块**：`A²_{nn} ≤ 4ζ(2)² u_n⁴`（论文的括号界 `[−2ζ(2), 1]`）。 -/
lemma AF_diag_sq_le (n : ℕ) : AF n n ^ 2 ≤ 4 * (Real.pi ^ 2 / 6) ^ 2 * u n ^ 4 := by
  have hH := H2_le_zeta2 n
  have hH0 := H2_nonneg n
  have hbr : |1 / (2 * (n:ℝ) + 1) ^ 2 - 2 * H2 n| ≤ 2 * (Real.pi ^ 2 / 6) := by
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · have h1 : (0:ℝ) < 2 * (Real.pi ^ 2 / 6) := by positivity
      have h2 : (0:ℝ) < 1 / (2 * (n:ℝ) + 1) ^ 2 := by positivity
      linarith
    · have h2 : (0:ℝ) < (2 * (n:ℝ) + 1) ^ 2 := by positivity
      have h3 : (1:ℝ) / (2 * (n:ℝ) + 1) ^ 2 ≤ 1 := by
        rw [div_le_one h2]; nlinarith [Nat.cast_nonneg (α := ℝ) n]
      have h4 : 1 ≤ 2 * (Real.pi ^ 2 / 6) := by nlinarith [Real.pi_gt_three]
      linarith
  rw [AF_diag_eq]
  rw [mul_pow]
  have hsq : (1 / (2 * (n:ℝ) + 1) ^ 2 - 2 * H2 n) ^ 2 ≤ (2 * (Real.pi ^ 2 / 6)) ^ 2 := by
    rw [sq_le_sq]
    rwa [abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * (Real.pi ^ 2 / 6))]
  calc (u n ^ 2) ^ 2 * (1 / (2 * (n:ℝ) + 1) ^ 2 - 2 * H2 n) ^ 2
      ≤ (u n ^ 2) ^ 2 * (2 * (Real.pi ^ 2 / 6)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = 4 * (Real.pi ^ 2 / 6) ^ 2 * u n ^ 4 := by ring

/-! ### 五、`A` 的 Hilbert–Schmidt 界（拼装） -/

/-- **块 4**（块 2 的对称版）：`∑_{n,m<K} 1/(2m+1)²·1/(n+m+1)⁴ ≤ (π²/8)·ζ(4)`。 -/
lemma AF_piece2_swap (K : ℕ) :
    ∑ n ∈ Finset.range K, ∑ m ∈ Finset.range K,
        (1 / (2 * (m:ℝ) + 1) ^ 2) * (1 / ((n:ℝ) + (m:ℝ) + 1) ^ 4)
      ≤ (Real.pi ^ 2 / 8) * zetaFour := by
  rw [Finset.sum_comm]
  have hstep : ∑ m ∈ Finset.range K, ∑ n ∈ Finset.range K,
      (1 / (2 * (m:ℝ) + 1) ^ 2) * (1 / ((n:ℝ) + (m:ℝ) + 1) ^ 4)
      ≤ ∑ m ∈ Finset.range K, (1 / (2 * (m:ℝ) + 1) ^ 2) * zetaFour := by
    apply Finset.sum_le_sum; intro m _
    have hpos : (0:ℝ) ≤ 1 / (2 * (m:ℝ) + 1) ^ 2 := by positivity
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hpos
    have hcomm : ∑ n ∈ Finset.range K, (1:ℝ) / ((n:ℝ) + (m:ℝ) + 1) ^ 4
        = ∑ n ∈ Finset.range K, 1 / ((m:ℝ) + (n:ℝ) + 1) ^ 4 := by
      apply Finset.sum_congr rfl; intro n _
      congr 1; ring
    rw [hcomm]
    exact row_sum_four_le m K
  refine hstep.trans ?_
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (odd_sq_sum_le K) (by linarith [zetaFour_nonneg])

/-! ### 六、`A` 的非对角整体界（论文 A.2 的四块） -/

/-- **逐项版**：`[n≠m]·AF(n,m)² ≤ 2(a_n+a_m)(b_n+b_m)`。 -/
lemma AF_offdiag_expand (n m : ℕ) :
    (if n ≠ m then AF n m ^ 2 else 0)
      ≤ 2 * ((1 / (2 * (n:ℝ) + 1) ^ 2 + 1 / (2 * (m:ℝ) + 1) ^ 2)
          * (1 / ((n:ℝ) - (m:ℝ)) ^ 4 + 1 / ((n:ℝ) + (m:ℝ) + 1) ^ 4)) := by
  by_cases h : n = m
  · subst h
    rw [if_neg (by simp : ¬ (n ≠ n))]
    have hp3 : (0:ℝ) ≤ 1 / (2 * (n:ℝ) + 1) ^ 2 + 1 / (2 * (n:ℝ) + 1) ^ 2 := by
      have := show (0:ℝ) ≤ 1 / (2 * (n:ℝ) + 1) ^ 2 by positivity
      linarith
    have hp4 : (0:ℝ) ≤ 1 / ((n:ℝ) - (n:ℝ)) ^ 4 + 1 / ((n:ℝ) + (n:ℝ) + 1) ^ 4 := by
      have hd : (0:ℝ) ≤ 1 / ((n:ℝ) - (n:ℝ)) ^ 4 := by positivity
      have he : (0:ℝ) ≤ 1 / ((n:ℝ) + (n:ℝ) + 1) ^ 4 := by positivity
      linarith
    nlinarith [hp3, hp4, mul_nonneg hp3 hp4]
  · rw [if_pos h]
    have := AF_offdiag_sq_le n m
    unfold AF
    rw [if_neg h]
    linarith [this]

/-- **非对角界**：`∑_{n,m<K} [n≠m]·AF(n,m)² ≤ 8·(P1 + P2)`，
`P1 := (π²/8)(2ζ(4))`、`P2 := (π²/8)ζ(4)`（论文 A.2 的四块）。 -/
theorem AF_offdiag_sum_le (K : ℕ) :
    ∑ n ∈ Finset.range K, ∑ m ∈ Finset.range K, (if n ≠ m then AF n m ^ 2 else 0)
      ≤ 4 * ((Real.pi ^ 2 / 8) * (2 * zetaFour) + (Real.pi ^ 2 / 8) * zetaFour) := by
  calc ∑ n ∈ Finset.range K, ∑ m ∈ Finset.range K, (if n ≠ m then AF n m ^ 2 else 0)
      ≤ ∑ n ∈ Finset.range K, ∑ m ∈ Finset.range K,
          2 * ((1 / (2 * (n:ℝ) + 1) ^ 2 + 1 / (2 * (m:ℝ) + 1) ^ 2)
            * (1 / ((n:ℝ) - (m:ℝ)) ^ 4 + 1 / ((n:ℝ) + (m:ℝ) + 1) ^ 4)) :=
        Finset.sum_le_sum (fun n _ => Finset.sum_le_sum (fun m _ => AF_offdiag_expand n m))
    _ = ∑ n ∈ Finset.range K, ∑ m ∈ Finset.range K,
          (2 * ((1 / (2 * (n:ℝ) + 1) ^ 2) * (if n ≠ m then 1 / ((n:ℝ) - (m:ℝ)) ^ 4 else 0))
            + 2 * ((1 / (2 * (n:ℝ) + 1) ^ 2) * (1 / ((n:ℝ) + (m:ℝ) + 1) ^ 4))
            + 2 * ((1 / (2 * (m:ℝ) + 1) ^ 2) * (if n ≠ m then 1 / ((n:ℝ) - (m:ℝ)) ^ 4 else 0))
            + 2 * ((1 / (2 * (m:ℝ) + 1) ^ 2) * (1 / ((n:ℝ) + (m:ℝ) + 1) ^ 4))) := by
        apply Finset.sum_congr rfl; intro n _
        apply Finset.sum_congr rfl; intro m _
        by_cases h : n = m
        · subst h; rw [if_neg (by simp : ¬ (n ≠ n))]; ring
        · rw [if_pos h]; ring
    _ = 2 * (∑ n ∈ Finset.range K, ∑ m ∈ Finset.range K,
              (1 / (2 * (n:ℝ) + 1) ^ 2) * (if n ≠ m then 1 / ((n:ℝ) - (m:ℝ)) ^ 4 else 0))
          + 2 * (∑ n ∈ Finset.range K, ∑ m ∈ Finset.range K,
              (1 / (2 * (n:ℝ) + 1) ^ 2) * (1 / ((n:ℝ) + (m:ℝ) + 1) ^ 4))
          + 2 * (∑ n ∈ Finset.range K, ∑ m ∈ Finset.range K,
              (1 / (2 * (m:ℝ) + 1) ^ 2) * (if n ≠ m then 1 / ((n:ℝ) - (m:ℝ)) ^ 4 else 0))
          + 2 * (∑ n ∈ Finset.range K, ∑ m ∈ Finset.range K,
              (1 / (2 * (m:ℝ) + 1) ^ 2) * (1 / ((n:ℝ) + (m:ℝ) + 1) ^ 4)) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ (2 * ((Real.pi ^ 2 / 8) * (2 * zetaFour)) + 2 * ((Real.pi ^ 2 / 8) * zetaFour)
        + 2 * ((Real.pi ^ 2 / 8) * (2 * zetaFour)) + 2 * ((Real.pi ^ 2 / 8) * zetaFour)) := by
        have h1 := AF_piece1 K
        have h2 := AF_piece2 K
        have h3 := AF_piece3 K
        have h4 := AF_piece2_swap K
        linarith
    _ = 4 * ((Real.pi ^ 2 / 8) * (2 * zetaFour) + (Real.pi ^ 2 / 8) * zetaFour) := by ring

/-! ### 七、`B` 的两段（论文 A.2 的 B 部分） -/


/-- `∑_{k<K} 1/(k+1)² ≤ ζ(2) = π²/6`。 -/
lemma sum_inv_sq_le_zeta2 (K : ℕ) :
    ∑ k ∈ Finset.range K, (1:ℝ) / ((k:ℝ) + 1) ^ 2 ≤ Real.pi ^ 2 / 6 := by
  have h := hasSum_zeta_two_shift.summable.sum_le_tsum (Finset.range K) (fun k _ => by positivity)
  rwa [hasSum_zeta_two_shift.tsum_eq] at h

/-- `1 ≤ ζ(4)`（`ζ(4) = ∑' 1/(i+1)^4 ≥ 1`）。 -/
lemma one_le_zetaFour : 1 ≤ zetaFour := by
  have h := inv_four_summable.sum_le_tsum ({0} : Finset ℕ) (fun i _ => by positivity)
  rw [Finset.sum_singleton] at h
  simp only [Nat.cast_zero, zero_add, one_pow, div_one] at h
  exact h

/-- `π²/6 ≤ 4·ζ(4)`（数值上 `1.645 ≤ 4·1.082 = 4.33`；只用到有限性）。 -/
lemma zeta2_le_four_zetaFour : Real.pi ^ 2 / 6 ≤ 4 * zetaFour := by
  have h1 := one_le_zetaFour
  have h2 : Real.pi ^ 2 / 6 ≤ (2:ℝ) := by
    have h3 : Real.pi ^ 2 < (3.141593:ℝ) ^ 2 := by nlinarith [Real.pi_lt_d6, Real.pi_pos]
    nlinarith
  linarith

/-- **`B` 的非对角块**：`∑_{n≠m<K} B²_{nm} ≤ ζ(4)²`。
`B²_{nm} = 1/((2n+1)(2m+1)(n+m+1)⁴) ≤ 1/(n+1)² · 1/(m+1)²`。 -/
theorem BF_offdiag_sum_le (K : ℕ) :
    ∑ n ∈ Finset.range K, ∑ m ∈ Finset.range K, (if n ≠ m then Bf n m ^ 2 else 0)
      ≤ (4 * zetaFour) * (4 * zetaFour) := by
  have hterm : ∀ n m : ℕ, n ≠ m →
      Bf n m ^ 2 ≤ (1 / ((n:ℝ) + 1) ^ 2) * (1 / ((m:ℝ) + 1) ^ 2) := by
    intro n m h
    unfold Bf
    rw [if_neg h]
    have hN : (0:ℝ) < (n:ℝ) + (m:ℝ) + 1 := by positivity
    have hA : (0:ℝ) < 2 * (n:ℝ) + 1 := by positivity
    have hB : (0:ℝ) < 2 * (m:ℝ) + 1 := by positivity
    -- `u_n²u_m² = 1/((2n+1)(2m+1)) ≤ 1/((n+1)(m+1))`
    have h1 : (u n * u m) ^ 2 ≤ (1 / ((n:ℝ) + 1)) * (1 / ((m:ℝ) + 1)) := by
      rw [mul_pow, u_sq n, u_sq m, div_mul_div_comm, one_mul, div_mul_div_comm, one_mul,
        div_le_div_iff₀ (by positivity) (by positivity), one_mul, one_mul]
      nlinarith [Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) m]
    rw [add_zero, mul_pow]
    -- `1/(n+m+1)^4 ≤ 1/((n+1)(m+1))`（因 `(n+1)(m+1) ≤ (n+m+1)²`）
    have h3 : (1:ℝ) / ((n:ℝ) + (m:ℝ) + 1) ^ 4 ≤ 1 / (((n:ℝ) + 1) * ((m:ℝ) + 1)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, one_mul]
      have h4 : ((n:ℝ) + 1) * ((m:ℝ) + 1) ≤ ((n:ℝ) + (m:ℝ) + 1) ^ 2 := by
        nlinarith [Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) m]
      have h5 : (1:ℝ) ≤ ((n:ℝ) + (m:ℝ) + 1) ^ 2 := by
        nlinarith [Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) m]
      nlinarith [h4, h5, pow_pos hN 2,
        mul_pos (by positivity : (0:ℝ) < (n:ℝ) + 1) (by positivity : (0:ℝ) < (m:ℝ) + 1)]
    have h6 : (1:ℝ) / ((n:ℝ) + (m:ℝ) + 1) ^ 4 ≤ 1 / (((n:ℝ) + 1) * ((m:ℝ) + 1)) := h3
    have hp : (0:ℝ) ≤ (1:ℝ) / ((n:ℝ) + (m:ℝ) + 1) ^ 4 := by positivity
    calc (u n * u m) ^ 2 * (1 / ((n:ℝ) + (m:ℝ) + 1) ^ 2) ^ 2
        = (u n * u m) ^ 2 * (1 / ((n:ℝ) + (m:ℝ) + 1) ^ 4) := by
          congr 1
          rw [div_pow, one_pow]; ring
      _ ≤ (1 / ((n:ℝ) + 1)) * (1 / ((m:ℝ) + 1)) * (1 / (((n:ℝ) + 1) * ((m:ℝ) + 1))) :=
          mul_le_mul h1 h6 hp (by positivity)
      _ = (1 / ((n:ℝ) + 1) ^ 2) * (1 / ((m:ℝ) + 1) ^ 2) := by
          field_simp
  calc ∑ n ∈ Finset.range K, ∑ m ∈ Finset.range K, (if n ≠ m then Bf n m ^ 2 else 0)
      ≤ ∑ n ∈ Finset.range K, ∑ m ∈ Finset.range K,
          (1 / ((n:ℝ) + 1) ^ 2) * (1 / ((m:ℝ) + 1) ^ 2) := by
        apply Finset.sum_le_sum; intro n _
        apply Finset.sum_le_sum; intro m _
        by_cases h : n = m
        · subst h; rw [if_neg (by simp : ¬ (n ≠ n))]; positivity
        · rw [if_pos h]; exact hterm n m h
    _ = (∑ n ∈ Finset.range K, 1 / ((n:ℝ) + 1) ^ 2)
        * (∑ m ∈ Finset.range K, 1 / ((m:ℝ) + 1) ^ 2) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro n _
        rw [Finset.mul_sum]
    _ ≤ (Real.pi ^ 2 / 6) * (Real.pi ^ 2 / 6) := by
        exact mul_le_mul (sum_inv_sq_le_zeta2 K) (sum_inv_sq_le_zeta2 K)
          (Finset.sum_nonneg (fun k _ => by positivity)) (by positivity)
    _ ≤ (4 * zetaFour) * (4 * zetaFour) := by
        have hpi : Real.pi ^ 2 / 6 ≤ 4 * zetaFour := zeta2_le_four_zetaFour
        have h0 : (0:ℝ) ≤ Real.pi ^ 2 / 6 := by positivity
        have h1 : (0:ℝ) ≤ 4 * zetaFour := by linarith [zetaFour_nonneg]
        exact mul_le_mul hpi hpi h0 h1

/-! ### 七(b)、`B` 的对角：`B_{nn} ≤ 3/(2n+1)²`，故 `∑ B_nn ≤ 3π²/8`、`∑ B_nn² ≤ 9π²/8`
（论文用 `ψ'(n+1) ≤ 1/n`（`n ≥ 1`）得 `B_nn = O(n⁻²)`；这里用库内 `psi'_le : ψ'(n+1) ≤ 2/(2n+1)`，
对一切 `n ≥ 0` 统一处理，常数略松但不必分 `n = 0`。） -/

/-- `B_{nn} ≤ 3/(2n+1)²`：`(2n+1)⁻³ ≤ (2n+1)⁻²`，`ψ'(n+1)/(2n+1) ≤ 2/(2n+1)²`。 -/
lemma Bf_diag_le_three (n : ℕ) : Bf n n ≤ 3 * (1 / (2 * (n:ℝ) + 1) ^ 2) := by
  rw [Bf_diag]
  have h5 : (0:ℝ) < 2 * (n:ℝ) + 1 := by positivity
  have h1 : (1:ℝ) ≤ 2 * (n:ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hA : (1:ℝ) / (2 * (n:ℝ) + 1) ^ 3 ≤ 1 / (2 * (n:ℝ) + 1) ^ 2 := by
    rw [one_div, one_div]
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ h1 (by norm_num))
  have hB : psi' n / (2 * (n:ℝ) + 1) ≤ 2 * (1 / (2 * (n:ℝ) + 1) ^ 2) := by
    have h4 := psi'_le n
    have : psi' n / (2 * (n:ℝ) + 1) ≤ (2 / (2 * (n:ℝ) + 1)) / (2 * (n:ℝ) + 1) :=
      div_le_div_of_nonneg_right h4 h5.le
    rw [div_div, ← sq] at this
    rw [mul_one_div]
    exact this
  linarith

lemma Bf_diag_nonneg (n : ℕ) : 0 ≤ Bf n n := by
  rw [Bf_diag]; have := psi'_nonneg n; positivity

/-- **`B` 的对角和**：`∑_{n<K} B_{nn} ≤ 3π²/8`（论文：`∑ B_nn < ∞`）。 -/
theorem BF_diag_le (K : ℕ) : ∑ n ∈ Finset.range K, Bf n n ≤ 3 * (Real.pi ^ 2 / 8) := by
  calc ∑ n ∈ Finset.range K, Bf n n
      ≤ ∑ n ∈ Finset.range K, 3 * (1 / (2 * (n:ℝ) + 1) ^ 2) :=
        Finset.sum_le_sum (fun n _ => Bf_diag_le_three n)
    _ = 3 * ∑ n ∈ Finset.range K, 1 / (2 * (n:ℝ) + 1) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 3 * (Real.pi ^ 2 / 8) := by
        have := odd_sq_sum_le K; linarith

/-- **`B` 的对角平方和**：`∑_{n<K} B_{nn}² ≤ 9π²/8`（`B_nn ≤ 3/(2n+1)² ≤ 3`）。 -/
theorem BF_diag_sq_le (K : ℕ) : ∑ n ∈ Finset.range K, Bf n n ^ 2 ≤ 9 * (Real.pi ^ 2 / 8) := by
  have hterm : ∀ n : ℕ, Bf n n ^ 2 ≤ 9 * (1 / (2 * (n:ℝ) + 1) ^ 2) := by
    intro n
    have h0 := Bf_diag_nonneg n
    have h3 := Bf_diag_le_three n
    have hq : (0:ℝ) < (2 * (n:ℝ) + 1) ^ 2 := by positivity
    have hle1 : (1:ℝ) / (2 * (n:ℝ) + 1) ^ 2 ≤ 1 := by
      rw [div_le_one hq]; nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hp : (0:ℝ) ≤ 1 / (2 * (n:ℝ) + 1) ^ 2 := by positivity
    calc Bf n n ^ 2 ≤ (3 * (1 / (2 * (n:ℝ) + 1) ^ 2)) ^ 2 := pow_le_pow_left₀ h0 h3 2
      _ = 9 * ((1 / (2 * (n:ℝ) + 1) ^ 2) * (1 / (2 * (n:ℝ) + 1) ^ 2)) := by ring
      _ ≤ 9 * ((1 / (2 * (n:ℝ) + 1) ^ 2) * 1) := by gcongr
      _ = 9 * (1 / (2 * (n:ℝ) + 1) ^ 2) := by ring
  calc ∑ n ∈ Finset.range K, Bf n n ^ 2
      ≤ ∑ n ∈ Finset.range K, 9 * (1 / (2 * (n:ℝ) + 1) ^ 2) :=
        Finset.sum_le_sum (fun n _ => hterm n)
    _ = 9 * ∑ n ∈ Finset.range K, 1 / (2 * (n:ℝ) + 1) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 9 * (Real.pi ^ 2 / 8) := by
        have := odd_sq_sum_le K; linarith

/-! ### 八、拼装：`‖A‖²_HS < ∞`、`‖B‖²_HS < ∞`、`∑ B_nn < ∞`（Lemma A.1 的三条有限性） -/

/-- 双重方框和的拆分：对角 + 非对角。 -/
lemma sum_sq_split (g : ℕ → ℕ → ℝ) (K : ℕ) :
    ∑ n ∈ Finset.range K, ∑ m ∈ Finset.range K, g n m ^ 2
      = ∑ n ∈ Finset.range K, g n n ^ 2
        + ∑ n ∈ Finset.range K, ∑ m ∈ Finset.range K, (if n ≠ m then g n m ^ 2 else 0) := by
  have hsplit : ∀ n m, g n m ^ 2
      = (if n = m then g n n ^ 2 else 0) + (if n ≠ m then g n m ^ 2 else 0) := by
    intro n m
    by_cases h : n = m
    · subst h; simp
    · simp [h]
  rw [Finset.sum_congr rfl (fun n _ => Finset.sum_congr rfl (fun m _ => hsplit n m))]
  simp only [Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl; intro n hn
  rw [Finset.sum_ite_eq, if_pos hn]

/-- 每个有限子集上的和 `≤ c` ⇐ 每个方框 `range K × range K` 上的和 `≤ c`（非负项）。 -/
lemma finset_sum_le_of_sq_sums_le (f : ℕ × ℕ → ℝ) (hf : ∀ p, 0 ≤ f p) (c : ℝ)
    (hK : ∀ K, ∑ n ∈ Finset.range K, ∑ m ∈ Finset.range K, f (n, m) ≤ c) (s : Finset (ℕ × ℕ)) :
    ∑ p ∈ s, f p ≤ c := by
  obtain ⟨K, hK'⟩ : ∃ K, s ⊆ Finset.range K ×ˢ Finset.range K := by
    refine ⟨(s.image Prod.fst).sup id + (s.image Prod.snd).sup id + 1, ?_⟩
    intro p hp
    simp only [Finset.mem_product, Finset.mem_range]
    constructor
    · have := Finset.le_sup (f := id) (Finset.mem_image_of_mem Prod.fst hp)
      simp only [id] at this; omega
    · have := Finset.le_sup (f := id) (Finset.mem_image_of_mem Prod.snd hp)
      simp only [id] at this; omega
  calc ∑ p ∈ s, f p ≤ ∑ p ∈ Finset.range K ×ˢ Finset.range K, f p :=
        Finset.sum_le_sum_of_subset_of_nonneg hK' (fun p _ _ => hf p)
    _ = ∑ n ∈ Finset.range K, ∑ m ∈ Finset.range K, f (n, m) := Finset.sum_product _ _ _
    _ ≤ c := hK K

/-- 方框和一致有界 ⇒ `ℕ × ℕ` 上可和。 -/
lemma summable_of_sq_sums_le (f : ℕ × ℕ → ℝ) (hf : ∀ p, 0 ≤ f p) (c : ℝ)
    (hK : ∀ K, ∑ n ∈ Finset.range K, ∑ m ∈ Finset.range K, f (n, m) ≤ c) : Summable f :=
  summable_of_sum_le hf (finset_sum_le_of_sq_sums_le f hf c hK)

/-- `AF` 就是库内 `O[k⁻²]` 的矩阵元（与 (A.1) 一致）。 -/
lemma AF_eq_Of (n m : ℕ) : AF n m = Of (fun k => 1 / (k:ℝ) ^ 2) n m := by
  rw [Of_invSq]; unfold AF KA
  by_cases h : n = m
  · subst h
    simp only [ite_true, ne_eq, not_true_eq_false, ite_false, add_zero]
    ring
  · simp only [h, ite_false, ne_eq, not_false_eq_true, ite_true, sub_zero]
    ring

/-- **`A` 的 HS 界**：`∑_{n,m<K} A²_{nm} ≤ 4ζ(2)²·ζ(2) + 4·(π²/8)·3ζ(4)`，对一切 `K`。 -/
theorem AF_HS_sq_le (K : ℕ) :
    ∑ n ∈ Finset.range K, ∑ m ∈ Finset.range K, AF n m ^ 2
      ≤ 4 * (Real.pi ^ 2 / 6) ^ 2 * (Real.pi ^ 2 / 6)
        + 4 * ((Real.pi ^ 2 / 8) * (2 * zetaFour) + (Real.pi ^ 2 / 8) * zetaFour) := by
  rw [sum_sq_split]
  have hd : ∑ n ∈ Finset.range K, AF n n ^ 2 ≤ 4 * (Real.pi ^ 2 / 6) ^ 2 * (Real.pi ^ 2 / 6) := by
    calc ∑ n ∈ Finset.range K, AF n n ^ 2
        ≤ ∑ n ∈ Finset.range K, 4 * (Real.pi ^ 2 / 6) ^ 2 * u n ^ 4 :=
          Finset.sum_le_sum (fun n _ => AF_diag_sq_le n)
      _ = 4 * (Real.pi ^ 2 / 6) ^ 2 * ∑ n ∈ Finset.range K, u n ^ 4 := by rw [Finset.mul_sum]
      _ ≤ 4 * (Real.pi ^ 2 / 6) ^ 2 * (Real.pi ^ 2 / 6) :=
          mul_le_mul_of_nonneg_left (sum_u_pow_four_le K) (by positivity)
  have ho := AF_offdiag_sum_le K
  linarith

/-- **`B` 的 HS 界**：`∑_{n,m<K} B²_{nm} ≤ 9π²/8 + 16ζ(4)²`，对一切 `K`。 -/
theorem BF_HS_sq_le (K : ℕ) :
    ∑ n ∈ Finset.range K, ∑ m ∈ Finset.range K, Bf n m ^ 2
      ≤ 9 * (Real.pi ^ 2 / 8) + (4 * zetaFour) * (4 * zetaFour) := by
  rw [sum_sq_split]
  have hd := BF_diag_sq_le K
  have ho := BF_offdiag_sum_le K
  linarith

/-- **Lemma A.1 (A)**：`‖A‖²_HS = ∑_{n,m≥0} A²_{nm} < ∞`（以 `ℕ × ℕ` 上可和陈述）。 -/
theorem AF_HS_summable : Summable (fun p : ℕ × ℕ => AF p.1 p.2 ^ 2) :=
  summable_of_sq_sums_le _ (fun _ => sq_nonneg _) _ (fun K => AF_HS_sq_le K)

/-- 同上，写成库内算子 `O[k⁻²]` 的矩阵元。 -/
theorem Of_invSq_HS_summable :
    Summable (fun p : ℕ × ℕ => Of (fun k => 1 / (k:ℝ) ^ 2) p.1 p.2 ^ 2) := by
  have h := AF_HS_summable
  simp only [AF_eq_Of] at h
  exact h

/-- **Lemma A.1 (B)**：`‖B‖²_HS = ∑_{n,m≥0} B²_{nm} < ∞`。 -/
theorem BF_HS_summable : Summable (fun p : ℕ × ℕ => Bf p.1 p.2 ^ 2) :=
  summable_of_sq_sums_le _ (fun _ => sq_nonneg _) _ (fun K => BF_HS_sq_le K)

/-- **Lemma A.1 (B, 迹)**：`∑_{n≥0} B_{nn} < ∞`。 -/
theorem BF_diag_summable : Summable (fun n => Bf n n) :=
  summable_of_sum_range_le Bf_diag_nonneg BF_diag_le

/-- `‖A‖²_HS` 的显式上界（论文的对应常数是 `4ζ(2)²·π²/8 + 2·(π²/8)·3ζ(4) ≈ 21.36`）。 -/
theorem AF_HS_tsum_le :
    ∑' p : ℕ × ℕ, AF p.1 p.2 ^ 2
      ≤ 4 * (Real.pi ^ 2 / 6) ^ 2 * (Real.pi ^ 2 / 6)
        + 4 * ((Real.pi ^ 2 / 8) * (2 * zetaFour) + (Real.pi ^ 2 / 8) * zetaFour) :=
  Real.tsum_le_of_sum_le (fun _ => sq_nonneg _)
    (finset_sum_le_of_sq_sums_le _ (fun _ => sq_nonneg _) _ (fun K => AF_HS_sq_le K))

/-- `‖B‖²_HS` 的显式上界。 -/
theorem BF_HS_tsum_le :
    ∑' p : ℕ × ℕ, Bf p.1 p.2 ^ 2 ≤ 9 * (Real.pi ^ 2 / 8) + (4 * zetaFour) * (4 * zetaFour) :=
  Real.tsum_le_of_sum_le (fun _ => sq_nonneg _)
    (finset_sum_le_of_sq_sums_le _ (fun _ => sq_nonneg _) _ (fun K => BF_HS_sq_le K))

/-- `∑ B_nn` 的显式上界：`tr B ≤ 3π²/8`。 -/
theorem BF_diag_tsum_le : ∑' n : ℕ, Bf n n ≤ 3 * (Real.pi ^ 2 / 8) :=
  BF_diag_summable.tsum_le_of_sum_range_le BF_diag_le

end Eliashberg
