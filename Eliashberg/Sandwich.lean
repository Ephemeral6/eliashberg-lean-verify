import Eliashberg.Compact
import Eliashberg.LemmaM

/-!
# 截断三明治 `P_N O[f] P_N`（`N → ∞`）

论文 §1.3–§2 反复使用 `N × N` 截断 `O^{(N)}[F] := P_N O[F] P_N`，并在 `N → ∞` 时过渡到
`ℓ²` 上的 `O[F]`（Corollary 2.4(iv)：`k^{(N)} → k`）。本文件提供这个过渡所需的三块：

| 定理 | 内容 |
|---|---|
| **`PNclm_isSelfAdjoint`** | `P_N = ∑_{m<N} e_m ⊗ e_m^*` 自伴 |
| **`sandwich_tendsto`** | `P_N O[f] P_N → O[f]`（算子范数），且显式界 `‖O − S_N‖ ≤ 2√τ_N` |
| **`sandwich_apply_pad`** | 在 `P_N` 的像上，三明治就是有限矩阵 `O^{(N)}[f]` 的作用 |

## 证明思路

`P_N` 自伴：`P_N` 的坐标形式是逐点截断，两边内积都塌缩成 `∑_{n<N} x_n y_n`（`tsum_eq_sum`）。

三明治收敛：`O − P_N O P_N = (O − O P_N) + (O − P_N O) P_N`，
而 `O − P_N O = (O − O P_N)†`（`O`、`P_N` 自伴 + `adjoint_comp`），故两项范数相等，
各 `≤ ‖O − O P_N‖ = ‖O − O_N‖ ≤ √τ_N`；再用 `tailHS_tendsto_zero`。

三明治在 `P_N` 像上是 `N × N` 矩阵：逐坐标算，`P_N` 幂等使内层坍缩，
`Op_PN_apply` 与 `Matrix.mulVec`/`dotProduct` 的展开逐项对上（`extN_fin`）。
-/

namespace Eliashberg

open scoped BigOperators ENNReal Matrix
open Filter Topology

noncomputable section

variable {f : ℕ → ℝ}

/-! ### 一、`P_N` 自伴 -/

/-- `P_N` 作用两次等于作用一次（逐点截断幂等）。 -/
lemma PN_PN (v : ℕ → ℝ) (N : ℕ) : PN ((PN v N : H) : ℕ → ℝ) N = PN v N := by
  apply lp.ext; funext n
  rw [PN_apply, PN_apply]
  by_cases h : n < N <;> simp [h]

lemma PNclm_idem_apply (N : ℕ) (x : H) : PNclm N (PNclm N x) = PNclm N x := by
  rw [PNclm_apply, PNclm_apply, PN_PN]

/-- `‖P_N x‖ ≤ ‖x‖`（截断只丢坐标）。 -/
lemma PNclm_apply_norm_le (N : ℕ) (x : H) : ‖PNclm N x‖ ≤ ‖x‖ := by
  have hcoord : ∀ n : ℕ, (((PNclm N x : H)) : ℕ → ℝ) n
      = if n < N then (x : ℕ → ℝ) n else 0 := by
    intro n
    rw [PNclm_apply, PN_apply]
  have h : ‖PNclm N x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [H_norm_sq, H_norm_sq]
    calc ∑' n : ℕ, (((PNclm N x : H)) : ℕ → ℝ) n ^ 2
        = ∑' n : ℕ, (if n < N then (x : ℕ → ℝ) n else 0) ^ 2 :=
          tsum_congr (fun n => by rw [hcoord n])
      _ = ∑ n ∈ Finset.range N, (if n < N then (x : ℕ → ℝ) n else 0) ^ 2 :=
          tsum_eq_sum (s := Finset.range N) (fun n hn => by
            rw [Finset.mem_range, not_lt] at hn
            simp [hn])
      _ ≤ ∑' n : ℕ, (x : ℕ → ℝ) n ^ 2 := by
          have hfin : ∑ n ∈ Finset.range N, (if n < N then (x : ℕ → ℝ) n else 0) ^ 2
              = ∑ n ∈ Finset.range N, (x : ℕ → ℝ) n ^ 2 := by
            apply Finset.sum_congr rfl; intro n hn
            rw [ite_eq_left (Finset.mem_range.mp hn)]
          rw [hfin]
          exact Summable.sum_le_tsum (Finset.range N) (fun n _ => sq_nonneg _) (H_summable_sq x)
  exact pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero |>.mp h

/-- **`‖P_N‖ ≤ 1`**。 -/
lemma PNclm_norm_le_one (N : ℕ) : ‖PNclm N‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
    rw [one_mul]; exact PNclm_apply_norm_le N x)

/-- 左边内积的截断形式：`⟨P_N x, y⟩ = ∑_{n<N} x_n y_n`。 -/
lemma inner_PN_left (x y : H) (N : ℕ) :
    inner ℝ (PN (x : ℕ → ℝ) N) y
      = ∑ n ∈ Finset.range N, (x : ℕ → ℝ) n * (y : ℕ → ℝ) n := by
  rw [H_inner]
  rw [tsum_eq_sum (s := Finset.range N)]
  · apply Finset.sum_congr rfl; intro n hn
    rw [PN_apply_of_lt (x : ℕ → ℝ) N n (Finset.mem_range.mp hn)]
  · intro n hn
    rw [Finset.mem_range, not_lt] at hn
    rw [PN_apply_of_ge _ N n hn, zero_mul]

/-- 右边内积的截断形式：`⟨x, P_N y⟩ = ∑_{n<N} x_n y_n`。 -/
lemma inner_PN_right (x y : H) (N : ℕ) :
    inner ℝ x (PN (y : ℕ → ℝ) N)
      = ∑ n ∈ Finset.range N, (x : ℕ → ℝ) n * (y : ℕ → ℝ) n := by
  rw [H_inner]
  rw [tsum_eq_sum (s := Finset.range N)]
  · apply Finset.sum_congr rfl; intro n hn
    rw [PN_apply_of_lt (y : ℕ → ℝ) N n (Finset.mem_range.mp hn)]
  · intro n hn
    rw [Finset.mem_range, not_lt] at hn
    rw [PN_apply_of_ge _ N n hn, mul_zero]

/-- **`P_N` 自伴**（有限个秩一投影 `e_m ⊗ e_m^*` 之和，每个都自伴）。 -/
theorem PNclm_isSelfAdjoint (N : ℕ) : IsSelfAdjoint (PNclm N) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  change inner ℝ (PNclm N x) y = inner ℝ x (PNclm N y)
  rw [PNclm_apply, PNclm_apply, inner_PN_left, inner_PN_right]

/-! ### 二、`P_N O[f] P_N → O[f]`（算子范数） -/

/-- **`O[f] − P_N O[f] = (Op hf − OpN hf N)†`**（`O`、`P_N` 都自伴）。 -/
lemma sub_OpN_adjoint (hf : L1 f) (N : ℕ) :
    (Op hf - (Op hf).comp (PNclm N)).adjoint = Op hf - (PNclm N).comp (Op hf) := by
  rw [map_sub, ContinuousLinearMap.adjoint_comp,
    (Op_isSelfAdjoint hf).adjoint_eq, (PNclm_isSelfAdjoint N).adjoint_eq]

/-- 三明治与 `O[f]` 的差分解：`O − P O P = (O − O P) + (O − P O) P`。 -/
lemma sub_sandwich_eq (hf : L1 f) (N : ℕ) :
    Op hf - (PNclm N).comp ((Op hf).comp (PNclm N))
      = (Op hf - (Op hf).comp (PNclm N))
        + ((Op hf - (PNclm N).comp (Op hf)).comp (PNclm N)) := by
  ext x
  simp only [sub_apply, add_apply, ContinuousLinearMap.comp_apply]
  abel

/-- **显式界**：`‖O[f] − P_N O[f] P_N‖ ≤ 2√τ_N`。 -/
lemma opNorm_sub_sandwich_le (hf : L1 f) (N : ℕ) :
    ‖Op hf - (PNclm N).comp ((Op hf).comp (PNclm N))‖
      ≤ 2 * Real.sqrt (tailHS f N) := by
  have h1 : ‖Op hf - (PNclm N).comp (Op hf)‖
      = ‖Op hf - (Op hf).comp (PNclm N)‖ := by
    rw [← sub_OpN_adjoint hf N, ContinuousLinearMap.adjoint.norm_map]
  have h2 : ‖(Op hf - (PNclm N).comp (Op hf)).comp (PNclm N)‖
      ≤ ‖Op hf - (PNclm N).comp (Op hf)‖ := by
    calc ‖(Op hf - (PNclm N).comp (Op hf)).comp (PNclm N)‖
        ≤ ‖Op hf - (PNclm N).comp (Op hf)‖ * ‖PNclm N‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖Op hf - (PNclm N).comp (Op hf)‖ * 1 :=
          mul_le_mul_of_nonneg_left (PNclm_norm_le_one N) (norm_nonneg _)
      _ = ‖Op hf - (PNclm N).comp (Op hf)‖ := mul_one _
  have h3 : ‖Op hf - (Op hf).comp (PNclm N)‖ ≤ Real.sqrt (tailHS f N) :=
    opNorm_sub_OpN_le hf N
  calc ‖Op hf - (PNclm N).comp ((Op hf).comp (PNclm N))‖
      = ‖(Op hf - (Op hf).comp (PNclm N))
          + ((Op hf - (PNclm N).comp (Op hf)).comp (PNclm N))‖ := by
        rw [sub_sandwich_eq hf N]
    _ ≤ ‖Op hf - (Op hf).comp (PNclm N)‖
          + ‖(Op hf - (PNclm N).comp (Op hf)).comp (PNclm N)‖ := norm_add_le _ _
    _ ≤ Real.sqrt (tailHS f N) + ‖Op hf - (PNclm N).comp (Op hf)‖ :=
        add_le_add h3 h2
    _ = Real.sqrt (tailHS f N) + ‖Op hf - (Op hf).comp (PNclm N)‖ := by rw [h1]
    _ ≤ Real.sqrt (tailHS f N) + Real.sqrt (tailHS f N) := add_le_add le_rfl h3
    _ = 2 * Real.sqrt (tailHS f N) := by ring

/-- **`P_N O[f] P_N → O[f]`**（算子范数；论文 Corollary 2.4(iv) 的拓扑部分）。 -/
theorem sandwich_tendsto (hf : L1 f) :
    Tendsto (fun N => (PNclm N).comp ((Op hf).comp (PNclm N))) atTop (𝓝 (Op hf)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsqrt : Tendsto (fun N => Real.sqrt (tailHS f N)) atTop (𝓝 0) := by
    have := (tailHS_tendsto_zero hf).sqrt
    rwa [Real.sqrt_zero] at this
  have hg : Tendsto (fun N => 2 * Real.sqrt (tailHS f N)) atTop (𝓝 0) := by
    have := hsqrt.const_mul (2 : ℝ)
    simpa using this
  refine squeeze_zero_norm (fun N => ?_) hg
  rw [norm_norm, norm_sub_rev]
  exact opNorm_sub_sandwich_le hf N

/-! ### 三、三明治在 `P_N` 的像上是有限矩阵 `O^{(N)}[f]` -/

/-- `n < N` 时三明治的坐标：`∑_{m<N} O[f]_{nm} (extN v)_m`。 -/
lemma PNclm_PN_extN (N : ℕ) (v : Fin N → ℝ) :
    PNclm N (PN (extN v) N) = PN (extN v) N := by
  rw [PNclm_apply]; exact PN_PN (extN v) N

lemma sandwich_apply_pad_coord (hf : L1 f) (N : ℕ) (v : Fin N → ℝ) (n : ℕ) (hn : n < N) :
    (((PNclm N).comp ((Op hf).comp (PNclm N)) (PN (extN v) N) : H) : ℕ → ℝ) n
      = ∑ m ∈ Finset.range N, Of f n m * extN v m := by
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, PNclm_PN_extN,
    PNclm_apply, PN_apply]
  simp only [hn, ite_true]
  rw [Op_PN_apply]

/-- `O^{(N)}[f] v` 的零延拓坐标：`∑_{m<N} O[f]_{nm} (extN v)_m`。 -/
lemma extN_ON_mulVec (N : ℕ) (v : Fin N → ℝ) (n : ℕ) (hn : n < N) :
    extN ((ON f).mulVec v) n = ∑ m ∈ Finset.range N, Of f n m * extN v m := by
  rw [extN_fin (v := (ON f).mulVec v) (i := ⟨n, hn⟩), Matrix.mulVec, dotProduct,
    ← Fin.sum_univ_eq_sum_range (fun m => Of f n m * extN v m) N]
  apply Finset.sum_congr rfl; intro m _
  rw [extN_fin]; rfl

/-- **三明治在 `P_N` 的像上就是有限矩阵 `O^{(N)}[f]`**：
`P_N O[f] P_N (P_N extN v) = P_N (extN (O^{(N)}[f] v))`。 -/
theorem sandwich_apply_pad (hf : L1 f) (N : ℕ) (v : Fin N → ℝ) :
    (PNclm N).comp ((Op hf).comp (PNclm N)) (PN (extN v) N)
      = PN (extN ((ON f).mulVec v)) N := by
  apply lp.ext; funext n
  rw [PN_apply]
  by_cases hn : n < N
  · rw [ite_eq_left hn]
    rw [sandwich_apply_pad_coord hf N v n hn, extN_ON_mulVec N v n hn]
  · rw [ite_eq_right hn]
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, PNclm_PN_extN,
      PNclm_apply, PN_apply_of_ge _ N n (Nat.le_of_not_lt hn)]

end

end Eliashberg
