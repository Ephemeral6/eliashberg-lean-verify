import Eliashberg.Compact
import Eliashberg.LemmaM
import Eliashberg.ConeLimit

/-!
# 零延拓 `extN` 与截断投影 `P_N` 的桥（task-577）

本文件把 `Fin N → ℝ` 上的有限维对象（`InConeN`、矩阵 `O^{(N)}[f]`）与
`ℓ²` 上的对象（`InCone`、`PN`、`extN`）对接起来。它们是 Proposition 1.11
（半群保锥）从有限维过渡到 `ℓ²` 的接口。

| 定理 | 内容 |
|---|---|
| `padN_eq_sum_single` | `P_N (extN v) = ∑_{i : Fin N} e_i (v i)` |
| `extN_injective` | `extN` 单射 |
| `padN_inCone_of_inConeN` | **锥的嵌入**：`InConeN v ⇒ InCone (P_N (extN v))` |
| `truncFn`、`truncFn_inConeN` | `x ∈ C` 的 `Fin N` 截断仍在 `C_N` |
| `PN_idem`、`PN_extN_truncFn` | `P_N` 幂等；`P_N (extN (truncFn x N)) = P_N x` |
-/

set_option maxHeartbeats 800000

namespace Eliashberg

open scoped BigOperators ENNReal

noncomputable section

/-! ### 一、`P_N ∘ extN` 是「按 `Fin N` 的单项和」 -/

/-- `P_N (extN v) = ∑_{i : Fin N} e_i (v i)`：零延拓后再截断，就是 `Fin N` 上的单项和。
逐坐标证明（`PN_eq_sum_single` 需要 `H` 的元素，而 `extN v` 只是数列）。 -/
theorem padN_eq_sum_single (N : ℕ) (v : Fin N → ℝ) :
    PN (extN v) N = ∑ i : Fin N, lp.single 2 (i : ℕ) (v i) := by
  apply lp.ext
  funext n
  rw [lp.coeFn_sum, PN_apply]
  by_cases h : n < N
  · rw [if_pos h, extN, dite_eq_left h, Finset.sum_apply,
      Finset.sum_eq_single (⟨n, h⟩ : Fin N)]
    · rw [lp.single_apply_self]
    · intro b _ hb
      rw [lp.single_apply_ne]
      intro hc
      exact hb (Fin.ext hc.symm)
    · intro hn
      exact absurd (Finset.mem_univ (⟨n, h⟩ : Fin N)) hn
  · rw [if_neg h, Finset.sum_apply, Finset.sum_eq_zero]
    intro i _
    rw [lp.single_apply_ne]
    intro hc
    exact h (hc ▸ i.isLt)

/-- `extN` 单射。 -/
lemma extN_injective {N : ℕ} : Function.Injective (extN : (Fin N → ℝ) → ℕ → ℝ) := by
  intro u v huv
  funext i
  have h := congrFun huv i.val
  simpa [extN, dite_eq_left i.isLt] using h

/-! ### 二、锥的嵌入 -/

/-- **锥的嵌入**：`InConeN v ⇒ InCone (P_N (extN v))`。这是 `SemigroupCone.lean`
里把有限维结论推到 `ℓ²` 的那个接口。 -/
lemma padN_inCone_of_inConeN {N : ℕ} {v : Fin N → ℝ} (hv : InConeN v) :
    InCone (PN (extN v) N) := by
  refine ⟨fun n => ?_, fun i j hij => ?_⟩
  · by_cases h : n < N
    · rw [PN_apply_of_lt _ _ _ h]
      unfold extN; rw [dite_eq_left h]; exact hv.2 ⟨n, h⟩
    · rw [PN_apply_of_ge _ _ _ (by omega)]
  · by_cases hj : j < N
    · have hi : i < N := by omega
      rw [PN_apply_of_lt _ _ _ hi, PN_apply_of_lt _ _ _ hj]
      unfold extN; rw [dite_eq_left hi, dite_eq_left hj]
      exact hv.1 ⟨i, hi⟩ ⟨j, hj⟩ (by rw [Fin.le_def]; exact hij)
    · rw [PN_apply_of_ge _ _ _ (by omega)]
      by_cases hi : i < N
      · rw [PN_apply_of_lt _ _ _ hi]
        unfold extN; rw [dite_eq_left hi]; exact hv.2 ⟨i, hi⟩
      · rw [PN_apply_of_ge _ _ _ (by omega)]

/-! ### 三、`ℓ²` 元素的截断 -/

/-- `x` 的 `Fin N` 截断。 -/
def truncFn (x : H) (N : ℕ) : Fin N → ℝ := fun i => (x : ℕ → ℝ) i.val

/-- `x ∈ C` ⇒ 其 `Fin N` 截断 `∈ C_N`。 -/
lemma truncFn_inConeN {x : H} (hx : InCone x) (N : ℕ) : InConeN (truncFn x N) :=
  ⟨fun i j hij => hx.2 i.val j.val (by rw [Fin.le_def] at hij; exact hij),
   fun i => hx.1 i.val⟩

/-- `PN` 幂等。 -/
lemma PN_idem (v : ℕ → ℝ) (N : ℕ) : PN (((PN v N : H)) : ℕ → ℝ) N = PN v N := by
  apply lp.ext
  funext n
  rw [PN_apply, PN_apply]
  by_cases h : n < N
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

/-- `P_N (extN (truncFn x N)) = P_N x`。 -/
lemma PN_extN_truncFn (x : H) (N : ℕ) : PN (extN (truncFn x N)) N = PN (x : ℕ → ℝ) N := by
  have h : extN (truncFn x N) = ((PN (x : ℕ → ℝ) N : H) : ℕ → ℝ) := by
    funext n
    by_cases hn : n < N
    · rw [extN, dite_eq_left hn]
      exact (PN_apply_of_lt (x : ℕ → ℝ) N n hn).symm
    · rw [extN, dite_eq_right hn]
      exact (PN_apply_of_ge (x : ℕ → ℝ) N n (by omega)).symm
  rw [h]
  exact PN_idem (x : ℕ → ℝ) N

end

end Eliashberg
