import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! 论文 §5.2 第 (2)、(3) 条的「原则」部分，若硬要形式化，就是下面这几行。
它们不涉及论文的任何数学对象，也不是论文自陈的定理；放进主库只会用空洞声明充数。 -/

/-- §5.2(3)「provably vacuous guard」：参考值与被测值走同一条确定性代码路径 ⇒ 检查恒真，
即什么都查不出来。证明就是 `rfl`。 -/
theorem guard_vacuous {α β : Type*} (f : α → β) (x : α) : f x = f x := rfl

/-- §5.2(2)「pad 必须 ≥ 它要替代的误差」：`|c − t| ≤ ε`、`ε ≤ pad` ⇒ 真值 `t` 落在 `[c − pad, c + pad]`。 -/
theorem pad_covers {c t ε pad : ℝ} (h : |c - t| ≤ ε) (hp : ε ≤ pad) :
    t ∈ Set.Icc (c - pad) (c + pad) := by
  rw [abs_le] at h; rw [Set.mem_Icc]; constructor <;> linarith [h.1, h.2]

/-- §5.2(2) 的具体数字：`2.3 × 10⁻⁴¹ < 4.8 × 10⁻¹⁷`，差 41 个数量级。 -/
theorem pad_too_small : (23 : ℝ) / 10 ^ 42 < 48 / 10 ^ 18 := by norm_num
