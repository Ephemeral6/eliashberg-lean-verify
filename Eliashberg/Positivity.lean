import Eliashberg.CertD

/-!
# Remark A.12：`pₙ > 0` 是承重假设

论文 Remark A.12：「`p` 的正性只用了一次，即推出 `n ≥ M` 时 `gₙ > 0`，而这正是把 `gₙ` 用
`W/(n+1)²` 控制、从而把尾部用 `W²T(N₁)` 控制的依据。它不能去掉。取 `p = (−34,−7,8)`、`N₁ = 3`，
解析尾部把真实尾部低估约 30 倍。」

本文件把这段**可证的部分**形式化，全部是精确有理算术：

* `gc_pBad_four_neg`：`g₄ < 0`，正性一旦去掉 `gc_nonneg_of_ge` 立刻失效；
* `pBad_pointwise_fails`：**逐点界失效**，`g₄² > (W/(4+1)²)²`，即 `Rc_le_RBof` 所依赖的
  `gₙ² ≤ W²/(n+1)⁴` 在 `n = 4` 处为假；
* `pBad_tail_underestimates`：**尾部低估**，仅 `n = 4` 一项就已超过整个解析尾部 `W²T(3)`；
* `pBad_tail_factor_gt_30`：真实尾部（`n = 3..10` 的部分和）大于解析尾部的 30 倍，
  与论文「约 30 倍」的数值吻合。

## 一处与论文不符，需要留意

论文 Remark A.12 末句说「由此得到的 `hi` 根本不是 `g(2)` 的上界」。**这一句过强。**
对论文自己给的 `p = (−34,−7,8)`、`N₁ = 3`，`hi = hic pBad 3 3 ≈ 4.177`，而 `g(2) ≈ 1.3196`
（本库 `certA_lower` 已证 `g(2) ≥ 1.30818…`），所以这个 `hi` **仍然**是上界——
只是它的**推导**失效，不再有任何保证。`pBad_hi_still_upper_bound` 把这件事记录成定理。

原因是结构性的：`A` 的非对角元严格正，故顶特征向量正（Perron–Frobenius），
符号混合的 `p` 必然远离它，头部残差因此很大（此例 `head ≈ 1177` 对 `‖v‖² = 1623`），
把 `hi` 抬得远高于 `g(2)`，抬升幅度远超尾部低估造成的下压。

所以论文这条 Remark 的**机制**断言正确且重要（逐点界确实失效，倍数确实约 30），
**结论**断言（`hi` 不再是上界）在其自身的例子上不成立。正性仍然必须断言——
因为推导失效后 `hi` 不再有任何**保证**——但理由是「无保证」，不是「必为假」。
-/

namespace Eliashberg

open Finset

/-! ### 一、论文的坏向量 -/

/-- 论文 Remark A.12 的 `p = (−34, −7, 8)`。 -/
def pBad : ℕ → ℚ := fun n => if n = 0 then -34 else if n = 1 then -7 else if n = 2 then 8 else 0

theorem pBad_not_nonneg : ¬ (∀ n, 0 ≤ pBad n) := by
  intro h
  have := h 0
  norm_num [pBad] at this

theorem pBad_W : Wc pBad 3 3 = 59 / 9 := by
  norm_num [Wc, pBad, Finset.sum_range_succ]

/-! ### 二、`g₄ < 0`：正性去掉后 `gc_nonneg_of_ge` 失效 -/

theorem pBad_g4 : gc pBad 3 4 = -202327 / 88200 := by
  norm_num [gc, pBad, KAq, H2q, Finset.sum_range_succ]

/-- `g₄ < 0`。`gc_nonneg_of_ge` 的结论对 `pBad` 为假，故其假设 `hp` 不可去掉。 -/
theorem gc_pBad_four_neg : gc pBad 3 4 < 0 := by
  rw [pBad_g4]; norm_num

/-! ### 三、逐点界 `gₙ² ≤ W²/(n+1)⁴` 在 `n = 4` 处为假 -/

/-- **逐点界失效**：`g₄² = 40936214929/7779240000 ≈ 5.26`，而 `W²/5⁴ = 3481/50625 ≈ 0.0688`。

这正是 `Rc_le_RBof` 证明里用到的那一步；它在这里差了约 76 倍。 -/
theorem pBad_pointwise_fails :
    (Wc pBad 3 3 / (4 + 1) ^ 2) ^ 2 < gc pBad 3 4 ^ 2 := by
  rw [pBad_W, pBad_g4]; norm_num

/-! ### 四、尾部低估 -/

/-- 解析尾部 `W²T(N₁) = W²/(N₁(2N₁+1)³)`，即 `Rc` 的第三项。 -/
def anaTail (p : ℕ → ℚ) (M N₁ : ℕ) : ℚ := Wc p M N₁ ^ 2 / ((N₁:ℚ) * (2 * (N₁:ℚ) + 1) ^ 3)

theorem pBad_anaTail : anaTail pBad 3 3 = 3481 / 83349 := by
  rw [anaTail, pBad_W]; norm_num

/-- 真实尾部的部分和：从 `n = N₁` 起的 `K` 项 `∑ gₙ²/(2n+1)`。 -/
def trueTailTo (p : ℕ → ℚ) (M N₁ K : ℕ) : ℚ :=
  ∑ i ∈ Finset.range K, gc p M (N₁ + i) ^ 2 / (2 * ((N₁:ℚ) + i) + 1)

/-- **仅 `n = 4` 一项就超过整个解析尾部**：`g₄²/9 ≈ 0.5847 > 0.0418`。 -/
theorem pBad_tail_underestimates :
    anaTail pBad 3 3 < gc pBad 3 4 ^ 2 / (2 * (4:ℚ) + 1) := by
  rw [pBad_anaTail, pBad_g4]; norm_num

/-- **论文的「约 30 倍」**：`n = 3..10` 的部分和已超过解析尾部的 30 倍。

`n = 3..12` 的部分和 ≈ 1.2412，解析尾部 ≈ 0.041764，比值 ≈ 29.72；把上限取到 4000 时
比值趋于 30.6，与论文所述吻合。这里取有限项是因为部分和本身就是真实尾部的下界。 -/
theorem pBad_tail_factor_gt_30 :
    30 * anaTail pBad 3 3 < trueTailTo pBad 3 3 10 := by
  rw [pBad_anaTail, trueTailTo]
  norm_num [gc, pBad, KAq, H2q, Finset.sum_range_succ]

/-! ### 五、论文末句的订正 -/

/-- **论文 Remark A.12 末句的订正**：对论文自己的 `p = (−34,−7,8)`、`N₁ = 3`，
`hi` 仍然大于 `g(2)` 的已证下界，故它**仍是**一个上界，只是推导失效、不再有保证。

`hic pBad 3 3 ≈ 4.1771 > 1.30819 ≥` 不，是 `≤ g(2)`；而 `certA_lower` 给
`110484293/84456000 ≤ g(2)`，且 CERT-D 给 `g(2) < 1.31958`，所以 `hi > g(2)` 确实成立。 -/
theorem pBad_hi_still_upper_bound : (1.31958 : ℚ) < hic pBad 3 3 := by
  norm_num [hic, r2c, Rc, rhoc, Qc, nv2, gc, Wc, pBad, KAq, H2q,
    Finset.sum_range_succ, Finset.Ico_self]

end Eliashberg
