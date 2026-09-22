import Eliashberg.Enclosure

/-!
# CERT-D（`M = 200`、`N₁ = 500`）：论文 (†) `1.318140211762671 ≤ g(2) ≤ 1.318140212373478`

论文 §B.4–B.5 印出 200 个整数 `p₀,…,p₁₉₉` 与 `N₁ = 500`。直接在 `ℚ` 上让 Lean 内核精确计算 (A.4)–(A.5)
需要约 10⁵ 次有理数运算（每次约 5 ms，且分子分母上千位），不可行。本文件改用**整数区间算术**：

* 取 `S := 10⁴⁰`。每个核项 `p_n p_m K(n,m)` 与 `H_n^{(2)}` 都夹在两个 `ℕ` 除法（向下取整）之间：
  `⌊a/b⌋ ≤ a/b < ⌊a/b⌋ + 1`（`natDiv_le`、`lt_natDiv_add_one`）。
* 于是 `ρ ∈ [rhoLo, rhoHi]`、`g_n ∈ [gLo n, gHi n]`，其中所有区间端点都是「`ℕ` 求和 / S」，
  求和用结构递归 `sumTo`（内核求值比 `Finset.sum` 快一个量级）。
* 通用引理 `Rc_le_RBof`、`hic_le_hiBof`：只要 `rl ≤ ρ ≤ rh`、`gl ≤ g ≤ gh`，就有
  `R ≤ RBof`、`ρ + r²/(ρ−13/25) ≤ hiBof`（头部用 `a ≤ x ≤ b ⇒ x² ≤ a² + b²`）。
* 数值事实 `certD_rhoLo`、`certD_hiB` 由 `decide +kernel` 精确验证。

最终 **`certD_g2`** 就是论文的 (†)，**`Cinf_enclosure`** 是 Cor 2.4(iii) 的
`C_∞ ∈ [0.182726247746, 0.182726247790]`（用 mathlib 的 20 位 `π` 界）。
-/

namespace Eliashberg

open scoped BigOperators
open Finset

/-! ### 结构递归求和与整数取整 -/

/-- `sumTo f n = ∑_{k<n} f k`，结构递归版。 -/
def sumTo (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => sumTo f n + f n

lemma sumTo_eq (f : ℕ → ℕ) (n : ℕ) : sumTo f n = ∑ k ∈ range n, f k := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumTo, ih, sum_range_succ]

lemma natDiv_le (a b : ℕ) : ((a / b : ℕ) : ℚ) ≤ (a : ℚ) / b := Nat.cast_div_le

lemma lt_natDiv_add_one (a b : ℕ) (hb : 0 < b) : (a : ℚ) / b < ((a / b : ℕ) : ℚ) + 1 := by
  have hb' : (0:ℚ) < b := by exact_mod_cast hb
  rw [div_lt_iff₀ hb']
  have h1 : (a:ℚ) = b * ((a / b : ℕ) : ℚ) + ((a % b : ℕ) : ℚ) := by
    exact_mod_cast (Nat.div_add_mod a b).symm
  have h2 : ((a % b : ℕ) : ℚ) < b := by exact_mod_cast Nat.mod_lt a hb
  rw [h1]; linarith

lemma dist_sq_rat (n m : ℕ) : ((Nat.dist n m : ℕ) : ℚ) ^ 2 = ((n:ℚ) - m) ^ 2 := by
  rcases le_total n m with h | h
  · rw [Nat.dist_eq_sub_of_le h, Nat.cast_sub h]; ring
  · rw [Nat.dist_eq_sub_of_le_right h, Nat.cast_sub h]

lemma KAq_nonneg (n m : ℕ) : 0 ≤ KAq n m := by
  unfold KAq
  apply add_nonneg (by positivity)
  split_ifs <;> positivity

/-! ### 核项与调和数的整数区间 -/

/-- 核项的整数下界：`⌊a/(n+m+1)²⌋ + [n≠m]⌊a/(n−m)²⌋ ≤ a K(n,m)`。 -/
def ktfl (a n m : ℕ) : ℕ := a / (n + m + 1) ^ 2 + (if n ≠ m then a / (Nat.dist n m) ^ 2 else 0)

/-- 核项的整数上界（每个取整加 1）。 -/
def ktce (a n m : ℕ) : ℕ :=
  (a / (n + m + 1) ^ 2 + 1) + (if n ≠ m then a / (Nat.dist n m) ^ 2 + 1 else 0)

lemma ktfl_le (a n m : ℕ) : (ktfl a n m : ℚ) ≤ (a:ℚ) * KAq n m := by
  unfold ktfl KAq
  have h1 := natDiv_le a ((n + m + 1) ^ 2)
  have h2 := natDiv_le a ((Nat.dist n m) ^ 2)
  push_cast at h1 h2 ⊢
  rw [dist_sq_rat] at h2
  split_ifs
  · rw [show (a:ℚ) * (1 / ((n:ℚ) + m + 1) ^ 2 + 1 / ((n:ℚ) - m) ^ 2)
        = (a:ℚ) / ((n:ℚ) + m + 1) ^ 2 + (a:ℚ) / ((n:ℚ) - m) ^ 2 by ring]
    linarith
  · rw [add_zero, add_zero, show (a:ℚ) * (1 / ((n:ℚ) + m + 1) ^ 2) = (a:ℚ) / ((n:ℚ) + m + 1) ^ 2 by ring]
    exact h1

lemma le_ktce (a n m : ℕ) : (a:ℚ) * KAq n m ≤ ktce a n m := by
  unfold ktce KAq
  have h1 := (lt_natDiv_add_one a ((n + m + 1) ^ 2) (by positivity)).le
  push_cast at h1 ⊢
  split_ifs with hnm
  · have hd : 0 < (Nat.dist n m) ^ 2 := by
      have : 0 < Nat.dist n m := Nat.dist_pos_of_ne hnm
      positivity
    have h2 := (lt_natDiv_add_one a ((Nat.dist n m) ^ 2) hd).le
    push_cast at h2
    rw [dist_sq_rat] at h2
    rw [show (a:ℚ) * (1 / ((n:ℚ) + m + 1) ^ 2 + 1 / ((n:ℚ) - m) ^ 2)
        = (a:ℚ) / ((n:ℚ) + m + 1) ^ 2 + (a:ℚ) / ((n:ℚ) - m) ^ 2 by ring]
    linarith
  · rw [add_zero, add_zero, show (a:ℚ) * (1 / ((n:ℚ) + m + 1) ^ 2) = (a:ℚ) / ((n:ℚ) + m + 1) ^ 2 by ring]
    exact h1

section Bounds

variable (q : ℕ → ℕ) (S : ℕ)

/-- `⌊S H_n^{(2)}⌋` 的下界。 -/
def hfl (n : ℕ) : ℕ := sumTo (fun k => S / (k + 1) ^ 2) n

/-- 上界。 -/
def hce (n : ℕ) : ℕ := sumTo (fun k => S / (k + 1) ^ 2 + 1) n

lemma hfl_le (n : ℕ) : (hfl S n : ℚ) ≤ S * H2q n := by
  unfold hfl H2q
  rw [sumTo_eq, mul_sum]
  push_cast
  apply sum_le_sum; intro k _
  have := natDiv_le S ((k + 1) ^ 2)
  push_cast at this
  rw [show (S:ℚ) * (1 / ((k:ℚ) + 1) ^ 2) = (S:ℚ) / ((k:ℚ) + 1) ^ 2 by ring]
  exact this

lemma le_hce (n : ℕ) : S * H2q n ≤ hce S n := by
  unfold hce H2q
  rw [sumTo_eq, mul_sum]
  push_cast
  apply sum_le_sum; intro k _
  have := (lt_natDiv_add_one S ((k + 1) ^ 2) (by positivity)).le
  push_cast at this
  rw [show (S:ℚ) * (1 / ((k:ℚ) + 1) ^ 2) = (S:ℚ) / ((k:ℚ) + 1) ^ 2 by ring]
  exact this

variable (M : ℕ)

/-- `q` 的有理数化。 -/
def qQ : ℕ → ℚ := fun n => (q n : ℚ)

def QposLo : ℕ := sumTo (fun n => sumTo (fun m => ktfl (q n * q m * S) n m) M) M
def QposHi : ℕ := sumTo (fun n => sumTo (fun m => ktce (q n * q m * S) n m) M) M
def QnegLo : ℕ := sumTo (fun n => hfl S n * q n ^ 2) M
def QnegHi : ℕ := sumTo (fun n => hce S n * q n ^ 2) M

lemma S_mul_Qc : (S:ℚ) * Qc (qQ q) M
    = (∑ n ∈ range M, ∑ m ∈ range M, ((q n * q m * S : ℕ) : ℚ) * KAq n m)
      - 2 * ∑ n ∈ range M, (S:ℚ) * H2q n * (q n : ℚ) ^ 2 := by
  unfold Qc qQ
  rw [mul_sub, mul_left_comm, mul_sum, mul_sum]
  congr 1
  · apply sum_congr rfl; intro n _
    rw [mul_sum]
    apply sum_congr rfl; intro m _; push_cast; ring
  · congr 1
    apply sum_congr rfl; intro n _; ring

lemma QposLo_le :
    (QposLo q S M : ℚ) ≤ ∑ n ∈ range M, ∑ m ∈ range M, ((q n * q m * S : ℕ) : ℚ) * KAq n m := by
  unfold QposLo
  simp only [sumTo_eq]
  rw [Nat.cast_sum]
  apply sum_le_sum; intro n _
  rw [Nat.cast_sum]
  exact sum_le_sum (fun m _ => ktfl_le _ n m)

lemma le_QposHi :
    ∑ n ∈ range M, ∑ m ∈ range M, ((q n * q m * S : ℕ) : ℚ) * KAq n m ≤ (QposHi q S M : ℚ) := by
  unfold QposHi
  simp only [sumTo_eq]
  rw [Nat.cast_sum]
  apply sum_le_sum; intro n _
  rw [Nat.cast_sum]
  exact sum_le_sum (fun m _ => le_ktce _ n m)

lemma QnegLo_le : (QnegLo q S M : ℚ) ≤ ∑ n ∈ range M, (S:ℚ) * H2q n * (q n : ℚ) ^ 2 := by
  unfold QnegLo
  simp only [sumTo_eq]
  push_cast
  exact sum_le_sum (fun n _ => mul_le_mul_of_nonneg_right (hfl_le S n) (sq_nonneg _))

lemma le_QnegHi : ∑ n ∈ range M, (S:ℚ) * H2q n * (q n : ℚ) ^ 2 ≤ (QnegHi q S M : ℚ) := by
  unfold QnegHi
  simp only [sumTo_eq]
  push_cast
  exact sum_le_sum (fun n _ => mul_le_mul_of_nonneg_right (le_hce S n) (sq_nonneg _))

/-- `ρ` 的整数区间端点。 -/
def rhoLo : ℚ := ((QposLo q S M : ℚ) - 2 * QnegHi q S M) / (S * nv2 (qQ q) M)
def rhoHi : ℚ := ((QposHi q S M : ℚ) - 2 * QnegLo q S M) / (S * nv2 (qQ q) M)

lemma rhoLo_le (hS : 0 < S) (hnv : 0 < nv2 (qQ q) M) : rhoLo q S M ≤ rhoc (qQ q) M := by
  unfold rhoLo rhoc
  have hS' : (0:ℚ) < S := by exact_mod_cast hS
  rw [div_le_div_iff₀ (by positivity) hnv]
  have h1 := QposLo_le q S M
  have h2 := le_QnegHi q S M
  have e := S_mul_Qc q S M
  nlinarith [h1, h2, e, hnv]

lemma le_rhoHi (hS : 0 < S) (hnv : 0 < nv2 (qQ q) M) : rhoc (qQ q) M ≤ rhoHi q S M := by
  unfold rhoHi rhoc
  have hS' : (0:ℚ) < S := by exact_mod_cast hS
  rw [div_le_div_iff₀ hnv (by positivity)]
  have h1 := le_QposHi q S M
  have h2 := QnegLo_le q S M
  have e := S_mul_Qc q S M
  nlinarith [h1, h2, e, hnv]

/-- `g_n` 的整数区间端点。 -/
def gfl (n : ℕ) : ℕ := sumTo (fun m => ktfl (q m * S) n m) M
def gce (n : ℕ) : ℕ := sumTo (fun m => ktce (q m * S) n m) M
def gLo (n : ℕ) : ℚ := ((gfl q S M n : ℚ) - (if n < M then 2 * (hce S n : ℚ) * q n else 0)) / S
def gHi (n : ℕ) : ℚ := ((gce q S M n : ℚ) - (if n < M then 2 * (hfl S n : ℚ) * q n else 0)) / S

lemma S_mul_gc (n : ℕ) : (S:ℚ) * gc (qQ q) M n
    = (∑ m ∈ range M, ((q m * S : ℕ) : ℚ) * KAq n m) - (if n < M then 2 * (S * H2q n) * q n else 0) := by
  unfold gc qQ
  rw [mul_sub, mul_sum]
  congr 1
  · apply sum_congr rfl; intro m _; push_cast; ring
  · split_ifs <;> ring

lemma gLo_le (hS : 0 < S) (n : ℕ) : gLo q S M n ≤ gc (qQ q) M n := by
  unfold gLo
  have hS' : (0:ℚ) < S := by exact_mod_cast hS
  rw [div_le_iff₀ hS', mul_comm (gc (qQ q) M n) (S:ℚ), S_mul_gc]
  unfold gfl
  rw [sumTo_eq, Nat.cast_sum]
  have h1 := sum_le_sum (fun m (_ : m ∈ range M) => ktfl_le (q m * S) n m)
  have h2 : (if n < M then 2 * (S * H2q n) * (q n : ℚ) else 0)
      ≤ (if n < M then 2 * (hce S n : ℚ) * q n else 0) := by
    split_ifs
    · have := le_hce S n
      have hq : (0:ℚ) ≤ q n := Nat.cast_nonneg _
      nlinarith
    · exact le_rfl
  linarith

lemma le_gHi (hS : 0 < S) (n : ℕ) : gc (qQ q) M n ≤ gHi q S M n := by
  unfold gHi
  have hS' : (0:ℚ) < S := by exact_mod_cast hS
  rw [le_div_iff₀ hS', mul_comm (gc (qQ q) M n) (S:ℚ), S_mul_gc]
  unfold gce
  rw [sumTo_eq, Nat.cast_sum]
  have h1 := sum_le_sum (fun m (_ : m ∈ range M) => le_ktce (q m * S) n m)
  have h2 : (if n < M then 2 * (hfl S n : ℚ) * q n else 0)
      ≤ (if n < M then 2 * (S * H2q n) * (q n : ℚ) else 0) := by
    split_ifs
    · have := hfl_le S n
      have hq : (0:ℚ) ≤ q n := Nat.cast_nonneg _
      nlinarith
    · exact le_rfl
  linarith

/-! ### `R` 与 `hi` 的区间上界（通用） -/

/-- `a ≤ x ≤ b ⇒ x² ≤ a² + b²`。 -/
lemma sq_le_of_between {a b x : ℚ} (ha : a ≤ x) (hb : x ≤ b) : x ^ 2 ≤ a ^ 2 + b ^ 2 := by
  rcases le_or_gt 0 x with hx | hx
  · nlinarith
  · nlinarith

/-- 以 `ρ`、`g_n` 的区间端点写出的 `R` 的上界。 -/
def RBof (p : ℕ → ℚ) (M N₁ : ℕ) (rl rh : ℚ) (gl gh : ℕ → ℚ) : ℚ :=
  (∑ n ∈ range M, ((gl n - rh * (2 * (n:ℚ) + 1) * p n) ^ 2
      + (gh n - rl * (2 * (n:ℚ) + 1) * p n) ^ 2) / (2 * (n:ℚ) + 1))
    + (∑ n ∈ Ico M N₁, gh n ^ 2 / (2 * (n:ℚ) + 1))
    + Wc p M N₁ ^ 2 / ((N₁:ℚ) * (2 * (N₁:ℚ) + 1) ^ 3)

lemma gc_nonneg_of_ge (p : ℕ → ℚ) (M : ℕ) (hp : ∀ n, 0 ≤ p n) (n : ℕ) (hn : M ≤ n) :
    0 ≤ gc p M n := by
  unfold gc
  rw [if_neg (by omega), sub_zero]
  exact sum_nonneg (fun m _ => mul_nonneg (hp m) (KAq_nonneg n m))

theorem Rc_le_RBof (p : ℕ → ℚ) (M N₁ : ℕ) (hp : ∀ n, 0 ≤ p n) (rl rh : ℚ)
    (hrl : rl ≤ rhoc p M) (hrh : rhoc p M ≤ rh) (gl gh : ℕ → ℚ)
    (hgl : ∀ n, gl n ≤ gc p M n) (hgh : ∀ n, gc p M n ≤ gh n) :
    Rc p M N₁ ≤ RBof p M N₁ rl rh gl gh := by
  unfold Rc RBof
  gcongr with n hn n hn
  · -- 头部
    have hc : 0 ≤ (2 * (n:ℚ) + 1) * p n := mul_nonneg (by positivity) (hp n)
    have ha : gl n - rh * (2 * (n:ℚ) + 1) * p n ≤ gc p M n - rhoc p M * (2 * (n:ℚ) + 1) * p n := by
      have := mul_le_mul_of_nonneg_right hrh hc
      linarith [hgl n]
    have hb : gc p M n - rhoc p M * (2 * (n:ℚ) + 1) * p n ≤ gh n - rl * (2 * (n:ℚ) + 1) * p n := by
      have := mul_le_mul_of_nonneg_right hrl hc
      linarith [hgh n]
    exact sq_le_of_between ha hb
  · -- 中段：`0 ≤ g_n`
    exact gc_nonneg_of_ge p M hp n (mem_Ico.mp hn).1
  · exact hgh n

/-- Temple 上端点的区间上界。 -/
def hiBof (p : ℕ → ℚ) (M N₁ : ℕ) (rl rh : ℚ) (gl gh : ℕ → ℚ) : ℚ :=
  rh + (RBof p M N₁ rl rh gl gh / nv2 p M) / (rl - 13/25)

theorem hic_le_hiBof (p : ℕ → ℚ) (M N₁ : ℕ) (hp : ∀ n, 0 ≤ p n) (hnv : 0 < nv2 p M) (rl rh : ℚ)
    (hrl : rl ≤ rhoc p M) (hrh : rhoc p M ≤ rh) (hβ : 13/25 < rl) (gl gh : ℕ → ℚ)
    (hgl : ∀ n, gl n ≤ gc p M n) (hgh : ∀ n, gc p M n ≤ gh n) :
    hic p M N₁ ≤ hiBof p M N₁ rl rh gl gh := by
  unfold hic hiBof r2c
  have hR := Rc_le_RBof p M N₁ hp rl rh hrl hrh gl gh hgl hgh
  have hRc0 : 0 ≤ Rc p M N₁ := by
    unfold Rc
    have h1 : 0 ≤ ∑ n ∈ range M, (gc p M n - rhoc p M * (2 * (n:ℚ) + 1) * p n) ^ 2 / (2 * (n:ℚ) + 1) :=
      sum_nonneg (fun n _ => by positivity)
    have h2 : 0 ≤ ∑ n ∈ Ico M N₁, gc p M n ^ 2 / (2 * (n:ℚ) + 1) :=
      sum_nonneg (fun n _ => by positivity)
    have h3 : 0 ≤ Wc p M N₁ ^ 2 / ((N₁:ℚ) * (2 * (N₁:ℚ) + 1) ^ 3) := by positivity
    linarith
  have h1 : Rc p M N₁ / nv2 p M ≤ RBof p M N₁ rl rh gl gh / nv2 p M :=
    div_le_div_of_nonneg_right hR hnv.le
  have h0 : 0 ≤ Rc p M N₁ / nv2 p M := div_nonneg hRc0 hnv.le
  have hβ' : 0 < rl - 13/25 := by linarith
  have hβ'' : rl - 13/25 ≤ rhoc p M - 13/25 := by linarith
  have h2 : Rc p M N₁ / nv2 p M / (rhoc p M - 13/25)
      ≤ RBof p M N₁ rl rh gl gh / nv2 p M / (rl - 13/25) :=
    div_le_div₀ (h0.trans h1) h1 hβ' hβ''
  linarith

end Bounds

/-! ### CERT-D 的数据：论文 §B.5 的 200 个整数（逐行五个）与 `N₁ = 500` -/

/-- 论文 §B.5 印出的 `p₀,…,p₁₉₉`。 -/
def pDlist : List ℕ := [
  10000000000000, 2285743212000, 704052782643, 275040141549, 129192238759,
  69558548160, 41394255879, 26538090678, 18006353993, 12770489195,
  9383177145, 7096071865, 5496446941, 4344167189, 3493097358,
  2850847236, 2357059336, 1971165571, 1665211817, 1419508201,
  1219912623, 1056088810, 920362582, 806954753, 711456688,
  630465432, 561325803, 501945415, 450660211, 406135522,
  367292402, 333252221, 303294568, 276824967, 253349915,
  232457420, 213801707, 197091126, 182078515, 168553474,
  156336145, 145272154, 135228498, 126090170, 117757379,
  110143254, 103171930, 96776956, 90899961, 85489526,
  80500243, 75891904, 71628825, 67679257, 64014894,
  60610443, 57443256, 54493012, 51741447, 49172108,
  46770152, 44522166, 42416004, 40440653, 38586111,
  36843279, 35203870, 33660323, 32205731, 30833776,
  29538670, 28315106, 27158211, 26063504, 25026862,
  24044484, 23112865, 22228768, 21389201, 20591395,
  19832784, 19110990, 18423807, 17769184, 17145215,
  16550127, 15982266, 15440094, 14922175, 14427165,
  13953814, 13500948, 13067472, 12652358, 12254644,
  11873429, 11507864, 11157156, 10820557, 10497363,
  10186916, 9888591, 9601804, 9326002, 9060663,
  8805296, 8559437, 8322648, 8094513, 7874642,
  7662664, 7458226, 7260998, 7070663, 6886924,
  6709497, 6538113, 6372517, 6212467, 6057733,
  5908095, 5763346, 5623287, 5487731, 5356497,
  5229414, 5106320, 4987060, 4871485, 4759455,
  4650833, 4545492, 4443309, 4344165, 4247950,
  4154556, 4063879, 3975822, 3890291, 3807196,
  3726451, 3647974, 3571684, 3497507, 3425370,
  3355204, 3286941, 3220517, 3155871, 3092944,
  3031678, 2972021, 2913918, 2857320, 2802178,
  2748446, 2696079, 2645034, 2595270, 2546745,
  2499424, 2453267, 2408239, 2364307, 2321437,
  2279597, 2238756, 2198884, 2159954, 2121937,
  2084807, 2048538, 2013105, 1978485, 1944653,
  1911588, 1879268, 1847672, 1816779, 1786571,
  1757028, 1728133, 1699866, 1672212, 1645152,
  1618672, 1592755, 1567387, 1542551, 1518233,
  1494420, 1471095, 1448244, 1425852, 1403900,
  1382364, 1361210, 1340362, 1319595, 1297437]

/-- `p_n`（`n ≥ 200` 时为 `0`）。 -/
def pDN (n : ℕ) : ℕ := pDlist.getD n 0

lemma pDlist_length : pDlist.length = 200 := by rfl

lemma pDN_eq_zero (n : ℕ) (hn : 200 ≤ n) : pDN n = 0 := by
  unfold pDN
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · rw [pDlist_length]; exact hn

lemma pDN_pos : ∀ n, n < 200 → 0 < pDN n := by decide +kernel

lemma pD_supp : ∀ n, 200 ≤ n → qQ pDN n = 0 := by
  intro n hn; unfold qQ; rw [pDN_eq_zero n hn]; simp

lemma pD_pos : ∀ n, n < 200 → 0 < qQ pDN n := by
  intro n hn; unfold qQ; exact_mod_cast pDN_pos n hn

lemma pD_nonneg : ∀ n, 0 ≤ qQ pDN n := fun n => Nat.cast_nonneg _

lemma nv2D_pos : 0 < nv2 (qQ pDN) 200 := by
  unfold nv2
  apply sum_pos
  · intro n hn
    have := pD_pos n (mem_range.mp hn)
    positivity
  · exact ⟨0, mem_range.mpr (by norm_num)⟩

/-- 整数化尺度 `S = 10⁴⁰`。 -/
def SD : ℕ := 10 ^ 40

lemma SD_pos : 0 < SD := by unfold SD; positivity

/-- `ρ`、`g_n` 的区间端点（作为常量，便于内核缓存）。 -/
def rhoLoD : ℚ := rhoLo pDN SD 200
def rhoHiD : ℚ := rhoHi pDN SD 200
def gLoD (n : ℕ) : ℚ := gLo pDN SD 200 n
def gHiD (n : ℕ) : ℚ := gHi pDN SD 200 n

/-- `ρ` 的 18 位小数区间 `[rl, rh]`（`rl` 正是论文 §B.4 印出的 `ρ ≥ 1.318140211762671039`）。 -/
def rlD : ℚ := 1318140211762671039 / 10^18
def rhD : ℚ := 1318140211762671040 / 10^18

/-- Temple 上端点的可计算上界（`ρ` 用字面量区间，`g_n` 用整数区间）。 -/
def hiBD : ℚ := hiBof (qQ pDN) 200 500 rlD rhD gLoD gHiD

set_option maxRecDepth 1000000 in
/-- **数值事实 1**（内核精确计算，约 4 万个整数核项）：`rl < ρ_lo`。 -/
theorem certD_rhoLo : rlD < rhoLoD := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **数值事实 2**（内核精确计算）：`ρ_hi < rh`。 -/
theorem certD_rhoHi : rhoHiD < rhD := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **数值事实 3**（内核精确计算，约 20 万个整数核项）：`hi_B < 1.318140212373478`。 -/
theorem certD_hiB : hiBD < 1318140212373478 / 10^15 := by
  decide +kernel

/-! ### 组装 -/

theorem certD_rl_le : rlD ≤ rhoc (qQ pDN) 200 :=
  certD_rhoLo.le.trans (rhoLo_le pDN SD 200 SD_pos nv2D_pos)

theorem certD_le_rh : rhoc (qQ pDN) 200 ≤ rhD :=
  (le_rhoHi pDN SD 200 SD_pos nv2D_pos).trans certD_rhoHi.le

theorem certD_rho_ge : (1318140211762671:ℚ) / 10^15 < rhoc (qQ pDN) 200 :=
  lt_of_lt_of_le (by unfold rlD; norm_num) certD_rl_le

theorem certD_rho_gt_beta : (13:ℚ) / 25 < rhoc (qQ pDN) 200 :=
  lt_trans (by norm_num) certD_rho_ge

theorem certD_hic_le : hic (qQ pDN) 200 500 < 1318140212373478 / 10^15 := by
  have h := hic_le_hiBof (qQ pDN) 200 500 pD_nonneg nv2D_pos rlD rhD certD_rl_le certD_le_rh
    (by unfold rlD; norm_num) gLoD gHiD
    (fun n => gLo_le pDN SD 200 SD_pos n) (fun n => le_gHi pDN SD 200 SD_pos n)
  exact h.trans_lt certD_hiB

/-- **CERT-D，即论文的 (†)**：`1.318140211762671 ≤ g(2) ≤ 1.318140212373478`。 -/
theorem certD_g2 : (1318140211762671:ℝ) / 10^15 < g2 ∧ g2 < 1318140212373478 / 10^15 := by
  have h := enclosure_of_cert (qQ pDN) 200 500 pD_supp pD_pos (by norm_num) (by norm_num)
    certD_rho_gt_beta
  constructor
  · calc (1318140211762671:ℝ) / 10^15 = (((1318140211762671:ℚ) / 10^15 : ℚ) : ℝ) := by
          push_cast; rfl
      _ < ((rhoc (qQ pDN) 200 : ℚ) : ℝ) := by exact_mod_cast certD_rho_ge
      _ ≤ g2 := h.1
  · calc g2 ≤ ((hic (qQ pDN) 200 500 : ℚ) : ℝ) := h.2
      _ < (((1318140212373478:ℚ) / 10^15 : ℚ) : ℝ) := by exact_mod_cast certD_hic_le
      _ = 1318140212373478 / 10^15 := by push_cast; rfl

/-- **Cor 2.4(iii)**：`C_∞ = √g(2)/(2π) ∈ [0.182726247746, 0.182726247790]`（用 20 位 `π` 界）。 -/
theorem Cinf_enclosure : (182726247746:ℝ) / 10^12 ≤ Cinf ∧ Cinf ≤ 182726247790 / 10^12 := by
  unfold Cinf
  have hpi0 : 0 < Real.pi := Real.pi_pos
  obtain ⟨hlo, hhi⟩ := certD_g2
  constructor
  · rw [le_div_iff₀ (by positivity), Real.le_sqrt (by positivity) (by linarith)]
    have hpi2 : Real.pi ^ 2 ≤ (3.14159265358979323847:ℝ) ^ 2 := by
      nlinarith [Real.pi_lt_d20, Real.pi_pos]
    calc (182726247746 / 10^12 * (2 * Real.pi)) ^ 2
        = 4 * (182726247746 / 10^12) ^ 2 * Real.pi ^ 2 := by ring
      _ ≤ 4 * (182726247746 / 10^12) ^ 2 * (3.14159265358979323847:ℝ) ^ 2 := by gcongr
      _ ≤ 1318140211762671 / 10^15 := by norm_num
      _ ≤ g2 := hlo.le
  · rw [div_le_iff₀ (by positivity), Real.sqrt_le_left (by positivity)]
    have hpi2 : (3.14159265358979323846:ℝ) ^ 2 ≤ Real.pi ^ 2 := by
      nlinarith [Real.pi_gt_d20, Real.pi_pos]
    calc g2 ≤ 1318140212373478 / 10^15 := hhi.le
      _ ≤ 4 * (182726247790 / 10^12) ^ 2 * (3.14159265358979323846:ℝ) ^ 2 := by norm_num
      _ ≤ 4 * (182726247790 / 10^12) ^ 2 * Real.pi ^ 2 := by gcongr
      _ = (182726247790 / 10^12 * (2 * Real.pi)) ^ 2 := by ring

end Eliashberg
