# Eliashberg 临界温度论文：Lean 4 形式化完整打包

打包日期：2026-09-22。对象：论文 *The critical temperature of the linearised Eliashberg
equations: existence, uniqueness, and the extremality of the Einstein spectrum*（v3，31 页）。

> **先读这条：本文件描述的是本机的完整打包目录，不等于这个 git 仓库的内容。**
> 下面「目录」一节列出的 `lean/`、`numerics/`、`paper/`、`audit/*-output.txt`
> 等，**大部分没有推进本仓库**。本仓库实际追踪的是：
>
> - `Eliashberg.lean` 与 `Eliashberg/`（44 个模块，放在仓库根而非 `lean/` 下）；
> - `lakefile.toml`、`lake-manifest.json`、`lean-toolchain`（重建所需的全部锁定）；
> - `audit/*.lean`（6 个审计脚本；它们的输出不入库，由 CI 每次重新生成并作为
>   artifact 上传）；
> - `.github/workflows/verify.yml`（干净机器上的 7 道闸门）；
> - `00-覆盖对照表.md`、`01-形式化进展.md`、本 `README.md`。
>
> 换言之：**重建与复核所需的东西是齐的**（源码 + 锁定 + 审计脚本 + CI），
> 缺的是过程性留档与数值镜像，那些留在原工作区。
> 用 `git ls-files` 看权威清单，不要照「目录」一节去找文件。

## 一句话结论

**论文中一切被论文自己陈述为定理的命题都已在 Lean 4 + mathlib 中证明。**
未形式化的只有三项，且三项论文自己都没有标成定理：§3 Conjecture 3.1（自标猜想）、
§3 的 \(\varpi\in(0,45]\) 区间扫描（自陈 numerical evidence，待验证不等式未印出）、
§6.2 库仑赝势（§6 开头自陈 "It contains no theorem."）。

> 2026-09-26 补：Conjecture 3.1 **本身**仍未形式化（也不打算——它对定理 A/B 不承重），
> 但它的**后果**已经接通：`theorem_2_1_of_conjecture`（`ConjectureBridge`）证明了
> 「若猜想成立 ⇒ Theorem B」。此前这一步在库内是断的，见 `01` 第十七轮。

## 数字

> **2026-09-26：两次入库。`DiracBridge`（42 → 43）与 `ConjectureBridge`（43 → 44），下表按本机实测回填。**
> `lake build Eliashberg` 与 `audit/*.lean` 在 `E:/lean-verify/eliashberg-rebuild`
> （Lean 树与本包逐字节一致，已 `diff -rq` 核过）上重跑。
> 43 模块状态的 CI（run `36236722176`）**已全绿**，干净机器逐项复现本机读数；
> 44 模块状态的 CI（`b371d47`，run `36244840150`）**已全绿**：闸门 0–5 逐项 success，
> 干净机器读数与本机逐字相同——`CHECKED modules=44 constants=1655 theorems=1469`、
> `AXIOMS_SEEN [Quot.sound, Classical.choice, propext]`、`NONSTANDARD_COUNT 0`、
> `GATE2 PASS: 覆盖模块数 = 源文件数 = 44`、`DIRAC_BRIDGE_IN_LIBRARY ok`。

| 项 | 当前值（44 模块） | 43 模块 | 上一轮读数（42 模块，2026-09-21 实测） |
|---|---|---|---|
| 模块 | **44**（+ 根文件 `Eliashberg.lean`） | 43 | 42 |
| 行数 | 12975 | 12837 | 12783 |
| 声明（内核实测） | 常量 **1655**、其中定理 **1469** | 常量 1645、定理 1459 | 常量 1642、定理 1456 |
| 声明（源码正则口径） | 未复测——1039 出自源码正则（口径订正见 `01` 第 779 行），本轮没有复现该正则，故不填 | 同左 | 1039 |
| `sorry` / `admit` / 自设 `axiom` / `native_decide` | 0 / 0 / 0 / 0（源码 grep rc=1 无命中；内核审计里 `sorryAx`、`Lean.ofReduceBool` 均未出现） | 同左 | 0 / 0 / 0 / 0 |
| 全库公理依赖 | 仅 `propext`、`Classical.choice`、`Quot.sound`（1655 条常量逐条检查，`NONSTANDARD_COUNT 0`） | 同左（1645 条） | 同左（1642 条） |
| 构建 | `BUILD_RC=0`，8960 jobs | 8959 jobs | 8958 jobs |
| 孤儿模块 | 0。判据：审计覆盖模块数 44 **等于** `Eliashberg/*.lean` 文件数 44，已做成 CI 闸门 2 的硬判据 | 0（43 = 43） | 0 |
| 工具链 | `leanprover/lean4:v4.34.0-rc2`，mathlib `9fa639972e2e` | 同左 | 同左 |
| 最新提交 | 本包不在 git 里；核验仓 `b371d47`（已推送） | `214cbfc` | `a474f0e` |

## 目录

```
README.md                         本文件
00-覆盖对照表.md                   论文每一条编号命题 → Lean 声明 → 模块 → 证明是否走了不同路线
01-形式化进展.md                   15 轮完整过程记录（每轮做了什么、为什么、踩了什么坑、发现论文哪些问题）
02-闭环核验报告.md                 论文问题定位、v1→v2→v3 三版改动核验、证书精确复算
lean/
  Eliashberg.lean                 根文件（import 全部 44 个模块）
  Eliashberg/*.lean               44 个模块源码
  lakefile.toml                   构建配置（含 [[lean_lib]] name = "Eliashberg"）
  lake-manifest.json              依赖锁定（mathlib 等 9 个包的精确 rev）
  lean-toolchain                  工具链版本
  build-log.txt                   本次 lake build 输出
  git-history.txt                 Eliashberg 相关全部提交（含逐文件统计）
audit/                            本轮独立审计的脚本与输出（不入库，可重跑）
  AxiomAudit.lean / -output.txt   遍历全库每条常量收集公理；非标准公理 0 条
  StmtCheck.lean / -output.txt    主定理陈述完整弹性化（pp.numericTypes），核对数字字面量类型
  StmtCheck2.lean / -output.txt   非空性：用点质量 δ₁ 实例化 Theorem A/B，证明假设可同时满足
  DiracBridge-output.txt          「ω² a.e. 常数 ⟺ P = δ_c」桥在库外单独编译时的输出留档；
                                  该脚本已于 2026-09-26 入库为 `lean/Eliashberg/DiracBridge.lean`
  DiracCheck.lean / -output.txt   取代上者的审计：钉两条桥定理**住在 `Eliashberg.DiracBridge` 模块里**
                                  （只 `#check` 名字的话，定理被挪回库外再同名声明也会显绿），
                                  并打印该模块全部常量（3 条：两条定理 + `simp [moment2]` 生成的 `moment2.eq_1`）
  AxiomAudit-output-43模块.txt    入库后重跑的公理审计：modules=43 constants=1645 theorems=1459，NONSTANDARD_COUNT 0
  Sec52Principles.lean / -output.txt  §5.2 (2)(3) 的「原则」写成 Lean 就是三条一行引理（故不入库）
  certD-vector-diff.txt           CERT-D 的 200 个整数与论文 §B.5 逐位比对：identical = True
numerics/                         数值镜像与复现（Python，与 Lean 定义逐字对应）
  scripts/*.py                    证书 A/A′/B/D 的精确有理复算、审计脚本
  mpmath-iv-atan2-audit.py / -output.txt   §5.2(1) 的独立复现（mpmath 1.3.0 的 iv.atan2 不向外取整）
  certD_p.txt, certD_Q.txt, v3-certd-vector.txt, *repro-output*.txt, reproduction-README.md
paper/
  paper_text_v3.txt               论文 v3 的纯文本抽取（供对照表引用行号）
```

## 如何重建

在一个已经 `lake build` 过 mathlib 的 Lean 项目里（或直接用 `nivat-lean` 仓库）：

```bash
# 1. 把 lean/Eliashberg.lean 与 lean/Eliashberg/ 放到项目根目录
# 2. lakefile.toml 里加入（或保留）：
#      [[lean_lib]]
#      name = "Eliashberg"
# 3. 工具链与依赖以 lean/lean-toolchain、lean/lake-manifest.json 为准
lake build Eliashberg              # 应输出 Build completed successfully
```

`Eliashberg` 库只依赖 mathlib，不依赖同仓库的 `Nivat` 库。

## 如何重跑审计

```bash
lake env lean audit/AxiomAudit.lean        # 预期：NONSTANDARD_COUNT 0，且 modules= 与源文件数相等
lake env lean audit/StmtCheck.lean         # 打印主定理的完整陈述
lake env lean audit/StmtCheck2.lean        # 预期：0 错误（非空性实例化通过）
lake env lean audit/DiracCheck.lean        # 预期：rc=0 且输出含 DIRAC_BRIDGE_IN_LIBRARY ok
grep -rn "sorry\|admit" lean/Eliashberg/   # 预期：无输出
```

> 孤儿模块判据：`AxiomAudit` 打印的 `modules=N` 必须**等于** `ls lean/Eliashberg/*.lean | wc -l`。
> `lake build` 不会碰根文件 import 链之外的文件，却照样报 `Build completed successfully`；
> 这条等式是唯一能把「文件存在」和「被编译且被审计」钉在一起的东西，已做成 CI 闸门 2 的硬判据。

## 主定理一览（Lean 名 → 论文）

| Lean | 论文 |
|---|---|
| `theorem_1_1_a`、`theorem_1_1_b` | Theorem A(a)：\(\exists T_0\)，\(\lambda k(P,T_0)>1\)；与临界面相交 |
| `theorem_1_14`、`kk_continuousOn`、`kk_tendsto_zero`、`corollary_1_17` | Theorem A(b)：严格递减、连续、\(\to0\)、\(T_c\) 唯一 |
| `theorem_2_3`、`theorem_2_3_Tc` | Theorem A(c)：\(k<g(2)\langle\omega^2\rangle/(2\pi T)^2\)，\(T_c<\tilde T_c\) |
| `theorem_2_1`、`theorem_2_1_strict`、`theorem_2_1_iff`、`theorem_2_1_iff_dirac` | Theorem B：\(k(P,T)\le h(\varpi_{rms})\)，等号 iff 点质量（最后一条即论文原话的陈述） |
| `theorem_A10` | Theorem A.10 = Theorem (∗)：Temple 包围 |
| `certA_g2`、`certA'_g2`、`certB_g2`、`certD_g2`、`Cinf_mem` | Appendix B 四个证书 + (†) + \(C_\infty\) |
| `semigroup_preserves_cone`、`exists_cone_eigenvector_l2` | Prop 1.11、1.12(3) 的 \(\ell^2\) 原始陈述 |
| `sSup_spectrum_eq_lam1` | 忠实性桥：库的 \(\lambda_1\)（有限 Rayleigh 上确界）= 论文的 \(\max\operatorname{spec}\) |

## 与论文的偏离（全部列出）

1. **若干证明走了不同路线，陈述不变**（对照表中标 ✅*）：Prop 1.11 用算子范数收敛替代 (F5) 强收敛；
   Prop 1.12(3) 用紧算子序列紧性替代谱投影；Theorem A.10 用二维子空间论证替代 Courant–Fischer；
   Lemma A.1 末句用序列紧性替代 Riesz 理论；(1.8) 不用 Bochner 积分。原因都是 mathlib 缺相应理论。
2. ~~**Theorem B 等号情形**的库内陈述是「\(\omega^2\) 几乎处处为常数」，与「\(P\) 是点质量」的桥未入库。~~
   **2026-09-26 已消除**：桥入库为 `Eliashberg/DiracBridge.lean`，`theorem_2_1_iff_dirac` 按论文原话
   陈述「等号 ⟺ \(P\) 是点质量」。**入库后尚未重新编译，待 `lake build` 与公理审计复跑确认。**
3. **HS 常数**：库给 \(13\pi^2/6+2\approx23.4\)，论文写 \(\le25\)，两者都成立。
4. **Lemma A.2 / Cor A.3 的 \(A\preceq B\)** 只在有限支撑向量层陈述（`quadForm_le_B`）；
   Cor A.6 的证明只需此层。

## 审读中发现的论文问题（已在过程文档详述）

- **Remark 1.16(a)**「Theorem B 比 (1.8) strictly stronger」方向反了：\(H\) 凹（论文自己的 Conjecture 3.1）
  时 Jensen 给出 (1.8) 更紧，Theorem B 是其推论（`theorem_2_1_of_theorem_1_8`）。
- **Remark A.12 末句**「由此得到的 hi 根本不是 \(g(2)\) 的上界」过强：对论文自己的例子它仍是上界，
  只是推导失效、不再有保证（`Positivity.lean`）。
- v1 的 (0.1) 笔误（v2 已修）、CERT-D 向量 v2 未印（v3 已印）等见 `02-闭环核验报告.md`。
