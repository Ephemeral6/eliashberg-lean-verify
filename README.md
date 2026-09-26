# Eliashberg 形式化：第三方环境重建核验

私有仓库，唯一用途是**在一台干净机器上复现**打包 `Eliashberg-Lean-完整打包-20260922`
所声称的两件事：

1. `lake build Eliashberg` 真的通过；
2. 全库公理依赖只有 `propext` / `Classical.choice` / `Quot.sound`，
   无 `sorryAx`、无 `Lean.ofReduceBool`、无自设公理。

起因：建仓时本机（Windows）实测下行约 25 KB/s，工具链 588 MB + mathlib cache 约 5 GB，
本地重建 ETA 约 60 小时，不可行，故改在 CI 上跑。

> 2026-09-26 复测：同一台机器下行约 630 KB/s，本地 `lake exe cache get` + `lake build Eliashberg`
> 实测 18:04→18:25 共 21 分钟（`CACHE_GET_RC=0`、`BUILD_RC=0`、8958 jobs，42 模块状态）。
> 上面那个 60 小时的数字已过期，保留为当时读数。CI 仍是**独立干净机器**这一层证据，不因本地能跑而取消。

## 内容来源

`lean-toolchain`、`lake-manifest.json`、`lakefile.toml`、`Eliashberg.lean`、
`Eliashberg/`、`audit/*.lean` 取自打包。
依赖 rev 由 `lake-manifest.json` 锁定（mathlib `9fa639972e2e`）。

**与打包的差异（2026-09-26 起，不再是逐字节一致）：**

- `Eliashberg/DiracBridge.lean`：Theorem B 等号情形的「论文原话版」，原先是库外审计脚本
  `audit/DiracBridge.lean`（单独 `lake env lean` 编译，因此不进 `lake build`、不进公理审计）。
  已入库并加进根文件 import；库外副本已删除——留着它会让闸门 5 验一份与库内无关的拷贝而照样显绿。
  模块数因此 42 → 43。定理签名与证明正文相对原件逐字节未改，差异只在 import、namespace、docstring。
- `audit/DiracCheck.lean`：新的闸门 5，取代直接编译 `audit/DiracBridge.lean`。
- 上述两项与根文件 import 行，在打包目录（权威源）里也已同步落地。

`lakefile.toml` 中保留了原有的 `[[lean_lib]] name = "Nivat"` 与
`defaultTargets = ["Nivat"]`——该库不属于本次核验对象，其源码目录不在包内，
故只显式构建 `Eliashberg` 目标。

## 闸门

见 `.github/workflows/verify.yml`。每道闸门单独取 `rc`，不经管道，
以免退出码被 `tail`/`head` 吞掉。

两条闸门钉的是「显绿但没在验东西」这类失效，不是数学内容：

- **闸门 2 的孤儿模块判据**：公理审计覆盖的模块数必须**等于** `Eliashberg/*.lean` 的文件数。
  `lake build` 不会碰根文件 import 链之外的文件，却照样报 `Build completed successfully`
  （stringgraph/formal 2026-09-16 就这么栽过）。这条把「文件存在」与「被编译且被审计」钉成同一个数。
  实测过反向：拿 42 模块的审计输出配 43 个源文件，判据变红。
- **闸门 5 的模块归属判据**：两条定理必须住在 `Eliashberg.DiracBridge` 模块里。
  只 `#check` 名字的话，把定理挪回库外再由别处声明同名也能显绿。

