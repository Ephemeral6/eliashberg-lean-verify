# Eliashberg 形式化：第三方环境重建核验

私有仓库，唯一用途是**在一台干净机器上复现**打包 `Eliashberg-Lean-完整打包-20260922`
所声称的两件事：

1. `lake build Eliashberg` 真的通过；
2. 全库公理依赖只有 `propext` / `Classical.choice` / `Quot.sound`，
   无 `sorryAx`、无 `Lean.ofReduceBool`、无自设公理。

起因：本机（Windows）实测下行约 25 KB/s，工具链 588 MB + mathlib cache 约 5 GB，
本地重建 ETA 约 60 小时，不可行。故改在 CI 上跑。

## 内容来源

`lean-toolchain`、`lake-manifest.json`、`lakefile.toml`、`Eliashberg.lean`、
`Eliashberg/`（42 个模块）、`audit/*.lean` 全部**逐字节取自打包**，未作修改。
依赖 rev 由 `lake-manifest.json` 锁定（mathlib `9fa639972e2e`）。

`lakefile.toml` 中保留了原有的 `[[lean_lib]] name = "Nivat"` 与
`defaultTargets = ["Nivat"]`——该库不属于本次核验对象，其源码目录不在包内，
故只显式构建 `Eliashberg` 目标。

## 闸门

见 `.github/workflows/verify.yml`。每道闸门单独取 `rc`，不经管道，
以免退出码被 `tail`/`head` 吞掉。
