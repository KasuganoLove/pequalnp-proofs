# L-meta-3358：七门后缀至多依赖六条输入线路

`L_meta_3358.lean` 证明任务的完整原命题：一个最多七门、含两个不同位置 NOT 门的 fan-in-two 电路，其输出最多依赖最初十七条线路中的六条。

本地项目严格检查器以 `check` 模式接受该文件，退出码 0，重新核验 1,680 个常量；使用的公理为 `propext`、`Quot.sound`、`Classical.choice`。完整本地输出保存在 `3358.check-minimal.log`，精确公开任务定义保存在 `gap.json`。这里的 `ACCEPTED (check)` 是本地检查结果，不是上游 PR 的官方裁决。

证明文件 SHA-256：`1bd5ad58f1c1be72f2e8f989165500ac8c0a2e0058fcab618ae26548f7d153b9`。

证明已保存到 [codex/L-meta-3358-20261124 分支](https://github.com/KasuganoLove/pequalnp-proofs/tree/codex/L-meta-3358-20261124)，[提交 9ed381f](https://github.com/KasuganoLove/pequalnp-proofs/commit/9ed381f4165528fa489bd1f2eff81c4bf57d811d)。上游 [PR #7168](https://github.com/open-goat/pequalnp-proofs/pull/7168) 已创建，等待官方裁决。

在仓库 `lean/` 目录可复核普通编译：

```sh
LEAN_NUM_THREADS=1 lake env lean -j1 ../research/2026-11-24/continuation-2/L-meta-3358/L_meta_3358.lean
```

若要重现完整检查，应在固定源码的干净副本中把本目录的证明放到 `gap.json` 指定的 `file`，把 `statement` 写入临时文本文件，并从仓库根目录调用 `node tools/check-lean.mjs <证明路径> <命题文本路径> check`。保留本次锁定的 Lean 和 Mathlib 版本。
