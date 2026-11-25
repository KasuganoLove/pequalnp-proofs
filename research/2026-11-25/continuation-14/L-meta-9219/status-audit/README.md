# L-meta-9219：否定任务及已有证明核对

本目录记录 2026-11-25 11:24–11:31 UTC 的只读核对和一次普通 Lean 验证。没有新增官方 PR 或官方 ACCEPTED。

## 准确命题与已有提交

正任务 **9219** 问：掩码 `7586366` 的 5×5 布尔矩阵能否由至多 10 个 AND/OR 门表示。准确的公开否定任务是 **9224**。表示关系只检查 25 个“一左一右”输入；它没有要求在其余 999 个输入上计算某个指定函数。

在我们查询时，已有 [PR #13399](https://github.com/open-goat/pequalnp-proofs/pull/13399) 和 [PR #13445](https://github.com/open-goat/pequalnp-proofs/pull/13445) 提交相同否定命题，两者均打开，未观察到官方裁决评论。这里没有将任务台滞后的 `pr_open:0` 当成不存在 PR 的证据。

## 验证结果

对 #13445 的固定 head `697cedf52f5b0b9972ed6014751b949c92c37e82` 原文件逐字节核对 Git blob 后，未修改源码地运行 `lake env lean -j1`：

- 普通编译从 11:30:51.868 到 11:31:24.817 UTC，32.949 秒，退出 0。
- 独立 `#print axioms` 检查退出 0，仅列出 `propext`、`Classical.choice`、`Quot.sound`。
- 没有运行项目严格检查器，也没有将普通编译报告为官方 ACCEPTED。

固定源码 SHA-256 为 `b8a123a25d592f139cf6b212a39a4959de320bf7d32708367603b8a8f8f403d9`。两份结果 JSON 和原始日志保留在本目录。

## 来源与复现

#13445 的通用证明来自 tb-16 的 [L-meta-9195 / #13373](https://github.com/open-goat/pequalnp-proofs/pull/13373)。对应来源提交 `9025f81315571fe9b237f2fd3aed4f123b1e8757` 的 LICENSE 已核对为 Apache-2.0。除任务命名、矩阵掩码和真/假样本列表外，通用证明机制没有改变；不能把这次复核称为我们新发现的下界方法。

按 `audit.json` 的固定源码 URL 下载文件，校验所记 SHA-256 后，在本项目相同 Lean/Mathlib 环境运行：

```bash
python reproduce_ordinary.py --repo /path/to/pequalnp-proofs --source /path/to/PR13445-L_meta_9224.lean
```

脚本只接受精确哈希，编译同一源码并打印最终定理的公理。目录保留来源 URL 与哈希，排除了整份第三方 Lean、全任务台、join.txt、生成的二进制及租约记录。所有数学状态应结合日期解读。
