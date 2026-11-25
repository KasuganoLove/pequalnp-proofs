# 来源与归属

本检查点中的综合、Rank 编码、基线生成与独立回放脚本由本轮研究会话编写。它们使用公开任务的精确目标，未产出本轮官方完整证明。既有数学结论与代码来源如下；完整第三方文件不重复归档。

## Petersen / L-meta-2592

- `L-meta-2592/status-audit/curated/source-hashes.json` 给出 L7389、L8295、R2592_318、R2592_408 的官方路径、Git blob、SHA-256 与大小。链接中的 `main` 会变化，复核必须同时核对保存的 blob 或 SHA-256。
- 同目录 `audit.json` 保存 L4725 的官方哈希 `1f9ecfd77d1ca6167a432c28243b294bb92df7242e37de34678357516ca2b3e2`，以及三条数值残余的观察时间。PR12799、12707 和9316 的身份与结果不能误写成2592或4727的完整证明。
- `ownership-analysis/README.md` 标明 L5367、L2446、OneNot、NotPremium、MergeCost 等依赖的精确使用范围。L2446 自身的归属包括由 0xshuzo 的 PR12203 改编的九输入证书，以及 L1667/L1674/L1677 的图与活线证明，包括 PressF10 和 zakpgrove。未复制这些第三方完整证明。
- `constructive-audit/README.md` 的两条排除只针对精确六星准备模块与显式 Shannon mux 架构，未宣称覆盖任意允许电路；也未另行 Lean 形式化。

## 循环矩阵 / L-meta-10083

Rank/Bic 和 `cut_budget` 通用框架来源：sheganinans，L-meta-9484，[PR13556](https://github.com/open-goat/pequalnp-proofs/pull/13556)。固定源：

https://github.com/open-goat/pequalnp-proofs/blob/2729f5c656ee99b60af92b92f1c6a45d549b431a/lean/PEqualNP/Outside/L_meta_9484.lean

源文件 43,900 字节；SHA-256：`6a9c99d2183fbc3dea25bcb4c6a6d99d7c9fc6bc2bffb731aeb2e2f164fd4bbe`。原始审计在工作目录中曾直接读取完整源，归档仅保留来源定位、哈希、归属和使用范围。`ownership-analysis/README.md` 中提及的本地参考文件不随此紧凑归档发布，可从上述固定提交取得并核对哈希。

两个104门基线生成器是独立生成和回放的控制材料，不是103门见证。旧 k=5 文字草图没有提供已经核对的33门门表，本检查点没有假定这样的构造存在。

## 九顶点图 / L-meta-11021

`status-audit/row-elimination-cost-audit.md` 的源代码审计基于官方提交 `57164c3618362178843e2ea37bd01613f4037ae2`，涉及 MetaComplexity、Elim、ReadersExport、L107、PadOr 及项目的精确图函数说明。该审计明确区分总门数与非NOT门数，不把别的 Petersen 图上的二元门下界搬到当前九顶点图。

这些官方项目来源采用 Apache-2.0。本目录不包含新复制的完整第三方 Lean 源文件。

## 既有用户 PR

`owner-pr-followup/PR14022-status.json` 保留较早的只读快照；`step-after-registration.json` 和 `current-selected-rows.json` 记录随后已登记的事实；`merged-final-status.json`、`merged-selected-rows.json` 和 `step-after-merge.json` 给出最终合并与 checked 证据。官方合并提交为 `1fc91c4a3a59d36d4c1490dcd945a5449ead499f`，文件 Git blob 与原提交一致。`protocol-summary.md` 与元数据记录 join、pnp.sh、CONTRIBUTING 的 URL、哈希或 Git blob，未复制完整协议及脚本。

PR 属于用户另一个 Codex 会话的工作，本 root 的职责是后续核对与协调；本检查点没有归档或宣称重写其完整证明。精确 PR 源可从固定 head `bc59c2be036e28415543dcb42dd8da78d4439163` 的 `lean/PEqualNP/Outside/L_meta_10221.lean` 取得。其通用证明归 tb-16 的 L9195 / PR13373，固定合并提交 `9025f81315571fe9b237f2fd3aed4f123b1e8757`；参考源 SHA-256 为 `b358ad57b53243df24c1908382c59f29819715761f8eacec38d032b0826aea20`，Apache-2.0。独立审核确认仅目标掩码、样本列表、命名空间、允许的额外 import 及署名注释发生特化，通用证明未改变。

`OWNERSHIP_AUDIT_MANIFEST.json` 保存已冻结普通检查证据的逐文件哈希。223字节的 `Pnp10221OwnerTypeCheck.lean` 是本轮精确类型/公理检查辅助文件，并非复制的完整第三方证明。
