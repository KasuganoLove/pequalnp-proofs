# 当前 P vs NP 协作状态

更新：2026-11-27；最后任务台观察 2026-11-27T03:19:20.889548+00:00（UTC）。

## 当前任务与阶段目标

本 root 没有有效租约。本轮连续 5 次分配均为 `gap:null`、`retry_after_s:300`；下一次最早请求时间 2026-11-27T03:24:20.889548+00:00（UTC）。分配接口和公开 open 状态存在差异，原因未确认；尚未获得新题，未做对应证明或搜索。

本轮没有新增官方 PR。用户要求的阶段里程碑仍是将可验证的证明提交官方上游；环境和工具准备不能替代该里程碑。用户其他会话的未公开租约状态未知，本 root 没有操作它们。

## 官方结果

- [PR #16085](https://github.com/open-goat/pequalnp-proofs/pull/16085)：2026-11-25 16:56:18 UTC 因竞争证明先合并而关闭，未合并；没有观察到我方 ACCEPTED 或数学 REJECTED。L-meta-12030 已由 Julleht 的 PR #16006 完成，不重送。
- 用户另一 Codex 会话的 [#17125](https://github.com/open-goat/pequalnp-proofs/pull/17125)、[#15225](https://github.com/open-goat/pequalnp-proofs/pull/15225) 已获 ACCEPTED 并合并。#17125 是归约，不代表完整父命题 L-meta-6390 已解决。
- 2026-11-27 03:08:50 UTC，官方仓库中作者 KasuganoLove 的开放 PR 为零，没有现成的开放 REJECTED/FAULT 等待修复。

## 最新可用入口

[C21：本轮恢复、状态证据和通用工具](2026-11-27/continuation-21/README.md)。Lean 4.36.0 / pinned Mathlib 的完整缓存已经恢复，Defs 与 PromiseColTree 编译成功。通用 witness 生成器通过12项Python检查、官方格式检查、一个合成 ordinary Lean 样例；不是实际题目证明，strict checker 未运行。Chrome 已确认 KasuganoLove 登录。

当前本地固定上游源码为 `3db0136bf094e975baaf20214b01e4b4579059f2`。后续提交前仍需核对上游和任务台；当前配置、guard、checker 与11月25日有变化，不得直接沿用旧runner。

## 历史研究边界

- C19保留12030 canonical 的普通Lean通过、公理查询和三次strict无verdict记录；关闭原因按本页新官方状态更新，不把竞争者验收归属本 root。
- C20保留12128的部分下界、13门控制及两次UNKNOWN搜索。其租约已于2026-11-25 15:32:41.409774 UTC释放，未因本轮恢复自动重启。
- C18及更早的部分结果继续保留原归属和验证级别。任何非完整证明、归约或UNKNOWN搜索均不写成完整命题已解决。
