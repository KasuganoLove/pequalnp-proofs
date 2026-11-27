# C21：恢复验证环境、校正官方状态、准备可复用电路工具

日期：2026-11-27。最新任务分配观察：2026-11-27T03:19:20.889548+00:00（UTC）。

## 本轮结果与边界

本轮没有新分配的任务租约，也没有新官方上游 PR。已经完成环境恢复、公开提交状态核对，以及通用电路 witness 生成器的形式化样例检查。用户要求的阶段里程碑仍是官方上游 PR；这些准备工作没有被记为已完成新的题目。

任务台已经连续 5 次以 HTTP 200 返回 `gap: null`、`retry_after_s: 300`。第一次使用 solid/prove，第二次使用官方脚本支持的精确任务参数，随后使用不带 level/kind 的普通分配。每次都遵守前一次的重试时间。精确行/状态接口同时把 L-meta-20580 列为 open、无人持有；已核对请求参数与当前 pnp.sh 一致、响应日期新鲜。服务端代码不可读，原因仍未确认。公开 open 标记不构成已获得租约。完整精选诊断和逐次脱敏结果在本目录；没有对未分配题目开展证明或搜索。

## 官方状态校正

- 我方 [PR #16085](https://github.com/open-goat/pequalnp-proofs/pull/16085) 已于 2026-11-25 16:56:18 UTC 关闭、未合并，原因是另一份证明先完成并合并。我方没有观察到 ACCEPTED 或数学 REJECTED 判决。L-meta-12030 已由 Julleht 的 [PR #16006](https://github.com/open-goat/pequalnp-proofs/pull/16006) 完成。
- 用户另一 Codex 会话的 [PR #17125](https://github.com/open-goat/pequalnp-proofs/pull/17125) 和 [PR #15225](https://github.com/open-goat/pequalnp-proofs/pull/15225) 均有 ACCEPTED 评论并已合并。前者是 L-meta-6390 的归约，不能算父命题已全部解决。其余新核实的合并记录见 `resume/owner-pr-status/README.md`。
- 2026-11-27 03:08:50 UTC，官方仓库作者 KasuganoLove 的 open PR 查询结果为零；没有等待接手修复的开放 REJECTED/FAULT 提交。该结论不涉及未公开的本地工作。

## 恢复后的固定环境

从 `3db0136bf094e975baaf20214b01e4b4579059f2` 恢复一份 checkout。Lean 4.36.0，Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`，9 项依赖实际 HEAD 与 manifest 逐一匹配。完整缓存 9,117 项下载并解包成功。`PEqualNP.Defs`、`PEqualNP.Library.Helpers.PromiseColTree` 串行构建均 exit 0；源配置、结果和日志在 `resume/ENVIRONMENT_MANIFEST.json` 中逐项列出。

本轮没有修改固定工具链、manifest、checker 或已有上游证明。Chrome 已只读确认登录为 KasuganoLove；未发生浏览器提交。

## 通用工具

`tooling/generate_promise_proof.py` 把外部给定的 gate list、row masks、边界和原始 statement 生成一份候选证明。它只使用 Defs 和 PromiseColTree，保留最终 statement 字节，所有 helper 在本文件自己的 namespace；大数使用短 limb 表达。所有限额使用紧邻 declaration 的 `set_option ... in`。

工具处理 NOT 的首 pin 语义、缺失线读 false、空门、非二次幂 promise 列的高位填充与真实行前缀关系。结论限于每侧恰有一个输入为真的 `Represents`，没有扩展成所有布尔输入上的等式。

验证结果：12 项 Python 合成检查全部通过；当前官方 format_py exit 0；单个合成 Lean 样例 exit 0，3.553 秒，输出为空。该样例不是官方 posted task，未运行 strict checker，也未提交到上游。根工具 `audit_circuit.py` 与 `union_circuit.py` 保留作后续独立核对及集合并子表达式共用准备，尚未用于实际题目、没有最优性结论。

## 继续入口

最早允许再次请求的时间为 2026-11-27T03:24:20.889548+00:00（UTC）；更晚的 allocator 回复优先。获得新租约之后才开始对应题目的数学/搜索，按时续租，固定最终候选后做格式、普通 Lean、精确命题及 strict 验证，再提交一文件一提交的官方 PR。旧 12128 租约仍已释放，不因本轮恢复自动重启它。

`MANIFEST.json` 记录本 checkpoint 的完整文件和 SHA256。私有租约文件、账号凭据、全台原始 JSON、完整第三方 join/pnp 源码及二进制缓存不在公共包中。
