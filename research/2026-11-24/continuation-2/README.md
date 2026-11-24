# P vs NP 第二轮接续记录 · 2026-11-24

本目录保存四个任务的证明、归约与诊断，工作仓库仍为 [KasuganoLove/pequalnp-proofs](https://github.com/KasuganoLove/pequalnp-proofs)。当前官方上游名为 [open-goat/pequalnp-proofs](https://github.com/open-goat/pequalnp-proofs)，仓库 ID 为 `1468025030`；这是此前上游仓库的当前归属，fork 不变。[元数据证据](https://api.github.com/repos/open-goat/pequalnp-proofs)

## 当前结果

| 任务 | 已完成 | 核验等级与未完成部分 |
| --- | --- | --- |
| [L-meta-3358](L-meta-3358/README.md) | 七门后缀含两个 NOT 时，输出至多依赖十七条初始线路中的六条。完整命题已证明。 | 本地严格 `check` 通过，退出码 0，重检 1,680 个常量。尚未创建上游 PR，也没有本轮官方接受裁决。 |
| [L-meta-3233](L-meta-3233/README.md) | 将原下界归约到“至少十三个非 NOT 门”和“至多两个 NOT 的剩余下界”；第一子命题已有自包含证明。 | 两份文件普通 Lean 编译与格式检查通过；严格检查两次退出 137，没有裁决。子命题打印预览通过，不等于严格检查通过。第二子命题仍开放。 |
| [L-meta-3384](L-meta-3384/README.md) | 证明了两个十一门校准电路；对记录的单调模型完成耦合重接线搜索。 | 校准命题普通 Lean 通过；有限搜索仅为计算证据，仍缺 NOT 情形、正规化与内核证书。完整任务未证明，已按 `missing_lemma` 归还。 |
| [L-gct-232](L-gct-232/README.md) | 排除了指定二维对称星形空间的独立第三方向扩张。 | 部分刚性引理普通 Lean 通过，符号恒等式经精确 SymPy 核对。一般三维空间的排除仍未证明，已按 `missing_lemma` 归还。 |

这里始终区分普通 Lean 编译、本地项目严格检查、有限计算和上游官方裁决。`L-meta-3358` 日志中的 `ACCEPTED (check)` 属于本地严格检查。

## 已保存的正式提交分支

- [codex/L-meta-3358-20261124](https://github.com/KasuganoLove/pequalnp-proofs/tree/codex/L-meta-3358-20261124)，提交 [`9ed381f`](https://github.com/KasuganoLove/pequalnp-proofs/commit/9ed381f4165528fa489bd1f2eff81c4bf57d811d)。
- [codex/R-meta-3233-713-20261124](https://github.com/KasuganoLove/pequalnp-proofs/tree/codex/R-meta-3233-713-20261124)，提交 [`86a9b1c`](https://github.com/KasuganoLove/pequalnp-proofs/commit/86a9b1c3e83eb90493b36c2c385b67dc67563213)。

本次快照中两份上游 PR 均尚未创建：GitHub 连接器创建 PR 返回 403，浏览器登录交接尚未完成。任务状态与记录时间见 [STATUS.json](STATUS.json)。第一子命题 `L-meta-3438` 已有他人的证明 PR [6461](https://github.com/open-goat/pequalnp-proofs/pull/6461)、[6591](https://github.com/open-goat/pequalnp-proofs/pull/6591)、[6636](https://github.com/open-goat/pequalnp-proofs/pull/6636)，本工作没有另开重复 PR。

## 复现与继续

源码基线为 [`048b39bb2c5b2c21da06d44218d16366086a68d9`](https://github.com/open-goat/pequalnp-proofs/tree/048b39bb2c5b2c21da06d44218d16366086a68d9)，Lean 为 `leanprover/lean4:v4.36.0`，Mathlib 锁定到 `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`。不要运行 `lake update` 改变复核依赖。各目录 README 给出相对于仓库的复现路径。

本轮普通编译使用 `LEAN_NUM_THREADS=1` 和 `lean -j1`；严格检查的资源故障单独记录，没有当作证明错误。研究分支用于保存可继续使用的结果，正式 PR 仍须按 [join.txt](https://pequalnp.com/join.txt) 只提交规定的一份 Lean 文件，并核对任务当前状态。

本目录没有保存任务私密标识或凭据。文件完整性见 `MANIFEST.json`。复用的上游代码遵循仓库 [Apache 2.0 许可证](../../../LICENSE)；具体来源在各任务记录中标明。

## 登录等待后的状态更新

2026-11-24 22:35（香港时间），安全登录接口返回不可用；两份上游 PR 仍未创建。3233 上次续期的有效时间已过，当前不声称持有有效租约；归约证明在到期前完成，后续提交前须重新核对题目及归约配额。3358 已有多份其他贡献者的 PR 排队，查询时未观察到接受裁决，也需先核对后续状态。已准备的标题、说明和分支见 [PR_READY.md](PR_READY.md)。
