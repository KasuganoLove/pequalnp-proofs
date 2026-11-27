# 2026-11-27 恢复前只读核验

核验窗口约 02:50–03:00 UTC。没有领取、续租、归还任务，没有远端写入、浏览器操作或新数学工作。

## 官方结果

- 我方 [PR #16085](https://github.com/open-goat/pequalnp-proofs/pull/16085)（L-meta-12030，KasuganoLove）在 2026-11-25 16:56:18 UTC 关闭，**未合并**。官方[说明](https://github.com/open-goat/pequalnp-proofs/pull/16085#issuecomment-7168756799)称另一份证明先获合并，此 PR 不再合并；未观察到对我方证明的 ACCEPTED 或数学 REJECTED 裁决。
- 竞争 [PR #16006](https://github.com/open-goat/pequalnp-proofs/pull/16006)（Julleht）在 16:25:22 UTC 收到 [ACCEPTED、exit 0](https://github.com/open-goat/pequalnp-proofs/pull/16006#issuecomment-7167955630)，[官方运行](https://github.com/open-goat/pequalnp-proofs/actions/runs/45640915949)。16:55:07 UTC 合并，merge commit `9ae8cae284541dcbc8e15821e6062affae1f73bf`。
- [12030 的精确行接口](https://pequalnp.com/desk/row?gap=L-meta-12030)现列为 checked；[12031](https://pequalnp.com/desk/row?gap=L-meta-12031)的 gaps、checked、withdrawn 均为空。两者 `/desk/step` 都是 not_open。当前接口没有提供 12031 的撤下原因或精确命题；不能仅从缺席写成“官方明确因孪生证明撤回”。精确 ID 的 PR 查询未找到12031条目。

## 分支与环境

02:52 UTC 的 GitHub 元数据与独立 `git ls-remote` 一致：

| 引用 | SHA |
|---|---|
| user fork main | `1fc91c4a3a59d36d4c1490dcd945a5449ead499f` |
| user fork codex/pnp-research-2026-11-24 | `e3bf0acf5e38daa631ca9b3f35a970d65f2001df` |
| upstream main | `3db0136bf094e975baaf20214b01e4b4579059f2` |

所查两个 fork 引用没有新增提交；未把这个结论扩大为所有其它 Codex 分支也无变化。上游 SHA 为 02:50:51 UTC 的提交，后续提交前仍应重新读取远端。

Lean 固定为 4.36.0，Mathlib 为 `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`；toolchain、lakefile、manifest、CheckLemma 与前次记录字节一致。Defs umbrella 新增 BranchingProgram，整个 Defs 子树未在本审计单独枚举。check-lean 新增内存检测依赖，构建内存故障可返回137。outside-guard 新增归约编号占用检查、固定成功尾行和真实路径校验。pnp.sh 已大幅更新。精确 blob 在 `configuration-comparison.json`，不得沿用旧 runner 或据 pins 相同推断所有源兼容。

## 最新参与契约

[join.txt](https://pequalnp.com/join.txt) 于 02:55:37 UTC 抓取，SHA256 `b0aedba67747eb8da8202cf0da588756e7b540d572cbd89326d4c70473eba58f`。原文与新脚本原文保存在本目录的 local-only 引用文件中；精选公共清单不重复分发完整第三方文本。

新的脚本明确支持精确领取 `next --unit ID`，也保留已有完整证明的 `next --proof-of ID`；两者不可合并。后者不能把另一持有人不足30分钟的先手保护当作已绕过，是否授予由服务端决定。普通 next 会附上经清理的 model 字段。

需要注意的差异：脚本提供 `submit --unleased`，而 join 仍要求只提交已交付/持有的任务，同时又描述无租约积分下限，两者的例外范围存在歧义；本轮未使用该选项。submit 自动补租约分支缺少 join 要求的 model 字段，可通过普通显式 next 路径避免。join 新增十进制数字最多20位的要求，所查两个本地预检中未找到对应检查，不代表可以违反；本轮没有调查所有服务端检查。详见 `protocol-contract.json`。

新检查资源说明为20分钟起、每个外部模块增加4分钟、总计最多45分钟，约6.5GB；超过限制不说明证明数学上错误。新文件应遵守最新公开规则及当前任务条目。

## 公开任务类别快照

02:51:54.696 UTC 快照含4384个 gaps、11781个 checked，hub 统计412个 offerable；行级 `offerable_now=true` 只有12条，均未显式标 level/kind，其中6条 held_now=false、6条 true。显式 solid/hard/open 分别450/304/112条，但不能据此推断有可分配任务。未标字段保留为 unspecified，没有自行猜成 warmup/prove。账户刚收到的 retry_after_s 比这份只读快照更新，必须遵守；快照不保证向特定账户分配。

## 清单与限制

`MANIFEST.json` 精选安全状态、来源、调用契约及小型接口响应。排除全台 JSON、完整join、完整旧/新第三方工具源。没有私有租约、令牌、邮箱或PR正文。当前审计不会重新打开12030或把我方未合并PR写成官方成果。
