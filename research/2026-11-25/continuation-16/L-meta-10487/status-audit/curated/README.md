# 10486 / 10487：命题与提交路线核对

本目录只记录公开状态和已公布的提交规则，不包含新的数学证明、租约操作或上游 PR 操作。

## 精确命题

`L-meta-10487` 的完整 statement 字段逐字等于 `¬ (` 加上 `L-meta-10486` 的 statement 再加 `)`。正命题 10486 要求：对指定七点十五边图，任意至多含一个 NOT 的二输入电路，都存在门数不增的纯 AND/OR 电路，且对全部输入计算同一函数。它没有固定的 11 门预算。

正命题的官方路径是 `lean/PEqualNP/Outside/L_meta_10486.lean`，最终定理名是 `PEqualNP.Outside.L_meta_10486`，允许的项目模块只有 `PEqualNP.Defs`，另可使用 Mathlib。正命题 statement 的 SHA256 为 `d5975fb801d7798de99550a1dfecd2cc4b67addef55892ca665243c496bd84fa`；负命题为 `c7cba5f480c602e08abf312e7606a448d7afc14d3b87f9b01502447646da00e8`。哈希不额外添加末尾换行。

## 公开状态的时间边界

所附两条 desk row 来自 2026-11-25 12:58:54.236 UTC 的公开快照，两者当时均无已登记 PR。12:59 分钟进行的精确任务号 PR 搜索也为空，原始精简结果保存在相邻的 `final-two-task-status/curated` 归档。13:06:55.584 UTC 对 10486 的一次 step 查询返回 HTTP 200、`state=leased`、一个 holder，起始时间 12:37:46.489 UTC。这不妨碍下述已完成证明入口，但不能据此推断持有者身份、工作进度或未来提交情况。

## 已公布的合法路线

[参与说明](https://pequalnp.com/join.txt) 在本次 13:06:55 UTC 取回时，SHA256 是 `2a4fd84354251825cf5bf5c44b736444c087f1926c9b432036b88326140277a1`。

- 第 179–180 行允许对所持任务证明其列出的否定孪生命题，按普通证明提交。因此，持有 10487 时研究并证明正命题 10486 有直接规则依据。
- 第 49、72–73 行公布 `tools/pnp.sh next --proof-of <step>`。前提是已经有一个仍开放任务的 checked proof；规则明确允许该任务同时被其他参与者持有，实际返回的条款会标记 race。
- 因此，精确 10486 证明完成本地检查后，负责人可以请求 `tools/pnp.sh next --proof-of L-meta-10486`，依据实际响应取得提交租约。本审计没有调用该入口。
- 第 144–154 行要求提交前续租；收到 410 就停止提交。提交应为一分支、一提交、一个新文件，PR 标题 `L-meta-10486`，正文单独一行 `Lease: <lease id>`；随后以 submitted 归还该提交租约。

[CONTRIBUTING.md](https://github.com/open-goat/pequalnp-proofs/blob/main/CONTRIBUTING.md) 当前 Git blob 为 `a6f7d8d32cdc74078cb85043b585c4fbd0145cca`。辅助声明放在与模块同名的命名空间内；最终全限定名定理置于文件最后，类型必须等同公开 statement。只能添加指定文件，大小不超过 512 KiB，不能使用 sorry、新公理或 native_decide；文件若定义自己的类型或实例，应在 PR 描述首行按规则声明需要人工审阅。

## 证明状态

独立 C++ 搜索所报告的十个二元门预算耗尽，只是计算线索。本目录不把它称为 Lean 证明、严格检查通过或官方 ACCEPTED。完整正命题仍须由实际证明文件和项目检查器确认。精简档不包含整份参与说明、第三方证明源码、二进制或任何私人租约字段。
