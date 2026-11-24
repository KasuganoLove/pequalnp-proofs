# L-meta-3233：首两门为 OR 的受限电路下界

## 当前范围

原任务要求：九输入 Petersen-minus-vertex 边函数的 fan-in-two AND/OR/NOT 电路，第一条计算线路为 `x4 OR x6`，第二门为 OR，且第二门输入列表满足指定置换下的字典序条件，必须至少有 16 门。完整命题尚未证明。

顶点 4、6 都是度数为 2 的非相邻顶点；不能将其他首门类型（例如 `x0 AND x6` 或 `x0 OR x2`）直接通过图自同构搬到本题。

## 已准备的实质性归约

令 B 为非 NOT 门数，N 为 NOT 门数。一般 Petersen-minus-vertex 电路满足 B ≥ 13，因此 B + N = size ≤ 15 时，N ≤ 2。

`R_meta_3233_713.lean` 将原任务归约到两个独立的闭命题：

1. 任意正确计算该边函数的 fan-in-two 电路至少有 13 个非 NOT 门。
2. 原任务中至多含 2 个 NOT 门的电路仍至少有 16 门。

第一条命题承担实际的组合计数内容：九个必要输入与至少五条分支线路给出非 NOT 门预算下界。其自包含证明复用上游 `L_meta_2165.lean` 的分支组及电路化简证明；原任务不允许导入这份 Outside 模块，所以在子证明中保留了所需证明代码。第一条精确命题也已作为独立任务 `L-meta-3438` 发布。

第二条仍是未解决的下界，归约没有声称解决它。第一条源码包含自定义 `Stat`、`Least`、`MaskGraph` 类型；如果作为独立证明提交，应在 PR 首行说明，按照项目要求进入人工阅读路径。归约文件自身只有两条假设和一个结论，没有新增类型或辅助声明。

验证状态：归约文件已通过固定 Lean 4.36.0 工具链的普通编译（退出码 0），并用 Python 确认结论与领取任务中的原始 statement 字节一致。两条假设的源码长度分别为 911 和 1,355 字符。另用与 CheckLemma 相同的绑定变量正规化和打印选项，对已编译归约作独立打印预览，得到 911 和 1,364 字符，均未超过 2,000 字符；第一条预览与任务 3438 逐字节一致。这只是打印诊断，不是严格检查器裁决。第一条子证明 `Pnp3233Binary.lean` 也已通过普通 Lean 编译（退出码 0，约 45 秒），其最终命题与任务 3438 和归约的第一条假设字节一致。归约的导入、文件格式、命名空间及公开任务规则检查均通过。第一次严格检查成功构建了文件，但验证器以退出码 137 终止，外层报告 CHECKER FAULT／退出码 3，没有给出数学裁决或 CHILD 输出。按任务负责人指示，仅以限制分配器内存峰值的设置重试一次，仍以相同的 137／3 退出码报告 CHECKER FAULT，未产生裁决或 CHILD 输出。严格检查重试已停止，结果待官方 CI；没有改动证明、检查器或固定构建配置。此前取消的编译也没有记为证明通过或失败。

## 第一条假设与现有投稿

第一条子证明是对上游现有分支计数论证的自包含提取。`Pnp3233Binary.lean` 的前 3,234 行辅助代码与固定上游 `L_meta_2165.lean` 相比，仅改动了命名空间；新增的是最终命题的短包装。它不是本次新发现的数学下界。

2026-11-24 13:42 UTC 从迁移后的官方仓库 `open-goat/pequalnp-proofs` 查询到，任务 3438 已有多个投稿：[PR #6461](https://github.com/open-goat/pequalnp-proofs/pull/6461)、[PR #6591](https://github.com/open-goat/pequalnp-proofs/pull/6591)、[PR #6636](https://github.com/open-goat/pequalnp-proofs/pull/6636)。其中 #6461 使用同一上游 `petersen_binary_lower` 证明路线，并已披露自定义类型。查询时这三份 PR 均未返回官方裁决评论，#6461 仍打开且未合并。为避免重复投稿，本次不另开 3438 PR；该已编译子证明作为 3233 归约第一条假设可完成的证据保存。

任务 3233 还有 [PR #6573](https://github.com/open-goat/pequalnp-proofs/pull/6573) 的另一条 dirty-AND 归约、13:44 UTC 新开的 [PR #6723](https://github.com/open-goat/pequalnp-proofs/pull/6723) 的十二个后缀搜索归约，以及 [PR #6271](https://github.com/open-goat/pequalnp-proofs/pull/6271)。#6723 在最终查询时仍打开且未合并，未返回裁决评论；这里没有复核它所称的子证明。已检查 #6271 的源码：其定理包含四条未证明的第三门分类假设，因此不是原任务的完整证明。查询时未观察到 3233 的完整证明获接受。

公开任务台于 13:50:11 UTC 仍列出 3233，`reductions: true` 且全局归约入口打开；公开列表未登记该父任务的归约，PR 字段仅列 #6271。不过 GitHub 已有 #6573 和 #6723 两条正确命名的待审归约，任务台的 PR 数量明显滞后，不能用它断言实际归约名额仍空。当前加入说明规定每题最多三条归约、每位参与者每题一条；发布前的活跃租约续期及官方接收结果由任务负责人确认。

## 有限的第二 OR 门信号预处理

`3233-second-or-patterns.py` 将第二门可读输入正规表示为 0…10：0…8 是原始变量，9 是 `x4 OR x6`，10 代表求值时尚不存在的线路（读取为 false）。空列表、单元素和二元素列表共 133 个，产生 53 种不同的 OR 信号。

对这 133 个有界列表直接施加题目的置换字典序条件，剩余 73 个列表、36 种信号。若再按照该图自同构对语义信号取商，可以列出 30 个轨道代表，但额外的电路正规化仍需证明，不能直接把 30 当作原条件已经剩下的情形数。

这些是有限 Python 计算，没有构成 Lean 证书，也没有从情形数推出任何门数下界。

## 来源

- [原任务台](https://data.pequalnp.com/data/desk/gaps.json)
- [固定源码中的 L_meta_2165.lean](https://github.com/open-goat/pequalnp-proofs/blob/048b39bb2c5b2c21da06d44218d16366086a68d9/lean/PEqualNP/Outside/L_meta_2165.lean)
- [原归约 R_meta_2744_7.lean](https://github.com/open-goat/pequalnp-proofs/blob/048b39bb2c5b2c21da06d44218d16366086a68d9/lean/PEqualNP/Outside/R_meta_2744_7.lean)

复用代码沿用仓库 Apache License 2.0。

## 提交准备

归约文件已由任务负责人发布到用户 fork 的 `codex/R-meta-3233-713-20261124` 分支，提交 `86a9b1c3e83eb90493b36c2c385b67dc67563213`。截至本记录完成时，尚未创建此归约的上游 PR；不能将分支发布写成官方提交或接受。

## 本轮归档与复现

归约已推到 fork 的 [codex/R-meta-3233-713-20261124 分支](https://github.com/KasuganoLove/pequalnp-proofs/tree/codex/R-meta-3233-713-20261124)，提交为 `86a9b1c3e83eb90493b36c2c385b67dc67563213`。当前没有本工作的上游 PR。

在仓库 `lean/` 目录，使用锁定工具链运行：

```sh
LEAN_NUM_THREADS=1 lake env lean -j1 ../research/2026-11-24/continuation-2/L-meta-3233/Pnp3233Binary.lean
LEAN_NUM_THREADS=1 lake env lean -j1 ../research/2026-11-24/continuation-2/L-meta-3233/R_meta_3233_713.lean
```

有限预处理从本任务存档目录运行 `python3 3233-second-or-patterns.py`；输出对应 `3233-second-or-patterns.json`。核验等级及严格检查器的两次无裁决故障见 `3233-validation.json` 和 `validation-summary.md`。两条预览命题文本及预览 JSON 也已保存；预览打印不是严格检查接受。

## Publication update

The reduction was submitted through the owner’s local Chrome as [PR #7182](https://github.com/open-goat/pequalnp-proofs/pull/7182) at 2026-11-24T14:43:18Z. It is open and awaits authoritative verification. The attempted post-submission desk release returned HTTP 410 because the old lease had expired; no successful lease-release registration is claimed. Earlier pending-publication notes above are historical.
