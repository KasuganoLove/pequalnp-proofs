# L-meta-4201：三个现有归约、公开快照与本地已完成分支

**父任务 L-meta-4201 仍未证明。本地已完成几何子题 L-meta-8470（严格检查通过）及干净电路子题 L-meta-8323（Defs-only 规范单文件严格检查通过）。矩形覆盖提取 8468 或全干净替代电路构造 8321 仍是实质缺口。**

源码核对固定在上游提交 [`259523a5b265318b84f9377f2feb965fd213f898`](https://github.com/open-goat/pequalnp-proofs/commit/259523a5b265318b84f9377f2feb965fd213f898)，提交时间为 2026-11-25 05:45:42 UTC。子题状态来自网站完整公开导出，导出时间为 05:50:45.796 UTC。任务台的 offerable 列表会省略 cut-of-cut 子题，因此本次通过网站公开 search/map 索引定位了精确编号和不可变记录。

以下表格的 `conjecture` 是原公开导出的历史状态，未根据本地证明改写。后续本地进展及本地检查状态单独列在下文；它们不代表官方任务系统已接受。

## 精确依赖表

| 已合并归约 | 子题 | 精确作用 | 公开快照状态（05:50 UTC） |
| --- | --- | --- | --- |
| [`R_meta_4201_1`](https://github.com/open-goat/pequalnp-proofs/blob/259523a5b265318b84f9377f2feb965fd213f898/lean/PEqualNP/Outside/R_meta_4201_1.lean) | [8121](https://data.pequalnp.com/data/lemma/L-meta-8121.93a0e686867d.json) | `IsAO2 42`，准确计算 PG(2,4) 关联函数，且 `doubleReread = []`，推出至少 104 个 OR 门 | conjecture |
| 同上 | [8123](https://data.pequalnp.com/data/lemma/L-meta-8123.fd20093c6570.json) | 对 OR 门数最少的正确 `IsAO2` 电路，若 doubleReread 非空，构造 OR 数不增加、doubleReread 长度严格下降的电路 | conjecture |
| [`R_meta_4201_777`](https://github.com/open-goat/pequalnp-proofs/blob/259523a5b265318b84f9377f2feb965fd213f898/lean/PEqualNP/Outside/R_meta_4201_777.lean) | [8321](https://data.pequalnp.com/data/lemma/L-meta-8321.8b8bf7576859.json) | 任意正确 Monotone2 电路可变成每个 AND 输出都蕴含最终输出的电路，且 OR 数不增加 | conjecture |
| 同上 | [8323](https://data.pequalnp.com/data/lemma/L-meta-8323.aafbf8331087.json) | 对具有上述全部 AND 安全性质的正确 Monotone2 电路，证明 OR 数至少 104 | conjecture |
| [`R_meta_4201_731`](https://github.com/open-goat/pequalnp-proofs/blob/259523a5b265318b84f9377f2feb965fd213f898/lean/PEqualNP/Outside/R_meta_4201_731.lean) | [8468](https://data.pequalnp.com/data/lemma/L-meta-8468.4b8481c425e2.json) | 从任意正确 Monotone2 电路提取非空关联矩形覆盖，使总权重 `Σ(|A|+|B|−1) ≤ OR数+1` | conjecture |
| 同上 | [8470](https://data.pequalnp.com/data/lemma/L-meta-8470.36fa4ba378c3.json) | 任意这样的关联矩形覆盖，权重至少 105 | conjecture |

三个归约的合并 PR 分别为 [#10843](https://github.com/open-goat/pequalnp-proofs/pull/10843)、[#10972](https://github.com/open-goat/pequalnp-proofs/pull/10972)、[#11026](https://github.com/open-goat/pequalnp-proofs/pull/11026)。最后一份 PR 明确说明作者曾在本地证明几何计数侧，但电路到覆盖的正规化仍未完成；不能把该描述当成已经合并的独立子题证明。

初次审计时按精确任务 ID 搜索上游所有状态的 PR，8321、8323、8468、8470 均返回 0 条结果。这是当时的搜索快照，不是对后续提交或索引状态的判断；本次会话没有创建这些子题的正式 PR。

## 本地完整证明：8470

新增研究模块 `lean/Pnp4201Cover105.lean`，SHA-256：

`32e921f17fdf18289897c03543d31a3cfc1245d441c13eea646a861446d799cc`

仅导入 `PEqualNP.Defs`，没有新增数据类型或 instance。证明的三步为：

1. 用 `decide +kernel` 验证精确模 21 关联关系共有 105 条边，且不同点的公共关联线数至多为 1。公共邻点证书只遍历 21×21 对点，不枚举四个独立顶点。
2. 一个完全包含于关联关系的非空矩形 `A×B` 必有一侧大小为 1，因此其边数为 `|A|+|B|−1`。非空条件确保自然数减法不会造成错误。
3. 所有 105 条边都属于覆盖的并；并集基数不超过各矩形基数之和。允许覆盖重叠，未假设边划分或矩形互不相交。

最后的 `exact_8470` 采用公开 `formal_statement` 原文；脚本逐字比较为相等。普通 Lean 编译退出 0、日志为空，已经生成 olean：

```bash
cd lean
lake env lean -o .lake/build/lib/lean/Pnp4201Cover105.olean Pnp4201Cover105.lean
```

另一位代理已做独立只读复核，未发现范围或基数推理问题。规范单文件 `strict-8470/L_meta_8470.lean`（SHA256 `25e91dfeadebb34eb713389b7ad14f9a30010da00d5f7e076901b37615dd1063`）已于 06:03:10 UTC 获得本地严格检查 **ACCEPTED (check)**：退出 0、246.4 秒、1,676 个常量，标准允许公理。

已准备 fork 分支 `codex/prove-meta-8470-2026-11-25`，头提交 `0cb59db32842e8a630c2baa8e3ada1ae6c4375a4`，源码与已检查版本一致。**没有领取 8470 子题，也没有创建正式 PR或取得官方接受结果。** 父任务研究范围不能替代单独子题的任务台领取要求。

## 后续本地完整证明：8323

`lean/Pnp4201CleanCase.lean` 已证明公共 L-meta-8323 的精确原文，源 SHA256 `f149c10630af19768cacaf80f315642752a1b32eace4cf00b76f2afb214167e8`；声明 SHA256 `ea9da5a93cdce2730e73e9dfe572610b1f6cb565daff7e96c8f55c0a6d8ccfbf` 与公共记录一致。普通 Lean 编译退出 0，唯一警告是公共命题自身未使用的 `x5` 绑定名，未修改原文。

该命题假设所有 AND 门取真都蕴含输出取真。常量传播明确保持这一性质；最小化限定在同函数、干净性和 OR 预算共同约束的类中；TopForm 构造保持该类。通用计数 `clean_top_or_bound` 随后证明 C4-free 图的边数不超过 OR 数加一，105 条精确关联边给出 104 下界。

最终规范单文件 `strict-8323/L_meta_8323.lean` 为 **179,631 字节**，仅导入 `PEqualNP.Defs`，SHA256 `43febc27f36b15f7c0503609ce9179931a9ac0d7a7a5ebae745b93f8fa47e3b6`。格式检查和普通检查均退出 0；最终严格检查从 07:09:07.275008 到 07:13:19.630050 UTC，**ACCEPTED (check)**、退出 0、2,344 个常量、252.355126 秒，最大子进程 RSS 6,917,320 KiB，标准允许公理。

此前两次严格尝试分别以 SIGKILL/−9（204.661428 秒）和 verifier 退出 137 / 外层退出 3（192.596593 秒）结束，均没有判定；首轮根因未确诊。对应 `attempt-1/2-strict-result.json` 与日志保留为历史记录。最终版本通过依赖裁剪移除 149 条不必需命令，使用显式边 `(0,21)` 证明边集非空，将三条邻接有限证书改为符号证明，并仅保留 Defs 导入。原始模块化源码、精确公共命题和来源归属保留。

准备分支 `codex/prove-meta-8323-2026-11-25` 的头提交为 `0873097889691e4d21f575dabed0c1cadd0bcb3a`，基线 `259523a5b265318b84f9377f2feb965fd213f898`；已核对一个提交、一个新增文件，远端源码与最终检查版本相同。没有领取 8323 子题，没有创建正式 PR，也没有官方接受结果。

这些结果解决的是已经干净的电路。它们没有提供 8321 所需的任意正确电路到全干净电路、且 OR 数不增加的转换。

## 其他可复用结果及其限制

- `L_meta_2233`：沿 OR-only 路径到达输出的 AND 门个数，不超过相应输出侧 OR 门数加 1。
- `L_meta_2234`：在无四环图及其列明前提下，叶侧覆盖量不超过叶侧 OR 门数加所选 AND 门数，并证明叶侧与输出侧 OR 集合不相交。本轮 `Pnp4201CleanOrCount` 已从 `L_meta_2235.core` 提取 OR 专用计数，并在干净 TopForm 前提下通过门值追踪构造所需边见证、门集合及中心/叶参数，完成 8323 的这一连接。
- `L_meta_4101_aux.CleanCount.pairCleanBound` 和 `L_meta_4913`、`L_meta_4915` 的公开结论是**总门数**预算，不能直接充当 OR 门数下界。
- 已有 5126 TopForm 扩展的公开最终结论列出总门数、junk 数及测试输入不变量；其具体 `step3_struct_tests` 继承了上游 `L_meta_1501.step3_struct` 的更强结构：删除门 `r` 的算子为 OR，新追加的末门也为 OR，其他门经 `rho` 重新编号后保持算子。因此这是 OR 换 OR 的步骤，其结构保留 OR 总数。此前本记录称“可能用 OR 替代 AND”是错误表述，已依据两个精确引理的结论更正。初次审计时的适用条件缺口是 `Least` / `IsLeastAO` 要求在所有等价 `IsAO2` 电路中按总门数全局最少；仅在给定 OR 预算内最少并不直接满足它。本轮已用独立的 `BudgetLeast` / `CleanLeast` 比较类及完整 V1/V2 预算、负输入不变量补上针对初始干净电路的结构论证。该进展不把任意脏电路自动变成干净电路，不能消除 8321。
- `R_meta_4201_1` 内部确实证明了一个从 Monotone2 到 `IsAO2` 的 OR 数不增加的常量传播正规化；它作为局部引理嵌在归约证明中。该结果不是“全部 AND 安全”的正规化，不能消除 8321。

`doubleReread` 是 `ReadK` 中基于两个方向的线性部分/proof-tree 项定义的边集合。它不是简单的输入 fanout，也不是每条原始线的语法读取次数。

## 当前剩余目标

在矩形覆盖路线中，8470 已通过本地严格检查；**8468 的任意电路到 OR 预算覆盖提取仍缺证明**。在全干净路线中，8323 的最终 Defs-only 规范证明已通过本地严格检查；**8321 的任意电路到全干净电路且 OR 数不增加的转换仍缺证明**。

针对初始干净电路的预算最小性及 TopForm 适用问题已由本轮专门模块解决。剩余缺口是对任意正确电路的上述结构转换，不再应描述成“8323 尚缺预算最小性连接”。无四环或最终输出在所有负例为 false，都不能单独推出所有中间 AND 安全。

父题 1477 还需要 sibling 4199 的至少 21 个 AND 门结论；该 sibling 在本次公开快照中仍未完成。因此本记录不声称证明 PG(2,4) 的 125 门总下界，更不声称解决 P versus NP。

精确子题原文、历史公开快照、来源提交及独立的后续本地状态另存于 `dependency-audit.json`。三份审查源码保存在 `audited-source/`，内容哈希与任务台记录一致。

## 交接状态

父任务 L-meta-4201 于 **2026-11-25 07:15:48.277414 UTC** 按 `missing_lemma` 释放，返回 HTTP 200。当前没有该父任务的活动 lease；脱敏回执见 `lease-handoff.json`。已准备的 8470、8323 分支均没有子题 lease 或正式 PR。父任务仍开放，后续缺口是 8321 或 8468。
