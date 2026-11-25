# Continuation 8：PG(2,4) 的矩形覆盖与干净电路 OR 下界

日期：2026-11-25。时间记录均使用 UTC。

本次沿父任务 **L-meta-4201** 研究，得到两个已通过本地严格检查的完整子题证明。父任务已按 `missing_lemma` 释放，当前没有该父任务的活动 lease。**父任务仍未完成**：现有成果尚不能把任意正确电路变成 OR 数不增加的全干净电路，也不能从任意电路提取满足所需预算的矩形覆盖。

## 当前核验与提交状态

| 对象 | 本地结果 | 严格检查 | 提交状态 |
| --- | --- | --- | --- |
| L-meta-8470：矩形覆盖权重至少 105 | 精确原文命题已证明 | **ACCEPTED (check)**；退出 0；1,676 个常量；246.4 秒 | 已准备用户 fork 分支；没有子题 lease、没有正式 PR、没有官方接受结果 |
| L-meta-8323：干净 Monotone2 电路至少有 104 个 OR 门 | 精确原文命题已证明 | **ACCEPTED (check)**；退出 0；2,344 个常量；252.355126 秒 | 已准备用户 fork 分支；没有子题 lease、没有正式 PR、没有官方接受结果 |
| L-meta-4201：任意正确 Monotone2 电路至少有 104 个 OR 门 | 未证明 | 不适用 | 仅记录父任务范围内的研究成果 |

`public-statements/` 与依赖审计中的 `conjecture` 是 **05:50:45.796 的公开快照**。它们保留原样；之后完成的本地证明记录在独立状态字段中。本地严格检查通过也不等于任务系统的官方接受。

## 1. 已通过严格检查的几何子题 L-meta-8470

精确关联关系有 21 个点和 21 条线：

```text
Inc(p,l) := (l.val + 21 - p.val) % 21 ∈ [0,5,7,17,20]
```

对完全包含于关联关系、覆盖所有关联对的非空矩形族，证明

\[
105 \leq \sum_{(A,B)} (|A|+|B|-1).
\]

`lean/Pnp4201Cover105.lean` 给出研究版本；规范单文件位于 `strict-8470/L_meta_8470.lean`，源 SHA256 为：

```text
25e91dfeadebb34eb713389b7ad14f9a30010da00d5f7e076901b37615dd1063
```

证明先用 `decide +kernel` 检查 105 条关联及两点至多一个公共关联线，再推出任何非空关联矩形至少一边是单点，最后使用覆盖并集的基数不超过矩形基数总和。覆盖可以重叠；没有分割或互不相交假设。

本地严格检查于 **06:03:10 UTC** 结束，模式 `check`，退出 0，用时 **246.41285785699984 秒**，复核 **1,676 个常量**，仅使用 `propext`、`Classical.choice`、`Quot.sound`。证据保存在 `strict-8470/strict-result.json` 和 `strict-check.log`。该规范文件仅导入 `PEqualNP.Defs`，没有新增数据类型或 instance。

用户 fork 上已准备分支 [codex/prove-meta-8470-2026-11-25](https://github.com/KasuganoLove/pequalnp-proofs/tree/codex/prove-meta-8470-2026-11-25)，头提交：

```text
0cb59db32842e8a630c2baa8e3ada1ae6c4375a4
```

其基线为 `259523a5b265318b84f9377f2feb965fd213f898`，差异已核对为一个提交、一个新增文件，远端源码与已检查源码一致。**这是准备分支，未创建正式 PR。** 父任务 lease 不替代子题领取；加入说明禁止为未持有步骤创建证明 PR。PR #11026 已描述其作者的本地几何思路，此归档不主张计数思想的发现优先权。

## 2. 已通过严格检查的 L-meta-8323：干净电路的 104-OR 下界

保留的模块化研究定理是：

```lean
PEqualNP.Outside.Pnp4201CleanCase.exact_8323
```

文件 `lean/Pnp4201CleanCase.lean` 的 SHA256：

```text
f149c10630af19768cacaf80f315642752a1b32eace4cf00b76f2afb214167e8
```

其声明与公共 `formal_statement` 逐字节一致，命题 SHA256 为 `ea9da5a93cdce2730e73e9dfe572610b1f6cb565daff7e96c8f55c0a6d8ccfbf`。普通 Lean 编译退出 0，并已生成 olean。唯一警告来自公共原文 OR 计数 recursor 中未使用的绑定名 `x5`；为保留原文，未重命名或屏蔽警告。详细记录见 `8323-local-validation.json`、`8323.statement.txt` 和 `validation/CleanCase-build.log`。

精确前提是：电路属于 `Monotone2`、准确计算指定的 42 输入关联函数，而且每个 AND 门取真都蕴含最终输出取真。证明链为：

1. **常量传播保持已有干净性。** `Pnp4201CleanNormalize` 处理空门、单输入门和默认 false 的缺失读取，保持每个保留 AND 门在所有目标负输入上的值；任何算子类别的计数均不增加。它没有把原本脏的 AND 变干净的假设。
2. **在干净类内最小化。** `Pnp4201CleanBudgetTopForm` 的 `CleanLeast` 明确把同一目标函数、干净性和 OR 预算列为比较条件。V1 删除门只减少算子计数；V2 删除一个 OR 并追加一个 OR，保持 OR 数。对目标负输入的门值相等保证干净性沿构造保留。
3. **通用 OR 专用计数。** `Pnp4201CleanOrCount.clean_top_or_bound` 对任意 C4-free 图证明：精确计算该图函数的干净 TopForm AO2 电路满足 `边数 ≤ OR数 + 1`。通过真实门值追踪、OR 可达性到严格锥的连接，直接构造边见证，没有使用额外 read-once、活门或全局总门数最小性前提。
4. **精确几何桥接。** `Pnp4201Graph` 把公共模关系连接到 `SimpleGraph (Fin 42)`，证明无四环及恰好 105 条排序边，从而得到 `104 ≤ OR数`。最终 OR 数与题目中的 `GateOp.casesOn` / `List.countP` 完全相同。

最终规范单文件是 `strict-8323/L_meta_8323.lean`，定理名为 `PEqualNP.Outside.L_meta_8323`，共 **179,631 字节**，仅导入 **`PEqualNP.Defs`**。当前已通过检查的源码 SHA256：

```text
43febc27f36b15f7c0503609ce9179931a9ac0d7a7a5ebae745b93f8fa47e3b6
```

最终严格检查从 **07:09:07.275008 UTC** 到 **07:13:19.630050 UTC**，返回 **ACCEPTED (check)**，退出 0，耗时 **252.355126 秒**，复核 **2,344 个常量**，仅使用 `propext`、`Quot.sound`、`Classical.choice`。最大子进程 RSS 为 **6,917,320 KiB**。格式检查和普通单文件编译也均退出 0。详细结果与日志保存在 `strict-8323/strict-result.json` 和 `strict-check.log`。

用户 fork 已准备分支 [codex/prove-meta-8323-2026-11-25](https://github.com/KasuganoLove/pequalnp-proofs/tree/codex/prove-meta-8323-2026-11-25)，头提交 `0873097889691e4d21f575dabed0c1cadd0bcb3a`，基线 `259523a5b265318b84f9377f2feb965fd213f898`。差异核对为一个提交、一个新增文件，远端源码与上述已检查文件完全一致。**没有持有 8323 子题 lease，没有创建正式 PR，也没有官方接受结果。**

### 严格检查的两次历史中断与最终处理

前两次严格检查均在验证阶段终止，**没有给出判定**。它们作为历史尝试保存，不作为当前最终结果：

| 历史尝试 | 观察结果 | 用时 | 证据 |
| --- | --- | --- | --- |
| 第一次，06:38:07 起 | `SIGKILL`，退出 −9，无判定；根因未确诊，怀疑资源压力 | 204.661428 秒 | `attempt-1-strict-result.json` / `attempt-1-strict-check.log` |
| 第二次，06:55:11 起 | 检查器报告 verifier 退出 137、没有判定；外层退出 3，最大子进程 RSS 7,084,280 KiB | 192.596593 秒 | `attempt-2-strict-result.json` / `attempt-2-strict-check.log` |

检查器会重新核验文件中的声明，包括未被最终定理使用的大型辅助结果。最终规范版本据依赖关系裁去 **149 条不必需命令**；用显式边 `(0,21)` 提供边集非空见证；把三条邻接有限证书替换为符号证明；移除不需要的 Mathlib 聚合导入，保留 Defs-only 环境。精确公共命题保持不变。

原始模块化研究源码及来源归属全部保留，未被这些打包优化覆盖；附加证明见 `lean/Pnp4201EdgeWitness.lean` 和 `lean/Pnp4201SymbolicAdj.lean`。打包记录 `strict-8323/L_meta_8323.bundle.json` 同时记录原模块哈希、最终哈希、裁剪及后续优化。

源码和只读审阅明确区分：保持**已有**干净性，与为任意正确电路创造干净表示。后者仍是 8321 的未解决义务。

## 3. 父任务仍缺什么

| 已合并归约 | 本次已完成的本地一侧 | 仍缺的另一侧 |
| --- | --- | --- |
| `R_meta_4201_777` | **8323**：干净电路 OR 数至少 104；本地严格检查通过 | **8321**：任意正确电路存在 OR 数不增加的全干净替代电路 |
| `R_meta_4201_731` | **8470**：所有关联矩形覆盖权重至少 105；本地严格检查通过 | **8468**：从任意正确电路提取权重至多 `OR数+1` 的关联矩形覆盖 |
| `R_meta_4201_1` | 此路线没有本轮完整子题证明 | 8121 的单读下界和 8123 的 double-reread 下降步骤 |

这两条主要路线各自缺一个实质性电路结构步骤，不能把它们当成已经完成的父题证明。输出在负例上为 false，也不蕴含每个中间 AND 输出为 false。`doubleReread` 是 ReadK 的 proof-tree / 线性部分定义，不是原始线的 fanout。

父题 1477 的 125 总门数结论还涉及 sibling 4199 的 AND 下界；本次未证明它。这里不声称完成 P versus NP。

## 4. 复用模块、独立审阅与小模型证据

`Pnp4201OrBudget` 证明了物理删除和常量传播对任意算子预算的不增加，并在预算内部最小化总门数；其剪枝推论包括二元输入不同、不可被先前线替代、AND 操作数在目标负输入上不可比较、OR 操作数在目标正输入上不可比较，以及每个门在某个目标正输入上为真。最后一项没有断言边对见证或 pivotality。

`Pnp4201BudgetTopForm` 是不要求全干净的预算版 TopForm；它的最小化不能自行继承初始电路的干净性。因此最终 8323 使用单独的 `Pnp4201CleanBudgetTopForm`。两种模块都保留，便于检查这一范围区别。

几何桥接的源文件、编译日志及复现元数据另存于 `graph-bridge/`。独立只读审阅在 `or-budget-review.md`、`budget-topform-review.md`、`clean-or-count-review.md`；干净类最小化的审阅和通用定理范围在 `clean-or-count-scope.md`。已有的三个预算模块 axiom audit 只报告标准允许公理，原始日志保存在 `validation/`。它们是组件检查记录；完整 8323 规范单文件的最终严格检查另见 `strict-8323/`，已通过。

计数材料复用上游 `L_meta_2235`（含 L2231/L2233/L2234）；线值和锥语义复用 `L_meta_1501`。`dependencies/Pnp2343Pruning.lean` 保留其源自 L1499 / PR3112、L2668、L1680、L1425 等的归属说明。源码遵循仓库 Apache-2.0 归属；未使用 L1501 的无预算全局最小电路结论来代替预算最小性。

`c6-or-search/` 保留一个有界反例探测：只固定 OR 数，每个 OR 端口和输出可为原始输入及先前 OR 输出的任意合取，吸收任意数量的中间 AND 层，并包含常量及缺失线默认 false 的情形；约束全部 64 个输入。四 OR 模型有 1,973 变量、8,016 子句，CaDiCaL 约 0.21 秒返回 UNSAT。已知五 OR 电路通过校准，解码的八门电路逐输入验证正确。**此结果是求解器证据；CNF 完备性和 UNSAT 结果没有经 Lean 核验。** 未把它用作 PG(2,4) 下界证明。

## 5. 复现

固定 Lean **4.36.0**、Mathlib **`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`**。当前源码与上游固定环境逐文件一致性的证据见 `env-compatibility.json`。

将 `strict-8470/L_meta_8470.lean` 和 `strict-8323/L_meta_8323.lean` 放在固定版本项目的 `lean/PEqualNP/Outside/` 对应路径后，从仓库根目录分别复现本地严格检查：

```sh
node tools/check-lean.mjs lean/PEqualNP/Outside/L_meta_8470.lean /absolute/path/to/continuation-8/strict-8470/statement.txt check
node tools/check-lean.mjs lean/PEqualNP/Outside/L_meta_8323.lean /absolute/path/to/continuation-8/strict-8323/statement.txt check
```

普通研究模块需将 `lean/` 中的研究源复制到项目 `lean/` 根目录。`dependencies/Pnp2343Pruning.lean` 也放在该根目录；`dependencies/L_meta_1501.lean` 与 `L_meta_2235.lean` 对应项目的 `lean/PEqualNP/Outside/`。保留固定版本依赖，在项目 `lean/` 目录按顺序运行：

```sh
lake env lean -j1 -o .lake/build/lib/lean/Pnp2343Pruning.olean Pnp2343Pruning.lean
lake env lean -j1 -o .lake/build/lib/lean/PEqualNP/Outside/L_meta_1501.olean PEqualNP/Outside/L_meta_1501.lean
lake env lean -j1 -o .lake/build/lib/lean/PEqualNP/Outside/L_meta_2235.olean PEqualNP/Outside/L_meta_2235.lean
lake env lean -j1 -o .lake/build/lib/lean/Pnp4201OrBudget.olean Pnp4201OrBudget.lean
lake env lean -j1 -o .lake/build/lib/lean/Pnp4201BudgetTopForm.olean Pnp4201BudgetTopForm.lean
lake env lean -j1 -o .lake/build/lib/lean/Pnp4201CleanBudgetTopForm.olean Pnp4201CleanBudgetTopForm.lean
lake env lean -j1 -o .lake/build/lib/lean/Pnp4201Cover105.olean Pnp4201Cover105.lean
lake env lean -j1 -o .lake/build/lib/lean/Pnp4201Graph.olean Pnp4201Graph.lean
lake env lean -j1 -o .lake/build/lib/lean/Pnp4201CleanNormalize.olean Pnp4201CleanNormalize.lean
lake env lean -j1 -o .lake/build/lib/lean/Pnp4201CleanOrCount.olean Pnp4201CleanOrCount.lean
lake env lean -j1 -o .lake/build/lib/lean/Pnp4201CleanCase.olean Pnp4201CleanCase.lean
```

这是保留的模块化研究复现流程。最终 8470 和 8323 规范单文件均已通过本地严格检查；`validation.json` 分别记录组件普通编译、历史无判定尝试、最终本地严格检查、准备分支和官方提交状态。本归档不包含 lease 凭据。

## 6. 最终交接

父任务 **L-meta-4201** 已于 **2026-11-25 07:15:48.277414 UTC** 按 `missing_lemma` 释放，接口返回 HTTP 200；当前没有该父任务的活动 lease。脱敏记录见 `lease-handoff.json`。

后续工作仍需解决 **8321** 的全干净替代电路构造，或 **8468** 的任意电路到预算矩形覆盖提取。两个已验证子题的独立分支已准备，但均未领取子题、未创建正式 PR、未取得官方接受。重新开始时应遵循任务台的合法分配流程，再决定对应步骤的提交。

## 后续公开状态同步

本检查点收尾时，官方仓库的规范名称已变为 `open-goat/pequalnp-proofs`。`L-meta-8470` 已由 **dantwiddy-max** 的 [PR #12699](https://github.com/open-goat/pequalnp-proofs/pull/12699) 于 2026-11-25 06:58:12 UTC 合并；这不是本会话提交的 PR。本会话的独立证明仍保留在准备分支，用于复现。

`L-meta-8323` 的公开 step 状态仍为 open，未显示持有人或等待中的 PR。本会话于 07:24:21 UTC 按文档重新请求分配，得到 gap=null 和 300 秒后重试的提示，未获得子题 lease。用户要求继续推进至可以正式提交公共 PR；因此本归档是已经完成成果的持久检查点，后续认领和提交工作继续。详见 `official-status-followup.json`。
