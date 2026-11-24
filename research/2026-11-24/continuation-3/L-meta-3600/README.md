# L-meta-3600：单次读取线路的关联对预算

## 已验证结果

`Pnp3600LineSingle.lean` 中的 `Pnp3600LineSingle.line_single_budget` 已通过固定 Lean 4.36.0 工具链的普通编译，退出码为 0，日志没有错误或警告。本次没有运行项目严格检查器。

设 `I` 是 N 个点与 N 条线之间的关系，任意两个不同点有唯一共同关联的线。设 C 是符合 `PEqualNP.TopForm.IsAO2 (N + N)` 的电路。只要求 C 对以下 N 个规范输入输出 false：选择一条线 l，打开 l 以及所有不在 l 上的点，关闭其他线。

那么，所有满足 `I p l` 且 `PEqualNP.ReadK.lineSingle C (N + N) (fun k => decide (N ≤ k)) p.val (N + l.val) = true` 的点线对，其数量至多为 `6 * C.size`。

`lineSingle` 是项目定义中关于电路证明树的单次线路读取标记；它不是关于某个原始输入在整份电路中仅出现一次的断言。计数命题不要求电路在所有输入上计算完整关联函数，也不要求平面阶数 q、`N = q² + q + 1` 或每条线有 q+1 个点。

完整的 L-meta-3600 仍未解决。这个结果控制 `lineSingle = true` 的关联对；`lineSingle = false` 的剩余关联对是后续预算论证的对象。将两个类别分别控制为 `6 * size` 和 `94 * size`，再使用全部关联对数量为 `N * (q + 1)`，才可推出任务要求的 `N * q ≤ 100 * size`。

## 证明来源与实际改动

证明主体复用 [上游 L_meta_2462.lean](https://github.com/open-goat/pequalnp-proofs/blob/89b96c0f464824a164434fb460926400b9943047/lean/PEqualNP/Outside/L_meta_2462.lean) 的计数论证，沿用仓库许可证。原文件的导出定理写作 `33 * size`，但实际证明把关联对分为 `R1`、`R2a`、`R2b` 三类，每类均注入 `Fin C.size × Fin 2`，已经给出了 `6 * size` 的计数。

对原论证的依赖逐处检查后发现：完整函数正确性的假设只用于证明上述规范单线输入被拒绝。本次将四处相应假设改为该较弱的拒绝条件，并证明原辅助输入 `zInput I l` 等于公开命题使用的 `Fin.append` 输入。随后删除原 `main` 中三个未使用的平面参数假设，并把最终常数改为 6。

因此，本次结果是对既有计数证明的假设削弱和显式收紧；不应将原有计数方法描述为本次新发现。

## 文件与复现

- 证明源码：仓库 `lean/Pnp3600LineSingle.lean`。
- 精确命题：`line-single.statement.txt`。
- 普通编译日志：`line-single.compile.log`。
- 来源、哈希与状态：`line-single.validation.json`。

在仓库的 `lean/` 目录运行：

```sh
LEAN_NUM_THREADS=1 lake env lean -j1 Pnp3600LineSingle.lean
```

源码只导入 `Mathlib.Data.Fintype.Prod`、`Mathlib.Data.Finset.Card` 与 `PEqualNP.Defs`；没有导入其他 Outside 证明。所有辅助声明均置于 `Pnp3600LineSingle` 命名空间。若后续获得正式子任务 ID，需把文件路径、辅助命名空间和最终定理名机械改为该任务规定的名称，再按项目流程检查。

## 其他已核对的边界

上游 `L_meta_2464` 的对称计数以及 `L_meta_2466` 的剩余类别计数带有额外假设；后一项明确需要 `IsReadK(..., 2)`。这些条件不能从本任务的最终输出正确性直接推出。全局拒绝条件可以沿输出向下的纯 OR 路径传递，经过 AND 门时必须另证另一个操作数为 true，不能把所有中间门视为局部可靠。

## Canonical proof copy and reduction review

The strict-checkable copy is `lean/PEqualNP/Outside/Pnp3600LineSingle.lean`,
with theorem `PEqualNP.Outside.Pnp3600LineSingle`. All helper declarations are
under the same namespace. It differs from the ordinary-compiled original only
by namespace qualification and final theorem naming. Its SHA-256 is
`c8c3a227e90b35428269012e032fdc9e28ac1232abf1949272a58b3d26917ea7`.
The original source remains unchanged for provenance.

A bounded review of `R_meta_3600_713.lean` confirmed that its first child is
structurally equal to the proved statement. Its second child bounds the
complementary incidence class by `94 * C.size`; this remains unproved.
A separate diagnostic using the checker's canonical binder renaming and
pretty-printer options printed children of **601** and **1260** characters,
respectively, below the 2000-character limit. It also verified that both
children are closed and nondependent. The reduction conclusion's source
text equals the recorded task statement. These diagnostics do not substitute
for the strict checker; see `children-preview.log` and `reduction-review.json`.

## 后续提交与严格检查状态

归约已通过本机 Chrome 提交为 [PR #7558](https://github.com/open-goat/pequalnp-proofs/pull/7558)，任务台以 `reduced` 成功归还租约。远端归约与本地编译文件逐字节相同。

两次严格检查都没有给出接受裁决：归约检查进程以 137 终止；规范命名的子证明 `Pnp3600LineSingleStrict.lean` 已通过严格脚本的构建阶段，但验证器以 137 退出，脚本报告 `CHECKER FAULT`、退出码 3。普通 Lean 编译通过与严格检查故障必须区分。官方裁决尚待返回。规范命名副本供将来的正式子任务迁移使用；此前已完成的原证明保持不变。
