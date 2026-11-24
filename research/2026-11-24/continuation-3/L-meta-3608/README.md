# L-meta-3608：有限索引规约与未完成搜索

## 结论与验证等级

原命题仍未证明，也没有找到反例。本次完成了可复用的 Lean 有限索引规约。两个 Z3 搜索均因 90 秒超时返回 `unknown`；这些结果不是不可满足证书，也不是 Lean 接受的否定结果。

固定源码版本为 `89b96c0f464824a164434fb460926400b9943047`，工具链是 Lean 4.36.0。最终普通 Lean 编译结果、文件哈希和搜索状态记录在 `VALIDATION.json`。本次没有运行项目严格检查器，没有提交上游证明或归约。

## 原任务

电路有 14 个后续门，输入为九个原始变量和免费提供的 `x₀ ∨ x₂`。它有恰好两个 NOT 门，第一个在位置 3 到 6，第二个在位置 12 以前或等于 12。NOT 至多读取一个输入，其他门至多读取两个输入。输出线为 23。

题设要求编号 0 到 22 的每条线都出现在某个门的输入中，多次读取的线至多三条；直接合并两个不同原始变量的 AND/OR 门，至少有一个变量被多次读取。目标是找到 512 个布尔输入中的一个，使输出不同于给定 Petersen 子图的边函数。公开原命题保存在 `gap.json`。

## 已完成的 Lean 规约

`Pnp3608Finite.lean` 定义 `capGate` 和 `capCircuit`，将所有门输入索引 `i` 换成 `min i 23`，保持门操作、门次序和输出索引。

这个界限是 **0 到 23，包含 23**，不是只保留已经产生的线。在每个门执行前，线列表最长为 23；因此索引 23 以及更大的索引当时都读出默认值 `false`。将大索引截断为 23 保留了这种行为。原有较小的未来线索引也不改动，其默认值行为仍然保留。规约没有假设所有输入都向后引用。

形式化结果包括：

- `getD_cap`、`step_cap`、`fold_cap`：逐步读取和完整执行不变。
- `wires_cap`、`eval_cap`、`eval_cap_3608`：全部线值与最终输出不变。
- `count_operands_cap`、`covers_cap`、`multi_cap`：小于 23 的索引计数、覆盖条件及多读线集合不变。
- `fanInTwo_cap`、`unaryNot_cap`、`size_cap`：门类型、扇入限制、NOT 的一元限制和门数保留。
- `two_nots_cap`：两个 NOT 门的位置和唯一性保留。
- `raw_pairs_cap`：直接合并两个原始变量时的多读线条件保留。
- `all_indices_cap`：规约后所有输入索引都不超过界限。
- `step_sortPair`、`fold_sortPair`：AND/OR 的双输入按索引排序不改变执行结果。

这些是辅助定理，不是 `L-meta-3608` 的最终证明。正式子题的形状没有被替换或削弱。

## 搜索模型与实际结果

`search_3608.py` 使用 Z3 5.4.1。模型包含全部 14 个门的操作、0/1/2 输入长度、两个 NOT 的位置、覆盖与多读限制，并允许未来索引。AND/OR 双输入按索引排序，利用交换律消除顺序对称性。所有操作均按项目 `Circuit.wires` 的默认 `false` 语义解释；空 AND 和空 NOT 为 `true`，空 OR 为 `false`。

| 搜索 | 输入样本 | 时间限制 | 结果 |
|---|---:|---:|---|
| 完整真值表 | 全部 512 个输入 | 90 秒 | `unknown` / `timeout` |
| 边界样本放宽 | 35 个输入 | 90 秒 | `unknown` / `timeout` |

35 个样本包括全零、全一、九个单变量输入、十二条边及十二个极大独立集。第二个模型只要求在这些样本上正确，是完整问题的放宽。如果它返回 SAT，仍必须逐一检查全部 512 个输入；本次没有获得这样的模型。两次搜索输出分别保存在 `search-result.json` 与 `search-frontier-result.json`。

## 数学路线与尚缺的论证

12 个至多二元的门加上两个至多一元 NOT，最多有 26 个输入出现位置。覆盖 23 条线后，只剩三个额外读取位置。因此题设“多读线至多三条”本身是已有计数约束的结果，并不能单独提供新的有力归约。此计数也已用于上游 `R_meta_2517_1.lean`。

把免费 OR 作为首门加回去，可以得到 15 门、13 个非 NOT 门的九输入电路。已有 `L_meta_3438.lean` 的通用下界也是至少 13 个非 NOT 门，所以任何反例都必须达到该下界。

已有五分支线论证通过 `Least` 对一个清理并最小化后的电路成立。不能由此直接宣称原后缀恰好有三条多读线、原始输入 0 和 2 各只读一次，或原后缀没有未来线引用。若继续走这条路线，需要证明相关清理、别名消去和最小化步骤保留所需的分支预算与种子 OR 结构；本次没有完成这种转移。有限索引规约只解决无界自然数索引的问题，不提供这一更强的结构正规化。

## 复现

将本目录的 `Pnp3608Finite.lean` 放入固定仓库的 `lean/` 目录，然后在该目录执行：

```sh
LEAN_NUM_THREADS=1 lake env lean -j1 Pnp3608Finite.lean
```

在本研究目录中，使用安装了 `z3-solver` 5.4.1.0 的 Python：

```sh
python search_3608.py --timeout-ms 90000 --output search-result.json
python search_3608.py --sample-mode frontier --timeout-ms 90000 --output search-frontier-result.json
```

超时和搜索顺序可能随环境而变化；应以各次实际输出为准。完整模型若返回 SAT，脚本会独立重新计算 512 个布尔输入并核对结构条件。任何搜索输出都不能替代 Lean 证明。

## 公开来源

- [任务项目](https://pequalnp.com/)
- [固定源码版本](https://github.com/open-goat/pequalnp-proofs/tree/89b96c0f464824a164434fb460926400b9943047)
- [父归约 R-meta-2517-1](https://github.com/open-goat/pequalnp-proofs/blob/89b96c0f464824a164434fb460926400b9943047/lean/PEqualNP/Outside/R_meta_2517_1.lean)
- [13 个非 NOT 门下界](https://github.com/open-goat/pequalnp-proofs/blob/89b96c0f464824a164434fb460926400b9943047/lean/PEqualNP/Outside/L_meta_3438.lean)
