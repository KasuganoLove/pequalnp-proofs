# P vs NP 研究记录 · 2026-11-24

本项目使用 [KasuganoLove/pequalnp-proofs](https://github.com/KasuganoLove/pequalnp-proofs)。这些研究记录保存于独立分支 `codex/pnp-research-2026-11-24` 的 `research/2026-11-24/` 目录；该分支不提交给上游。正式贡献另建分支，每个上游 PR 只增加对应任务的一份 Lean 文件。

## 当前结果

| 任务 | 已有结果 | 尚未完成的部分 |
| --- | --- | --- |
| **L-meta-2534** | 已在固定 Lean 环境中证明其正命题 `Pnp2534Positive.positive`。分配的任务是该命题的否定，因此这份本地证明说明分配命题为假。 | 这是已验证的数学诊断，尚无本工作的上游 `ACCEPTED` 裁决。 |
| **L-meta-2309** | 已在本地证明 `Pnp2309Scratch.active_reader_count_positive`：任务所用的归一化有效读取门数至少为 1。结合任务假设“至多 1”，剩余情形恰好为 1。 | 完整任务尚未证明。现有上游约化 `R_meta_2309_1` 还需要收缩首个反相器，并排除至多 14 个门、至多一个直接读取门、允许输入极性翻转的电路。 |
| **L-meta-2604** | 对分配的完整命题，本地 Lean 编译、文件格式检查及公理审计已通过。命题将一个足以使输出为真的 OR 输入提升到最终 OR 门，并保持电路函数不变。 | 提交前续租返回 HTTP 410：该题已被其他参与者证明并关闭。本工作未提交该题 PR，也未获得该题的上游接受或贡献署名。本地严格验证程序以退出码 137 结束，没有给出判定。 |

这里区分三种状态：**本地 Lean 编译通过**、**本地严格检查通过**、**上游权威检查接受**。前两种不能替代最后一种。后续正式状态以对应上游 PR 的检查记录为准。

### L-meta-2534：为什么最初的反例思路不成立

模型允许不存在的输出线读取为 `false`，所以常假函数可以用零个门表示。正命题证明通过常量传播删除附加的假输入及其 OR 读取门，并分别处理输出为常量或保留线路的情形。常真输出需要单独证明剩余预算至少容纳一个常真门。

### L-meta-2309：已排除零读取，尚未排除一次读取

零读取时，切换 `x₀` 不会改变任何后续线路。全假输入与仅 `x₀` 为真的输入排除了输出线 9 和 0；仅 `x₁` 为真与 `x₀,x₁` 同时为真的输入则要求目标函数改变，产生矛盾。证明使用了逐门求值的不变式，并处理 NOT 只读取第一个输入的规则。

“只有一个直接读取门”仍允许该门的输出被后续门反复使用，因此不能据此当作整条电路只使用一次该变量。恰好一次读取的门数下界仍是实质性缺口。

## 文件与复现

- `Pnp2534PositiveScratch.lean`：正命题的完整本地证明。
- `Pnp2309Scratch.lean`：读取门数至少为 1 的完整本地证明。
- `L_meta_2604.lean`：本地完成的完整证明，因题目已关闭而未提交。
- `assignments.json`：三个任务的原始公开 `gap` 字段，包括精确命题和允许导入的模块。

在已安装 elan、`lake` 可用的环境中，从仓库的 `lean/` 目录执行：

```bash
lake exe cache get
lake build PEqualNP.Defs
lake env lean ../research/2026-11-24/Pnp2534PositiveScratch.lean
lake env lean ../research/2026-11-24/Pnp2309Scratch.lean
lake env lean ../research/2026-11-24/L_meta_2604.lean
```

| 依赖 | 固定版本 |
| --- | --- |
| Lean | `leanprover/lean4:v4.36.0` |
| Mathlib | `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` |
| 本次上游源码基线 | `053be9da917778f72c6ebf4516bc3fbbce26e187` |

保留仓库的工具链与依赖锁定文件，不运行 `lake update`。任务办理规则见 [join.txt](https://pequalnp.com/join.txt) 与 [CONTRIBUTING.md](https://github.com/brilliant-hq/pequalnp-proofs/blob/main/CONTRIBUTING.md)。本目录只保存公开数学内容；任务租约与凭据保存在本地运行状态中。

## 来源与许可

`Pnp2534PositiveScratch.lean` 中的常量传播、线路模拟及相关辅助证明复用并改写自上游 [`L_meta_174.lean`](https://github.com/brilliant-hq/pequalnp-proofs/blob/053be9da917778f72c6ebf4516bc3fbbce26e187/lean/PEqualNP/Outside/L_meta_174.lean)。`Pnp2309Scratch.lean` 的列表与线路模拟辅助证明参考了同一仓库的 `L_meta_2305.lean`，并加入本任务的有效读取不变式及具体输入论证。

上述上游代码使用 **Apache License 2.0**；许可证保留在仓库根目录的 [`LICENSE`](../../LICENSE)。本记录的状态说明不构成对 P vs NP 已解决的声明。
