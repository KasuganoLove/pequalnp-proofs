# 2026-11-25 第四轮续推

## 完整证明：L-meta-7019

`L_meta_7019.lean` 完整证明任务台发布的精确原命题。项目固定环境中的检查器返回 **ACCEPTED (check)**、退出码 **0**，内核重检 **1,834** 项声明。公理只有 `propext`、`Quot.sound`、`Classical.choice`。

目标是将 `ReadK.lineSingle` 标记的关联对数量控制在 `38 * C.size`。这是定义库中的证明树标记条件，不是整个电路中某个输入只被读取一次。我们复用上一轮已经完成的更强结论 `6 * C.size`：对每条线 l，只激活该线，同时在点侧激活所有不与 l 关联的点。此输入没有活跃的关联点线对，活跃线数恰好为 1，所以题目的稀疏拒绝条件适用。由此获得计数定理所需的单线拒绝性质，最后把系数 6 放宽到 38。

计数证明改编自上游 `L_meta_2462` 的三类关系注入论证。上一轮去掉了没有使用的全域正确性与几何条件，并明确给出原论证已蕴含的系数 6。本轮新增的是对 7019 公开陈述的适配、命名空间整理与完整检查；不把原有计数方法记作新发明。

- [完整证明](L-meta-7019/L_meta_7019.lean)
- [原命题](L-meta-7019/statement.txt)
- [检查器原始输出](L-meta-7019/CheckLemma-check.log)
- [验证摘要和文件哈希](L-meta-7019/validation.json)

截至本次记录，尚未取得 L-meta-7019 的正常任务台分配。公开状态接口显示该题仍开放；参与说明要求通过 `/desk/next` 取得分配，未提供定向认领参数。正常与 hard 队列请求都返回暂时无可分配题目。因此本文件是**本地完整检查通过的研究成果，尚未向上游提交，没有官方收录结论**。未尝试未公布的定向认领接口。

## 已修复的归约：L-meta-3600

[PR #7558](https://github.com/open-goat/pequalnp-proofs/pull/7558) 原版本的官方退回理由为 `reduce-extra`。定义展开额外生成了 `PEqualNP.MetaComplexity.NestedCover.gateAt.eq_1`，违反归约文件只能声明一个定理的要求。

修复仅将该处证明改为直接应用 `List.getD_eq_getElem`，两个子命题和结论均保持原样。修复后检查器返回 **ACCEPTED (reduce)**、退出码 **0**，内核重检 **1,667** 项声明。

两个子题分别控制 lineSingle 类与其补集，系数为 6 和 94。第一项已有完整证明，第二项仍开放；归约本身不证明整个射影平面电路下界。

原题现在已有三个接受并合并的活跃归约：`R_meta_3600_421`、`R_meta_3600_584`、`R_meta_3600_672`。参与说明规定每题最多三个活跃归约，因此本轮保存修复，不将其作为第四个活跃归约重新提交。香港时间 2026-11-25 11:58:25 已关闭 #7558，并在说明中链接本地核验记录。修复提交保留在用户分支 `codex/reduce-meta-3600-713`，提交为 `0a0f000c43698759cba85b5cd1e11b0d8a442191`。已关闭 PR 的历史 head 仍为原提交；修复内容以本目录和用户分支为准。

- [修复后的归约](L-meta-3600/R_meta_3600_713.lean)
- [精确原命题](L-meta-3600/statement.txt)
- [完整检查日志](L-meta-3600/CheckLemma-reduce.log)
- [验证摘要](L-meta-3600/validation.json)

## L-meta-1031：已验证的局部删门与模型衔接

本轮正常领取了 L-meta-1031，并持续处理其最小电路结构问题。完整原题尚未证明或反驳；三个归约名额也已占满。

三项新的研究结果通过固定 Lean 环境编译：

- [Pnp1031Pruning.lean](L-meta-1031/Pnp1031Pruning.lean) 给出真正删除一个门、重定向所有后续引用与输出的充分条件。替代线在所有输入上不超过原门，并在每个图边输入上与它一致时，删门保持整个图函数和电路模型，且恰好减少一个门。由此排除某类交集只有一个点的纯 OR 乘积出现在最小电路中，并限制其安全后继。
- [Pnp1031Normalization.lean](L-meta-1031/Pnp1031Normalization.lean) 证明非恒定函数的 Monotone2 电路可在不增加总门数的条件下变成 IsAO2 电路；对图边函数补上无边图情形后，得到两种最小性定义的等价性。此处所有 AND 和 OR 门均计入成本。
- [Pnp1031OwnershipFinite.lean](L-meta-1031/finite-tests/Pnp1031OwnershipFinite.lean) 证明任意简单图和任意 Monotone2 电路中，所有 AND 门全局正确，当且仅当每个 AND 门都拒绝全零输入和全部非边双点输入。双点允许重复端点，所以包含单点测试；零输入测试不可省略。此结论不需要电路输出正确、最小性、无三角形或无四环假设。

前两份文件分别改编已有门绕接和常量传播代码；第三份复用线值求值引理，新增独立输入上的见证归纳。它要求所有 AND 门一起满足测试，只测试一个门不够。另有 [条件式归属推论](L-meta-1031/finite-tests/Pnp1031OwnershipBridge.lean)，组合现有上游定理，从满足这些测试的最小电路构造每个 AND 都拥有非空星形边集的最小电路。

来源、精确限制、验证级别与尚缺的全局清理步骤见 [删门与模型说明](L-meta-1031/README.md) 和 [有限测试说明](L-meta-1031/finite-tests/README.md)。上述研究文件均为普通 Lean 编译通过，不声称已通过原题的官方检查。完整原题仍缺少满足这些条件的最小电路的存在性。本轮租约于香港时间 2026-11-25 12:02:54 以 `missing_lemma` 归还，任务台确认成功。

## 上游状态核对

香港时间 2026-11-25 上午核对：

| PR | 实际状态 |
| --- | --- |
| [#7182](https://github.com/open-goat/pequalnp-proofs/pull/7182) | 官方 ACCEPTED；香港时间 2026-11-25 04:44:48 合并。父题 3233 已由后续工作关闭，本归约在任务台标记为 moot。 |
| [#7168](https://github.com/open-goat/pequalnp-proofs/pull/7168) | 其他贡献者的证明先合并，本 PR 因重复关闭；没有观察到数学拒绝。 |
| [#7558](https://github.com/open-goat/pequalnp-proofs/pull/7558) | 原版本官方退回；本轮因归约名额已满关闭。修复版本本地检查通过并保存在用户分支和本目录。 |

评论、官方运行编号、已发布子题映射与公开任务台节选保存在 [audit](audit) 中。用户此前新增的 2798 反证及 3233 原生检查记录保留原样。

## 复现

本轮使用官方提交 `57164c3618362178843e2ea37bd01613f4037ae2`、Lean `v4.36.0`、Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`。检查器和构建配置均未修改；完整 Mathlib 缓存和 `PEqualNP.Defs` 按固定版本构建。

在此官方版本的独立检出中，将证明复制到同名 `lean/PEqualNP/Outside/` 路径，保留原命题文件，分别运行：

```sh
node tools/check-lean.mjs lean/PEqualNP/Outside/L_meta_7019.lean path/to/L-meta-7019/statement.txt check
node tools/check-lean.mjs lean/PEqualNP/Outside/R_meta_3600_713.lean path/to/L-meta-3600/statement.txt reduce
```

完整日志中的 MANIFEST 保存了所有依赖源文件的 SHA-256，可据此识别后续定义变化。
