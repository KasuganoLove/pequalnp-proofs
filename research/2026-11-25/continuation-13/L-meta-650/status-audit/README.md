# L-meta-650：当前依赖与可复用证明审计

本次只读审计未找到可直接解决 650 的已完成证明。650 要求完整 PG(2,3) 关联函数的至多 63 门 Monotone2 电路；目前已检查的规范化与零/单 junk 结果，只把反向下界推进到至少两个 junk AND 的情形。这里没有新数学证明、Lean 编译、任务分配或远端写入，也不是本阶段的官方提交成果。

## 时间与来源

- [公开任务台](https://data.pequalnp.com/data/desk/gaps.json)：2026-11-25 10:34:05 UTC 获取，内容时间 10:32:40.336 UTC，完整响应 SHA256 记录在 public-status.json；完整全台 JSON 不随本目录归档。
- [650 状态](https://pequalnp.com/desk/step?gap=L-meta-650)：10:34:03 UTC 返回 leased、holders=1；这不是新分配请求，也不据此推断持有者身份。
- 源码从固定上游提交 `62127f3af70786085fa09c6453d036c7cde890ce` 于 10:39:50 UTC 读取；下载的六个依赖文件 SHA256 全部匹配公开台账。4181 的现有本地文件亦匹配。
- 公开代码仓库为 [open-goat/pequalnp-proofs](https://github.com/open-goat/pequalnp-proofs)。此目录仅保存所需状态子集、来源与哈希，不重复保存大型第三方 Lean 文件。

## 正反命题和现有构造分支

650 与 972 使用相同 26 输入、52 条边和 Monotone2 语义。972 断言所有正确电路至少 64 门，因此它等价于 650 的否定。2032 是 972 的字面否定，逻辑上与 650 等价；不能把 2032 称为 650 的反命题。上述三题在本次快照中仍 posted，均无打开的证明 PR。

| 650 的 live cut | 已 checked 的子题 | 未解决的实质子题 |
|---|---|---|
| R_meta_650_713 | 2054：有限几何负样本覆盖 | 2056：满足边界测试的 63 门见证 |
| R_meta_650_517 | 2217：用 AND、OR 两门接回一点 | 2215：25 输入、61 门、共享两个输出的见证 |
| R_meta_650_1 | 3771：有限几何负样本覆盖 | 3773：带规范首门的 63 门见证 |

三条 cut 均 open，650 的 reductions_live=3。没有第四条归约名额。已检查的几何或组合引理不提供这些电路见证。

## 可直接引用的反向下界依赖

[R_meta_972_5](https://github.com/open-goat/pequalnp-proofs/blob/62127f3af70786085fa09c6453d036c7cde890ce/lean/PEqualNP/Outside/R_meta_972_5.lean) 精确分成四个假设：

| 子题 | 语义 | 当前状态 |
|---|---|---|
| 4181 | 非空图上的正确 Monotone2 电路，可转为不更大的最小 IsAO2 TopForm 电路 | checked |
| 8725 | 二分且无四环图的最小 IsAO2 电路，junk 数不等于 1 | checked |
| 8791 | PG3 最小 TopForm 电路若 junk 为空，则至少 64 门 | checked |
| 8793 | PG3 最小 TopForm 电路若至少两个 junk，则至少 64 门 | posted，无证明 PR |

第一项带非空图和正确图函数条件。第二项没有断言 junk 总为空。第三项只覆盖零 junk。第四项仍是全下界的实质缺口，不能通过合成前三项消去。

8793 还有三条 live cut。R8793_7 用已 checked 的通用 ledger 7862，剩余 8943 要排除具有给定三个计数约束的小电路。R8793_291 用已 checked 的计数 9047，剩余 9049 要证明

`13 + |Ustar| ≤ |tops \ centreless| + 2|centreless| + |junk| + |orN \ lam|`。

8943、9049 都是 depth 2，快照中无证明 PR。它们的完整语句保存在 public-status.json。[PR #13108](https://github.com/open-goat/pequalnp-proofs/pull/13108) 于 09:42:48 UTC 合并 R8793_26，把首门输入归一到 `[0,b]`、`b ∈ {0,1,13,15}`，仍要求输运和四类下界子命题；当前快照未列出该 cut 的新子题编号，本审计没有猜测编号。

## 新结果与容易混淆的记录

**971 是 Heawood 专门定理。** [PR #13091](https://github.com/open-goat/pequalnp-proofs/pull/13091) 已于 09:34:44 UTC 合并；台账把源文件标为 checked，SHA256 为 `24a7f69db99fb56060c3d343f15f36688f1ee8fdc1b3d76f0942ee9874c2138e`。其最终定理是 14 输入、21 条边的 Heawood Monotone2 门数至少 27，并非所有无四环图的通用公式，也不是 PG3 的 64 门下界。若想由限制输入转移该结果，还需另证足够的删门计数，不能直接推出 972。连接器返回的 advisory run 失败记录也保留在 pr-evidence.json；本审计以官方 checked 条目和实际合并状态表述事实，没有虚构未返回的 ACCEPTED 评论。

**#13253 不是 63 门见证。** [作者关闭说明](https://github.com/open-goat/pequalnp-proofs/pull/13253#issuecomment-7159431947) 明确说投错 step ID。66 行源文件用一个零输入 AND 的恒真电路，反驳“任意 Monotone2 函数都可转为不更大的精确二输入 IsAO2 电路”。IsAO2 在全 false 输入必为 false，因此该无非恒定前提的归约假设过强。它没有计算 PG3 函数，也不证明公开 L8781 的语句。对应 R972_733 已在本次台账标为 dead；不要把该源文件当作 650 或 8781 的完整证明。带非恒定图函数条件的 checked 4181 不受这个反例影响。

**旧 PG3 normal-form 缺口仍在。** 1684、1692、2718、5741、5743、8847 仍未解决。2716 的 [PR #4938](https://github.com/open-goat/pequalnp-proofs/pull/4938) 仍打开且未合并，head=`1e1b84679544b083d3e240bac25ae6be219b8dcd`；此前记录有官方 ACCEPTED，但这不解决 sibling2718 的规范化存在性。1751 的无嵌套 AND 下界已 checked，nested 最小电路分支6140仍未解决。

## 归档范围与使用

`dependency-source-hashes.json` 给出固定 URL、大小和哈希，供重新取回第三方证明。`public-status.json` 是相关任务与归约的紧凑子集，`pr-evidence.json` 保存必要 PR 元数据，`L-meta-8793.statement.txt` 保留精确残余命题。此处没有任何租约标识、授权材料、完整全台数据、二进制或编译产物。

结论限于截至上述时刻可查到的来源。仍需新的数学论证或一个经过完整正确性验证的 63 门电路，才能提交 650 或其反向下界的完整证明。
