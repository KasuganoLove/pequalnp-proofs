# 电路模型与可用结论的边界

核对日期：2026-11-24。以下文献用于排除不成立的推理捷径；它们本身不证明本次任务的 27 门或 124 门下界。

## 单层化需要额外证明

Stasys Jukna 的 *Disproving the Single Level Conjecture* 给出二次布尔函数族：一般单调电路可以达到线性规模，而只有一层 AND 门的单调电路需要接近二次的规模。因此，不能把任意共享 AND/OR 电路无代价改写为一层 AND 门后套用覆盖计数。

这项结果针对一般函数族；它没有否定 Fano 平面或 4 阶射影平面可能具有特殊正规形。若本次任务要使用这样的正规形，仍须对这些图和题目的精确电路定义单独证明。

来源：[ECCC TR05-021，含作者修订稿](https://eccc.weizmann.ac.il/report/2005/021/)；[SIAM Journal on Computing 36(1), 83–98, DOI](https://doi.org/10.1137/S0097539705447001)。

## Read-k 约束的是形式单项式中的次数

Jukna 的 *Notes on Boolean Read-k and Multilinear Circuits* 将布尔电路的 OR、AND 形式上换成加法、乘法。Read-k 要求每个 prime implicant 至少有一个支撑相同、各变量次数不超过 k 的形式单项式。它不是输入线的扇出限制，也不是每个变量在整个 DAG 中只出现 k 次。

因此，L-meta-2309 的“只有一个直接读取门”不能直接替换为 read-once 条件；L-meta-2348 的形式导数也不能直接等同于布尔函数在该输入上的敏感性。布尔恒等式 x AND x = x 不会消除形式乘积中的变量重数。

来源：[arXiv:2207.08701v3，2023-11-21](https://arxiv.org/abs/2207.08701v3)。具体证明仍以仓库 `Defs/ReadK.lean` 和分配命题为准。

## 仓库现有精确门数公式的范围

上游的 [Note 1](https://github.com/brilliant-hq/pequalnp-proofs/blob/053be9da917778f72c6ebf4516bc3fbbce26e187/notes/note-1-edge-function-exact-size.md) 讨论森林、环和长链图的精确值 |E| + tau(G) - 1。其中长链图定理要求高阶顶点之间有足够长的距离。当前两个射影平面关联图的高阶顶点直接相邻，不满足该条件，因而不能直接引用这条公式作为目标下界。

同样，标准星形构造给出的 27 或 125 个门是上界。将其升级为任意单调共享电路的下界，正是当前尚缺的论证。
