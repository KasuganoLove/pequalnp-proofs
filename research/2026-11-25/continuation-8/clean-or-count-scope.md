# 干净电路的 OR 门计数：已检查组件

`Pnp4201CleanOrCount.lean`（SHA256 `171665a973dec6ebe230ad3daca21d98a8065ef73f412f87028b32c7f1a202fd`）已通过普通 Lean 编译，退出码 0，日志为空，并产生可导入的 olean。本记录不是官方严格检查或上游接受记录。

## 精确结论

`PEqualNP.Outside.Pnp4201CleanOrCount.clean_top_or_bound` 对任意有限简单图 `G : SimpleGraph (Fin n)` 和电路 `C` 证明：若 `G` 满足 `TopForm.NoFourCycle`，`C` 满足 `TopForm.IsAO2`、精确计算 `graphFun G ∅`、处于 `TopForm G C`，且每个真实 AND 门均满足 `BelowF G C j`，则排序后的图边数至多是题目原样使用的 OR 门 `List.countP` 加一。

该定理没有总门数最小性、OR 预算最小性、活门、输入不重复或 read-once 前提。它也不声明任意正确电路都存在干净替代电路。

## 证明连接

1. `fire_trace`：任意值为真的线，要么在 OR 支持中包含一个值为真的原始输入，要么通过 OR 链到达一个值为真的 AND 门。
2. `or_reach_into_input` 将 AND 操作数的 OR 可达性转为严格锥关系。干净性和 TopForm 联合排除该操作数的 AND 祖先。
3. 对被接受的边输入，输出处的原始输入见证由单点输入拒绝性质排除；因此得到一个 OR 链通向输出的 AND 门。其两操作数的原始输入见证分居边的两个端点。
4. 从上游 `L_meta_2235.core` 提取 OR 专用计数：叶侧 OR 集与输出侧 OR 集不交，边数不超过两者总数加一。最终将索引集合基数精确转换为公开题目的 OR `List.countP`。

计数依赖上游 L2231/L2233/L2234，经 `L_meta_2235` 提供；线值和锥 API 来自 `L_meta_1501`。源文件均按仓库 Apache-2.0 归属引用；本文件未使用 L1501 的无预算全局最小电路结论。

## 独立审阅干净类最小化

只读审阅 `Pnp4201CleanBudgetTopForm.lean`，SHA256 `48e7d9aa2a5ddd8b8be6a118903cb74c8e4e0b36d7cc22e74bedc5568cd465fc`，未发现范围错误：`CleanLeast` 的每个比较电路显式要求 `Clean`；`exists_clean_minimum` 的 `Nat.find` 集合显式包含同一函数、干净性和原 OR 预算；选择后的比较预算通过传递性回到原预算。`V1_clean` 与 `V2_clean` 使用每个目标负输入上的保留门值相等来保持干净性，V2 的新增末门明确为 OR。不存在从无干净性约束的最小电路推断干净性的步骤。

## 复现

在已按仓库固定版本配置的 `lean/` 目录运行：

```bash
lake env lean -o .lake/build/lib/lean/PEqualNP/Outside/L_meta_2235.olean PEqualNP/Outside/L_meta_2235.lean
lake env lean -o .lake/build/lib/lean/PEqualNP/Outside/L_meta_1501.olean PEqualNP/Outside/L_meta_1501.lean
lake env lean -o .lake/build/lib/lean/Pnp4201CleanOrCount.olean Pnp4201CleanOrCount.lean
```

固定 Lean 4.36.0；Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`。源码基线及最新公共 Defs 的逐文件一致性见同目录 `env-compatibility.json`。
