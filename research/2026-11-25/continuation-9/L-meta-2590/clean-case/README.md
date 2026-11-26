# L-meta-2590：Petersen 图的干净电路 20 门下界

本组件已完成并冻结：两个证明模块普通 Lean 编译退出 0、日志为空；六个关键声明的 axiom audit 退出 0，仅报告 `propext`、`Classical.choice`、`Quot.sound`。没有运行官方严格检查，没有提交 PR，也没有取得官方接受结果。

**这不是整个 L-meta-2590 的证明。** 它证明所有初始 AND 已安全的 Monotone2 电路至少需要 20 门，并给出任意 19 门反例必须具有的明确脏 AND 见证。

## 精确范围

| 声明 | 假设 | 结论 |
| --- | --- | --- |
| `Pnp2590Graph.target_eq_graphFun` | 精确公共任务的 15 项目标表达式 | 等于所定义 Petersen 简单图的 `graphFun G ∅` |
| `noFourCycle`、`edge_count`、`cover_ge_six` | 同一精确图 | 无四环、15 条排序边、任意顶点覆盖至少 6 个点 |
| `Pnp2590CleanBound.clean_top_cover` | 任意有限 C4-free 图；精确 AO2、TopForm、所有 AND 均 BelowF | 构造顶点覆盖，其点数不超过电路的实际 AND 门数 |
| `top_and_ge_six`、`top_or_ge_fourteen`、`top_size_ge_twenty` | Petersen；精确 AO2、TopForm、所有 AND 均 BelowF | AND ≥ 6、OR ≥ 14、总门数 ≥ 20 |
| `clean_size_ge_twenty`、`clean_or_ge_fourteen` | 精确计算 Petersen 目标的 Monotone2；所有 AND 均 BelowF | 原电路总门数 ≥ 20、OR ≥ 14 |
| `small_correct_has_dirty_and` | Monotone2，门数 ≤ 19，精确计算同一目标 | 存在真实 AND 门及目标负输入，使该门取真 |

`BelowF` 的含义是该 AND 门取真时目标函数必取真。几何有限证书均使用 `decide +kernel`；没有 `native_decide`。

## 证明连接和适用限制

泛型覆盖证明复用上游 `L_meta_2235.s2231` 的中心构造：每个相关 AND 的两个 OR 支持构成图内矩形；无四环保证至少一边至多含一个点，选该侧作为中心。全部中心的并覆盖图边，其点数不超过 AND 门数。新的干净 TopForm 边见证定理覆盖所有被接受的边，无需额外 read-once 假设。结合 Petersen 顶点覆盖下界得到 AND ≥ 6；复用 continuation-8 的 OR 专用计数得到 OR ≥ 14。

从一般干净 Monotone2 到 TopForm 的步骤明确保持初始干净性、总门数上界和 OR 上界，覆盖空门、单输入门及缺失读取的默认 false 语义。它并不直接保持初始 AND 上界。因此 **AND ≥ 6 只对上述 TopForm 电路声明**；转回原始干净 Monotone2 的声明是总门数 ≥ 20 和 OR ≥ 14。不能把这两种范围混淆。

最后的脏 AND 见证是一个任意目标负输入。它不保证输入支撑是一个非边对，不保证所有 singleton 上 AND 关闭，也不假设电路最小。排除这种脏电路，或者给出一个真实 19 门电路，仍是完整 2590 的剩余工作。

## 来源和独立审阅

- Petersen 的边表和目标表达式取自父目录 `statement.txt` 对应的公共 L-meta-2590 命题。
- 通用中心/覆盖构造改编自上游 `L_meta_2235.s2231`，遵循仓库 Apache-2.0 归属；原 read-once 限制由已证明的干净 TopForm 见证条件替代。
- OR 计数、干净类最小化及常量传播复用冻结的 continuation-8 模块，保留其中 L1501、L2235、Pnp2343Pruning 等的原始归属。
- `remote_status` 代理做了独立只读审阅：边表与公共2590一致；未发现前提或结论范围错误；确认 AND ≥ 6 限定于 TopForm，脏见证没有偷偷强化为 pair 或 unit-off。审阅未修改源码或运行 Lean。

## 复现

完整准备步骤见 [REPRODUCE.md](REPRODUCE.md)，可执行入口为 [reproduce.sh](reproduce.sh)。脚本要求独立工作树固定在上游 `259523a5b265318b84f9377f2feb965fd213f898`，使用已有 Lean 4.36.0 和固定 Mathlib 缓存，核对全部冻结源文件后按依赖顺序编译并运行 axiom audit。它拒绝覆盖不同内容的源文件。

```bash
bash /absolute/path/to/clean-case/reproduce.sh \
  /absolute/path/to/fresh-checkout \
  /absolute/path/to/research/2026-11-25/continuation-8
```

本次归档仅检查了脚本语法、11 个源码的路径和 SHA-256、依赖顺序；没有执行脚本或再次运行 Lean。哈希、原始编译记录和精确状态见 `validation.json`。本目录仅保存已完成的研究组件，没有规范 `L_meta_2590` 完整证明文件。

## 停止点

CleanBound 的成功退出于 07:53:13 UTC 观察到。父代理随后报告续租在 **07:53:45 UTC 返回 410**，并要求停止新证明工作。此后仅收集已经启动的只读 axiom audit 和归档冻结文件；没有扩展定理或操作 lease。后续研究需先有新的有效任务授权。
