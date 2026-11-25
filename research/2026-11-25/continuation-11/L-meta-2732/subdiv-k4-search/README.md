# 细分 K4 的指定 free-OR 构造搜索

## 结果

300 秒的有界随机搜索正常结束，退出 0。**没有找到 14 门后缀，也没有得到 26 门 Heawood 见证。** 这不是该受限构造不存在的证明，更不能推出所有 26 门 Heawood 电路不存在。

- 用时：300.001 秒。
- 求值：3,224,441,185 次，包含重复状态。
- 重启：26,870 次；初始单字段邻域检查 68,376 次。
- 最优 24 个极值行误差：FP 0，FN 1。
- 对最优候选独立枚举全部 1,024 个原始输入：FP 0，FN 13。

`best-14.json` 明确不正确，不是证明见证。没有生成 `candidate-14.json` 或 `heawood-26.json`。

## 目标、耦合输入和计数

十个原始输入按 `[a,b,e,f,c,d,p,q,r,s]` 编号为 0–9。边表为

```text
(0,5),(1,5),(2,4),(3,4),
(0,6),(2,6),(0,7),(3,7),
(1,8),(2,8),(1,9),(3,9).
```

额外的第 10 号线固定等于 `raw4 OR raw5`，不是独立第十一个布尔变量。搜索在这 11 条初始线上构造至多 14 个二输入 AND/OR 门。若成功，连同指定 OR 就得到 15 门核心。

12 个边输入和全部 12 个极大负输入完整约束这个单调的十输入函数。`prepare.py` 独立枚举极大负输入，并逐项比对 ownership 代理提供的 `five-star-free-or/problem.json`；24 行均按相同的耦合 OR 编码。

种子来自四个原顶点的 star 构造（删除一个门）以及六个细分顶点的 star 构造（删除三个门），共 4352 个种子，可能重复。搜索允许任意回读的二输入 AND/OR、重复操作数及任意输出线，没有强制干净性或门数配比。

## 与完整 Heawood 的连接已校验

原始输入映射到 Heawood 输入：

```text
0…9 -> [0,3,2,4,13,7,8,10,12,11].
```

指定 OR 在完整电路中为第 14 号线，后缀中所有线号 `w≥10` 映射到 `w+4`。随后补上中心 1（额外邻居 9），再补中心 5 和 6 的 star；后缀若为 14 门，总数为 `14+12=26`。

`verify_and_map.py` 独立验证 1,024 个原始输入，并对正确核心拼接后独立枚举全部 16,384 个 Heawood 输入。这个拼接流程已经用已知 15 门后缀跑通：它连同免费 OR 是 **16 门核心**，最终形成 **27 门** Heawood 电路，16,384 个输入全部通过。这个检查验证映射和线号偏移，没有冒充目标 14 门后缀。

## 实际运行与文件

- `search14.cpp`：本次实际搜索源码，改编自相邻 `search26/search26.cpp`。
- `prepare.py`、`problem.json`、`rows.txt`、`seeds.txt`：完整输入与种子。
- `verify_and_map.py`：独立标量验证及拼接。
- `search.log`、`run-summary.json`：运行日志和统计。
- `best-14.json`、`best-14-verification.json`：失败候选及反例检查。
- `known-star-suffix15.json`、`known-star-verification.json`、`heawood-27.json`：仅用于校验的正确 27 门基线。

单线程进程使用 `nice(5)`，地址空间上限 512 MiB、CPU 上限 310 秒。编译、搜索、标量检查均退出 0，编译无警告。未运行 Lean、strict checker、远端写入或 lease 操作。

仅在具有相应有效任务授权时重新运行搜索；从本目录执行：

```bash
python3 prepare.py
g++ -O3 -std=c++17 -Wall -Wextra search14.cpp -o search14
python3 verify_and_map.py known-star-suffix15.json
./search14 300
python3 verify_and_map.py best-14.json
```

搜索每次重启会检查当前目录的 `STOP` 文件并停止，也响应 SIGTERM/SIGINT。固定随机种子为 `273220261125`；迭代次数受 CPU 竞争影响。本次没有触发停止文件或信号。

## 紧凑检查点说明

本次发布省略可执行文件、临时 PID 和可由 prepare.py 确定性生成的 seeds.txt。完整原始文件哈希及排除原因见顶层 STAGING.json；重跑前先执行目录内的 prepare.py。
