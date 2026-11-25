# Heawood 26 门候选的限时搜索

## 已观察到的结果

单线程搜索按预定的 300 秒上限正常结束，退出 0；**没有找到正确的 26 门候选**。这不是不存在证明，也没有解决 L-meta-2732 或其否定命题。

- 用时：300.001 秒。
- 电路求值次数：2,913,080,851（包含重复状态，不代表同样数量的不同电路）。
- 随机重启：24,274。
- 初始单字段邻域检查：183,040 次。
- 最优极值行误差：false positive = 0，false negative = 1。
- 对冻结最优电路独立枚举全部 16,384 个输入：false positive = 0，false negative = 47。

`best-26.json` 是一个明确不正确的近似候选，不应当作为见证提交。没有生成 `candidate-26.json`。

## 精确目标和搜索模型

边表直接从父目录的公共 `statement.txt` 提取，是 14 个输入、21 条边的指定 Heawood 图。极小正输入为 21 个边对；458 个负输入中恰有 37 个极大负输入：2 个支撑大小为 7，14 个大小为 5，21 个大小为 4。共 58 个极值行可存入一个 64 位字。

每个候选包含 26 个有序二输入门，`op=0` 为 AND、`op=1` 为 OR。所有读取只指向原始输入或较早门；允许相同输入和任意输出线。搜索没有强制 all-AND-clean、单层 AND、star 形式或固定 AND/OR 门数。它没有覆盖整个语法空间，因此失败不能给出 UNSAT 或复杂度下界。

由于候选全为单调 AND/OR 电路，若同时接受所有边对且拒绝所有极大负输入，就能推出目标在所有输入上的一致性。搜索本身没有找到这样的候选。`verify.py` 使用独立的逐输入布尔求值器，在完整真值表上核验电路，而不依赖 64 位训练求值实现。

## 种子和来源

`prepare.py` 从两侧 star 分解生成 128 个 27 门构造；每个构造删除一个门并将后续读取替换为它的一个操作数，得到 6912 个 26 门种子（可能重复）。保存的 `known-27.json` 已通过全部 16,384 个输入的独立检查。

局部搜索结构改编自此前归档的 `research/2026-11-25/continuation-7/bounded-search/local_search.cpp`，重新实现为 14 输入、26 门、单字极值行求值，加入不同误差权重、活跃门偏置、多个温度计划及候选池。本目录保存完整实际运行源码。

本次进程的地址空间上限为 512 MiB，CPU 上限为 310 秒，使用 `nice(5)`。没有运行 Lean、strict checker、远端操作或 lease 操作；任务授权和续租由父代理管理。

## 文件和复现

- `prepare.py`：提取目标、生成完整极值行和种子。
- `search26.cpp`：实际运行的启发式搜索源码。
- `verify.py`：独立全输入检查。
- `search.log`、`run-summary.json`：完整进度及结果。
- `known-27.json`、`known-27-verification.json`：已知正确的 27 门构造。
- `best-26.json`、`best-26-verification.json`：最优但不正确的 26 门候选。

仅在具有相应有效任务授权时重新运行搜索。从本目录执行：

```bash
python3 prepare.py
g++ -O3 -std=c++17 -Wall -Wextra search26.cpp -o search26
python3 verify.py known-27.json
./search26 300
python3 verify.py best-26.json
```

实际运行使用固定随机种子 `273220261125`。外部时间限制、CPU 竞争可能改变达到的迭代数。编译无警告，搜索和独立检查均退出 0。没有 DRAT/LRAT 证明或官方结论。

## 紧凑检查点说明

本次发布省略可执行文件、临时 PID 和可由 prepare.py 确定性生成的 seeds.txt。完整原始文件哈希及排除原因见顶层 STAGING.json；重跑前先执行目录内的 prepare.py。
