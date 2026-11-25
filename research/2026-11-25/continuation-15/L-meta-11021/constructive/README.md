# L-meta-11021：有界 15 门见证搜索

公开任务要求反驳九顶点图函数的 16 门下界。只要找到至多 15 门的 AND/OR/NOT 电路，即可给出完整的正向见证。这里没有把失败的搜索当作下界证明。

**最终结果：UNKNOWN。** 唯一一次搜索于 2026-11-25 12:18:57 UTC 达到 300 秒墙钟限时后终止，退出码 −15；实际墙钟 300.012 秒、CPU 299.522 秒、峰值 RSS 158,076 KiB。没有 SAT 候选，也没有 UNSAT 判定。没有重跑。

图边为 04、05、15、26、36、07、27、47、18、38、48、68。要求对全部 **512 个布尔输入** 正确，不是 oneEach 矩阵表示问题。

## 已确认的基线

`baseline16.json` 是实际 16 门 AND/OR 电路，输出为线 24。独立直接回放全部 512 行，零错误。这只给出 16 门上界，不能完成当前目标。两个三角形为 047 和 368；分别提取三角形的四门公式没有得到 15 门构造。

## 唯一一次综合任务

`synthesize15.py` 构造透明的选择器/Tseitin CNF，并启动单个 CaDiCaL 进程。预算为 300 秒、1 GiB 虚拟地址空间，没有自动重试。`result.json` 记录实际终态和资源使用，`solver.log` 保留原始输出，`run.log` 保留运行摘要。

编码固定 9 个原始输入、15 个按顺序生成的门，最后一门为输出。每门可以为 AND、OR、NOT、常假或常真；AND/OR 可重复操作数，因此支持拷贝。操作数只读取原始输入或更早的门。NOT 只读第一个操作数。所有 512 行均加入最终输出约束。CNF 共 23,595 个变量、436,607 个子句、8,166,694 字节，SHA256 为 `6e7e6831adc179eb4d6d63fb6e5c5212f666b93771ab883008f1a3d1917d1ad9`。

`audit_encoding.py` 独立核对五种操作的全部 40 个三变量真值情形；用另一个直接回放的合法电路核对 436,095 个内部子句；逐项核对 512 个输出约束；另外核对 16 门基线。检查通过。该检查不是 Lean 证明，也不是对综合编码完备性的正式证明。

若求解器返回 SAT，脚本必须独立直接回放候选的全部 512 行，并检查 CNF 每个子句；有任何错误则不能视为见证。即使返回 UNSAT，也只报告编码模型中的结果，本目录没有给公开 `FanInTwo` 模型提交形式化归约或 UNSAT 证书。最终状态与有无见证应以 `result.json` 为准。

## 复现

使用现成的 Python 3 与 CaDiCaL，无额外 Python 依赖。在本目录运行：

```sh
python3 synthesize15.py --solver /absolute/path/to/cadical --seconds 300
python3 audit_encoding.py
```

若只重新生成并审计编码、不启动求解器：

```sh
python3 - <<'PY'
from pathlib import Path
from synthesize15 import prepare
prepare(Path.cwd())
PY
python3 audit_encoding.py
```

`formula.cnf` 和完整选择器映射 `encoding.json` 可由脚本重建，不需要作为长期小型归档的一部分。这里没有 Lean 编译、严格检查器结果或官方接收声明。
