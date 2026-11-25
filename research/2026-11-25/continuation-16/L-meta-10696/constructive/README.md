# L-meta-10696：12门综合与13门控制

这是根代理已完成的单次构造搜索记录。搜索允许AND、OR、NOT、常假、常真门，重复操作数支持拷贝；两两NOT选择器约束使整个12门电路至多含一个NOT。原始输入为0–6，所有门读取较早的线，末门为输出；全部128个输入都被约束。

`result.json` 记录最终 **UNKNOWN**：墙钟300.011秒，CPU299.402秒，最大RSS93,088 KiB，达到墙钟上限后exit−15。没有SAT见证或UNSAT判定，没有自动重跑。

`baseline13.json` 给出13门单调电路，已有直接Python回放记录：全部128输入正确。这不是最小性证明，也没有解决公开的等大小替换命题。根代理的电路综合源由同会话11021的透明选择器编码改编；10487随后复用相同机制并独立审计其新实例。

已有Python3和CaDiCaL时，在本目录重建编码并运行相同预算：

```sh
python3 synthesize12.py --solver /absolute/path/to/cadical --seconds 300
```

如只需要重建编码、不启动求解器：

```sh
python3 - <<'PY'
from pathlib import Path
from synthesize12 import prepare
prepare(Path.cwd())
PY
```

生成的 `formula.cnf` 和完整 `encoding.json` 是可再生中间文件，未加入归档。小型 `encoding-summary.json` 保留原始CNF大小、哈希、变量与子句数。源程序会独立回放任何SAT候选并检查全部CNF子句，但本次没有候选可供回放。没有Lean、严格检查或正式下界声明。
