# VALUE 通用 LRAT 环境准备

此目录记录通用依赖准备，不包含任何新领取 VALUE 题目的数学工作或官方证明提交。固定上游为 `open-goat/pequalnp-proofs@57d6c2fdf69978aecff3559c7ab6b442a2d3c3f1`。

## 已完成

主工作区仍为 `pequalnp-proofs@57164c3618362178843e2ea37bd01613f4037ae2`。对固定上游的逐字节比较确认：`Defs/` 整目录、`Defs.lean`、Lean 工具链、Lake 配置/manifest、`check-lean.mjs`、`CheckLemma.lean`、LRAT Checker 和 Shannon helper 相同。`Defs/` 的 Git tree 为 `e1343d2a024b07570497077743e536a48c6c8c9c`。Lean 为 4.36.0，Mathlib 固定为 `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`。没有运行 `lake update`、修改配置或覆盖已有证明文件。

仅将缺失的两份官方原文 `LinkN.lean`、`LinkN2.lean` 加入主工作区。两文件 Git blob 分别为 `ddea982d0c14d4183789f35d8c583bc51bc53383`、`9a273de3c59200c5ee3c00306b01f15a95217986`；已有 b9 工作树中也含有完全相同的文件。完整来源与 SHA256 见 `environment-compatibility.json`。

顺序运行普通 Lean，每次一个线程，结果如下：

| 模块 | 退出码 | 耗时 | 编译消息 |
|---|---:|---:|---|
| `PEqualNP.Library.LRAT.Checker` | 0 | 2.221 秒 | 无 |
| `PEqualNP.MetaComplexity.Helpers.Shannon` | 0 | 8.598 秒 | 无 |
| `PEqualNP.Library.LRAT.LinkN` | 0 | 15.354 秒 | 100 条上游既有弃用/linter 警告 |
| `PEqualNP.Library.LRAT.LinkN2` | 0 | 6.894 秒 | 59 条上游既有弃用/linter 警告 |

全部阶段合计约 33.1 秒，最高子进程 RSS 为 3,100,336 KiB。四个 olean 现位于主工作区 `lean/.lake/build/lib/lean/` 对应模块路径。编译前的计时包装器曾因系统没有 `/usr/bin/time` 而未启动 Lean；改用 Python `resource` 后完成以上唯一一次实际构建。日志与退出码见 `build-results.json`、`build-*.log`、`build-*.time.txt`。这些是普通库构建，未运行官方 strict checker。

## 可复用的精确接口

导入 `PEqualNP.Library.LRAT.LinkN2` 后，声明仍位于 namespace `PEqualNP.Library.LRAT.LinkN`：

```lean
size_of_unsat2 (n s : ℕ) (f : (Fin n → Bool) → Bool) (rows : List ℕ)
  (hrows : ∀ r ∈ rows, r < 2 ^ n)
  (hU : ¬ FormulaSat (enc2 n s (rowFun n f) rows)) :
  ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n f t → s + 1 ≤ t
```

`enc2` 是 `enc ++ fLex`：额外约束来自已证明的词典序正常形，不是自行添加的求解器剪枝。它覆盖任意 fan-in 至多 2 的 AND/OR/NOT 电路，允许正常化和 padding。任何给定的 `rows` 只需各自小于 `2^n`；其不可满足性就足以推出全输入计算所需的门数下界。有限样本上找到 SAT 模型则必须另外核对真实目标域，不能自动视为完整见证。

已有官方生成器位于 b9 工作树 `notes/data/lrat-link/`，字节匹配固定上游：

```sh
python3 gennot.py N S EDGE_LIST formula.cnf [rows]
cadical --lrat --no-binary --unsat -t SECONDS formula.cnf proof.lrat
python3 genrow.py formula.cnf proof.lrat generated.lean NAMESPACE N S ROWS FEXPR --not --seg HINTS
```

`gennot.py` 的现成 CLI 仅解析两位单字符顶点标签，如 `01,12,23`；不能原样用于顶点标签大于 9 的图。省略 `rows` 时使用全部输入；`rows` 模式使用极小真/极大假输入，对有 NOT 的模型只是较弱但健全的下界测试。官方编码中操作编号 0/1/2/3 分别为 AND/OR/TRUE/NOT；无效输入线解释为 false。`genrow.py --not` 会构造 Lean 中的实际 `enc2` 并应用 `size_of_unsat2`，不是假定外部 DIMACS 文件正确。

证书消费端为 `check_sound` 或 packed words 版本 `checkW_sound`，用 `by decide +kernel`。长证书可通过 `checkFirst_sound`、`checkSeg_sound`、`checkLast_sound` 分段；未观察到 `checkPacked` API。生成器只接受正 LRAT RUP hints，遇到 RAT hints 会拒绝。默认生成的全局 `set_option` 不符合 Outside 提交流程，需要逐声明局部化为 `set_option ... in`，然后再执行当前格式检查和官方 checker。只提交实际租约允许的导入与最终命题。

仓库内 `notes/data/lrat-link/trial-not/P4Not.lean` 是同一接口的通用示例：导入 LinkN2，经 packed LRAT 得 `unsat`，再经 `size_of_unsat2` 得下界。这里仅检查了模板结构，没有为该旧示例重新运行证明或声明它是某个当前 VALUE 任务的官方验收记录。当前已合并 VALUE 文件格式由另一独立工具审计记录。

## 构建复现

对包含固定上游原文、已缓存上述工具链与 Mathlib 的工作区，在 `lean/` 中顺序运行：

```sh
lake env lean -j1 -M6500 -o .lake/build/lib/lean/PEqualNP/Library/LRAT/Checker.olean PEqualNP/Library/LRAT/Checker.lean
lake env lean -j1 -M6500 -o .lake/build/lib/lean/PEqualNP/MetaComplexity/Helpers/Shannon.olean PEqualNP/MetaComplexity/Helpers/Shannon.lean
lake env lean -j1 -M6500 -o .lake/build/lib/lean/PEqualNP/Library/LRAT/LinkN.olean PEqualNP/Library/LRAT/LinkN.lean
lake env lean -j1 -M6500 -o .lake/build/lib/lean/PEqualNP/Library/LRAT/LinkN2.olean PEqualNP/Library/LRAT/LinkN2.lean
```

先创建相应输出目录。此次本地调用设置 `ELAN_HOME=/workspace/scratch/65f339da29fe/pnp-tools/elan` 并把其 `bin` 加入 PATH；自动记录脚本 `build_lrat_dependencies.py` 包含完整命令、源 blob 校验以及拒绝覆盖不同原文的逻辑。源代码版权与许可属于上游，归档只保留必要的来源/hash/验证记录，不将整份第三方参考源当作本轮原创成果。
