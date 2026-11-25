# 11315：局部 Lean 核验与未完成的完整候选

这里的全部结果是本地普通 Lean 记录。**没有本 root 的完整 11315 证明、严格检查通过记录或新官方 PR。** 11315 的正式结局见 `../official-closure/`：ptrdsh 的 PR15263 于 2026-11-25 14:18:51 UTC 合并，随后官方 desk 登记 checked。

## 已核验与未核验范围

| 源文件／尝试 | 普通 Lean 结果 | 真实范围 |
|---|---|---|
| `broad-tactic/Pnp11315Core.lean` | exit0，23.487秒 | 通用 signed live-wire 完整性、Circuit 编译桥、给定 search 拒绝后的下界；没有实例递归拒绝。 |
| `Pnp11315SplitCore.lean` | exit0 | 一步 children 展开与 search 汇总。 |
| `Pnp11315FiniteBridge.lean` | exit0，3.023秒 | 第一层恰92分支、仅完整初始子表可分离、以及以所有分支拒绝为前提的汇总。 |
| `Pnp11315States.lean` | exit0，20.254秒 | 92个显式状态与原 children 索引逐一相等；不是92个递归拒绝。 |
| `Pnp11315Explicit1.lean` | exit0，42.556秒，最大RSS6,791,524KiB | **只有索引1** 的递归拒绝及对应 branch_1。其余91分支不能据此视为通过。 |
| `Pnp11315BlockBridge.lean` | exit0，3.625秒 | 通用有限索引及 treeBlock 汇总；没有数值拒绝。 |
| `L_meta_11315.literal.lean` | exit137，106.718秒，最大RSS6,950,340KiB | 原始完整候选未得到完整判定。 |
| `Pnp11315BranchesSpecial.lean` | 300.016秒后 wall_limit，exit−15 | 八个特殊分支的组合尝试没有完整判定。 |
| `Pnp11315Branches0`…`5` | 只生成，未运行 | 未核验的候选分组。 |
| 当前 `Pnp11315Core.lean`，四个精确 tactic 导入 | exit0，15.598秒，最大RSS3,485,328KiB | 仅缩减导入后的 Core；没有在该版本上重新完成所有依赖模块或递归拒绝。 |

最后一个 Core 作业开始于 **14:21:16.942787 UTC**，关闭心跳返回于 **14:21:23.452684 UTC**，作业于 **14:21:32.540812 UTC** 自行完成。Root 尝试停止时发现它已结束。没有在关闭通知后新启动 Lean／搜索或继续该任务的数学工作。日志里的四条指数求值阈值提示保留于 `Pnp11315Core.log`；该 Core 最终退出0。

## 固定环境与复现

本地基础 checkout：`57164c3618362178843e2ea37bd01613f4037ae2`。Lean：`leanprover/lean4:v4.36.0`；Mathlib：`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`。使用已安装的 `lake` 及已有依赖缓存，不运行 `lake update`。

在一个隔离、固定到上述提交的 checkout 中，已有工具链和依赖后：

```bash
bash /path/to/continuation-17/L-meta-11315/formalization/reproduce_helpers.sh \
  /absolute/path/to/isolated/pequalnp-proofs
```

脚本依次构建 Core、SplitCore、FiniteBridge、States、BlockBridge，采用与原来依赖核验匹配的 `broad-tactic` Core。它拒绝覆盖内容不同的已有文件，并且不会自动运行完整候选、Special 或 Explicit1。这个复现脚本在归档时仅做 shell 语法与路径核对，**没有再次执行 Lean**。

States 的原始126,175字节按原字节顺序存为文本片段，记录在本检查点根目录 `large-files.json`。脚本自动恢复这些片段。也可只恢复单个文件：

```bash
python3 /path/to/continuation-17/restore_file.py \
  L-meta-11315/formalization/Pnp11315States.lean /tmp/Pnp11315States.lean
```

原 `prepare_explicit_states.py` 和 `historical-tools/prepare_literal_proof.py` 保留原工作区布局假设；它们是历史生成记录，不应直接在任意目录运行。前者可由保留的第一层数据重建未收录的其余91个 Explicit 模块。原始完整候选已经保留，无需再次获取模板才能阅读它。较大且可再生的第二层状态表按 worker supplement 中的哈希与生成脚本记录，没有重复存储。

## 来源与归属

主证明框架改编自已 checked 的 L9539，参考 SHA256 `f0ea1c9ca867450a030a85e2152c13be57db5b8f1f7ed96c891c06afe3edd876`。原注释保留 L9136、partymejker 的 L9146、k-sandhu 的 L8633，以及 L8463／L1449 的 Apache-2.0 来源。

BlockBridge 中 `treeBlock`、`treeBlock_at`、`treeBlock_merge` 来自 odinfree 的官方 PR14954，合并提交 `3f343d41f5196063193260b654053e2c750b7878`，同样保留 Apache-2.0 归属。有限索引桥来自本会话之前的 Pnp10486NestedBridge。本检查点不复制完整第三方参考证明，也不将 ptrdsh 的正式11315证明归为本 root 工作。
