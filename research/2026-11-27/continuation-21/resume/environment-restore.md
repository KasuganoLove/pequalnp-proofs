# 2026-11-27 通用 Lean 环境恢复

环境已就绪。当前 checkout 固定在上游 `3db0136bf094e975baaf20214b01e4b4579059f2`，未修改任何跟踪源码，也未执行任务台操作、远端写入或旧任务证明。

## 最短入口

```bash
source /workspace/scratch/65f339da29fe/pnp-tools/env.sh
cd /workspace/scratch/65f339da29fe/pequalnp-proofs/lean
lake env lean -j1 path/to/your-file.lean
```

`ELAN_HOME` 固定为 `/workspace/scratch/65f339da29fe/pnp-tools/elan`。官方 elan 安装使用了 `--no-modify-path --default-toolchain none`，随后只安装仓库指定的 `leanprover/lean4:v4.36.0`。没有改动 shell 配置文件。

## 固定版本与验证

| 项目 | 结果 |
| --- | --- |
| Lean | 4.36.0，compiler commit `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9` |
| Mathlib | `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` |
| 依赖锁定 | 全部 9 个依赖的实际 Git HEAD 与 `lake-manifest.json` 一致 |
| 完整缓存 | `lake exe cache get` exit 0；9,117 项下载、解包完成；`Mathlib.olean` 存在 |
| `PEqualNP.Defs` | exit 0；130.59 秒；最大子进程 RSS 2,961,576 KiB |
| `PEqualNP.Library.Helpers.PromiseColTree` | exit 0；21.46 秒；最大子进程 RSS 3,020,972 KiB |

实际构建命令为：

```bash
LEAN_NUM_THREADS=1 lake exe cache get
LEAN_NUM_THREADS=1 lake build +PEqualNP.Defs
LEAN_NUM_THREADS=1 lake build +PEqualNP.Library.Helpers.PromiseColTree
```

两个目标串行执行，未运行默认全项目或 Outside 构建，未运行 `lake update`。存在上游已有的模块系统及废弃名称提示，没有构建错误，也没有为消除提示而改源码。

最初尝试的计时包装因系统没有 `/usr/bin/time` 而退出 127，尚未启动 Lean；改用 Python 标准库计时后，上述构建均通过。该启动记录保留在 `defs-build-launch-attempt0.log`。

## 可用资源与交接

记录时剩余磁盘约 **5.49 GiB**、可用内存约 **8.52 GiB**。只有一份固定 Mathlib 环境。所有环境恢复作业已退出；后续大型 Lean 检查仍应由 root 统一安排。

新版本的 Defs umbrella、`check-lean.mjs`、`check-lean-memory.mjs`、`outside-guard.mjs` 和 `pnp.sh` 均来自上述当前上游 pin。`environment-source-provenance.json` 记录精确源码 hash；旧检查器未复用。

旧本地候选和搜索目录在本次恢复前已不在 scratch 中。本次没有重新运行 12030/12128 旧任务。当前研究入口仍为用户 fork 的 `codex/pnp-research-2026-11-24` 分支下 `research/ACTIVE_WORK.md`；恢复时读到的 head 是 `e3bf0acf5e38daa631ca9b3f35a970d65f2001df`，其内容是历史交接，不能据此恢复任何租约。

本记录仅证明通用本地环境可用，不是任何新数学任务的证明或官方检查结果。
