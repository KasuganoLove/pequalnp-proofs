# 冻结的 L2590 干净电路结果：普通 Lean 复现

本说明复现本目录已完成的两个证明模块及六项 axiom audit。其结论是 **干净 Monotone2 电路至少 20 门**，并将可能的 19 门反例归约到具有脏 AND 的情形。它不证明完整 L-meta-2590，也不运行官方严格检查或提交结果。

## 固定环境

- 上游仓库：<https://github.com/open-goat/pequalnp-proofs>。
- 目标工作树的 HEAD 必须精确为 `259523a5b265318b84f9377f2feb965fd213f898`。
- 已安装 Lean `leanprover/lean4:v4.36.0`，通过现有 `ELAN_HOME` 定位。
- Mathlib 提交为 `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`；所有其他依赖须与目标工作树的 `lean/lake-manifest.json` 一致。
- 需要已有的完整 Mathlib 编译缓存，包括 `Mathlib.olean`：冻结的上游 L1501 和 L2235 模块使用 `import Mathlib`。
- 需要 Bash、Python 3、Git 及常用 GNU 文件工具。不要运行 `lake update`。

原检查在工作树 `57164c3618362178843e2ea37bd01613f4037ae2` 上完成；其 Defs、工具链、依赖配置与上述复现提交的一致性记录在 continuation-8 的 `env-compatibility.json`。这里要求固定复现提交，避免随上游主分支变化。

## 准备独立工作树

下面是供后续审阅执行的命令模板。将绝对路径改为本机实际路径；`pnp_target` 必须是尚不存在的新目录，`pnp_cache` 指向已验证的固定依赖缓存。

```bash
pnp_source_repo=/absolute/path/to/existing/pequalnp-proofs
pnp_target=/absolute/path/to/new/pnp2590-review
pnp_cache=/absolute/path/to/existing/pequalnp-proofs/lean/.lake/packages
pnp_clean_case=/absolute/path/to/clean-case
pnp_cont8=/absolute/path/to/research/2026-11-25/continuation-8
export ELAN_HOME=/absolute/path/to/existing/elan
pnp_pin=259523a5b265318b84f9377f2feb965fd213f898

# 只在现有仓库尚无该提交时读取远端；不推送或更新任何远端引用。
git -C "$pnp_source_repo" cat-file -e "${pnp_pin}^{commit}" || \
  git -C "$pnp_source_repo" fetch https://github.com/open-goat/pequalnp-proofs.git "$pnp_pin"
git -C "$pnp_source_repo" worktree add --detach "$pnp_target" "$pnp_pin"

# 仅共享依赖包；项目自身的 .lake/build 保持属于这个新工作树。
mkdir -p "$pnp_target/lean/.lake"
ln -s "$pnp_cache" "$pnp_target/lean/.lake/packages"

bash "$pnp_clean_case/reproduce.sh" "$pnp_target" "$pnp_cont8"
```

如果归档仍保持 `continuation-8` 与 `continuation-9` 的相邻目录结构，脚本可自动找到 continuation-8，第二个参数可以省略。显式提供参数适用于移动后的单独归档。

## 脚本执行的操作

`reproduce.sh` 先检查目标提交、干净的受跟踪文件、已有工具链和每个依赖包的固定提交。它随后检查全部 11 个冻结源码的 SHA-256，并在复制前检查所有目的地：已有文件必须逐字节一致；任何不同内容都会导致退出，不覆盖该文件。不能将整个 `.lake` 或项目 `.lake/build` 链接到另一个工作树。

通过全部检查后，脚本只复制缺少的源码，按下面的依赖顺序生成普通 Lean 编译结果：

1. `PEqualNP.Defs` 的项目构建。
2. `Pnp2343Pruning`、`L_meta_1501`、`L_meta_2235`。
3. `Pnp4201OrBudget`、`Pnp4201BudgetTopForm`、`Pnp4201CleanBudgetTopForm`、`Pnp4201CleanNormalize`、`Pnp4201CleanOrCount`。
4. `Pnp2590Graph`、`Pnp2590CleanBound`。
5. `Pnp2590CleanBoundAudit` 的六项 `#print axioms`。

它使用目标仓库的 `tools/bin/lake` 排队入口，并指定已缓存的 Lean 4.36.0 二进制。每个普通源码检查使用 `lake env lean -j1`；各步骤日志写入目标仓库中新建的 `pnp2590-reproduction-*` 目录。任一步失败即停止。预期 audit 只列出 `propext`、`Classical.choice`、`Quot.sound`。

脚本本身不访问任务台、不持有或续租任务、不做远端写入，也不运行 strict checker。准备工作树示例中的 `git fetch` 是可选的公开源码读取。若继续进行新的任务研究，应先确认相应有效授权。

## 本次打包验证

本次只执行了 shell 语法检查及源码路径、哈希、导入顺序的静态核对。**没有执行复现脚本，没有再次运行 Lean。** 已完成证明的原始普通检查、axiom 输出及范围记录保持在 `validation.json` 和本目录的日志中；此次打包不改变其验证等级。
