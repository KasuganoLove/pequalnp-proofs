# 本地形式化材料：通用桥已通过，完整拒绝未完成

这里保存原 3,192 位、1,596 个正负输入配对的尝试。完整目标有 114 个正输入、14 个负输入。新的 420 位数据位于相邻 `edge-signed-probe/`；不得将两种表示的 88／108 分支数混用。

## 固定环境

- 实际本地 checkout：`57164c3618362178843e2ea37bd01613f4037ae2`。
- Lean：`leanprover/lean4:v4.36.0`。
- Mathlib：`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`。
- 使用已有固定依赖缓存；不要通过 `lake update` 改变环境。

下面的脚本复制现有已冻结源文件到该提交的独立 checkout，拒绝覆盖不同的同名文件，然后依次运行普通 Lean：

```bash
bash reproduce_helpers.sh /absolute/path/to/isolated/pequalnp-proofs
```

顺序是 `narrow-import/Pnp10486LiteralCore.lean`、`Pnp10486SplitCore.lean`、`Pnp10486FiniteBridge.lean`。三者在原运行中退出码均为 0；Core 有四条 exponent threshold 提示，另两者日志为空。该脚本未在归档时执行。需预先准备所记录版本的 Lean、Mathlib 与 `PEqualNP.Defs` 缓存。

## 状态对应

- `L_meta_10486.literal.lean`：完整候选，普通 Lean 退出 137，无完整判定。对应 `ordinary-literal-result.json`。
- `Pnp10486BranchesSpecial.lean`：索引 73、76、83、85 的数值核验尝试；完整／较窄导入分别对应 `*.full_mathlib.result.json` 与 `*.result.json`，均退出 137。
- `Pnp10486Branches0.lean` 至 `3.lean`：只生成了分组源，未运行。
- `Pnp10486LiteralCompute.lean`：历史编译求值探测，60 秒超时，**不是 kernel 证明**。
- `Pnp10486NestedBridge.lean`：通用索引桥已写好，未编译；不含固定数值或搜索结果。
- `independent-first-level*`、`independent-second-level*`：只计算有限层数据，未递归证明拒绝。第二层四组分别有 100、93、100、93 个后继。
- `independent-literal-*`：类型、来源、1,596 配对、位方向和 12 门控制的独立源码／数据复核，不能代替未完成的 kernel 数值核验。

原框架来源及 Apache-2.0 归属保留在各 Lean 文件头。L9539 精确参考文件的 Git blob 为 `97b870167d92317dd76d669567451bf277a9909a`，SHA256 为 `f0ea1c9ca867450a030a85e2152c13be57db5b8f1f7ed96c891c06afe3edd876`。公开来源见 `../../L-meta-10696/status-audit/curated/reference-summary.json`。`../historical-tools/prepare_literal_proof.py` 是原工作区生成脚本，保留作来源记录；它需要原相对目录与该参考文件，不应在当前 fork 根目录盲目执行。现存冻结源已足够复现上述模块。

正式 10486 的 checked 证明来自 odinfree 的 PR14954，而不是本目录的候选。本目录没有新的严格检查通过记录或官方证明提交。
