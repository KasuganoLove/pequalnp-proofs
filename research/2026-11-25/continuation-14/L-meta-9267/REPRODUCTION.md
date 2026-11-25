# 9269 候选的无整份第三方源码复现

候选的完整证明来自 tb-16 已合并的 L9195，本目录只保存确定的实例改写、内容哈希和验证日志，不重复收录其 109 KB 原件。

固定来源：

- [L9195 源文件](https://github.com/open-goat/pequalnp-proofs/blob/9025f81315571fe9b237f2fd3aed4f123b1e8757/lean/PEqualNP/Outside/L_meta_9195.lean)
- [同一提交的 Apache-2.0 LICENSE](https://github.com/open-goat/pequalnp-proofs/blob/9025f81315571fe9b237f2fd3aed4f123b1e8757/LICENSE)
- 来源 SHA-256：`b358ad57b53243df24c1908382c59f29819715761f8eacec38d032b0826aea20`
- 本地候选 SHA-256：`9253c0badb498bde9adaa04174a4e4af04c83119c3033de9fa724d3c3d1c4d5f`

将固定来源原件放在相邻的 `L-meta-9219/status-audit/upstream-L_meta_9195.lean` 后，从本目录运行：

```sh
python reconstruct_candidate.py --source ../L-meta-9219/status-audit/upstream-L_meta_9195.lean --output L_meta_9269.lean
python independent-review/check_adaptation.py
```

脚本先核对来源哈希，再替换 namespace、掩码和 OO/ZZ，补充来源注释，最后核对候选哈希。candidate-from-9195.patch 给出同一修改的可读差异。两个脚本不执行新搜索，也不把数据复核当作形式化验证。

普通 Lean 原始运行在固定项目环境退出 0，18.326 秒。需要独立复现时，可把重建文件放入官方模块路径后运行 `lake env lean -j1 PEqualNP/Outside/L_meta_9269.lean`。本次严格检查运行已在 `strict.log` 记录为 CHECKER FAULT（验证器退出 137）；没有严格通过或官方 ACCEPTED。

已有 [PR #13475](https://github.com/open-goat/pequalnp-proofs/pull/13475) 含相同非注释代码，并早于本地候选。归档用于可复查性，不是新 PR 或新的数学方法。不要把复现说明视为再次运行相同失败检查的授权。
