# 2026-11-25 证明与复核

## 后续进展：第四轮续推

[continuation-4](continuation-4/README.md) 保存了 L-meta-7019 的完整证明和 L-meta-3600 归约的修复。两份文件分别通过本地项目检查器的 check 与 reduce 模式。7019 尚待正常任务台分配后正式提交；3600 的三个活跃归约名额已满，修复作为研究成果保留。最新核对还确认 #7182 已获官方接受并合并，#7168 因其他证明先合并而关闭。

## L-meta-3233

网页端此前遇到两次退出码 137。桌面端在同一固定上游版本 `048b39bb` 上复核了原提交 `86a9b1c3`，验证器返回 `ACCEPTED (reduce)`、退出码 0，耗时 32.39 秒，重新检查 1,648 项声明。两个子命题的文本与网页端保存的预览逐字节一致。第一条也是已发布的 L-meta-3438，第二条是至多两个 NOT 门情形的下界。正式裁决以现有 [PR #7182](https://github.com/open-goat/pequalnp-proofs/pull/7182) 为准。[本地验证摘要](L-meta-3233/validation.json) · [原生验证器输出](L-meta-3233/CheckLemma-native-reduce.log)

## L-meta-2798

该命题断言，对每个满足条件的奇数阶射影平面，总能找到至多 $2n$ 个门的二元 AND/OR 电路精确计算点线关联。本文件以 211 阶射影平面给出反例。点数和线数各为 44,733，固定两个点变量后，其余变量仍对输出有影响。两次门消去给出严格下界 $2n < C.size$，所以至少需要 89,467 个门，题设上限为 89,466。

项目检查器按 `refute` 模式读取领取时的原命题，返回 `ACCEPTED (refute)`、退出码 0，内核复核 1,903 项声明。复核时，官方任务台对 L-meta-2798 返回 `not_open`。这份反证作为研究成果保存在 fork 中。[Lean 反证](L-meta-2798/L_meta_2798.lean) · [原命题](L-meta-2798/statement.txt) · [检查器记录](L-meta-2798/CheckLemma-refute.log)

## 上游记录

已合并的完整子命题为 [L-meta-2802](https://github.com/open-goat/pequalnp-proofs/pull/5157)。两份已合并的归约为 [L-meta-2782](https://github.com/open-goat/pequalnp-proofs/pull/5212) 和 [L-meta-2519](https://github.com/open-goat/pequalnp-proofs/pull/5362)。[L-meta-2289](https://github.com/open-goat/pequalnp-proofs/pull/5195) 已关闭，其他贡献者的证明先被采用。[L-meta-3358](https://github.com/open-goat/pequalnp-proofs/pull/7168) 已由用户账号提交。
