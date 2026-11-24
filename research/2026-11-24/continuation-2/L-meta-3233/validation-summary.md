# L-meta-3233 核验记录

- `Pnp3233Binary.lean`：普通 Lean 编译退出码 0；自包含证明的 SHA-256 为 `1d371093585147a16d3c4c9b2bc7674c83ca4e045c2a751bda546a598c5826de`。
- `R_meta_3233_713.lean`：普通 Lean 编译退出码 0；SHA-256 为 `62a995ce1687419ad0ca4b396e807786c76ac1cec21b91649fe64419dab829e7`。结论与任务原文逐字一致，导入及归约文件格式检查通过。
- 第一次严格检查：验证进程退出码 137，包装程序退出码 3，`CHECKER FAULT`，未打印子命题或给出裁决。
- 限制分配器后的唯一一次重试：仍为验证进程退出码 137、包装程序退出码 3，未给出裁决。此后未继续重试。这不能解释为证明被数学上拒绝，也不是严格验证通过。
- 独立的打印诊断：退出码 0，打印后两条子命题长度为 911 和 1,364 个字符；第一条与 `L-meta-3438` 相同。它只确认打印内容和长度，不替代严格验证。
- `L-meta-3438` 已有他人的证明 PR [6461](https://github.com/open-goat/pequalnp-proofs/pull/6461)、[6591](https://github.com/open-goat/pequalnp-proofs/pull/6591)、[6636](https://github.com/open-goat/pequalnp-proofs/pull/6636)，本工作没有另开重复 PR。

原始故障日志名 `3233.check.log`、`3233.check-malloc.log` 是本轮来源标识；本目录保存的是该摘要和结构化验证记录。普通编译通过、打印诊断通过、严格检查通过和官方接受四种状态分别记录。
