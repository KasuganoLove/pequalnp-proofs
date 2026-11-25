# 依赖来源与许可

本研究归档位于 pequalnp-proofs 项目内；上游[仓库许可](https://github.com/open-goat/pequalnp-proofs/blob/62127f3af70786085fa09c6453d036c7cde890ce/LICENSE)为 Apache License 2.0。

## Pnp650TransferCore.lean

这个54,508字节的必要形式化依赖提取自上游 [L_meta_5228.lean](https://github.com/open-goat/pequalnp-proofs/blob/62127f3af70786085fa09c6453d036c7cde890ce/lean/PEqualNP/Outside/L_meta_5228.lean) 的通用 `LocalLambda` 至 `LocalSingleMix`、`LocalMixerTransfer` 部分。原文件 SHA256 为 `0b3f20c44ae8739ae961579014fe617e87e12e3af5d333c91c658990ee82eada`；只改变外层namespace并添加来源说明，没有复制后续特定图的大型有限证书。原文将OR路径刻画归功于willakone的[项目PR3118](https://github.com/open-goat/pequalnp-proofs/pull/3118)。这些既有证明不被称为本次原创。

提取依赖的 SHA256 为 `59b1952ef33eebc22880906a408bc6218c09c8510c78607b8e2fa900d835474b`。新子情形 Pnp650SingleMixer.lean 对它的import是真实构建依赖，所以本归档完整保存该最小来源切片；不以只提供外部链接替代必要源码。

## 其余来源

971、3516、516、575和其他已检查上游结果均通过固定URL、声明名、行号及哈希索引引用。SAT出口调用项目原有 `PEqualNP.Defs.LratEncoding.enc2`，编码定义未修改。CaDiCaL为项目固定Lean工具链内的程序，二进制不收入归档。新工作是实例化、有限审计、局部证明组合、限时搜索支持和独立验证；完整范围见各子目录README。
