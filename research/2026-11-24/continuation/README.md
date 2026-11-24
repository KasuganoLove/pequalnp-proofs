# 2026-11-24 研究接续

工作仓库为 `KasuganoLove/pequalnp-proofs`。以下文件使用 Lean 4.36.0 和项目固定的 Mathlib 修订 `fc4f59e`。每个上游 PR 各有一个提交，仅新增一个 Lean 文件。

## 上游提交

| 任务 | 已验证的结论 | 提交 |
| --- | --- | --- |
| L-meta-2802 | Petersen 图删去一个顶点后，即使免费提供额外输入 `x₀ ∨ x₆`，九个原始输入仍各有必要。给定至多十五次原始读取，除 0、6 外至少有一个输入恰被门读取一次。 | [PR 5157](https://github.com/brilliant-hq/pequalnp-proofs/pull/5157) |
| L-meta-2289 | 指定九顶点边函数无法由题设的至多十三个中间门和末端 AND 实现。证明还给出首门为 `x₀ ∧ x₆` 的完整电路需至少十六个门。证明使用 L-meta-1667 的原始图证书，并令 `x₆ = false` 利用删点后的十三门下界。 | [PR 5195](https://github.com/brilliant-hq/pequalnp-proofs/pull/5195) |
| L-meta-2782 | 将原问题归约为一般的非孤立点线关联下界和阶数至少 200 的剩余情形。第一个子命题已有逐字匹配的独立证明。 | [PR 5212](https://github.com/brilliant-hq/pequalnp-proofs/pull/5212) |

以上两份完整证明分别通过本地项目检查器的 `check`，归约通过 `reduce`。上游裁决及合并状态以各 PR 的官方记录为准。

## 射影平面

- [PlaneLowRange.lean](PlaneLowRange.lean) 证明有界扇入电路的全部 $2n$ 个输入都必要时至少需要 $2n-1$ 个门，并推得 $101≤q≤199$ 的原题结论。文末给出例外集合预算的精确逻辑关系。
- [PlaneEssentialInputs.lean](PlaneEssentialInputs.lean) 以检查器重新打印的第一个子命题为最终定理。检查器按 `check` 模式独立验过。
- [PlaneGateElim.lean](PlaneGateElim.lean) 使用项目的输入消去引理，把门数下界提高到 $2n$。这覆盖 $q=200$。该文件用到了 `PermInputs` 和 `LowMergeWires` 两个库模块。$q≥201$ 的原题下界仍开放。

## L-meta-1922

- [PetersenRows.lean](PetersenRows.lean) 证明题中 24 个测试输入足以确定整个单调函数。12 个正样本给出全部边，12 个负样本给出全部极大独立集。使用原有归约打印的子命题运行本地检查器，结果为 `ACCEPTED (check)`。
- [PetersenSecondAnd.lean](PetersenSecondAnd.lean) 排除了 28 个后续计算状态。免费线路是 `x₀ ∨ x₄`，若下一门是它与 `xᵢ` 的 AND，且 `i ≠ 0,4`，则在两个操作数保留或丢弃的四种选择下，十三个后续门都不够。令 `x₀=x₄=false` 后，剩余子图需要至少十一门。此研究文件使用 [L-meta-2289 的本轮证明文件](https://github.com/KasuganoLove/pequalnp-proofs/blob/1c6c0284346c35cf6898194bf0dea2fa74fcf7ad/lean/PEqualNP/Outside/L_meta_2289.lean) 提供的证书工具。

要复核独立研究文件，在仓库 `lean` 目录构建所用项目模块后，运行 `lake env lean <研究文件路径>`。正式提交的复核还需使用对应 PR 内的模块以及任务台原命题。
