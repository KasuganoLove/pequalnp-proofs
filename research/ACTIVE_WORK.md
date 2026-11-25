# 当前 P vs NP 协作状态

## 当前有效租约

**本root没有有效任务租约。** 最近的L-meta-12128已于2026-11-25 **15:32:41.409774 UTC**以`missing_lemma`释放，HTTP200。关闭后没有启动该题的新数学、Lean或求解器工作。用户其他Codex会话（包括先前11030）的租约状态未知，本root未操作它们。继续具体任务研究前，需要按当前公开流程重新获得合法分配。

## 已公开的本root贡献

L-meta-12030的完整候选已通过普通Lean及当前文本guard，并已提交公开上游 **PR16085**：https://github.com/open-goat/pequalnp-proofs/pull/16085 。创建时间15:10:07 UTC；root于15:10:51.646204 UTC以`submitted`释放，HTTP200。

公开head为`2372e819a59762ba46009b456bcb7e27a226aca8`，一个commit新增一个文件；canonical源SHA256为`052c0e4396cdacee1909ddbf8b6e39d859bb960676599515c5ad60b9a202d11b`，Git blob为`f4a4e975bb4dd60160086cc01b3232c7959ea88c`。公开canonical与PR head未改。root于15:38:52 UTC最终只读确认PR仍open、merged=false、comments=0，head及canonical源均未变。官方判决仍待核实，本记录不声明ACCEPTED或合并。

本地严格检查的三个实际结果：

1. attempt1：ELAN路径缺失，0.275秒，checker exit3，没有verdict。
2. attempt2：原canonical在verifier阶段退出137，262.994秒，checker exit3，没有verdict。
3. attempt3：未发布的35分块实验在文件build阶段通过；verifier仍退出137，211.273秒，最高RSS6,557,908KiB，checker exit3，没有verdict。

root暂不继续优化该实验。随后公理查询exit0，仅列`propext`、`Classical.choice`、`Quot.sound`；这不替代strict verifier的完整重放。Julleht有竞争PR16006，不能把其结果归属本root。用户要求的公开上游PR已经创建；后续官方验收应按实际证据另行记录。

## 本次归档

- **C19**：12030的精确来源、128行独立重放、普通/格式检查、标准公理审计、三次strict FAULT和公开发布记录。完整源码已经公开，归档不重复复制。
- **C20**：12128普通Lean通过的“非NOT门至少九个／有NOT则总门至少十个”研究部分；十三门全64行控制；十门和十一门两次120秒UNKNOWN搜索；MAJ5引出的总门数至少十一逻辑路线尚未组装。没有完整12128证明或该题官方PR。

C19/C20在已发布C18提交`7cc37d33bddb94ca90b4580c2ee9fad9f4ca86e5`之上合并归档；最终提交号以远端发布记录为准。研究partial的Outside导入不能直接用作12128的正式文件，其官方导入仅允许Defs。负面搜索结果不构成下界证明。

## 先前贡献归属

用户另一Codex会话创建的PR14022已合并并使10221 checked，本root不认领其创建。10486的PR14954归属odinfree，11315的PR15263归属ptrdsh。12030保留对ptrdsh/L10458通用证明来源的归属；不要把复用、普通检查与官方验收混为一谈。
