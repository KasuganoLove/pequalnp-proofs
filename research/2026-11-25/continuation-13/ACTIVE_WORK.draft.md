# ACTIVE_WORK — 2026-11-25 continuation-13

## 项目目标与当前提交状态

继续使用 `KasuganoLove/pequalnp-proofs`，官方上游为 `open-goat/pequalnp-proofs`。用户要求本阶段形成合法的官方上游PR并收到官方ACCEPTED；**本检查点尚未达到该标准**，没有新的官方PR或ACCEPTED。浏览器连接已恢复：root通过Browser插件观察确认本地Chrome的GitHub会话为KasuganoLove；认证连接不再是当前阻碍。

先前的8323精确证明仍保留，曾通过本地严格检查，但 **2026-11-25 11:08:20 UTC 的step API返回NOT_OPEN**。11:09:49.108 UTC台账不在gaps、checked、withdrawn中列出8323；当前上游规范文件404，也未找到对应证明PR。父题4201及其R4201_777仍open，cut哈希未变，关闭原因未知。不能声称已被接受、已撤回或仍可直接提交。相关草稿proposal为 **BLOCKED、未发送**；证据在本检查点的submission-status-update目录。

## 刚关闭的研究任务

**L-meta-650** 已于 **2026-11-25 11:14:32.704521 UTC** 成功归还：HTTP200，reason=`missing_lemma`。本轮没有活跃求解器或Lean任务。root将单独记录下一次合法分配；此文件不假定任何新租约。最后已记录的allocator观察是11:07:22 UTC返回gap=null、retry_after_s=300，不推断原因。

650要求PG(2,3)的26输入、52边关联函数有至多63门Monotone2电路；完整见证及反向64门下界都仍未解决。

### 完成并保留的工作

- 单次300秒局部SAT：五点加13线、18输入20边，搜索23门，结果UNKNOWN，无模型、无UNSAT结论或证书。已知24门局部基线的262,144输入及接回后的64门全图基线的67,108,864输入均经普通全枚举验证，零错误，仍超预算。
- 一个普通Lean已验证的局部引理：给定二分、无四环、IsAO2、无centreless top、唯一exceptional OR，以及显式top shape和正边trace，推出 `Ustar.card ≤ 1`。完整源、必要提取依赖、复现脚本、日志与标准公理审计已归档。它不是650、972、8793的完整证明，未经过官方strict checker。
- 几何枚举、限制输入与新Heawood证明的可迁移性审计；精确指出诱导Heawood限制不存在及朴素余因子平均界缺少什么前提。
- 一个非形式化的多输出Boolean和架构障碍，排除只在纯线变量准备网络中加入AND来把标准星形64门降为63门；不排除一般混合电路。

### 剩余数学缺口

R972_5的4181、8725、8791三个前提已checked，剩8793的至少两个junk AND情形。其ledger/count子工具7862、9047也已checked，8943与9049仍需新的论证。不要把Bzero等同junk数，不要假定每个中间AND自动受输出函数约束，也不要把已撤回的 `u=4,t=12,c=0 ⇒ o≥4` 草图重新当成结果。

## 检查点位置

本次待root发布的目录是 `research/2026-11-25/continuation-13/`；发布前本地staging为 `pnp-publication-staging/continuation-13/`。它仅收录本轮650工作及必要状态变更，排除了租约秘密、完整全台JSON、无用第三方全文、CNF、大映射、可再生明细与二进制。

发布之前最后由root验证的research分支head为 `0d0ad82d8ebf74a431135bc5b995e654a9aae91b`（continuation-12）；发布后应将此行替换为实际新head。本文件是ACTIVE_WORK更新草稿，没有直接修改远端或既有ACTIVE_WORK。
