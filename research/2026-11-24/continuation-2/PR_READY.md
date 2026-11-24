# 待提交的上游 PR

两份分支已推到用户 fork；本快照尚未创建上游 PR。GitHub 连接器对上游创建 PR 返回 403，安全登录接口返回不可用，需完成手动登录交接后继续。不要把分支推送或本地 ACCEPTED 当作官方提交成功。

上游：`open-goat/pequalnp-proofs`；base：`main`。

## L-meta-3358

- Title: `L-meta-3358`
- Head: `KasuganoLove:codex/L-meta-3358-20261124`
- Commit: `9ed381f4165528fa489bd1f2eff81c4bf57d811d`
- [已核对的比较页](https://github.com/open-goat/pequalnp-proofs/compare/main...KasuganoLove:pequalnp-proofs:codex/L-meta-3358-20261124?expand=1)

投稿前重新核对排队结果：14:34 UTC 查询到本题已有多份其他贡献者的 PR，尚未观察到接受裁决。

### Body

Proves L-meta-3358, the first published child of the merged reduction R_meta_2519_608 (#5362).

Backward dependency tracing bounds the number of initial input positions used by one output by one plus the number of non-NOT gates. With at most seven gates and two distinct NOT gates, at most six of the seventeen initial positions are needed.

This carries forward Prepared2519ChildOne, completed while working on the parent task. The mathematical proof is unchanged; the namespace matches the published child and the Mathlib import is narrowed to Finset.Card.

Validation: the theorem statement is byte-for-byte identical to the published statement; the fixed Lean 4.36.0 build and import/plain-file/namespace guard pass. The project's independent local checker returned ACCEPTED (check), rechecking 1,680 constants with only propext, Classical.choice and Quot.sound. The initial full-Mathlib attempt hit a resource FAULT; the final narrowed-import file passed. Authoritative upstream verification is pending.

One commit, one added Lean file.

## R-meta-3233-713

- Title: `R-meta-3233-713`
- Head: `KasuganoLove:codex/R-meta-3233-713-20261124`
- Commit: `86a9b1c3e83eb90493b36c2c385b67dc67563213`
- [分支](https://github.com/KasuganoLove/pequalnp-proofs/tree/codex/R-meta-3233-713-20261124)

提交前重新核对任务状态与归约配额；公开任务台可能落后于 GitHub 队列。

### Body

Reduces L-meta-3233 to two independent closed subgoals: the existing L-meta-3438 non-NOT gate lower bound, and the original circuit lower bound restricted to at most two NOT gates.

If a counterexample has at most fifteen gates, the first subgoal supplies at least thirteen non-NOT gates. The disjoint NOT/non-NOT counts sum to the circuit size, so the circuit has at most two NOT gates; the second subgoal then rules it out. This leaves the first-wire and canonical second-OR conditions unchanged.

The first child is byte-identical to the published L-meta-3438 statement. I also compiled a supporting proof of that child by adapting the existing upstream Petersen binary lower-bound proof; it is archived in the fork's research branch, not added to this one-file reduction PR. Existing proof PRs #6461, #6591 and #6636 already cover that child, so no duplicate proof PR is submitted.

Validation: the final conclusion is byte-for-byte identical to the task statement. The fixed Lean 4.36.0 build and the project's import/plain-file/namespace guard pass. Two local strict-check attempts reached the independent verifier and ended with exit 137 / wrapper exit 3 (CHECKER FAULT), without a verdict. A separate Lean pretty-printer diagnostic reports closed child lengths 911 and 1,364 characters, both below 2,000; these are diagnostic previews, not strict-check CHILD output. Authoritative reduction validation is pending upstream CI.

One commit, one added Lean file. The complete L-meta-3233 theorem is still open pending its remaining child.

