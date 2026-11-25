# C19：L-meta-12030 的公开 PR 与复现审计

**公开上游 PR 已创建：[open-goat/pequalnp-proofs#16085](https://github.com/open-goat/pequalnp-proofs/pull/16085)。** 本 root 于2026-11-25 15:10:07 UTC创建该PR，head为 `2372e819a59762ba46009b456bcb7e27a226aca8`，一个commit只新增一个证明文件。15:10:51.646204 UTC以 `submitted` 释放，HTTP200。用户要求的公开上游PR这一事实已经发生；官方判决仍须与本地验证区别。

此包冻结第三次本地严格复核结束及随后公理审计的实际结果：普通Lean和当前格式guard通过，最终定理的公理列表只有标准三公理，三次strict均为FAULT、没有verdict。root暂不继续优化；公开canonical源和PR head保持不变。归档代理仅重新运行一次当前纯文本格式guard，没有运行Lean、求解器、租约请求或远端写入。

## 精确源与验证状态

canonical 文件为 `lean/PEqualNP/Outside/L_meta_12030.lean`，58,118字节，SHA256为 `052c0e4396cdacee1909ddbf8b6e39d859bb960676599515c5ad60b9a202d11b`，Git blob为 `f4a4e975bb4dd60160086cc01b3232c7959ea88c`。它已公开于上述固定提交，本包不重复复制完整Lean源码。`provenance/source.json`保存不可变取回地址、源hash、精确命题hash及上游来源。

| 检查 | 结果与范围 |
|---|---|
| 独立标量重放 | 十门AND/OR控制在全部128个输入上与精确题面相等；三个限制步骤及K4核心另行核对。 |
| 普通Lean | exit0，42.999秒，最高RSS4,439,600KiB；完整精确题面编译通过。 |
| 公理审计 | 结果记录于15:32:28.637128 UTC，exit0，6.374秒；最终定理仅依赖`propext`、`Classical.choice`、`Quot.sound`。 |
| 当前格式guard | 已保存实际命令与输出：2026-11-25 15:28:49.932243—15:28:50.084817 UTC，exit0，0.153秒；校验前确认公开canonical源hash未变。 |
| 本地strict attempt1 | 15:06:44.933406开始，0.275秒，exit3；ELAN路径缺失导致verifier无法构建。 |
| 本地strict attempt2 | 15:08:28.052809—15:12:51.047248，262.994秒，exit3；verifier退出137，明确报告没有verdict。 |
| 本地strict attempt3（未发布拆分实验） | 15:20:50.430823—15:24:21.703476，211.273秒，最高RSS6,557,908KiB；文件build阶段通过，verifier退出137，checker退出3，没有verdict。 |
| 官方PR | 已创建，公开head/source绑定；本包尚未确认后续官方ACCEPTED或合并结论。 |

前两次strict使用同一份公开canonical源。第三次实验把一条`searchS_false`计算拆成35条`(s,m0)`不透明引理再有限汇总，实验源65,583字节、SHA256为`e2c93bdfcd6296b6045fd506fa7fc2fe913f7f0fcf5886d47202393dd4fc9eb3`。它在strict文件build阶段通过，但verifier仍退出137，没有发布。环境路径故障与verifier被终止都没有提供数学拒绝或接受判决，不能替代官方checker结果。三次原始日志、结果和实验源hash保存在`strict-attempts/`，与普通Lean记录分别保存。随后独立执行的`axioms-probe.lean`只查询已编译canonical定理的依赖，日志列出标准三公理；这项审计不能替代strict verifier的完整重放，也不改变三次FAULT状态。

## 证明结构和作者归属

本题是指定七顶点图函数的NOT移除命题。候选复用ptrdsh已合并PR15263/L-meta-11315中的通用结构证明，其更早来源为L-meta-10458，仓库许可证Apache-2.0；候选头部及本包来源记录均保留这一归属。

新增实例数据包括精确图表、依次把变量1、2、4设为false后的三个真值表、改变赋值10/68/17、持续非零赋值9，以及一个显式十门AND/OR电路。保留的四个变量0、3、5、6形成K4。已有通用证书给该核心至少七次保零二元操作；三次删除各计至少一次，得到至少十个非NOT门。含NOT的电路于是至少十一门，十门单调控制足以替换；原本没有NOT的电路原样返回。

这是基于已证明通用引理的实例化，没有启动新的七输入全电路搜索。普通Lean检查的是完整精确题面。独立Python审计只检查实例数据，不冒充重新证明通用下界。

## 可复现材料

`L-meta-12030/`包含公开题面、实例化生成器、普通Lean日志、独立128行重放脚本与结果、初始提交环境审计、公开发布记录和去除私密租约内容的submitted事件。原始冻结manifest保留其来源身份；其中所列完整候选源有意省略，可从`provenance/source.json`给定的公共固定提交取回。

在单独工作副本中复现有限数据：

```sh
cd L-meta-12030
python3 independent-audit/verify_witness_and_restrictions.py
```

脚本会更新本副本的验证JSON。若要重建候选，先取回上游固定commit `7dd594cc96b1fc5b83ca9266a00cef93d6871df6` 的 `L_meta_11315.lean`，其SHA256必须为 `e13152ef69931ca79dc9f4354f6752a38f3c17a48863616654032ab41a18b131`，再给生成器显式路径：

```sh
python3 prepare_structural.py --reference /path/to/L_meta_11315.lean --output /path/to/checkout/lean/PEqualNP/Outside/L_meta_12030.lean
```

生成器校验来源hash、全部有限数据和最终命题，并拒绝覆盖不同内容。也可直接从公共PR固定提交取回最终文件，核对上述源hash后，在固定环境的`lean/`中运行：

```sh
lake env lean -j1 -o .lake/build/lib/lean/PEqualNP/Outside/L_meta_12030.olean PEqualNP/Outside/L_meta_12030.lean
```

拆分实验可由`formalization/prepare_split.py`从上述canonical源重建，无需再次保存65,583字节临时Lean源。该原始脚本按原工作区布局定位文件：在一个临时工作目录下放置`pequalnp-proofs/lean/PEqualNP/Outside/L_meta_12030.lean`，并把脚本置于`pnp-session-2026-11-25/continuation-12/L-meta-12030/formalization/prepare_split.py`，然后执行它。脚本校验canonical源SHA并拒绝覆盖已经存在的实验文件；重建只生成源，不运行Lean。该实验不是公开PR的版本。

本轮采用Lean4.36.0、Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`；提交基底为upstream `28df579920ab2d24173303380ba8d951c8c0d263`，Defs与已用本地环境逐字节相同。正式严格复核由root使用未修改的官方checker完成。

初始desk/PR搜索的“未观察到PR”记录明确限于其旧快照。Julleht的竞争PR16006在15:03:17已经打开；本root的PR16085不得借用对方的后续结果。当前新任务12128单独记在ACTIVE_WORK，未纳入此12030证据包。C19以已发布C18提交`7cc37d33bddb94ca90b4580c2ee9fad9f4ca86e5`为基底，根tree为`bccc7574a50d28289941636f29cc3d45aeabee51`。
