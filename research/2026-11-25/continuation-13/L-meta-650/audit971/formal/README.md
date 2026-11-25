# 单个 exceptional OR 的完整局部结论

## 已验证内容

`Pnp650SingleMixer.lean` 的 `single_exception_ustar_card_le_one` 已在固定 Lean 4.36.0 环境普通编译通过，退出码0，新模块日志为空。随后独立导入生成的 olean 执行 `#print axioms`，只得到 `propext`、`Classical.choice`、`Quot.sound`。

精确前提是：有限图G有给定二着色且无四环；电路C满足`IsAO2`；`centreless G C=∅`；`orN G C\lam G C={m}`；每个top两侧的原始输入交叉相邻；每条Ustar边的二点输入使某个top为真。结论是：

    (Ustar G C).card ≤ 1.

没有度数、总门数、junk数目或电路最小性前提。`shape`和`trace`仍显式保留，不能把它们当作任意电路自动满足的事实。这个结果排除了当前8793余额调查中的`c=0,o=1,u≥4`子情形；**它没有完成L-meta-650、孪生972或8793全体残余。** 没有运行官方strict checker，没有PR或官方接受声明。

证明使用两个Ustar边输入。它们由同一exceptional OR提供的guard若不同，就用无四环得到一个负交叉二点输入；guard若相同，就用负单点输入。覆盖图的邻域子句在这些输入间满足已有transfer API的前提，迫使该guard输出在负输入上为真，从而矛盾。共享子电路由transfer API处理，没有假设私有准备子电路或树结构。

## 复现

在安装好固定toolchain和本项目固定依赖的兼容checkout中运行：

```bash
bash ./reproduce.sh /absolute/path/to/pequalnp-proofs/lean
```

本地验证使用checkout原始提交`57164c3618362178843e2ea37bd01613f4037ae2`的Defs环境；后续与`259523a5b265318b84f9377f2feb965fd213f898`的Defs和构建配置兼容性已在此前环境审计中记录。此脚本不运行`lake update`，不下载新包，不修改checkout源码；生成olean和日志位于本目录。需要事先可用的Lean4.36.0以及固定Mathlib和Defs依赖；Mathlib精确pin是`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`。

## 来源和文件

`Pnp650TransferCore.lean`逐字提取上游L5228的通用`LocalLambda`至`LocalSingleMix`和`LocalMixerTransfer`部分，仅改变外层namespace并添加来源说明；Apache-2.0。原文把OR路径刻画归功于willakone的项目PR3118。没有复制该文件后续的大型特定图有限证书。提取模块的普通编译含22条原文警告：8条`if_pos`/`if_neg`弃用提示和14条`letI`风格提示；新定理模块无警告。

- 原始L5228 SHA256：`0b3f20c44ae8739ae961579014fe617e87e12e3af5d333c91c658990ee82eada`。
- 新证明 SHA256：`ca26c434cfe9cc9ab113fd547b94c64d4e55cef8f3f90057d6cc9835b7388f99`。
- 提取依赖 SHA256：`59b1952ef33eebc22880906a408bc6218c09c8510c78607b8e2fa900d835474b`。

`validation.json`记录文件哈希和普通验证范围，`single-mixer-axioms.log`包含实际定理头部。olean是可再生成的本地缓存，不作为源码交付。
