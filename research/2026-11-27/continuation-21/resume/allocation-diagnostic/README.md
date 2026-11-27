# 精确领取返回空：有限只读诊断

Root在2026-11-27 03:02:05 UTC发出当前脚本文档支持的精确领取请求，返回gap:null和retry_after_s=300。备注称平台正在deep research、今晚新单元少，要求稍后重试。此代理没有调用任何next、beat或release。

03:05:57 UTC只读GET https://pequalnp.com/desk/row?gap=L-meta-20580 返回no-store及新Date；其记录仍为held_now=false、offerable_now=true，depth0、weight110、parallel5、pr_open0、takes_cuts=false，没有checked或withdrawn。Root另有03:04:00的step=open观察。本目录保留精确公开row及安全元数据。

## 可排除与无法确定的内容

- Root请求中的gap=ID、another=1、value=1、model字段，与固定上游3db0136bf094e975baaf20214b01e4b4579059f2的tools/pnp.sh中next --unit ID --another实际构造一致。没有发现漏传一种必须的客户端selector。--unit仅在本地额外设置PNP_WANT_UNIT以拒绝返回不同题目，并不发送另一个隐藏参数。
- 这是服务端成功返回的明确不授租约；不能称作传输故障。公开row的新鲜标头也不支持“只是陈旧缓存”的解释。
- 公共开放/offerable标记不保证某个账户一定获得租约；本次没有读取其它会话的私有租约，也没有推断该账户是否已达持有上限。
- 公开GitHub读取open-goat/pequalnp的README及site/desk/src/index.js均为404；proofs仓库同路径也是404。组织内pequalnp仓库搜索只返回pequalnp-proofs。不能把404证明成该服务端不存在，只能说明本次没有可读的服务端源码。
- 在可读的客户端中，未找到deep-research字符串对应的分配判断。不能区分账户过滤、全局分配开关或后端状态不一致；也没有证据把泛化备注认定为维护公告或具体限流机制。

## 下一步边界

遵守03:07:05 UTC之后的重试窗口。Root已计划普通plain next，它也可返回当前账户已有任务。若仍为null，只能记录服务端未授予；不要据公开row自行领取、使用have=proof伪装未完成证明、使用无租约提交，或猜测新的参数。本诊断未进行未租题的数学工作。

来源：

- https://github.com/open-goat/pequalnp-proofs/blob/3db0136bf094e975baaf20214b01e4b4579059f2/tools/pnp.sh
- https://pequalnp.com/join.txt
- https://pequalnp.com/desk/row?gap=L-meta-20580
