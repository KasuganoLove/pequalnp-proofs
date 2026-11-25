# Singular 本地精确计算环境

**可用版本：Singular 4.4.0（44005，64 位）**。这是官方预编译 Linux 包，原始工作区解压目录为 `pnp-tools/singular/4.4.0-x86_64-Linux/`；本检查点不包含工具二进制或下载归档。保留完整目录结构，二进制会查找相邻的库和数据目录。

## 使用

```bash
/workspace/scratch/65f339da29fe/pnp-tools/singular/4.4.0-x86_64-Linux/bin/Singular -q --no-rc /absolute/path/to/input.sing
```

也可仅在需要的 shell 中加入 PATH：

```bash
export PATH=/workspace/scratch/65f339da29fe/pnp-tools/singular/4.4.0-x86_64-Linux/bin:$PATH
```

这不需要 root、系统安装或更改 Lean 环境。没有修改 shell 启动配置。

## 已验证的通用证书路径

`smoke.sing` 只使用有理数环 `Q[x,y]` 中的小型理想 `I=<xy-1,y²>`。它加载 `general.lib`，分别调用 `liftstd(I,T,"std")` 和 `liftstd(I,T,"slimgb")`，检查结果为 `[1]`，并在精确多项式环中验证 `matrix(G)=matrix(I)*T`。

两种算法均退出 0，并返回相同乘子 `(-xy-1,x²)`，因此

```text
(-xy-1)*(xy-1)+x²*y² = 1.
```

运行本例：

```bash
/workspace/scratch/65f339da29fe/pnp-tools/singular/4.4.0-x86_64-Linux/bin/Singular -q --no-rc /workspace/scratch/65f339da29fe/pnp-tools/singular/smoke.sing
```

结果在 `logs/smoke.log`。这只是计算环境检查，没有执行当前或过去的项目任务方程，也不构成 Lean 核验。

## 版本选择与依赖

先试用了官方 `Singular-4.4.1-Rocky8.tar.gz`。它依赖当前主机缺少的 `libmpfr.so.4` 和 `libreadline.so.7`，因此未将它设为可用版本；本检查点在 installation.json 中保留该次失败的依赖记录。

官方 4.4.0 Linux 包的全部 ELF 依赖均已解析，包括当前主机的 `libreadline.so.8`、`libtinfo.so.6`、`libstdc++.so.6` 等。`--version` 报告 GMP 6.2.1、NTL 11.5.1、FLINT 2.8.5；这不表示已另行安装可供 Python 使用的这些库。

两个归档均从官方 HTTPS 下载地址取得，均与同目录官方 `MD5SUM` 一致；本地 SHA-256、运行状态及完整来源见 `installation.json`。未安装系统依赖，未创建跨 ABI 软链接。

## 官方来源

- 下载目录：<https://www.singular.uni-kl.de/ftp/pub/Math/Singular/UNIX/>
- 手工安装说明：<https://www.singular.uni-kl.de/ftp/pub/Math/Singular/UNIX/INSTALL_unix.txt>
- `liftstd` 变换证书说明：<https://www.singular.uni-kl.de/Manual/latest/sing_294.htm>

原始工作区保留下载与诊断日志。本检查点仅发布本说明、installation.json、smoke.sing 与 logs/smoke.log；重新安装须从上述官方来源下载并核对 installation.json 中记录的校验值。
