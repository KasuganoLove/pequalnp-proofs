# Lean 4.36.0 的只读并行度核验

最短构建调用：在项目lean目录运行 `LEAN_NUM_THREADS=1 lake build +PEqualNP.Defs`。这条命令在本核验中没有执行。

Lake的构建Job.async使用Lean默认任务池；v4.36.0的runtime/object.cpp读取LEAN_NUM_THREADS并据此初始化任务池。Lake本版CLI没有-j/--jobs，所查源中也没有LAKE_JOBS读取。环境变量约束Lake默认构建worker，不能解读成整个进程树恰好只有一个OS线程：I/O有dedicated线程。直接检查单个Lean源时使用 `lake env lean -j1 file.lean`；-j1是Lean参数。

本机执行的唯一二进制命令为lean --help，确认版本4.36.0、commit611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9和-j/--threads参数。没有构建、安装、修改配置或证明文件。

源证据：
- https://github.com/leanprover/lean4/blob/v4.36.0/src/runtime/object.cpp （Git blob fb7a5ccc488f33d03683117f55a42fec01dd0081；get_lean_num_threads与lean_init_task_manager）
- https://github.com/leanprover/lean4/blob/v4.36.0/src/lake/Lake/Build/Job/Monad.lean （Job.async）
- https://github.com/leanprover/lean4/blob/v4.36.0/src/lake/Lake/CLI/Help.lean （完整Lake选项）
- https://github.com/leanprover/lean4/blob/v4.36.0/src/Init/System/IO.lean （IO.Process.output）
