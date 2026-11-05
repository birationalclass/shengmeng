# Linear 编译资源管控

2026-10-11：用户报告卡顿、内存不足和程序闪退。Windows System 日志的资源耗尽事件 2004 在今天出现三次；23:12 的记录中两个 lean.exe 分别提交约 43.3 GiB 和 24.6 GiB 内存。之后出现 Codex 挂起记录。机器有约 64 GiB 物理内存。证据记录的是本机故障，不能据此判定 GitHub Actions 被取消的原因。

所有正式编译、私有试验和公理审计统一通过 `lean_runner.run_file`。它在 Lean 执行前设置 Windows Job Object，不能安装保护时拒绝启动。

| 控制项 | 默认限制 |
| --- | --- |
| 同时运行的 Lean 编译 | 1；跨启动器的 Windows 命名互斥锁，忙时拒绝重复任务 |
| Lean 与子进程的总提交内存 | 8 GiB，Windows 硬限制；Lean 同时传入 `-M8192` |
| Lean 线程池 | `-j2` 和 `LEAN_NUM_THREADS=2` |
| CPU | Windows Job 总 CPU 配额最多 25%，低于正常优先级 |
| 单次编译墙钟时间 | 20 分钟；超时终止该任务的全部子进程 |
| 启动门槛 | 可用物理内存至少 16 GiB，系统提交占用低于 75%，提交余量至少 12 GiB |
| 单次任务预防性停止 | 提交内存达到硬上限的 95% 即结束，避免在上限处反复申请内存 |
| 运行中停止门槛 | 可用物理内存低于 12 GiB、提交占用达到 80% 或提交余量低于 12 GiB |
| 磁盘与日志 | 至少 5 GiB 磁盘余量；每次编译输出最多读取 32 MiB，超量失败 |
| 异常启动器退出 | 最后一个 Job 句柄关闭后清理该任务全部子进程 |
| 自动重试 | 超时或内存限制失败的相同源码被锁定，不能由定时任务反复重跑 |

配置在 `resource-policy.json`。编译入口：`lean_runner.py`；Windows 保护：`resource_guard.py`。本次上限有程序检查，不能通过配置无意提高到 8 GiB / 2 线程 / 25% CPU / 20 分钟以上。

每次运行在 `.lake/resource-control/runs/<id>/resource.json` 保存实际退出码、OS 确认的限制、峰值内存、启动前后系统内存，以及对应 stdout/stderr。被限制中断、源码变化、编译失败及缺少产物都不算验证通过；产物先写临时名称，成功后才接受。相同源码的资源失败保存在 `.lake/resource-control/holds/`；应先修补证明或拆分审计，再在已有上限内验证，不能绕开保护或自动放大上限。

测试涵盖内存分配被拒绝、跨进程串行锁、启动低内存拒绝、运行中压力退出、超时清理子进程、启动器异常退出清理、非法配置拒绝。真实 Lean 另检查库导入、内核检查、分批产物接受、失败时旧产物保留和禁止相同源码自动重试。测试记录在 `research/resource-safety-install-*/` 与 `research/resource-safety-validation/validation.json`。

先前 checkpoint181 的整体验证在本机内存耗尽时中断，未完成公理审计和冻结；checkpoint180 仍是最近完整本地验证。原 Lemma4.1/4.2 和主定理继续保持未完成。资源控制测试不是数学进展，也不能代替主定理验证。

不改变系统分页文件，不关闭安全软件，不结束其他应用的进程。后续定时工作沿用这些限制；若触发保护，保存证据并报告，不反复启动相同任务。

参考接口：[Windows Job Objects](https://learn.microsoft.com/en-us/windows/win32/procthread/job-objects)、[Job memory limits](https://learn.microsoft.com/en-us/windows/win32/api/winnt/ns-winnt-jobobject_basic_limit_information)、[Job CPU rate](https://learn.microsoft.com/en-us/windows/win32/api/winnt/ns-winnt-jobobject_cpu_rate_control_information)、[atomic job assignment](https://learn.microsoft.com/en-us/windows/win32/api/processthreadsapi/nf-processthreadsapi-updateprocthreadattribute)。Lean 参数已用本项目固定版本 `lean --help` 核对。

## 临时文件位置（2026-10-14）

用户询问 C 盘临时文件增长。后续本任务的临时 Lean 源码、私有脚本、截图与发布中转采用 `work/d-drive-staging-20261014/`，路径及复制哈希校验记录见 `research/d-drive-staging-current.json`。只同步 `formalization/linear`，避免再在 C 盘复制整站音频视频。现有 C 盘任务目录暂保留为历史副本；C 盘根目录的 Windows 分页、交换、转储及第三方程序文件不属于本任务。已安装的 Python/Codex 运行时仍可在 C 盘，编译输出、日志、资源记录与冻结源码仍位于权威 D 盘工程。资源上限、失败保留与 hold 规则不变。
