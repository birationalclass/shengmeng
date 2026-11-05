"""Bound only this project's child processes; never change Windows settings.

Windows 10+ job-list process creation applies limits BEFORE code runs. A named
mutex serializes independent build/audit/private/heartbeat compiler launchers.
No unsafe fallback is allowed when an OS guard cannot be installed.

References: Microsoft Learn Job Objects, UpdateProcThreadAttribute,
JOBOBJECT_EXTENDED_LIMIT_INFORMATION and JOBOBJECT_CPU_RATE_CONTROL_INFORMATION.
"""
from pathlib import Path
from dataclasses import dataclass, asdict
import ctypes as C
from ctypes import wintypes as W
import datetime
import hashlib
import json
import os
import shutil
import subprocess
import time
import uuid

MIB = 1024 * 1024
MUTEX_NAME = r"Local\ShengMengLeanCompilerSafety-v1"


@dataclass(frozen=True)
class Policy:
    schema_version: int = 1
    max_concurrent_compilers: int = 1
    lean_memory_mb: int = 8192
    job_memory_mib: int = 8192
    lean_threads: int = 2
    cpu_percent: int = 25
    timeout_seconds: float = 1200
    minimum_free_physical_mib: int = 16384
    stop_free_physical_mib: int = 12288
    maximum_commit_percent: float = 75
    stop_commit_percent: float = 80
    minimum_commit_headroom_mib: int = 12288
    minimum_disk_free_mib: int = 5120
    maximum_output_mib: int = 32
    poll_seconds: float = 1.0
    automatic_retry_after_resource_failure: bool = False

    def __post_init__(self):
        # Configuration cannot silently disable safety or increase the ceiling.
        conditions = [self.schema_version == 1, self.max_concurrent_compilers == 1,
                      32 <= self.job_memory_mib <= 8192,
                      32 <= self.lean_memory_mb <= self.job_memory_mib,
                      1 <= self.lean_threads <= 2, 1 <= self.cpu_percent <= 25,
                      0 < self.timeout_seconds <= 1200, 0 < self.poll_seconds <= 1.0,
                      0 < self.maximum_output_mib <= 32,
                      0 < self.stop_free_physical_mib <= self.minimum_free_physical_mib,
                      0 < self.maximum_commit_percent <= self.stop_commit_percent <= 80,
                      self.minimum_commit_headroom_mib > 0, self.minimum_disk_free_mib > 0,
                      self.automatic_retry_after_resource_failure is False]
        if not all(conditions):
            raise ValueError("unsafe or invalid resource policy; no compiler will be launched")


def load_policy(path):
    return Policy(**json.loads(Path(path).read_text(encoding="utf-8")))


class GuardRefused(RuntimeError):
    pass


class BasicLimits(C.Structure):
    _fields_ = [("PerProcessUserTimeLimit", C.c_longlong),
                ("PerJobUserTimeLimit", C.c_longlong), ("LimitFlags", W.DWORD),
                ("MinimumWorkingSetSize", C.c_size_t), ("MaximumWorkingSetSize", C.c_size_t),
                ("ActiveProcessLimit", W.DWORD), ("Affinity", C.c_size_t),
                ("PriorityClass", W.DWORD), ("SchedulingClass", W.DWORD)]


class IOCounts(C.Structure):
    _fields_ = [(name, C.c_ulonglong) for name in
                ("ReadOperationCount", "WriteOperationCount", "OtherOperationCount",
                 "ReadTransferCount", "WriteTransferCount", "OtherTransferCount")]


class ExtendedLimits(C.Structure):
    _fields_ = [("BasicLimitInformation", BasicLimits), ("IoInfo", IOCounts),
                ("ProcessMemoryLimit", C.c_size_t), ("JobMemoryLimit", C.c_size_t),
                ("PeakProcessMemoryUsed", C.c_size_t), ("PeakJobMemoryUsed", C.c_size_t)]


class CPURate(C.Structure):
    _fields_ = [("ControlFlags", W.DWORD), ("CpuRate", W.DWORD)]


class PerfInfo(C.Structure):
    _fields_ = [("cb", W.DWORD)] + [(name, C.c_size_t) for name in
                ("CommitTotal", "CommitLimit", "CommitPeak", "PhysicalTotal",
                 "PhysicalAvailable", "SystemCache", "KernelTotal", "KernelPaged",
                 "KernelNonpaged", "PageSize")] + [(name, W.DWORD) for name in
                ("HandleCount", "ProcessCount", "ThreadCount")]


class StartupInfo(C.Structure):
    _fields_ = [("cb", W.DWORD), ("lpReserved", W.LPWSTR), ("lpDesktop", W.LPWSTR),
                ("lpTitle", W.LPWSTR)] + [(name, W.DWORD) for name in
                ("dwX", "dwY", "dwXSize", "dwYSize", "dwXCountChars", "dwYCountChars",
                 "dwFillAttribute", "dwFlags")] + [("wShowWindow", W.WORD),
                ("cbReserved2", W.WORD), ("lpReserved2", C.c_void_p),
                ("hStdInput", W.HANDLE), ("hStdOutput", W.HANDLE), ("hStdError", W.HANDLE)]


class StartupInfoEx(C.Structure):
    _fields_ = [("StartupInfo", StartupInfo), ("lpAttributeList", C.c_void_p)]


class ProcessInfo(C.Structure):
    _fields_ = [("hProcess", W.HANDLE), ("hThread", W.HANDLE),
                ("dwProcessId", W.DWORD), ("dwThreadId", W.DWORD)]


def _apis():
    if os.name != "nt":
        raise GuardRefused("Windows job protection is unavailable; refusing an unbounded launch")
    k = C.WinDLL("kernel32", use_last_error=True)
    ps = C.WinDLL("psapi", use_last_error=True)
    specs = {
        "CreateMutexW": ([C.c_void_p, W.BOOL, W.LPCWSTR], W.HANDLE),
        "WaitForSingleObject": ([W.HANDLE, W.DWORD], W.DWORD),
        "ReleaseMutex": ([W.HANDLE], W.BOOL),
        "CloseHandle": ([W.HANDLE], W.BOOL),
        "CreateJobObjectW": ([C.c_void_p, W.LPCWSTR], W.HANDLE),
        "SetInformationJobObject": ([W.HANDLE, C.c_int, C.c_void_p, W.DWORD], W.BOOL),
        "QueryInformationJobObject": ([W.HANDLE, C.c_int, C.c_void_p, W.DWORD, C.c_void_p], W.BOOL),
        "TerminateJobObject": ([W.HANDLE, W.UINT], W.BOOL),
        "GetExitCodeProcess": ([W.HANDLE, C.POINTER(W.DWORD)], W.BOOL),
        "InitializeProcThreadAttributeList": ([C.c_void_p, W.DWORD, W.DWORD, C.POINTER(C.c_size_t)], W.BOOL),
        "UpdateProcThreadAttribute": ([C.c_void_p, W.DWORD, C.c_size_t, C.c_void_p, C.c_size_t, C.c_void_p, C.c_void_p], W.BOOL),
        "DeleteProcThreadAttributeList": ([C.c_void_p], None),
        "CreateProcessW": ([W.LPCWSTR, W.LPWSTR, C.c_void_p, C.c_void_p, W.BOOL,
                            W.DWORD, C.c_void_p, W.LPCWSTR, C.POINTER(StartupInfoEx),
                            C.POINTER(ProcessInfo)], W.BOOL),
    }
    for name, (argtypes, restype) in specs.items():
        fn = getattr(k, name)
        fn.argtypes, fn.restype = argtypes, restype
    ps.GetPerformanceInfo.argtypes = [C.POINTER(PerfInfo), W.DWORD]
    ps.GetPerformanceInfo.restype = W.BOOL
    return k, ps


def _check(ok):
    if not ok:
        raise C.WinError(C.get_last_error())


def memory_snapshot():
    _, ps = _apis()
    perf = PerfInfo(cb=C.sizeof(PerfInfo))
    _check(ps.GetPerformanceInfo(C.byref(perf), C.sizeof(perf)))
    return {
        "physical_mib": round(perf.PhysicalTotal * perf.PageSize / MIB, 1),
        "free_physical_mib": round(perf.PhysicalAvailable * perf.PageSize / MIB, 1),
        "committed_mib": round(perf.CommitTotal * perf.PageSize / MIB, 1),
        "commit_limit_mib": round(perf.CommitLimit * perf.PageSize / MIB, 1),
        "commit_headroom_mib": round((perf.CommitLimit - perf.CommitTotal) * perf.PageSize / MIB, 1),
        "commit_percent": round(100 * perf.CommitTotal / perf.CommitLimit, 2),
    }


def pressure_reason(snapshot, policy, *, starting):
    reserve = policy.minimum_free_physical_mib if starting else policy.stop_free_physical_mib
    percent = policy.maximum_commit_percent if starting else policy.stop_commit_percent
    if snapshot["free_physical_mib"] < reserve:
        return f"free RAM below {reserve} MiB"
    if snapshot["commit_percent"] >= percent:
        return f"system commit at or above {percent}%"
    if snapshot["commit_headroom_mib"] < policy.minimum_commit_headroom_mib:
        return "insufficient system commit headroom"
    return None


class CompilerLease:
    """Crash-released, cross-process mutex; busy runs do not queue extra work."""
    def __init__(self, name=MUTEX_NAME):
        self.name, self.handle, self.k = name, None, None

    def __enter__(self):
        self.k, _ = _apis()
        self.handle = self.k.CreateMutexW(None, False, self.name)
        _check(self.handle)
        status = self.k.WaitForSingleObject(self.handle, 0)
        if status not in (0, 0x80):  # WAIT_OBJECT_0 / WAIT_ABANDONED
            self.k.CloseHandle(self.handle)
            self.handle = None
            raise GuardRefused("another protected compiler is running; no second compiler launched")
        return self

    def __exit__(self, *_):
        if self.handle:
            self.k.ReleaseMutex(self.handle)
            self.k.CloseHandle(self.handle)
            self.handle = None


def run_bounded(args, *, input_bytes, cwd, env, state_dir, policy, mutex_name=MUTEX_NAME):
    """CompletedProcess-compatible result; any guard refusal is a nonzero exit.

    stdin and compiler output use files, avoiding an unbounded capture_output
    allocation. The OS job covers all descendants and dies with this launcher.
    """
    import msvcrt
    state_dir = Path(state_dir)
    state_dir.mkdir(parents=True, exist_ok=True)
    run_id = uuid.uuid4().hex
    run_dir = state_dir / run_id
    run_dir.mkdir()
    record = {"id": run_id, "started_at": datetime.datetime.now().astimezone().isoformat(),
              "launcher_pid": os.getpid(), "command": list(map(str, args)),
              "source_sha256": hashlib.sha256(input_bytes).hexdigest(),
              "policy": asdict(policy), "status": "starting", "peak_job_memory_mib": 0}
    record_path = run_dir / "resource.json"
    record_path.write_text(json.dumps(record, indent=2), encoding="utf-8")
    started = time.monotonic()
    rc, reason = 127, None
    job, attrs, process = None, None, ProcessInfo()
    k = None
    lease = CompilerLease(mutex_name)
    try:
        with_lease = lease.__enter__()
        if with_lease:
            k, _ = _apis()
            record["memory_before"] = memory_snapshot()
            reason = pressure_reason(record["memory_before"], policy, starting=True)
            if reason:
                raise GuardRefused(reason)
            if shutil.disk_usage(state_dir).free < policy.minimum_disk_free_mib * MIB:
                raise GuardRefused("insufficient disk space for compiler logs/artifacts")
            job = k.CreateJobObjectW(None, None)
            _check(job)
            limits = ExtendedLimits()
            limits.BasicLimitInformation.LimitFlags = 0x2000 | 0x100 | 0x200 | 0x8
            limits.BasicLimitInformation.ActiveProcessLimit = 4
            limits.ProcessMemoryLimit = limits.JobMemoryLimit = policy.job_memory_mib * MIB
            _check(k.SetInformationJobObject(job, 9, C.byref(limits), C.sizeof(limits)))
            cpu = CPURate(0x1 | 0x4, policy.cpu_percent * 100)  # ENABLE | HARD_CAP
            _check(k.SetInformationJobObject(job, 15, C.byref(cpu), C.sizeof(cpu)))
            _check(k.QueryInformationJobObject(job, 9, C.byref(limits), C.sizeof(limits), None))
            _check(k.QueryInformationJobObject(job, 15, C.byref(cpu), C.sizeof(cpu), None))
            if limits.JobMemoryLimit != policy.job_memory_mib * MIB or cpu.CpuRate != policy.cpu_percent * 100:
                raise GuardRefused("OS did not confirm the requested memory and CPU limits")
            record["os_confirmed_limits"] = {"job_memory_mib": limits.JobMemoryLimit // MIB,
                                             "process_memory_mib": limits.ProcessMemoryLimit // MIB,
                                             "cpu_percent": cpu.CpuRate / 100}
            size = C.c_size_t()
            k.InitializeProcThreadAttributeList(None, 2, 0, C.byref(size))
            attrs = C.create_string_buffer(size.value)
            _check(k.InitializeProcThreadAttributeList(attrs, 2, 0, C.byref(size)))
            job_list = (W.HANDLE * 1)(job)
            _check(k.UpdateProcThreadAttribute(attrs, 0, 0x2000D, job_list,
                                               C.sizeof(job_list), None, None))
            in_path, out_path, err_path = [run_dir / n for n in ("stdin.lean", "stdout.log", "stderr.log")]
            in_path.write_bytes(input_bytes)
            with in_path.open("rb") as fi, out_path.open("wb") as fo, err_path.open("wb") as fe:
                handles = [msvcrt.get_osfhandle(f.fileno()) for f in (fi, fo, fe)]
                for handle in handles:
                    os.set_handle_inheritable(handle, True)
                handle_list = (W.HANDLE * 3)(*handles)
                _check(k.UpdateProcThreadAttribute(attrs, 0, 0x20002, handle_list,
                                                   C.sizeof(handle_list), None, None))
                startup = StartupInfoEx()
                startup.StartupInfo.cb = C.sizeof(startup)
                startup.StartupInfo.dwFlags = 0x100  # STARTF_USESTDHANDLES
                startup.StartupInfo.hStdInput, startup.StartupInfo.hStdOutput, startup.StartupInfo.hStdError = handles
                startup.lpAttributeList = C.cast(attrs, C.c_void_p)
                block = C.create_unicode_buffer("\0".join(f"{key}={val}" for key, val in
                                                sorted(env.items(), key=lambda item: item[0].upper())) + "\0\0")
                command = C.create_unicode_buffer(subprocess.list2cmdline(list(map(str, args))))
                # NO_WINDOW | EXTENDED_STARTUPINFO | UNICODE_ENVIRONMENT | BELOW_NORMAL
                flags = 0x08000000 | 0x00080000 | 0x400 | 0x4000
                try:
                    _check(k.CreateProcessW(str(args[0]), command, None, None, True, flags,
                                           block, str(cwd), C.byref(startup), C.byref(process)))
                finally:
                    for handle in handles:
                        os.set_handle_inheritable(handle, False)
                k.CloseHandle(process.hThread)
                process.hThread = None
                record.update(status="running", child_pid=int(process.dwProcessId),
                              limits_installed_before_start=True)
                record_path.write_text(json.dumps(record, indent=2), encoding="utf-8")
                while True:
                    wait = k.WaitForSingleObject(process.hProcess, int(policy.poll_seconds * 1000))
                    _check(k.QueryInformationJobObject(job, 9, C.byref(limits), C.sizeof(limits), None))
                    record["peak_job_memory_mib"] = round(limits.PeakJobMemoryUsed / MIB, 1)
                    if wait == 0:
                        code = W.DWORD()
                        _check(k.GetExitCodeProcess(process.hProcess, C.byref(code)))
                        rc = int(code.value)
                        record["status"] = "passed" if rc == 0 else "process_failed"
                        break
                    if wait != 0x102:
                        raise RuntimeError(f"unexpected process wait result {wait}")
                    if time.monotonic() - started >= policy.timeout_seconds:
                        reason, rc = "wall-clock timeout", 124
                    elif limits.PeakJobMemoryUsed >= policy.job_memory_mib * MIB * 0.95:
                        reason, rc = "job memory reached 95% of its hard limit", 75
                    elif out_path.stat().st_size + err_path.stat().st_size > policy.maximum_output_mib * MIB:
                        reason, rc = "compiler output exceeded the log limit", 125
                    else:
                        reason = pressure_reason(memory_snapshot(), policy, starting=False)
                        if reason:
                            rc = 75
                    if reason:
                        _check(k.TerminateJobObject(job, rc))
                        k.WaitForSingleObject(process.hProcess, 5000)
                        record["status"] = "stopped_by_guard"
                        break
    except GuardRefused as exc:
        rc, reason, record["status"] = 75, str(exc), "refused"
    except (Exception, KeyboardInterrupt) as exc:
        rc = 130 if isinstance(exc, KeyboardInterrupt) else 127
        reason, record["status"] = f"{type(exc).__name__}: {exc}", "guard_error"
    finally:
        if k:
            if job:
                # Closing the last job handle kills any still-running descendant.
                k.CloseHandle(job)
            if process.hProcess:
                k.WaitForSingleObject(process.hProcess, 5000)
                k.CloseHandle(process.hProcess)
            if process.hThread:
                k.CloseHandle(process.hThread)
            if attrs:
                k.DeleteProcThreadAttributeList(attrs)
        lease.__exit__()
        record.update(returncode=rc, reason=reason,
                      elapsed_seconds=round(time.monotonic() - started, 3))
        try:
            record["memory_after"] = memory_snapshot()
        except Exception as exc:
            record["memory_after_error"] = str(exc)
        record_path.write_text(json.dumps(record, indent=2), encoding="utf-8")
    limit = policy.maximum_output_mib * MIB
    texts = []
    for path in (run_dir / "stdout.log", run_dir / "stderr.log"):
        if path.exists():
            with path.open("rb") as f:
                data = f.read(limit + 1)
            if len(data) > limit:
                rc, record["status"] = 125, "stopped_by_guard"
                reason = "compiler output exceeded the log limit"
                data = data[:limit]
            texts.append(data.decode("utf-8", errors="replace"))
        else:
            texts.append("")
    if reason:
        texts[1] += f"\nRESOURCE GUARD: {reason}. This run is NOT verified.\n"
    record.update(returncode=rc, reason=reason)
    record_path.write_text(json.dumps(record, indent=2), encoding="utf-8")
    result = subprocess.CompletedProcess(args, rc, *texts)
    result.resource_record = record
    result.resource_log = str(record_path)
    return result
