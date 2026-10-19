"""Run the pinned compiler on exact bytes under mandatory resource safeguards.

ModuleSetup, imports and kernel/trust settings remain unchanged. A failed,
refused, timed-out or interrupted run cannot promote compiler artifacts.
"""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import uuid
from resource_guard import load_policy, run_bounded

LEAN = 'D:/codex/Lean/elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean.exe'
ROOT = Path(__file__).resolve().parent


def run_file(file, *, cwd, env, output=None, module=None):
    cwd = Path(cwd)
    p = Path(file)
    if not p.is_absolute():
        p = cwd / p
    raw = p.read_bytes()
    name = module or p.relative_to(cwd).with_suffix('').as_posix().replace('/', '.')
    policy = load_policy(ROOT / 'resource-policy.json')
    source_hash = hashlib.sha256(raw).hexdigest()
    holds = ROOT / '.lake/resource-control/holds'
    holds.mkdir(parents=True, exist_ok=True)
    hold_path = holds / (hashlib.sha256((name + ':' + source_hash).encode()).hexdigest() + '.json')
    if hold_path.exists():
        hold = json.loads(hold_path.read_text(encoding='utf-8'))
        proc = subprocess.CompletedProcess([], 75, '',
            f'RESOURCE HOLD: unchanged source {name} previously exceeded a resource limit. '
            'No automatic retry and no verification. Inspect the recorded failure and fix the proof.\n')
        proc.source_sha256, proc.lean_module = source_hash, name
        proc.resource_record = {**hold, 'status': 'held', 'returncode': 75, 'artifacts_accepted': False}
        proc.resource_log = str(hold_path)
        return proc
    setups = ROOT / '.lake/compiler-setups'
    setups.mkdir(parents=True, exist_ok=True)
    setup = setups / (uuid.uuid4().hex + '.json')
    setup.write_text(json.dumps({'name': name, 'isModule': False, 'importArts': {},
                                'dynlibs': [], 'plugins': [], 'options': {}}), encoding='utf-8')
    args = [LEAN, '--stdin', '--setup', str(setup),
            f'-M{policy.lean_memory_mb}', f'-j{policy.lean_threads}']
    staged = None
    if output is not None:
        dest = Path(output)
        if not dest.is_absolute():
            dest = cwd / dest
        dest.parent.mkdir(parents=True, exist_ok=True)
        # Lean 4 also writes .olean.private/.server and .ir; stage the entire set.
        staged = dest.parent / ('.guard-' + uuid.uuid4().hex + '.olean')
        args += ['-o', str(staged)]
    args += [str(file)]
    child_env = dict(env)
    child_env['LEAN_NUM_THREADS'] = str(policy.lean_threads)
    proc = run_bounded(args, input_bytes=raw, cwd=cwd, env=child_env,
                       state_dir=ROOT / '.lake/resource-control/runs', policy=policy)
    proc.source_sha256 = source_hash
    proc.lean_module = name
    if p.read_bytes() != raw:
        proc.returncode = 76
        proc.resource_record['status'] = 'source_changed'
        proc.stderr += '\nSource changed during compilation; artifacts not accepted.\n'
    if staged is not None and proc.returncode == 0:
        if not staged.exists():
            proc.returncode = 77
            proc.resource_record['status'] = 'missing_artifact'
            proc.stderr += '\nNo compiled olean was produced; artifacts not accepted.\n'
        else:
            # Publish main olean last, so an interrupted promotion cannot mark a
            # stale/partial output newer than its source for the build cache.
            for suffix in ('.olean.private', '.olean.server', '.ir', '.ir.sig', '.olean'):
                source = Path(str(staged)[:-6] + suffix)
                target = Path(str(dest)[:-6] + suffix)
                if source.exists():
                    os.replace(source, target)
    if staged is not None:
        # Only individually named outputs of this invocation; no recursive delete.
        for suffix in ('.olean', '.olean.private', '.olean.server', '.ir', '.ir.sig'):
            Path(str(staged)[:-6] + suffix).unlink(missing_ok=True)
    setup.unlink(missing_ok=True)
    proc.resource_record.update(returncode=proc.returncode, artifacts_accepted=proc.returncode == 0,
                                module=name, source_sha256=proc.source_sha256)
    Path(proc.resource_log).write_text(json.dumps(proc.resource_record, indent=2), encoding='utf-8')
    text = proc.stdout + proc.stderr
    memory_failure = (proc.returncode != 0 and (
        re.search(r'out of memory|bad_alloc|memory allocation|maximum memory|memory limit', text, re.I)
        or proc.resource_record.get('peak_job_memory_mib', 0) >= policy.job_memory_mib * 0.9))
    if proc.returncode in (124, 125) or memory_failure or proc.resource_record.get('status') == 'stopped_by_guard':
        hold_path.write_text(json.dumps({
            'module': name, 'source_sha256': source_hash, 'resource_log': proc.resource_log,
            'returncode': proc.returncode, 'reason': proc.resource_record.get('reason') or 'memory limit reached',
            'automatic_retry': False}, indent=2), encoding='utf-8')
    return proc
