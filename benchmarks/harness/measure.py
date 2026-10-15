"""Run one benchmark process under a CPU pin, a memory cap, and a wall-clock limit.

The memory cap uses a child memory cgroup when the harness may create one
(cgroup v1 `memory.limit_in_bytes` or v2 `memory.max`), because
garbage-collected runtimes reserve far more virtual memory than they use, which
makes RLIMIT_AS unreliable. Without a writable cgroup the run proceeds without
a memory cap and the record says so.
"""
from dataclasses import dataclass, asdict
import os
from pathlib import Path
import signal
import subprocess
import threading
import time
import uuid


class Cgroup:
    """A temporary child memory cgroup; `create` returns None when unavailable."""

    def __init__(self, path, version):
        self.path, self.version = path, version

    @classmethod
    def create(cls, limit_bytes):
        for line in Path('/proc/self/cgroup').read_text().splitlines():
            hierarchy, controllers, relative = line.split(':', 2)
            if 'memory' in controllers.split(','):
                base, version = Path('/sys/fs/cgroup/memory') / relative.lstrip('/'), 1
                break
        else:
            relative = Path('/proc/self/cgroup').read_text().splitlines()[-1].split(':', 2)[2]
            base, version = Path('/sys/fs/cgroup') / relative.lstrip('/'), 2
        path = base / f'bench-{uuid.uuid4().hex[:12]}'
        try:
            path.mkdir()
        except OSError:
            return None
        group = cls(path, version)
        try:
            if version == 1:
                (path / 'memory.limit_in_bytes').write_text(str(limit_bytes))
                swap = path / 'memory.memsw.limit_in_bytes'
                if swap.exists():
                    swap.write_text(str(limit_bytes))
            else:
                (path / 'memory.max').write_text(str(limit_bytes))
                (path / 'memory.swap.max').write_text('0')
        except OSError:
            group.remove()
            return None
        return group

    def add(self, pid):
        (self.path / 'cgroup.procs').write_text(str(pid))

    def oom_killed(self):
        if self.version == 1:
            fields = dict(line.split() for line in (self.path / 'memory.oom_control').read_text().splitlines())
            if 'oom_kill' in fields:
                return int(fields['oom_kill']) > 0
            return int((self.path / 'memory.failcnt').read_text()) > 0
        events = dict(line.split() for line in (self.path / 'memory.events').read_text().splitlines())
        return int(events.get('oom_kill', 0)) > 0

    def peak_bytes(self):
        name = 'memory.max_usage_in_bytes' if self.version == 1 else 'memory.peak'
        try:
            return int((self.path / name).read_text())
        except OSError:
            return None

    def remove(self):
        for _ in range(50):
            try:
                self.path.rmdir()
                return
            except OSError:
                time.sleep(0.02)


@dataclass
class Process:
    returncode: int | None
    signal: int | None
    wall_s: float
    user_s: float
    system_s: float
    maxrss_kb: int
    timed_out: bool
    oom: bool
    cgroup_peak_kb: int | None
    memory_capped: bool

    def as_dict(self):
        return asdict(self)


def run(cmd, *, cwd, env, timeout_s, memory_bytes, cpu, stdout, stderr):
    """Run `cmd`, pinned to `cpu`, and return its resource use."""
    group = Cgroup.create(memory_bytes) if memory_bytes else None

    def child_setup():
        # Join the cgroup and the CPU set before exec, so every byte is charged.
        if cpu is not None:
            os.sched_setaffinity(0, {cpu})
        if group is not None:
            group.add(os.getpid())

    with open(stdout, 'wb') as out, open(stderr, 'wb') as err:
        start = time.monotonic()
        proc = subprocess.Popen(cmd, cwd=cwd, env=env, stdout=out, stderr=err,
                                preexec_fn=child_setup, start_new_session=True)
        timed_out = threading.Event()

        def kill():
            timed_out.set()
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass

        timer = threading.Timer(timeout_s, kill)
        timer.start()
        _, status, usage = os.wait4(proc.pid, 0)
        wall = time.monotonic() - start
        timer.cancel()
        proc.returncode = os.waitstatus_to_exitcode(status)
        # Reap any helper processes the tool left in its session.
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
    oom = False
    peak = None
    if group is not None:
        oom = group.oom_killed()
        peak = group.peak_bytes()
        group.remove()
    sig = -proc.returncode if proc.returncode < 0 else None
    return Process(
        returncode=proc.returncode if proc.returncode >= 0 else None, signal=sig, wall_s=wall,
        user_s=usage.ru_utime, system_s=usage.ru_stime, maxrss_kb=usage.ru_maxrss,
        timed_out=timed_out.is_set(), oom=oom and not timed_out.is_set(),
        cgroup_peak_kb=peak // 1024 if peak is not None else None, memory_capped=group is not None)
