#!/usr/bin/env python3
"""Build local Lean imports dependency-first, one memory-watched Lake call at a time.

Fetch the pinned external dependency cache with `lake exe cache get` first.
This orders local modules only; it cannot serialize missing external packages.
"""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import re
import signal
import subprocess
import sys


MODULE = re.compile(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*")


def imports(path: Path) -> list[str]:
    """Read the import header, without loading large certificate bodies."""
    result: list[str] = []
    depth = 0
    with path.open() as source:
        for line in source:
            clean = []
            i = 0
            while i < len(line):
                if line.startswith("/-", i):
                    depth += 1
                    clean.append(" ")
                    i += 2
                elif depth and line.startswith("-/", i):
                    depth -= 1
                    i += 2
                elif depth:
                    i += 1
                elif line.startswith("--", i):
                    break
                else:
                    clean.append(line[i])
                    i += 1
            tokens = "".join(clean).split()
            if not tokens or tokens == ["prelude"] or tokens == ["module"]:
                continue
            if tokens[0] != "import":
                if "import" in tokens:
                    raise ValueError(f"{path}: unsupported import header")
                break
            if len(tokens) < 2 or any(not MODULE.fullmatch(t) for t in tokens[1:]):
                raise ValueError(f"{path}: malformed import header")
            result.extend(tokens[1:])
    if depth:
        raise ValueError(f"{path}: unterminated header comment")
    return result


def build_order(root: Path, target: str) -> list[str]:
    paths = [root / "PeaceableQueens.lean", *sorted((root / "PeaceableQueens").rglob("*.lean"))]
    modules = {".".join(p.relative_to(root).with_suffix("").parts): p
               for p in paths if p.is_file()}
    finished: set[str] = set()
    active: list[str] = []
    order: list[str] = []

    def visit(name: str) -> None:
        if name in active:
            raise ValueError("local import cycle: " + " -> ".join([*active, name]))
        if name in finished:
            return
        if name not in modules:
            raise ValueError(f"missing local module: {name}")
        active.append(name)
        for dependency in imports(modules[name]):
            if dependency == "PeaceableQueens" or dependency.startswith("PeaceableQueens."):
                visit(dependency)
        active.pop()
        finished.add(name)
        order.append(name)

    visit(target)
    return order


def build(root: Path, order: list[str], log_dir: Path, external: list[str]) -> int:
    log_dir.mkdir(parents=True, exist_ok=True)
    child: subprocess.Popen | None = None
    interrupted = False
    child_signalled = False

    def terminate_current() -> None:
        nonlocal child_signalled
        if child is not None and not child_signalled:
            child_signalled = True
            try:
                # Each job owns a fresh session. Signal the group so that even
                # the watchdog's tiny pre-trap startup window cannot orphan a
                # compiler when cancellation arrives just after it forks.
                os.killpg(child.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass  # The process exited between observing it and sending TERM.

    def stop(signum: int, _frame: object) -> None:
        nonlocal interrupted
        interrupted = True
        # The watchdog also traps TERM and performs descendant cleanup.
        terminate_current()

    previous = {sig: signal.signal(sig, stop) for sig in (signal.SIGINT, signal.SIGTERM)}
    try:
        jobs = []
        if external:
            jobs.append(("external-cache-preflight", ["lake", "--no-build", "--no-cache", "build",
                                                      *[f"+{name}" for name in external]]))
        jobs.extend((name, ["lake", "build", f"+{name}"]) for name in order)
        for number, (name, command) in enumerate(jobs, 1):
            if interrupted:
                return 130
            log = log_dir / f"{name}.log"
            print(f"SERIAL_BUILD {number}/{len(jobs)} START {name}", flush=True)
            child_signalled = False
            with log.open("w") as output:
                child = subprocess.Popen(
                    [str(root / "scripts/run_with_memory_limit.sh"), *command],
                    cwd=root, stdout=output, stderr=subprocess.STDOUT, start_new_session=True,
                )
                # A signal arriving during Popen must not leave a newly spawned job running.
                if interrupted:
                    terminate_current()
                status = child.wait()
                child = None
            if interrupted:
                return 130
            if status:
                print(f"SERIAL_BUILD FAILED {name}; inspect {log}", file=sys.stderr)
                if name == "external-cache-preflight":
                    print("Fetch the pinned external cache with `lake exe cache get` first.", file=sys.stderr)
                return status if status > 0 else 128 - status
            print(f"SERIAL_BUILD OK {name}; log={log}", flush=True)
    finally:
        for sig, handler in previous.items():
            signal.signal(sig, handler)
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plan", action="store_true", help="print ordered modules without building")
    parser.add_argument("--target", default="PeaceableQueens", help="local module and its dependencies")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    try:
        order = build_order(root, args.target)
    except ValueError as error:
        parser.error(str(error))
    if args.plan:
        print("\n".join(order))
        return 0
    external = sorted({dependency for name in order
                       for dependency in imports(root / (name.replace(".", "/") + ".lean"))
                       if dependency != "PeaceableQueens" and not dependency.startswith("PeaceableQueens.")})
    return build(root, order, root / ".lake/serial-project-logs", external)


if __name__ == "__main__":
    sys.exit(main())
