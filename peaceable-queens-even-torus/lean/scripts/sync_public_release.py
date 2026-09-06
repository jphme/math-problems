#!/usr/bin/env python3
"""Synchronize the peaceable-queens paper and Lean release into the public repository.

Copies, from this working repository into ``<public>/peaceable-queens-even-torus/``:

* the paper source, PDF and submission archive;
* the complete reviewer closure of the Lean project (``REVIEWER_FILES.txt``,
  i.e. the ``PeaceableQueens.Corollaries`` import closure plus the pinned
  project files), the umbrella module, the documentation, the verification
  workflow scripts, the value checker and the verification evidence directory.

Files under the public ``lean/`` directory that are not part of that set are
removed, so the public copy mirrors the release exactly. The ancillary bundle
``anc/`` and the public folder's own ``README.md`` are never touched here.

The script checks both source manifests against the import closure before
copying and verifies every copied file byte for byte afterwards. It does not
run Lean and does not commit; inspect ``git status`` in the public checkout.
"""

from __future__ import annotations

import argparse
import filecmp
from pathlib import Path
import shutil
import sys

from verification_manifest import source_files

LEAN_PREFIX = Path("peaceable_queens/lean")
PAPER_PREFIX = Path("peaceable_queens/paper")
PUBLIC_DIR = Path("peaceable-queens-even-torus")

LEAN_EXTRAS = (
    "PeaceableQueens.lean",
    ".gitignore",
    "README.md",
    "FORMAL_PROOF.md",
    "PAPER_CORRESPONDENCE.md",
    "VERIFICATION.md",
    "FORMAL_PROOF_GUIDE.tex",
    "FORMAL_PROOF_GUIDE.pdf",
    "VERIFICATION_FILES.txt",
    "REVIEWER_FILES.txt",
    "scripts/verification_manifest.py",
    "scripts/build_project_serial.py",
    "scripts/run_with_memory_limit.sh",
    "scripts/AuditUpperBound.lean",
    "scripts/check_upper_bound_axioms.py",
    "scripts/check_paper_values.cpp",
    "scripts/sync_public_release.py",
)
LEAN_EXTRA_DIRS = ("verification",)
PAPER_FILES = (
    "peace_even_torus.tex",
    "peace_even_torus.pdf",
    "peace_even_torus-arxiv.tar.gz",
)


def lean_release_files(project: Path) -> list[str]:
    for target, manifest in (("PeaceableQueens.Main", "VERIFICATION_FILES.txt"),
                             ("PeaceableQueens.Corollaries", "REVIEWER_FILES.txt")):
        expected = "\n".join(source_files(project, target)) + "\n"
        if (project / manifest).read_text(encoding="utf-8") != expected:
            raise ValueError(f"refresh {manifest}: it differs from {target}'s source closure")
    files = list(source_files(project, "PeaceableQueens.Corollaries"))
    files += list(LEAN_EXTRAS)
    for directory in LEAN_EXTRA_DIRS:
        root = project / directory
        if root.is_dir():
            files += sorted(str(p.relative_to(project)) for p in root.rglob("*") if p.is_file())
    missing = [f for f in files if not (project / f).is_file()]
    if missing:
        raise ValueError("missing release inputs: " + ", ".join(missing))
    return sorted(set(files))


def sync(repo: Path, public: Path, dry_run: bool) -> tuple[int, int, int]:
    project = repo / LEAN_PREFIX
    target = public / PUBLIC_DIR
    if not (public / ".git").exists() or not target.is_dir():
        raise ValueError(f"{public} is not the public repository checkout")
    lean_files = lean_release_files(project)
    plan: list[tuple[Path, Path]] = [(project / f, target / "lean" / f) for f in lean_files]
    plan += [(repo / PAPER_PREFIX / f, target / f) for f in PAPER_FILES]
    for source, _ in plan:
        if not source.is_file():
            raise ValueError(f"missing release input: {source}")
    keep = {destination.resolve() for _, destination in plan}
    stale = [p for p in (target / "lean").rglob("*")
             if p.is_file() and p.resolve() not in keep and ".lake" not in p.parts]
    copied = changed = 0
    for source, destination in plan:
        same = destination.is_file() and filecmp.cmp(source, destination, shallow=False)
        if not same:
            changed += 1
            if not dry_run:
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(source, destination)
        copied += 1
    for path in stale:
        if not dry_run:
            path.unlink()
    if not dry_run:
        for path in sorted({p.parent for p in stale}, key=lambda p: -len(p.parts)):
            if path.is_dir() and not any(path.iterdir()):
                path.rmdir()
        for source, destination in plan:
            if not filecmp.cmp(source, destination, shallow=False):
                raise ValueError(f"copy verification failed: {destination}")
    return copied, changed, len(stale)


def main() -> None:
    repo = Path(__file__).resolve().parents[3]
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--public", type=Path, default=Path.home() / "dev2/math_problems",
                        help="checkout of jphme/math-problems")
    parser.add_argument("--dry-run", action="store_true", help="report without writing")
    args = parser.parse_args()
    try:
        copied, changed, removed = sync(repo, args.public.resolve(), args.dry_run)
    except (OSError, ValueError) as error:
        parser.error(str(error))
    mode = "DRY_RUN" if args.dry_run else "SYNCED"
    print(f"PUBLIC_RELEASE_{mode} files={copied} changed={changed} removed_stale={removed} "
          f"target={args.public / PUBLIC_DIR}")


if __name__ == "__main__":
    sys.exit(main())
