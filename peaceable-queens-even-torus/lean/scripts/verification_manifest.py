#!/usr/bin/env python3
"""List a local source closure without invoking Lean or reading build artifacts.

Run without arguments to update VERIFICATION_FILES.txt, or with --check to
check it. Use --target and --output for another endpoint. Paths in the
manifest are relative to the Lean project directory.
The existing serial driver's import parser handles comments and detects
missing local modules and cycles. External dependencies are pinned separately.
"""

from __future__ import annotations

import argparse
from pathlib import Path

from build_project_serial import build_order


def source_files(root: Path, target: str = "PeaceableQueens.Main") -> list[str]:
    """The exact local source closure and pinned project configuration."""
    modules = build_order(root, target)
    files = sorted([
        "lakefile.toml", "lake-manifest.json", "lean-toolchain",
        *(name.replace(".", "/") + ".lean" for name in modules),
    ])
    for name in files:
        if not (root / name).is_file():
            raise ValueError(f"missing verification source: {name}")
    return files


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--target", default="PeaceableQueens.Main")
    parser.add_argument("--output", type=Path, default=Path("VERIFICATION_FILES.txt"),
                        help="manifest path relative to the Lean project")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    try:
        files = source_files(root, args.target)
        content = "\n".join(files) + "\n"
        output = root / args.output
        if args.check:
            if output.read_text(encoding="utf-8") != content:
                raise ValueError(f"{args.output} differs from the {args.target} import closure")
        else:
            output.write_text(content, encoding="utf-8")
    except (OSError, ValueError) as error:
        parser.error(str(error))
    size = sum((root / name).stat().st_size for name in files)
    print(f"VERIFICATION_MANIFEST_OK target={args.target} modules={len(files) - 3} "
          f"files={len(files)} bytes={size}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
