#!/usr/bin/env bash
# Checks every certificate used by Theorems 4 and 5 of the note: the weak-game certificates and
# the strong-game X strategies with two checkers each, the strong-game O strategies with three.
# Run from this directory:  bash verify_all.sh
# Needs uv (https://docs.astral.sh/uv/), Python >= 3.8 (no third-party packages) and a C++17
# compiler (clang++, or set CXX). Decompresses the weak-game certificates and builds strong/check6b
# in a temporary directory that is removed on exit, so nothing is left inside anc/.
# Peak memory about 2.7 GB (strong/chk.py on i4_b6_full).
set -u
cd "$(dirname "$0")"
TMP="$(mktemp -d "${TMPDIR:-/tmp}/verify_all.XXXXXX")" || exit 1
trap 'rm -rf "$TMP"' EXIT
PY="uv run python"
fail=0; n=0

run() {  # run <pattern that must appear in the output> <command...>
  local pat="$1"; shift
  local out
  out="$("$@" 2>&1)"
  n=$((n + 1))
  if printf '%s\n' "$out" | grep -q -- "$pat"; then
    printf 'ok    %s\n' "$(printf '%s\n' "$out" | grep -- "$pat" | tail -1)"
  else
    fail=$((fail + 1))
    printf 'FAIL  %s\n%s\n' "$*" "$out"
  fi
}

for f in certs/n*.txt.gz; do b="$(basename "$f" .gz)"; gzip -dc "$f" > "$TMP/$b"; done

I4='0,0;1,0;2,0;3,0'
L5='0,0;1,0;0,1;2,0;3,0'
Y5='0,0;1,0;2,0;1,1;3,0'
N5='1,0;0,1;2,0;1,1;3,0'

echo "== weak-game certificates, check_cert.py"
cc() { run '^PASS' $PY check_cert.py "$TMP/$1.txt" --expect-board "$2" --expect-shape "$3" --expect-kind "$4" --expect-budget "$5"; }
cc n9_b5_full   5x5 "$I4" breakerwin -1
cc n9_b6_lt6    6x6 "$I4" breakerwin 5
cc n9_b6_moves  6x6 "$I4" makerwin 6
cc n13_b5_full  5x5 "$L5" breakerwin -1
cc n13_b6_lt7   6x6 "$L5" breakerwin 6
cc n13_b6_moves 6x6 "$L5" makerwin 7
cc n14_b5_full  5x5 "$Y5" breakerwin -1
cc n14_b6_lt6   6x6 "$Y5" breakerwin 5
cc n14_b6_moves 6x6 "$Y5" makerwin 6
cc n15_b4_full  4x4 "$N5" breakerwin -1
cc n15_b5_lt6   5x5 "$N5" breakerwin 5
cc n15_b5_moves 5x5 "$N5" makerwin 6

echo "== Breaker certificates, independent checker fresh_checker/check_breaker2.py"
for f in n9_b5_full n9_b6_lt6 n13_b5_full n13_b6_lt7 n14_b5_full n14_b6_lt6 n15_b4_full n15_b5_lt6; do
  run 'RESULT PASS' bash -c "cd fresh_checker && $PY check_breaker2.py '$TMP/$f.txt'"
done

echo "== Maker certificates, exhaustive concrete replay play_cert.py"
for f in n9_b6_moves n13_b6_moves n14_b6_moves n15_b5_moves; do
  run '^PASS exhaustive' $PY play_cert.py "$TMP/$f.txt" --games 1000 --exhaustive 20000000
done

echo "== strong-game strategies, check_strong.py and fresh_checker/check_strong2.py"
# Each strategy file must state the board, shape and budget of the theorem before it is checked.
hdr() {  # hdr <file> <board> <shape as in the header> <budget>
  local h; h="$(gzip -dc "certs/$1.txt.gz" | sed -n '1,8p')"
  printf '%s\n' "$h" | grep -qx "board $2 $2" && printf '%s\n' "$h" | grep -qx "shape $3" &&
    printf '%s\n' "$h" | grep -qx 'kind strongwin' && printf '%s\n' "$h" | grep -qx "budget $4"
}
strong() {  # strong <file> <board> <shape> <budget>
  run '^PASS strongwin' bash -c "$(declare -f hdr); hdr $1 $2 '$3' $4 || { echo 'header mismatch'; exit 1; }; $PY check_strong.py certs/$1.txt.gz"
  run 'RESULT PASS' bash -c "$(declare -f hdr); hdr $1 $2 '$3' $4 || { echo 'header mismatch'; exit 1; }; cd fresh_checker && $PY check_strong2.py ../certs/$1.txt.gz"
}
strong strong_n15_b5_d6 5 '1,0 0,1 2,0 1,1 3,0' 6
strong strong_n14_b6_d6 6 '0,0 1,0 2,0 1,1 3,0' 6
strong strong_n9_b7_d7  7 '0,0 1,0 2,0 3,0' 7
strong strong_n13_b7_d9 7 '0,0 1,0 0,1 2,0 3,0' 9

echo "== strong-game O strategies, strong/check6.py, strong/check6b and strong/chk.py"
# Built with -fno-vectorize: Apple clang 21 at plain -O2 miscompiles a loop of the strong solver's
# placement generator; the checker is built the same way (see README.md, build note). GCC spells
# the flag -fno-tree-vectorize.
CXX="${CXX:-clang++}"
if "$CXX" --version 2>/dev/null | grep -qi clang; then NOVEC=-fno-vectorize; else NOVEC=-fno-tree-vectorize; fi
"$CXX" -O2 "$NOVEC" -std=c++17 -o "$TMP/check6b" strong/check6b.cpp || { echo "FAIL  cannot build strong/check6b"; exit 1; }
ostrat() {  # ostrat <file> <board> <shape> <budget> <placements>
  local f="certs/$1.txt.gz"
  run "^PASS ostrategy board=$2x$2 shape=$3 budget=$4 placements=$5 " \
    $PY strong/check6.py "$f" --expect-kind ostrategy --expect-board "$2" --expect-shape "$3" --expect-budget "$4" --max-rss-mb 3800
  run "^PASS ostrategy board=$2x$2 .* budget=$4 placements=$5 " \
    bash -c "gzip -dc '$f' | '$TMP/check6b' - --expect-kind ostrategy --expect-board $2 --expect-shape '$3' --expect-budget $4 --expect-placements $5"
  run '^PASS$' $PY strong/chk.py "$f" --kind ostrategy --board "$2" --shape "$3" --budget "$4"
}
ostrat i4_b6_full 6 "$I4" 18 36
ostrat l5_b6_full 6 "$L5" 18 120
ostrat i4_b7_K6   7 "$I4" 6  56
ostrat l5_b7_K8   7 "$L5" 8  192

if [ "$fail" -eq 0 ]; then
  echo "ALL $n CHECKS PASSED"
else
  echo "$fail OF $n CHECKS FAILED"; exit 1
fi
