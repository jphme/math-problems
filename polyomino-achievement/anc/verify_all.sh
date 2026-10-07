#!/usr/bin/env bash
# Checks every certificate used by Theorems 4 and 5 of the note with both checkers.
# Run from this directory:  bash verify_all.sh
# Needs uv (https://docs.astral.sh/uv/) and Python >= 3.8; no third-party packages.
# Decompresses the weak-game certificates next to the .gz files (gunzip -k).
set -u
cd "$(dirname "$0")"
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

for f in certs/n*.txt.gz; do gunzip -k -f "$f"; done

I4='0,0;1,0;2,0;3,0'
L5='0,0;1,0;0,1;2,0;3,0'
Y5='0,0;1,0;2,0;1,1;3,0'
N5='1,0;0,1;2,0;1,1;3,0'

echo "== weak-game certificates, check_cert.py"
cc() { run '^PASS' $PY check_cert.py "certs/$1.txt" --expect-board "$2" --expect-shape "$3" --expect-kind "$4" --expect-budget "$5"; }
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
  run 'RESULT PASS' bash -c "cd fresh_checker && $PY check_breaker2.py ../certs/$f.txt"
done

echo "== Maker certificates, exhaustive concrete replay play_cert.py"
for f in n9_b6_moves n13_b6_moves n14_b6_moves n15_b5_moves; do
  run '^PASS exhaustive' $PY play_cert.py "certs/$f.txt" --games 1000 --exhaustive 20000000
done

echo "== strong-game strategies, check_strong.py and fresh_checker/check_strong2.py"
# Each strategy file must state the board, shape and budget of the theorem before it is checked.
hdr() {  # hdr <file> <board> <shape as in the header> <budget>
  gzip -dc "certs/$1.txt.gz" | sed -n '1,8p' > "$1.hdr"
  grep -qx "board $2 $2" "$1.hdr" && grep -qx "shape $3" "$1.hdr" && grep -qx 'kind strongwin' "$1.hdr" && grep -qx "budget $4" "$1.hdr"
  local r=$?; rm -f "$1.hdr"; return $r
}
strong() {  # strong <file> <board> <shape> <budget>
  run '^PASS strongwin' bash -c "$(declare -f hdr); hdr $1 $2 '$3' $4 || { echo 'header mismatch'; exit 1; }; $PY check_strong.py certs/$1.txt.gz"
  run 'RESULT PASS' bash -c "$(declare -f hdr); hdr $1 $2 '$3' $4 || { echo 'header mismatch'; exit 1; }; cd fresh_checker && $PY check_strong2.py ../certs/$1.txt.gz"
}
strong strong_n15_b5_d6 5 '1,0 0,1 2,0 1,1 3,0' 6
strong strong_n14_b6_d6 6 '0,0 1,0 2,0 1,1 3,0' 6
strong strong_n9_b7_d7  7 '0,0 1,0 2,0 3,0' 7
strong strong_n13_b7_d9 7 '0,0 1,0 0,1 2,0 3,0' 9

if [ "$fail" -eq 0 ]; then
  echo "ALL $n CHECKS PASSED"
else
  echo "$fail OF $n CHECKS FAILED"; exit 1
fi
