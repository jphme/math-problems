#!/usr/bin/env bash
# Regenerates the twelve weak-game certificates of Table 1 with solver.cpp into regen/
# and checks each with check_cert.py. Run from this directory:  bash regenerate_weak.sh
# The solver's flags are those of validate_small.py. Regenerated files can differ from
# the ones in certs/ (solver version); every one must PASS.
set -eu
cd "$(dirname "$0")"
[ -x solver ] || clang++ -O2 -std=c++17 -o solver solver.cpp
mkdir -p regen
BRK="--no-null --pair-budget 300 --pair-try 20 --pair-strat 10"
gen() {  # gen <name> <board> <shape> <maker budget, or full> <kind> <extra flags>
  local name=$1 b=$2 shape=$3 d=$4 kind=$5; shift 5
  local eb=$d; [ "$d" = full ] && eb=-1
  if [ "$d" = full ]; then
    ./solver --board "$b" --shape "$shape" --full --cert "regen/$name.txt" "$@" | grep -E "^(DONE|ABORT)"
  else
    ./solver --board "$b" --shape "$shape" --dmin "$d" --dmax "$d" --cert "regen/$name.txt" "$@" | grep -E "^(DONE|ABORT)"
  fi
  uv run python check_cert.py "regen/$name.txt" --expect-board "${b}x${b}" --expect-shape "$shape" --expect-kind "$kind" --expect-budget "$eb"
}
I4='0,0;1,0;2,0;3,0'; L5='0,0;1,0;0,1;2,0;3,0'; Y5='0,0;1,0;2,0;1,1;3,0'; N5='1,0;0,1;2,0;1,1;3,0'
gen n9_b5_full   5 "$I4" full breakerwin $BRK
gen n9_b6_moves  6 "$I4" 6    makerwin
gen n9_b6_lt6    6 "$I4" 5    breakerwin $BRK
gen n13_b5_full  5 "$L5" full breakerwin $BRK
gen n13_b6_moves 6 "$L5" 7    makerwin
gen n13_b6_lt7   6 "$L5" 6    breakerwin $BRK
gen n14_b5_full  5 "$Y5" full breakerwin $BRK
gen n14_b6_moves 6 "$Y5" 6    makerwin
gen n14_b6_lt6   6 "$Y5" 5    breakerwin $BRK
gen n15_b4_full  4 "$N5" full breakerwin $BRK
gen n15_b5_moves 5 "$N5" 6    makerwin
gen n15_b5_lt6   5 "$N5" 5    breakerwin $BRK
