#!/bin/zsh
run() { name=$1; n=$2; K=$3; shift 3; cells="$@"
  for g in weak strong; do
    a=$(./naive_b $n $g $K ${=cells})
    b=$(./ttt_new $name $n $g -$K 100 22 | tail -1 | sed -E 's/^K=[0-9]+ P1_WINS.*/1/; s/^K=.* no_win.*/0/')
    echo "$name n=$n K=$K $g naive=$a ttt=$b"
  done; }
for K in 3 4; do
run I3 5 $K 0 0 1 0 2 0
run L3 5 $K 0 0 1 0 0 1
run L4 5 $K 0 0 1 0 2 0 2 1
run S4 5 $K 0 0 1 0 1 1 2 1
run T4 5 $K 0 0 1 0 2 0 1 1
run P5 5 $K 0 0 1 0 0 1 1 1 0 2
run I4 5 $K 0 0 1 0 2 0 3 0
run T4 4 $K 0 0 1 0 2 0 1 1
run L4 4 $K 0 0 1 0 2 0 2 1
run S4 4 $K 0 0 1 0 1 1 2 1
done
run N5 5 5 0 0 1 0 2 0 2 1 3 1
run Y5 5 5 0 0 1 0 2 0 3 0 1 1
run I4 5 5 0 0 1 0 2 0 3 0
