#!/bin/zsh
# compare naive vs ttt on tiny boards. args: name cells...
run() { name=$1; n=$2; shift 2; cells="$@"
  for g in weak strong; do
    a=$(./naive $n $g ${=cells} | sed 's/.*: //')
    b=$(./ttt_new $name $n $g -$(( n*n+1 )) 100 22 | tail -1)
    # find minimal K by iterating
    bm=$(./ttt_new $name $n $g $(( (n*n+1)/2 )) 100 22 | grep -E "P1_WINS|no_win" | tail -1 | sed -E 's/^K=([0-9]+) P1_WINS.*/P1 wins in \1/; s/^K=.* no_win.*/no P1 win/')
    echo "$name n=$n $g naive=[$a] ttt=[$bm]"
  done; }
run I3 3 0 0 1 0 2 0
run I3 4 0 0 1 0 2 0
run L3 3 0 0 1 0 0 1
run L3 4 0 0 1 0 0 1
run S4 3 0 0 1 0 1 1 2 1
run S4 4 0 0 1 0 1 1 2 1
run L4 3 0 0 1 0 2 0 2 1
run L4 4 0 0 1 0 2 0 2 1
run T4 4 0 0 1 0 2 0 1 1
run O4 3 0 0 1 0 0 1 1 1
run O4 4 0 0 1 0 0 1 1 1
run I4 4 0 0 1 0 2 0 3 0
run P5 4 0 0 1 0 0 1 1 1 0 2
run Y5 4 0 0 1 0 2 0 3 0 1 1
run N5 4 0 0 1 0 2 0 2 1 3 1
run L5 4 0 0 1 0 2 0 3 0 3 1
