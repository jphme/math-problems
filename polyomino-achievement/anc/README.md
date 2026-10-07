# Ancillary files: Achievement numbers of four small polyominoes

Jan Philipp Harries, October 7, 2026.

These files prove Theorems 4 and 5 of the note. Every statement there reduces to an explicit
strategy for one player, stored as a certificate in `certs/`, and checked by short Python programs
that share no code with the search programs. The solvers are included to regenerate the
certificates, to reproduce the computed (uncertified) values of Remark 7 and to rerun the
single-checker comparison of Remark 8; the proofs do not depend on them.

Tested with Python 3.14.6 (via `uv`), Apple clang 21 (C++17), macOS on arm64. The Python programs
use only the standard library. Runtimes below are wall-clock times on that machine.

## Quick check

```
cd anc
shasum -a 256 -c MANIFEST
bash verify_all.sh
```

`verify_all.sh` decompresses the weak-game certificates next to the `.gz` files and runs 32 checks
(about 50 s; peak memory under 0.5 GB). Expected output:

```
== weak-game certificates, check_cert.py
ok    PASS breakerwin board=5x5 shape=4 cells budget=unlimited opening=[] cert_nodes=10130 checked_states=10130
ok    PASS breakerwin board=6x6 shape=4 cells budget=5 opening=[] cert_nodes=2227 checked_states=2227
ok    PASS makerwin board=6x6 shape=4 cells budget=6 opening=[] cert_nodes=2615 checked_states=2615 envelope_cells=32
ok    PASS breakerwin board=5x5 shape=5 cells budget=unlimited opening=[] cert_nodes=321 checked_states=465
ok    PASS breakerwin board=6x6 shape=5 cells budget=6 opening=[] cert_nodes=981 checked_states=1157
ok    PASS makerwin board=6x6 shape=5 cells budget=7 opening=[] cert_nodes=11075 checked_states=11075 envelope_cells=35
ok    PASS breakerwin board=5x5 shape=5 cells budget=unlimited opening=[] cert_nodes=293 checked_states=463
ok    PASS breakerwin board=6x6 shape=5 cells budget=5 opening=[] cert_nodes=213 checked_states=213
ok    PASS makerwin board=6x6 shape=5 cells budget=6 opening=[] cert_nodes=3913 checked_states=3913 envelope_cells=30
ok    PASS breakerwin board=4x4 shape=5 cells budget=unlimited opening=[] cert_nodes=1 checked_states=1
ok    PASS breakerwin board=5x5 shape=5 cells budget=5 opening=[] cert_nodes=84 checked_states=84
ok    PASS makerwin board=5x5 shape=5 cells budget=6 opening=[] cert_nodes=3882 checked_states=3882 envelope_cells=25
== Breaker certificates, independent checker fresh_checker/check_breaker2.py
ok    RESULT PASS {'P_strict': 4676, 'P_relaxed': 0, 'm': 295, 'b': 5159, 'D': 0, 'Z': 0, 'visits': 10130, 'pass': 182}
ok    RESULT PASS {'P_strict': 0, 'P_relaxed': 962, 'm': 37, 'b': 1228, 'D': 0, 'Z': 0, 'visits': 2227}
ok    RESULT PASS {'P_strict': 223, 'P_relaxed': 0, 'm': 10, 'b': 232, 'D': 0, 'Z': 0, 'visits': 465}
ok    RESULT PASS {'P_strict': 148, 'P_relaxed': 414, 'm': 17, 'b': 578, 'D': 0, 'Z': 0, 'visits': 1157}
ok    RESULT PASS {'P_strict': 222, 'P_relaxed': 0, 'm': 10, 'b': 231, 'D': 0, 'Z': 0, 'visits': 463}
ok    RESULT PASS {'P_strict': 0, 'P_relaxed': 100, 'm': 5, 'b': 104, 'D': 4, 'Z': 0, 'visits': 213, 'pass': 4}
ok    RESULT PASS {'P_strict': 1, 'P_relaxed': 0, 'm': 0, 'b': 0, 'D': 0, 'Z': 0, 'visits': 1}
ok    RESULT PASS {'P_strict': 0, 'P_relaxed': 40, 'm': 2, 'b': 41, 'D': 1, 'Z': 0, 'visits': 84, 'pass': 1}
== Maker certificates, exhaustive concrete replay play_cert.py
ok    PASS exhaustive concrete replay: 174766 real states, worst 6 Maker moves
ok    PASS exhaustive concrete replay: 702984 real states, worst 7 Maker moves
ok    PASS exhaustive concrete replay: 288636 real states, worst 6 Maker moves
ok    PASS exhaustive concrete replay: 89274 real states, worst 6 Maker moves
== strong-game strategies, check_strong.py and fresh_checker/check_strong2.py
ok    PASS strongwin board=5x5 shape=5 cells: 253534 X-to-move positions, worst 6 X moves (budget 6)
ok    RESULT PASS positions visited 253534 of 253534 max X moves 6
ok    PASS strongwin board=6x6 shape=5 cells: 1023521 X-to-move positions, worst 6 X moves (budget 6)
ok    RESULT PASS positions visited 1023521 of 1023521 max X moves 6
ok    PASS strongwin board=7x7 shape=4 cells: 333113 X-to-move positions, worst 7 X moves (budget 7)
ok    RESULT PASS positions visited 333113 of 333113 max X moves 7
ok    PASS strongwin board=7x7 shape=5 cells: 948483 X-to-move positions, worst 9 X moves (budget 9)
ok    RESULT PASS positions visited 948483 of 948483 max X moves 9
ALL 32 CHECKS PASSED
```

`check_breaker2.py` counts pairing leaves as `P_strict` (the pairs meet every live placement) or
`P_relaxed` (they meet every placement still completable within Maker's remaining budget, which is
what the proof rule requires; see the note, Section 4).

## Files

| file | role |
|---|---|
| `certs/*.txt.gz` | the 16 certificates of Table 1 (below) |
| `check_cert.py` | checker for weak-game certificates (Breaker and Maker), checker A |
| `play_cert.py` | exhaustive concrete replay of a weak-game Maker certificate against every Breaker reply, checker R |
| `check_strong.py` | exhaustive checker for strong-game strategies, checker S |
| `fresh_checker/check_breaker2.py` | second, separately written checker for Breaker certificates, checker B |
| `fresh_checker/check_strong2.py` | second, separately written checker for strong-game strategies, checker T |
| `fresh_checker/common.py` | placement enumeration of the second checkers |
| `fresh_checker/index_own.py` | regenerates A246521 for sizes 1 to 5 and identifies the indices n = 9, 13, 14, 15 |
| `solver.cpp` | the search program that produced the certificates (weak and strong game, certificate export) |
| `regenerate_weak.sh` | regenerates and checks the 12 weak-game certificates of Table 1 |
| `validate_small.py` | runs the weak-game comparison with A380597/A380598 for n = 1..21 (Remark 8) |
| `split_run.py` | resumable driver for the Snaky 8x8 Breaker certificates (Remark 9) |
| `fresh_solver/ttt.cpp` | second, separately written solver (weak and strong game, no certificates) |
| `fresh_solver/naive.cpp`, `naive_b.cpp` | unpruned minimax and unpruned budgeted search, used to validate `ttt.cpp` |
| `fresh_solver/cmp.sh`, `cmp2.sh` | the validation runs (zsh scripts) |
| `oeis_data/` | the terms of A380597 and A380598 (44 each, from the sequence entries, in b-file format) and the first 60 terms of A246521, read by `validate_small.py` and `index_own.py` |
| `verify_all.sh` | runs every check of Table 1 |
| `LICENSE.txt` | MIT license |
| `MANIFEST` | SHA-256 of every file except itself |

## The certificates

Shapes are given as cell lists `x,y`; cells of a W x W board are numbered `y*W + x`.
I4 = `0,0;1,0;2,0;3,0`, L5 = `0,0;1,0;0,1;2,0;3,0`, Y5 = `0,0;1,0;2,0;1,1;3,0`,
N5 = `1,0;0,1;2,0;1,1;3,0`. The index n is the A380597/A380598 index.

| file | statement | size | SHA-256 of the `.gz` file | SHA-256 of the decompressed file |
|---|---|---|---|---|
| `n9_b5_full.txt.gz` | I4: Breaker wins the full weak game on 5x5 | 10,130 nodes | `61939a5975538fc9fbd08a6a979956906230aacac1562a14674c98d30b41f037` | `cc38861c21b2bd3711537381383ac59206321b8e9c06d04dd2ad061378312582` |
| `n9_b6_moves.txt.gz` | I4: Maker wins on 6x6 within 6 moves | 2,615 nodes | `e39d34ebf0d60d4e54ba8346488be642748804d0e6a9b54c4caa3272a32e035b` | `5c65934640c5cbad707b1feb1cd3d63dd935e16986739cd61be07be461057812` |
| `n9_b6_lt6.txt.gz` | I4: Breaker stops 5 Maker moves on 6x6 | 2,227 nodes | `2f0c0655b5a2c671abed2ce1cef76c0d47b765900811a9dc935a9d2f76ba0e25` | `e36a3e3a61ffb0fee116c467cf556580ec6b3b7afe785a9a6cad8b8e8566d4ed` |
| `strong_n9_b7_d7.txt.gz` | I4: X wins the strong game on 7x7 within 7 moves | 333,113 positions | `b5e5598025f7beb2223f5db75d68dc4d7bdaaef2776a6dc8b65b0c9c60104b36` | `bbf50b945657ff2c228d60f110dd647aee319902a8ad44e66e33c0c5fdc5e203` |
| `n13_b5_full.txt.gz` | L5: Breaker wins the full weak game on 5x5 | 321 nodes | `4ff7bdf469ea4d8e10955c2367f5d0ed449f4dcf5e6c76c1611460249c35131b` | `248932620d6099a233825814fcb37d0f6527cafa96b7dc398b39df6977b9e14c` |
| `n13_b6_moves.txt.gz` | L5: Maker wins on 6x6 within 7 moves | 11,075 nodes | `54194e554936f17b1f9002159cf312750f790e3896ade4d059e6b9c340225d9c` | `f8407fb4c806d576e96b0e441cbf1d0acd29110722a1a74bafc2adea30b6fd24` |
| `n13_b6_lt7.txt.gz` | L5: Breaker stops 6 Maker moves on 6x6 | 981 nodes | `cdae547724372bfde059eaf20c32640b48a8e423bd2b8c524e59ecfe5f629d23` | `3e1f097f8e083328c278b6073dbf011b15c89dcaf1c0797e1a5ddeeba6d5624c` |
| `strong_n13_b7_d9.txt.gz` | L5: X wins the strong game on 7x7 within 9 moves | 948,483 positions | `a69786e9a045c8b0b45f836ea727ba9495f43004de6081a54fb1c22ed2763cb0` | `2e47f41fe062d60a909ffa72a3e517a2eaf28cb5ce4e0798f19102bd45e48e14` |
| `n14_b5_full.txt.gz` | Y5: Breaker wins the full weak game on 5x5 | 293 nodes | `24c8803746942e1aa234cbfadd40542bc6f846487afb4e5170beeaf0bce0bbd7` | `f3862be7122bcbc77307d3d4d55324e32b5e04de1b8845c6367f83f2ce92a2bf` |
| `n14_b6_moves.txt.gz` | Y5: Maker wins on 6x6 within 6 moves | 3,913 nodes | `f9faee7d5aaa627469d035c7d4c62a6917640eb8d7de8f5e592538c2e589dff1` | `b6c5da88ff87d18f6457ec9ec65b1f7be5ccd1b6351323de7f6496e0fd9978e2` |
| `n14_b6_lt6.txt.gz` | Y5: Breaker stops 5 Maker moves on 6x6 | 213 nodes | `d4fc5296b85bf2379f45757040c491f3bb24774d0fd1cc374027437816a0a15f` | `b38fad50d1c26b129267f2de3469b5d943ac8e5e1ca1fb7536d46480548749a5` |
| `strong_n14_b6_d6.txt.gz` | Y5: X wins the strong game on 6x6 within 6 moves | 1,023,521 positions | `e453549ab35254d9d0449c78d5678bd6c80e0d1407bfeff8fa226c84f42f61ce` | `6ba3c3e4f909679f917070497a8c84d86c60c3a01a55f3dde4f092f16e4c1cb2` |
| `n15_b4_full.txt.gz` | N5: Breaker wins the full weak game on 4x4 (one pairing) | 1 node | `8c967c5fd2256ea8d8a35edc142016edbb1509960120bd6267ca9d88c490d4c9` | `be2100aa061f72fdc673c366c576d0fc92d8e066de2a653840239151b4a1c455` |
| `n15_b5_moves.txt.gz` | N5: Maker wins on 5x5 within 6 moves | 3,882 nodes | `4ed4f8a7a90214127eac5b6b4cadf7e84dd5721aafa5803b63216f401de6da27` | `0e4a648fbc02661106c14553b627532cc0fafc8a39d9c4017feadaf69e0d1ab2` |
| `n15_b5_lt6.txt.gz` | N5: Breaker stops 5 Maker moves on 5x5 | 84 nodes | `4bcbf4c395a2af1f02171f868a447ed821c42ce95016c34954d2f8cc6962c096` | `635f49a8f4e0ec152f1a8cfb03d4e7816da4064c896a7f9e98f41f8677b8b9b6` |
| `strong_n15_b5_d6.txt.gz` | N5: X wins the strong game on 5x5 within 6 moves | 253,534 positions | `e9f49ef34ad4fa2762cc3bf006c8016129a9d7cdf26921b64ab456131895184c` | `7011fb18b519782299682f8b047117374ca81296cfd57aab0ecc9a317b432b9b` |

How they combine (note, proof of Theorems 4 and 5): for each shape, the full-game Breaker
certificate on (b-1)x(b-1) gives board number >= b in both games (Lemmas 2(a) and 3); the Maker
certificate gives weak board number <= b and weak move number <= m; the budget Breaker certificate
gives weak move number >= m, and strong move number >= m when the strong board number equals b
(Y5, N5) (Lemma 2(a)); the strong strategy gives the strong upper bounds, and for I4 and L5 the
strategy on 7x7 gives strong board number <= 7.

## Running the checks one by one

`check_cert.py` and `play_cert.py` read uncompressed files; the other checkers read `.gz` directly.

```
for f in certs/n*.txt.gz; do gunzip -k -f "$f"; done
uv run python check_cert.py certs/n9_b5_full.txt --expect-board 5x5 --expect-shape "0,0;1,0;2,0;3,0" --expect-kind breakerwin --expect-budget -1
uv run python play_cert.py certs/n13_b6_moves.txt --games 1000 --exhaustive 20000000
(cd fresh_checker && uv run python check_breaker2.py ../certs/n13_b6_lt7.txt)
uv run python check_strong.py certs/strong_n13_b7_d9.txt.gz                       # 19 s, about 0.4 GB
(cd fresh_checker && uv run python check_strong2.py ../certs/strong_n13_b7_d9.txt.gz)   # 4 s
(cd fresh_checker && uv run python index_own.py)
```

`check_cert.py` options: `--expect-board WxH --expect-shape 'x,y;..' --expect-kind makerwin|breakerwin
--expect-budget N` (-1 = full game), `--max-rss-mb` (default 4000) and `--time-limit SEC`; it prints
`PASS ...`, `FAIL reason` (exit 1) or `ABORT ...` (exit 2, resource cap, no verdict).

`fresh_checker/index_own.py` compares its enumeration with the first 22 terms of A246521 in
`oeis_data/b246521.txt`. Expected output:

```
first terms [0, 1, 3, 7, 11, 15, 23, 27, 30, 75, 31, 47, 62, 79, 91, 94, 143, 181, 182, 188, 406, 1099]
matches saved A246521 data for 22 terms (sizes<=5 part): True len 22
I4 = A246521(10) -> A380597/8 index n=9
L5 = A246521(14) -> A380597/8 index n=13
Y5 = A246521(15) -> A380597/8 index n=14
N5 = A246521(16) -> A380597/8 index n=15
```

## Certificate formats

**Weak game** (`check_cert.py`, `check_breaker2.py`, `play_cert.py`). Header lines `board W H`,
`shape x,y x,y ...`, `kind makerwin|breakerwin`, `budget d` (Maker's moves; -1 = full game),
`opening` (cells played before the root, alternately Maker and Breaker; empty here), `root id`,
`end`; then node lines, each `TYPE id ...`. Lines starting with `#` are comments.

- Breaker certificates:
  - `m id pass c:child c:child ...`: Maker to move. Every free cell that is d-relevant (lies in a
    placement without Breaker cells that misses at most d cells) needs a child; `pass` is `-` or a
    node id, required if some free cell is not d-relevant. The pass child is evaluated at the same
    cells with budget d-1.
  - `b id cell child`: Breaker claims `cell`, which must be free and d-relevant.
  - `P id u1 v1 u2 v2 ...`: pairing leaf at Maker's turn: disjoint pairs of free cells such that
    every placement without Breaker cells that misses at most d cells contains a pair.
  - `D id`: no d-relevant cell left. `Z id`: budget 0.
  - After every Maker move the checker verifies that Maker owns no placement.
- Maker certificates:
  - `M id cell child|WIN`: Maker claims `cell`; `WIN` requires a completed placement.
  - `B id default c:child ...`: Breaker to move; explicit children for some replies, `default` for
    the others (`-` if none). `check_cert.py` accepts the default only for replies outside the
    default subtree's envelope (Maker's cells in it and the cells of the placements completed in
    it). `play_cert.py` does not use this rule: it plays the strategy on the real board against every
    legal reply.

**Strong game** (`check_strong.py`, `check_strong2.py`). Header `board`, `shape`, `kind strongwin`,
`budget d`, `opening` (empty), `end`; then lines `X <X cells> <O cells> <cell>`, the two cell sets as
hexadecimal bitmasks, meaning: in this position (X to move) X claims `cell`. The checkers start from
the empty board, apply X's move, accept if X owns a placement, fail if X's move count reaches the
budget without one or the board is full, and otherwise try every free cell as O's reply, failing if O
owns a placement. Every table entry is reached.

The soundness of the three Breaker rules (pass children, pairing leaves, `D` leaves) is
Proposition 11 of the note.

## The search program `solver.cpp`

```
clang++ -O2 -std=c++17 -o solver solver.cpp
./solver --board N[xM] --shape 'x,y;..' [--game weak|strong] [--dmin a --dmax b | --full] [--cert FILE]
         [--tt-mb MB] [--max-rss-mb MB] [--time-limit SEC] [--no-null] [--pair-budget K --pair-try K --pair-strat K]
```

It answers "does the first player win within d of his own moves?" for d = a..b in increasing order
(stopping at the first win), or for an unlimited budget with `--full`, and prints a final
`DONE maker_wins min_moves=d`, `DONE maker_cannot_win up_to_d=d`, or `ABORT ...`. With `--cert` it
exports a certificate (weak game: both outcomes; strong game: first-player wins only). Search rules,
none of which the checkers trust:

1. Immediate win and double threat (both games); forced block (strong game).
2. Relevance: neither player needs to claim a cell that lies in no placement completable within
   the remaining budget (weak game: Lemma 10 and Proposition 11 of the note; strong game: not proved
   by hand, which is why strong wins are only claimed with an exported strategy that enumerates
   every reply of O).
3. Null-move envelope (weak, Maker-win proofs): if Maker wins after a Breaker pass, every Breaker
   move outside the cells used by that winning subtree also loses.
4. Pairing leaves and pairing-based move restriction for Breaker-win proofs (the `P` rule).
5. Transposition table keyed by the minimum of the 8 Zobrist hashes under the board symmetries
   (64-bit); a collision could make a verdict wrong, which is why verdicts alone are only reported
   as computed.

Regenerating the certificates (the stored ones were exported by an earlier version of the solver,
so regenerated files can differ in size; every regenerated certificate passes the checkers):

```
bash regenerate_weak.sh                      # 12 weak certificates into regen/, each checked; about 2 s
./solver --board 5 --shape "1,0;0,1;2,0;1,1;3,0" --game strong --dmin 6 --dmax 6 --tt-mb 512 --cert s_n15.txt
./solver --board 6 --shape "0,0;1,0;2,0;1,1;3,0" --game strong --dmin 6 --dmax 6 --tt-mb 512 --cert s_n14.txt
./solver --board 7 --shape "0,0;1,0;2,0;3,0" --game strong --dmin 7 --dmax 7 --tt-mb 512 --max-rss-mb 3800 --cert s_n9.txt
./solver --board 7 --shape "0,0;1,0;0,1;2,0;3,0" --game strong --dmin 9 --dmax 9 --tt-mb 2048 --max-rss-mb 3800 --cert s_n13.txt
for f in s_n15 s_n14 s_n9 s_n13; do uv run python check_strong.py $f.txt; done
```

The N5 export takes under a second and gives 65,359 positions (`PASS strongwin board=5x5 shape=5
cells: 65359 X-to-move positions, worst 6 X moves (budget 6)`); the I4 and L5 7x7 exports take about
1 s and 5 s, with peak memory about 0.6 GB and 2.3 GB.

Computed values of Remark 7(i) with this solver (no certificate; L5 needs about 2 GB):

```
./solver --board 7 --shape "0,0;1,0;2,0;3,0" --game strong --dmin 1 --dmax 7 --tt-mb 512             # DONE maker_wins min_moves=7
./solver --board 7 --shape "0,0;1,0;0,1;2,0;3,0" --game strong --dmin 7 --dmax 9 --tt-mb 2048       # DONE maker_wins min_moves=9 (about 1 min)
```

**Remark 8**, the comparison for all A380597/A380598 entries n = 1..21 (sizes up to 5) in the
weak game. `validate_small.py` reads the three files of `oeis_data/` from a directory `oeis_fetch/`
next to its own directory, so run it from a scratch copy:

```
[ -x solver ] || clang++ -O2 -std=c++17 -o solver solver.cpp
cp -R . "$TMPDIR/anc" && cd "$TMPDIR/anc"
mkdir -p ../oeis_fetch results && cp oeis_data/b*.txt ../oeis_fetch/
uv run python validate_small.py --game weak --n 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21 --bmax 8 --time-limit 240
```

It writes certificates to `certs/small/` and one JSON record per entry to
`results/validate_weak.jsonl`, and runs `check_cert.py` on every certificate (about 15 s in total).
Every check passes; the records show `matches_oeis: true` for all n except 9, 13, 14, 15, where it
finds (6,6), (6,7), (6,6), (5,6). For the entries with value 0 it certifies Breaker wins on every
board up to 8x8 only.

**Snaky 8x8 (Remark 9).** One Breaker certificate per class of Maker's first cell (10 classes),
each checked with `check_cert.py`; certificates and records go to `certs/b8_recheck/` and
`results/b8_recheck.jsonl`. About 40 minutes with three processes of up to 3.5 GB each; the largest
class (first cell 3) needs `--tt-mb 2048`. The final line is
`DONE breaker_wins board=8: all 10 first-move classes certified`.

```
uv run python split_run.py --mode breaker --board 8 --tag b8_recheck --max-rss-mb 3500 --tt-mb 2048 --job-hours 1 --jobs 3
```

## The second solver `fresh_solver/ttt.cpp`

Written separately from the rules, without certificates; boards up to 8x8; built-in shapes I3, L3,
I4, L4, T4, S4, O4, L5, Y5, N5, P5.

```
cd fresh_solver
clang++ -O2 -std=c++17 -o ttt ttt.cpp
./ttt <shape> <n> <weak|strong> <K | -K> [timeoutSec] [ttBits]
```

`K` tries budgets 1..K and stops at the first win; `-K` tests budget K only. Output lines
`K=k P1_WINS` or `K=k no_win_within_K`. The table has 2^ttBits entries of 24 bytes (default 25,
about 0.8 GB). Values used in the note (each under 4 s with `300 24`):

| command | last lines |
|---|---|
| `./ttt I4 5 weak -13` | `K=13 no_win_within_K` |
| `./ttt I4 6 weak 7` | `K=5 no_win_within_K`, `K=6 P1_WINS` |
| `./ttt L5 5 weak -13` | `K=13 no_win_within_K` |
| `./ttt L5 6 weak 8` | `K=6 no_win_within_K`, `K=7 P1_WINS` |
| `./ttt Y5 5 weak -13` / `strong -13` | `K=13 no_win_within_K` |
| `./ttt Y5 6 weak 7` / `strong 7` | `K=5 no_win_within_K`, `K=6 P1_WINS` |
| `./ttt N5 4 weak -8` | `K=8 no_win_within_K` |
| `./ttt N5 5 weak 7` / `strong 7` | `K=5 no_win_within_K`, `K=6 P1_WINS` |
| `./ttt I4 7 strong 8` | `K=6 no_win_within_K`, `K=7 P1_WINS` |
| `./ttt L5 7 strong 10` | `K=8 no_win_within_K`, `K=9 P1_WINS` (3 s) |
| `./ttt T4 4 weak -8`, `./ttt L4 3 weak -5` (also `strong`) | `no_win_within_K` |
| `./ttt T4 5 weak 5`, `./ttt L4 4 weak 5`, `./ttt S4 3 weak 6` (also `strong`) | first `P1_WINS` at K = 4, 4, 5 |

A budget equal to the board's capacity (13 on 5x5, 8 on 4x4) is the full game.

6x6 strong game, Remark 7(ii) (about 1.6 GB with ttBits 26):

```
./ttt I4 6 strong -11 600 26     # K=11 no_win_within_K, about 150 s
./ttt L5 6 strong -13 1200 26    # K=13 no_win_within_K, about 880 s
```

Validation against unpruned search (zsh scripts; they call the binary `ttt_new`):

```
clang++ -O2 -std=c++17 -o ttt_new ttt.cpp
clang++ -O2 -std=c++17 -o naive naive.cpp
clang++ -O2 -std=c++17 -o naive_b naive_b.cpp
zsh cmp.sh     # 3x3 and 4x4 boards, 11 shapes, both games: every line has naive=[..] equal to ttt=[..]; about 100 s
zsh cmp2.sh    # 5x5 (and 4x4) boards, budgets 3 to 5, both games: every line has naive=x ttt=x; about 7 s
```
