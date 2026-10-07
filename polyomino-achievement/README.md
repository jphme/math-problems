# Achievement numbers of four small polyominoes

In Harary's achievement game for a polyomino two players alternately claim cells of an n x n
board, and the first player tries to own a congruent copy of the polyomino. The board number b is
the side of the smallest square board on which the first player can force this, and the move
number m is the number of the first player's moves needed there. Gardner's tables (1979, 1992,
2001) list (b, m) without proofs; OEIS [A380597](https://oeis.org/A380597) and
[A380598](https://oeis.org/A380598) reproduce the 2001 values. The note proves:

| polyomino | A380597/A380598 index | tabulated (b, m) | weak (Maker-Breaker) game | strong game |
|---|---|---|---|---|
| I-tetromino | 9 | (7, 8) | (6, 6) | b is 6 or 7; first player wins on 7x7 within 7 moves |
| L-pentomino | 13 | (7, 10) | (6, 7) | b is 6 or 7; first player wins on 7x7 within 9 moves |
| Y-pentomino | 14 | (7, 9) | (6, 6) | (6, 6) |
| N-pentomino | 15 | (6, 6) | (5, 6) | (5, 6) |

So the tabulated values (7, 9) of the Y-pentomino and the board number 6 of the N-pentomino are
wrong in both games; for the I-tetromino and the L-pentomino both values are wrong in the weak game
and at least one of each pair is wrong in the strong game. Whether the first player wins the 6x6
strong game for these two shapes is open (no win within 11 and 13 moves, computed).

Every statement is proved by an explicit strategy (a certificate) that short Python checkers verify
exhaustively. Every Breaker certificate and every strong-game strategy is accepted by two
separately written checkers; the weak-game Maker strategies are replayed exhaustively against every
Breaker reply. The search programs that found the strategies are included but not needed for the
proofs.

## Contents

| file | description |
|---|---|
| [`polyomino_achievement.pdf`](polyomino_achievement.pdf) | the note |
| [`polyomino_achievement.tex`](polyomino_achievement.tex) | LaTeX source (article class) |
| [`polyomino_achievement-arxiv.tar.gz`](polyomino_achievement-arxiv.tar.gz) | arXiv source package (the `.tex` and `anc/`) |
| [`anc/`](anc/) | certificates, checkers, both solvers, scripts; see [`anc/README.md`](anc/README.md) |
| [`anc/MANIFEST`](anc/MANIFEST) | SHA-256 of every ancillary file |
| [`anc/LICENSE.txt`](anc/LICENSE.txt) | MIT license for the programs and certificates |

## Verify

```
cd anc
shasum -a 256 -c MANIFEST
bash verify_all.sh
```

Needs [uv](https://docs.astral.sh/uv/) (Python standard library only). The script runs 32 checks in
about one minute and ends with `ALL 32 CHECKS PASSED`. `anc/README.md` lists every command with its
expected output, the certificate formats, the SHA-256 of each certificate, and how to regenerate the
certificates and the computed values with the two solvers (a C++17 compiler is needed for those).

## AI disclosure

The solvers, checkers and scripts and drafts of the note were developed in sessions assisted by
large-language-model coding tools; see the section "Use of AI tools" of the note. The proofs rest on
the lemmas in the note and on certificates that the included checkers verify.
