# Achievement numbers of four small polyominoes

In Harary's achievement game for a polyomino two players alternately claim cells of an n x n
board, and the first player tries to own a congruent copy of the polyomino. The board number b is
the side of the smallest square board on which the first player can force this, and the move
number m is the number of the first player's moves needed there. Gardner's tables (1979, 1992,
2001) list (b, m) without proofs; OEIS [A380597](https://oeis.org/A380597) and
[A380598](https://oeis.org/A380598) reproduce the 2001 values. The note proves:

| polyomino | A380597/A380598 index | tabulated (b, m) | weak (Maker-Breaker) game | strong game |
|---|---|---|---|---|
| I-tetromino | 9 | (7, 8) | (6, 6) | (7, 7) |
| L-pentomino | 13 | (7, 10) | (6, 7) | (7, 9) |
| Y-pentomino | 14 | (7, 9) | (6, 6) | (6, 6) |
| N-pentomino | 15 | (6, 6) | (5, 6) | (5, 6) |

So the tabulated values (7, 9) of the Y-pentomino and the board number 6 of the N-pentomino are
wrong in both games. For the I-tetromino and the L-pentomino both values are wrong in the weak game;
in the strong game the board number 7 is correct and the move numbers 8 and 10 are wrong (they are
7 and 9). In the strong game the first player does not win these two shapes on 6x6, so Gardner's
1979 board number 6 holds for them only in the weak game, and the statement of the A380597 example line that the I-tetromino game "is a draw for square
boards of side length less than 7" is true in the strong game and false in the weak game.

Every statement is proved by an explicit strategy (a certificate) that short checkers verify
exhaustively. Every Breaker certificate and every strategy of the first player in the strong game
is accepted by two separately written checkers, and every strategy of the second player in the
strong game (the 6x6 games and the 7x7 lower bounds for the I-tetromino and the L-pentomino) by
three; the weak-game Maker strategies are replayed exhaustively against every Breaker reply. The
search programs that found the strategies are included but not needed for the proofs.

## Contents

| file | description |
|---|---|
| [`polyomino_achievement.pdf`](polyomino_achievement.pdf) | the note |
| [`polyomino_achievement.tex`](polyomino_achievement.tex) | LaTeX source (article class) |
| [`polyomino_achievement-arxiv.tar.gz`](polyomino_achievement-arxiv.tar.gz) | arXiv source package (the `.tex` and `anc/`) |
| [`anc/`](anc/) | certificates, checkers, the three solvers, scripts; see [`anc/README.md`](anc/README.md) |
| [`anc/MANIFEST`](anc/MANIFEST) | SHA-256 of every ancillary file |
| [`anc/LICENSE.txt`](anc/LICENSE.txt) | MIT license for the programs and certificates |

## Verify

```
cd anc
shasum -a 256 -c MANIFEST
bash verify_all.sh
```

Needs [uv](https://docs.astral.sh/uv/) (Python standard library only) and a C++17 compiler for one
of the checkers (built with `-O2 -fno-vectorize`, see the build note in `anc/README.md`). The script
runs 44 checks in about 4 minutes, with peak memory 2.7 GB, and ends with
`ALL 44 CHECKS PASSED`. `anc/README.md` lists every command with its expected output, the
certificate formats, the SHA-256 of each certificate, and how to regenerate the certificates and
the computed values with the three solvers.

## Build

```
tectonic polyomino_achievement.tex
COPYFILE_DISABLE=1 tar --no-xattrs --exclude='.DS_Store' --exclude='__pycache__' \
  -czf polyomino_achievement-arxiv.tar.gz polyomino_achievement.tex anc
```

Run the second command after `anc/` has been cleaned (no `certs/n*.txt` or `strong/check6b`).
The tarball has the `.tex` at top level and `anc/` as a directory; `shasum -a 256 -c MANIFEST`
inside the unpacked `anc/` passes.

## AI disclosure

The solvers, checkers and scripts and drafts of the note were developed in sessions assisted by
large-language-model coding tools; see the section "Use of AI tools" of the note. The proofs rest on
the lemmas in the note and on certificates that the included checkers verify.
