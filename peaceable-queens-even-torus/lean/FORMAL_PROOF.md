# A formalization-ready proof of $t(2q) = H(2q)$

This document rewrites the proof of the main theorem ("Theorem 1" below) of *Peaceable
queens on even tori: an exact parity formula* (`paper/peace_even_torus.tex`, July 27
2026; OEIS A279405) as a dependency-ordered sequence of self-contained formal statements
S1–S66. Paper results are cited by their stable LaTeX labels (e.g. `lem:lines`) rather
than by printed numbers. It is the
specification against which the companion Lean 4 / Mathlib development in this directory
(`PeaceableQueens/`) is written, and it delimits exactly what remains beyond that
development.

Every statement carries one of four tags:

| tag | meaning |
|---|---|
| `[LEAN]` | formalized in the companion Lean development (names given per statement) |
| `[CERT]` | reduces to a finite certified object; the object's data and the exact per-record check a verifier must perform are specified in the statement |
| `[ALG]` | pen-and-paper algebra over $\mathbb{Q}$ (occasionally $\sqrt3$, always reducible to integer comparisons); each step is sized to be one Lean lemma |
| `[COMP]` | exhaustive finite search, off the even theorem's critical path except for five small even orders (which the Lean development can instead decide directly; see §11) |

Numerical conventions: $n$ is the board order, $n = 2q$ throughout the even theorem;
$\kappa = 4-2\sqrt3$, $s = \sqrt3-1$ (so $\kappa = s^2$), $\gamma = 1 - 1/\sqrt3$.


## §0 Formal objects

The Lean development fixes the following objects (namespace `PeaceableQueens`); everything
later is stated against them.

* **Board.** For `n : ℕ`, the board is `(ZMod n) × (ZMod n)`; a *cell* is a pair
  $(r,c)$. All four line families wrap: through $(r,c)$ pass row $r$, column $c$,
  diagonal $d = r-c$ and antidiagonal $a = r+c$, each family indexed by `ZMod n`.
* **`SharesLine (p q : (ZMod n) × (ZMod n)) : Prop`** —
  $p_1 = q_1 \lor p_2 = q_2 \lor p_1 - p_2 = q_1 - q_2 \lor p_1 + p_2 = q_1 + q_2$.
  Two queens attack exactly when they share a line. `SharesLine` is reflexive
  (equal cells share a row: $p_1 = p_1$); this makes black/white disjointness automatic
  in S3 rather than a separate hypothesis.
* **`IsPeaceable (B W : Finset ((ZMod n) × (ZMod n))) : Prop`** —
  $\forall b \in B,\ \forall w \in W,\ \lnot\,\mathrm{SharesLine}\ b\ w$.
  Attacks within one army are allowed, exactly as in A279405.
* **`HasPeaceable (n m : ℕ) : Prop`** — $\exists B\,W$, `IsPeaceable B W` and
  $|B| = |W| = m$.
* **`t (n : ℕ) : ℕ := Nat.findGreatest (HasPeaceable n) (n^2)`** — the toroidal
  peaceable-queens maximum. The cap $n^2$ is legitimate because any army is a set of
  cells (S5); `findGreatest` makes `t` a total function (defined with classical
  decidability; it becomes *computable* through S11). Only $n = 2q \ge 2$
  is referred to by Theorem 1.
* **`H (q : ℕ) : ℕ`** — the parity formula
  $$H(q) := \max_{(r_0,r_1,c_0,c_1)\in\{0,\dots,q\}^4}
    \min\bigl(r_0c_1 + r_1c_0,\ (q-r_0)(q-c_0) + (q-r_1)(q-c_1)\bigr),$$
  implemented as a `Finset.sup` over `(Finset.range (q+1))^4`. **Indexing convention:**
  Lean's `H q` is the paper's $H(2q)$; the main theorem reads `t (2*q) = H q`.
  The subtraction is ℕ-subtraction; this is harmless because every argument satisfies
  $r_i, c_i \le q$ (they range over `Finset.range (q+1)`), where truncated and integer
  subtraction agree.
* **`blackCells`, `whiteCells`** — for `R C D A : Finset (ZMod n)`,
  `blackCells R C D A` is the filter of the universal cell set by
  $r \in R \land c \in C \land r-c \in D \land r+c \in A$, and
  `whiteCells R C D A = blackCells Rᶜ Cᶜ Dᶜ Aᶜ` (complements family by family).
* **`lineMax (n : ℕ) : ℕ`** — the line-colouring optimum
  $\max_{R,C,D,A} \min(|\mathrm{blackCells}|, |\mathrm{whiteCells}|)$, a `Finset.sup`
  over all $(2^n)^4$ quadruples; decidable, and evaluated by `decide`/`native_decide`
  for small $n$.

The global proof structure is: `t = lineMax` (S11), the parity construction gives
`H q ≤ t (2q)` for all $q$ (S14), and three regimes give `t (2q) ≤ H q`:
$q \ge 130$ (S55, algebra on top of the two branch certificates and two support cuts),
$q \in \{3,5\} \cup \{10,\dots,129\}$ (S59, the cut-envelope ladder), and
$q \in \{1,2,4,6,7,8,9\}$ (S60, S61, S64).


## §1 The line-colouring reduction

**S1 (Definition: `SharesLine`).** `[LEAN]`
As in §0. One Lean lemma each: reflexivity, symmetry.

**S2 (Definition: `IsPeaceable`).** `[LEAN]`
As in §0.

**S3 (Disjointness is automatic).** `[LEAN]`
If `IsPeaceable B W` and $B \cap W \ne \emptyset$, then a common cell $p$ gives
`SharesLine p p` by reflexivity of S1, contradicting S2. Hence
`IsPeaceable B W → Disjoint B W`.

**S4 (Definition: `HasPeaceable`).** `[LEAN]`
As in §0.

**S5 (Elementary facts about `HasPeaceable`).** `[LEAN]`
(a) `HasPeaceable n 0` (take $B = W = \emptyset$; S2 is vacuous).
(b) For $n \ge 1$: if `HasPeaceable n m` then $m \le n^2$ (the board is finite and an
army is a `Finset` of cells, so $m = |B| \le n^2$; for $n = 0$ the type `ZMod 0` is
$\mathbb{Z}$ and the bound is vacuously irrelevant — no statement below touches
$n = 0$).
(c) If `HasPeaceable n m` and $m' \le m$ then `HasPeaceable n m'` (pass to subsets of
size $m'$ of both armies; S2 is monotone under shrinking).

**S6 (Definition: `t`).** `[LEAN]`
As in §0, `t n = Nat.findGreatest (HasPeaceable n) (n^2)`.

**S7 (Characterization of `t`).** `[LEAN]`
For all $n \ge 1$ and all $m$: `HasPeaceable n m ↔ m ≤ t n`. Forward: S5(b) and
`Nat.le_findGreatest`. Backward: `Nat.findGreatest_spec` (using S5(a) for $t\,n = 0$)
and S5(c). Hence `t n` is the true maximum army size.

**S8 (Definitions: `blackCells`, `whiteCells`).** `[LEAN]`
As in §0. One lemma: membership unfolding; one lemma:
`whiteCells R C D A = blackCells Rᶜ Cᶜ Dᶜ Aᶜ` (definitional).

**S9 (Line-colouring equivalence — paper `lem:lines`).** `[LEAN name: hasPeaceable_iff_lineSets]`
For all $n \ge 1$ and all $m$:
`HasPeaceable n m ↔ ∃ R C D A, m ≤ |blackCells R C D A| ∧ m ≤ |whiteCells R C D A|`.

*Proof obligations.*
(⇒) Given peaceable armies $B, W$ with $|B| = |W| = m$, let $R$ = rows carrying a black
queen, similarly $C, D, A$. No line carries queens of both colours (two such queens
would share a line, contradicting S2), so every white queen's four lines lie in the
complements. Hence $B \subseteq \mathrm{blackCells}\ R\,C\,D\,A$ and
$W \subseteq \mathrm{whiteCells}\ R\,C\,D\,A$, giving both cardinality bounds.
(⇐) Choose any $m$-subsets $B \subseteq \mathrm{blackCells}$,
$W \subseteq \mathrm{whiteCells}$. They are peaceable: a black–white shared line would
be an element of one of $R, C, D, A$ and simultaneously of its complement. (For $m = 0$
both sides hold trivially.)

**S10 (Definition: `lineMax`).** `[LEAN]`
As in §0.

**S11 (The queens disappear — `t_eq_lineMax`).** `[LEAN]`
For all $n \ge 1$: `t n = lineMax n`. From S7 and S9; the bound
$\min(|\mathrm{blackCells}|,|\mathrm{whiteCells}|) \le n^2$ keeps everything inside the
`findGreatest` cap. From here on, no statement mentions queens; a *configuration* is a
quadruple $(R,C,D,A)$ with $B := |\mathrm{blackCells}|$, $W := |\mathrm{whiteCells}|$.


## §2 The formula and the lower bound

**S12 (Definition: `H`).** `[LEAN]`
As in §0 (Lean `H q` = paper $H(2q)$).

**S13 (Parity-separated construction — paper `prop:lower`, counting part).** `[LEAN]`
Let $q \ge 1$, $n = 2q$, and $0 \le r_0, r_1, c_0, c_1 \le q$. Choose
$R \subseteq \mathbb{Z}/2q\mathbb{Z}$ consisting of any $r_0$ even and $r_1$ odd labels,
$C$ of any $c_0$ even and $c_1$ odd labels, and $D = A = \{\text{odd labels}\}$. Then
$$|\mathrm{blackCells}| = r_0c_1 + r_1c_0, \qquad
  |\mathrm{whiteCells}| = (q-r_0)(q-c_0) + (q-r_1)(q-c_1).$$
*Reason (one line each):* a cell $(r,c)$ is black-homogeneous iff $r \in R$, $c \in C$
and both $r-c$, $r+c$ are odd, i.e. iff $r \in R$, $c \in C$ and $r, c$ have opposite
parities; it is white-homogeneous iff $r \notin R$, $c \notin C$ and $r + c$ is even,
i.e. $r, c$ of equal parity. Counting by parity classes (each class has exactly $q$
labels) gives the two products of counts.

**S14 (Lower bound — `H_le_t`).** `[LEAN]`
For every $q \ge 1$: `H q ≤ t (2*q)`. From S13, S9 and S7, maximizing over the four
counts. **This half of Theorem 1 is fully formalized for all $q$.**

**S15 (Values of $H$ — paper Table 1).** `[LEAN]`
Machine-checked value lemmas (finite evaluation of S12), Lean `H q` for
$q = 1,\dots,20$, i.e. paper $H(n)$ for even $n = 2,\dots,40$:

| $n$ | 2 | 4 | 6 | 8 | 10 | 12 | 14 | 16 | 18 | 20 |
|---|---|---|---|---|---|---|---|---|---|---|
| $H(n)$ | 0 | 2 | 4 | 8 | 12 | 18 | 25 | 32 | 42 | 51 |

| $n$ | 22 | 24 | 26 | 28 | 30 | 32 | 34 | 36 | 38 | 40 |
|---|---|---|---|---|---|---|---|---|---|---|
| $H(n)$ | 64 | 74 | 90 | 101 | 120 | 133 | 153 | 170 | 190 | 210 |


## §3 Continuous estimates on $H$ and the escape margin

These are real/rational inequalities about the *formula* $H$ only; no configurations.
All $\sqrt3$ comparisons reduce to integer comparisons stated explicitly.

**S16 (Algebraic identities — paper `eq:XYid`).** `[ALG]`
Let $q > 0$ and $r_0, r_1, c_0, c_1 \in [0,q]$ be real. Put
$X = r_0c_1 + r_1c_0$, $Y = (q-r_0)(q-c_0) + (q-r_1)(q-c_1)$, and (normalized)
$\rho = (r_0+r_1)/q$, $\chi = (c_0+c_1)/q$, $\xi = 1-\rho$, $\eta = 1-\chi$,
$z = \frac{(r_0-r_1)(c_0-c_1)}{q^2}$. Then
$$\frac{X-Y}{q^2} = \rho + \chi - 2 - z, \qquad
  \frac{X+Y}{q^2} = 2 - \rho - \chi + \rho\chi = 1 + \xi\eta,$$
and $|z| \le \rho\chi$ (since $|r_0-r_1| \le r_0+r_1$ and likewise for the columns).
Each identity is a ring computation; one Lean lemma each.

**S17 (Continuous upper bound — paper `lem:Hupper`).** `[ALG]`
With the notation of S16, $\min(X,Y) \le \kappa q^2$ where $\kappa = 4-2\sqrt3$.
Sub-lemmas, each one Lean step:
(a) if $\xi\eta \le 0$ then $\min(X,Y) \le (X+Y)/2 \le q^2/2 < \kappa q^2$
    (the last since $\kappa > 1/2$, i.e. $7 > 4\sqrt3$, i.e. $49 > 48$);
(b) the domain map $(r_0,r_1,c_0,c_1) \mapsto (q-r_0, q-r_1, q-c_1, q-c_0)$ exchanges
    $X$ and $Y$ and sends $(\xi,\eta)$ to $(-\xi,-\eta)$, so assume $\xi,\eta \ge 0$;
(c) if $X \ge Y$: from S16, $z \le \rho+\chi-2$ and $z \ge -\rho\chi$ give
    $2\xi + 2\eta - \xi\eta \le 1$; with $w = \sqrt{\xi\eta} \in [0,1]$, AM–GM gives
    $4w - w^2 \le 1$, hence $w \le 2-\sqrt3$, hence
    $\min(X,Y) \le (X+Y)/2 = q^2(1+w^2)/2 \le q^2(1+(2-\sqrt3)^2)/2 = \kappa q^2$;
(d) if $Y \ge X$ and $X > \kappa q^2$: then $\xi\eta > 2\kappa-1 = (2-\sqrt3)^2$, so
    $w > 2-\sqrt3$; but $X/q^2$ is bilinear with fixed sums $\rho,\chi$, hence
    $X/q^2 \le \rho\chi = (1-\xi)(1-\eta) \le (1-w)^2 < (\sqrt3-1)^2 = \kappa$,
    a contradiction.

**S18 (Integer consequence).** `[ALG]`
For every $q \ge 1$: $H(2q) \le \lfloor \kappa q^2 \rfloor$
($H$ is an integer maximum of $\min(X,Y)$ over integer points of the S17 domain).

**S19 (Continuous lower bound — paper `lem:Hlower`).** `[ALG]`
For every $q \ge 1$: $H(2q) \ge \kappa q^2 - \gamma q - \tfrac14$, where
$\gamma = 1 - 1/\sqrt3 = s/(1+s)$. Sub-lemmas:
(a) for integer $0 \le P \le 2q$, the profile
    $(0, \lfloor P/2 \rfloor, \lceil P/2 \rceil, 0)$ has
    $X = \lfloor P^2/4 \rfloor$ and $Y = 2q^2 - qP$, so
    $H(2q) \ge \min(\lfloor P^2/4 \rfloor,\ 2q^2 - qP)$;
(b) writing $2sq = m + \theta$, $m = \lfloor 2sq \rfloor$, $\theta \in [0,1)$:
    $P = m$ gives value $\ge \kappa q^2 - sq\theta - \tfrac14$, and $P = m+1$ gives
    value $\ge \kappa q^2 - q(1-\theta) - \tfrac14$;
(c) $\max_{0 \le \theta < 1} \min(s\theta, 1-\theta) = s/(1+s) = \gamma$, attained at
    $s\theta = 1-\theta$.

**S20 (Escape comparison — paper `lem:escape`).** `[ALG]`
(a) $\kappa - \tfrac{527}{1000} > \tfrac{1}{125}$; equivalently $693 > 400\sqrt3$;
    equivalently the integer comparison $480249 > 480000$.
(b) $\gamma < \tfrac12$; equivalently $2 > \sqrt3$; equivalently $4 > 3$.
(c) For every $q \ge 64$:
    $H(2q) - \tfrac{527}{1000} q^2 > \tfrac{q^2}{125} - \tfrac{q}{2} - \tfrac14 > 0$
    (first inequality from S19 + (a) + (b); second from
    $q(\tfrac{64}{125} - \tfrac12) - \tfrac14 = \tfrac{3q}{250} - \tfrac14 \ge
     \tfrac{192}{250} - \tfrac14 > 0$).


## §4 Configurations, parity counts, and the 42-equation moment system

From here through §9, $n = 2q$.

**S21 (Definition: outer counts and profile).** `[ALG]`
Fix a configuration $(R,C,D,A)$ on the $2q$-torus with $B = |\mathrm{blackCells}|$,
$W = |\mathrm{whiteCells}|$. For $i \in \{0,1\}$ let
$r_i = \#\{\rho \in R : \rho \equiv i \pmod 2\}$, likewise $c_i, d_i, a_i$. Each parity
class of $\mathbb{Z}/2q\mathbb{Z}$ has exactly $q$ labels, so all eight counts lie in
$\{0,\dots,q\}$. The *normalized profile* is
$x = (r_0, r_1, c_0, c_1, d_0, d_1, a_0, a_1)/q \in [0,1]^8$ (this coordinate order is
fixed for all certificates below).

**S22 (Incidence — paper `lem:inc`).** `[ALG]`
Let $\ell, \ell'$ be lines of two distinct families on the $n$-torus.
(a) Unless $\{\ell,\ell'\}$ is a diagonal–antidiagonal pair, they meet in exactly one
cell (explicit inverse maps: row $r$ / column $c$ meet at $(r,c)$; row $r$ / diagonal
$d$ at $(r, r-d)$; etc.).
(b) A diagonal $d$ and antidiagonal $a$ meet in the fibre $\varphi^{-1}(d,a)$ of
$\varphi(r,c) = (r-c, r+c)$; $\ker\varphi = \{(r,r) : 2r = 0\}$ has order 1 for odd
$n$ and order 2 for even $n$ (generated by $(n/2, n/2)$). For even $n$, the fibre has
two cells, differing by $(n/2,n/2)$, when $d \equiv a \pmod 2$, and is empty otherwise
(image size count: $n^2/2$ nonempty fibres, and exactly $n^2/2$ equal-parity pairs).

**S23 (Budget — paper `lem:budget`).** `[ALG]`
Complementing all four line sets exchanges $B$ and $W$ (by S8) and replaces
$|R|+|C|+|D|+|A|$ by $4n$ minus it. Hence if some configuration has
$\min(B,W) \ge m$, one with $|R|+|C|+|D|+|A| \le 2n$ does too.

**S24 (Block marginals).** `[ALG]`
Partition the board into four blocks $G_{ij} = \{(r,c) : r \equiv i,\ c \equiv j
\pmod 2\}$, each of $q^2$ cells; inside $G_{ij}$ every cell has square parity
$e = i \oplus j$, so its diagonal and antidiagonal labels both have parity $e$.
Define, for each block and each atom $\varepsilon = (\varepsilon_R, \varepsilon_C,
\varepsilon_D, \varepsilon_A) \in \{0,1\}^4$,
$$p_{ij}(\varepsilon) = q^{-2}\,\#\{(r,c) \in G_{ij} : [r \in R] = \varepsilon_R,\
  [c \in C] = \varepsilon_C,\ [r-c \in D] = \varepsilon_D,\ [r+c \in A] =
  \varepsilon_A\},$$
and write $E_{ij}[\cdot]$ for the corresponding expectation. Then
$\sum_\varepsilon p_{ij}(\varepsilon) = 1$ and
$$E_{ij}[\varepsilon_R] = \tfrac{r_i}{q},\quad E_{ij}[\varepsilon_C] = \tfrac{c_j}{q},
  \quad E_{ij}[\varepsilon_D] = \tfrac{d_e}{q},\quad
  E_{ij}[\varepsilon_A] = \tfrac{a_e}{q}.$$
*Reason:* within $G_{ij}$ each family's relevant parity class is swept uniformly — the
map sending a cell to the index of its line label within its parity class has all
fibres of size $q$.

**S25 (Pair factorization).** `[ALG]`
For each block $(i,j)$ and each pair of distinct families other than $\{D,A\}$,
$$E_{ij}[\varepsilon_R\varepsilon_C] = \tfrac{r_ic_j}{q^2},\quad
  E_{ij}[\varepsilon_R\varepsilon_D] = \tfrac{r_id_e}{q^2},\quad
  E_{ij}[\varepsilon_R\varepsilon_A] = \tfrac{r_ia_e}{q^2},\quad
  E_{ij}[\varepsilon_C\varepsilon_D] = \tfrac{c_jd_e}{q^2},\quad
  E_{ij}[\varepsilon_C\varepsilon_A] = \tfrac{c_ja_e}{q^2}.$$
*Reason:* writing $r = 2r' + i$, $c = 2c' + j$ with $r', c' \in \mathbb{Z}_q$, the five
label-pair maps $(r',c')$, $(r', r'-c')$, $(r', r'+c')$, $(c', r'-c')$, $(c', r'+c')$
are (up to a block-dependent translation) linear maps $\mathbb{Z}_q^2 \to
\mathbb{Z}_q^2$ of determinant $\pm1$, hence bijections; every label pair occurs
exactly once, so the moment is the product of the two densities. Five bijection
lemmas, one per pair.

**S26 (Diagonal–antidiagonal aggregate).** `[ALG]`
For each square parity $e \in \{0,1\}$:
$$\sum_{i \oplus j = e} E_{ij}[\varepsilon_D\varepsilon_A] = \frac{2\,d_e a_e}{q^2}.$$
*Reason:* by S22(b), each equal-parity pair $(d,a)$ meets the board in exactly two
cells differing by $(q,q)$, and both lie in the union of the two blocks with
$i \oplus j = e$ (in the *same* block iff $q$ is even, in different blocks otherwise —
either way in the union); summing the two blocks counts each pair exactly twice.
**Per-block $\{D,A\}$ factorization is false** (the map $(r',c') \mapsto (r'-c',r'+c')$
has determinant 2, and for $4 \mid n$ both lifts land in one block); this is why the
system has $4\cdot10 + 2 = 42$ equations and not 44. Any formalization must keep the
two aggregate rows aggregated.

**S27 (The moment system — paper `lem:moments`).** `[ALG]`
Collecting S24–S26: every configuration satisfies the 42 equations (10 per block: one
normalization, four marginals, five pair moments; plus two aggregates), whose
right-hand sides involve exactly the 22 distinct products
$r_ic_j$ (4), $r_id_e$ (4), $r_ia_e$ (4), $c_jd_e$ (4), $c_ja_e$ (4), $d_ea_e$ (2)
of outer counts; and
$$\frac{B}{q^2} = \sum_{i,j} p_{ij}(1,1,1,1), \qquad
  \frac{W}{q^2} = \sum_{i,j} p_{ij}(0,0,0,0).$$
Write $E \in \mathbb{Q}^{42 \times 64}$ for the coefficient matrix of the 64 atom
variables $p_{ij}(\varepsilon)$ in these equations (columns indexed by
$(i,j,\varepsilon)$), and $b(x) \in \mathbb{Q}[x]^{42}$ for the right-hand-side vector,
each entry $1$, an $x$-coordinate, or one of the 22 products; so $Ep = b(x)$ holds at
the configuration's own profile.


## §5 The canonical chamber

**S28 (Symmetry transformations).** `[ALG]`
Each of the following is an affine bijection of the board mapping lines to lines, hence
preserves $\{B, W\}$ (as a multiset):
(a) complementing all four line sets: exchanges $B \leftrightarrow W$ and replaces
    $\sum x_i$ by $8 - \sum x_i$ (normalized);
(b) $(r,c) \mapsto (r+1, c)$: exchanges the two row parity classes and simultaneously
    both diagonal and both antidiagonal classes; similarly $(r,c) \mapsto (r, c+1)$
    for the columns;
(c) $(r,c) \mapsto (c,r)$ (transpose): exchanges rows with columns, fixes
    antidiagonals, negates diagonals;
(d) $(r,c) \mapsto (r,-c)$: fixes row parities, permutes column labels within their
    parity classes, exchanges the diagonal with the antidiagonal family.
One Lean-sized lemma per transformation.

**S29 (Chamber normalization — paper `lem:chamber`).** `[ALG]`
Every configuration can be transformed by S28 moves, without changing
$\{B, W\}$, into one whose normalized profile satisfies the five *chamber*
inequalities
$$r_0 \le r_1,\qquad c_0 \le c_1,\qquad r_0 + r_1 \le c_0 + c_1,\qquad
  d_0 + d_1 \le a_0 + a_1,\qquad \textstyle\sum_{i=1}^{8} x_i \le 4.$$
*Order of moves and non-interference:* complementation (a) enforces the budget; row and
column unit translations (b) sort $r_0 \le r_1$ and $c_0 \le c_1$; transpose (c) orders
the row/column totals; (d) orders the two diagonal-family totals. A unit translation
swaps $(d_0,d_1)$ and $(a_0,a_1)$ *simultaneously*, so it does not disturb the
$d$-vs-$a$ total comparison; the transpose affects neither total.


## §6 The leaf linear programme and dual-leaf soundness

**S30 (McCormick validity).** `[ALG]`
Let $l_i \le x_i \le u_i$ and $l_j \le x_j \le u_j$ and $y_{ij} = x_ix_j$. Then
$$-y_{ij} + l_ix_j + l_jx_i \le l_il_j,\qquad -y_{ij} + u_ix_j + u_jx_i \le u_iu_j,$$
$$y_{ij} - u_ix_j - l_jx_i \le -u_il_j,\qquad y_{ij} - l_ix_j - u_jx_i \le -l_iu_j,$$
and $l_il_j \le y_{ij} \le u_iu_j$ when $0 \le l$. These are exactly the expansions of
$(x_i-l_i)(x_j-l_j) \ge 0$, $(u_i-x_i)(u_j-x_j) \ge 0$, $(u_i-x_i)(x_j-l_j) \ge 0$,
$(x_i-l_i)(u_j-x_j) \ge 0$; one `nlinarith`-sized lemma each.

**S31 (Definition: the leaf LP).** `[ALG]`
For a box $[l,u] \subseteq [0,1]^8$, the *leaf LP* has variables
$z = (x, y, p, t) \in \mathbb{R}^{8+22+64+1} = \mathbb{R}^{95}$ and rows:
* 42 equalities $Ez = e$: the moment system of S27 with each product $x_ix_j$ in
  $b(x)$ replaced by the variable $y_{ij}$;
* 95 non-bound inequality rows $Az \le b$: the $4 \times 22 = 88$ McCormick rows of
  S30, the budget row, the four chamber ordering rows of S29, and the two objective
  rows $t \le \sum_{ij} p_{ij}(1,1,1,1)$, $t \le \sum_{ij} p_{ij}(0,0,0,0)$;
* box bounds $l \le x \le u$, $l_il_j \le y_{ij} \le u_iu_j$, and $p \ge 0$.

**S32 (Feasibility transfer).** `[ALG]`
Let a configuration satisfy the chamber inequalities (S29) and have normalized profile
$x \in [l,u]$. Then $z = (x,\ (x_ix_j)_{ij},\ p,\ \min(B,W)/q^2)$, with $p$ the atom
frequencies of S24, is feasible for the leaf LP of S31. *Reason:* equalities by S27;
McCormick and box rows by S30; budget and chamber by S29; objective rows by S27's
$B, W$ identities. (This statement replaces the paper's optimum
$\mathrm{OPT}_{42}(x)$: no compactness or attainment argument is needed in the
formalization — every certificate bound is applied directly to this feasible point.)

**S33 (Dual-leaf soundness — paper `lem:dualleaf`).** `[ALG]`
Consider the leaf LP of S31. Let $\mu \in \mathbb{Q}^{95}$ with $\mu \le 0$ and
$\nu \in \mathbb{Q}^{42}$, and form
$L(z) = t + \mu^{\mathsf T}(Az - b) + \nu^{\mathsf T}(Ez - e)$.
Suppose, after collecting terms:
(i) the coefficient of $t$ in $L$ is $0$;
(ii) the coefficient vector $\omega \in \mathbb{Q}^{64}$ of the atom variables
     satisfies $\omega \le 0$,
so $L(z) = \ell_0 + \ell(x,y) + \omega^{\mathsf T}p$ with
$\ell_0 = -\mu^{\mathsf T}b - \nu^{\mathsf T}e$ and $\ell$ linear. Then every feasible
$z$ satisfies
$$t \ \le\ \ell_0 + \max_{(x,y) \in \mathrm{box}} \ell(x,y),$$
and the maximum is computed exactly coordinate by coordinate, taking each interval
endpoint matching the sign of its coefficient in $\ell$.
*Proof:* feasibility gives $\mu^{\mathsf T}(Az-b) \ge 0$ (componentwise product of two
nonpositives) and $\nu^{\mathsf T}(Ez-e) = 0$, so $t \le L(z)$; then $\omega \le 0$,
$p \ge 0$ give $L(z) \le \ell_0 + \ell(x,y)$; a linear function on a product of
intervals is maximized at endpoints coordinatewise.


## §7 The two branch certificates

**S34 (Certificate format and per-node verifier obligations).** `[CERT]`
A *branch certificate* is a rooted binary tree over a rational box in $[0,1]^8$
(coordinate order as in S21). Data and checks:

* **Root record:** the root box and the claimed threshold $\tau = \tfrac{527}{1000}$.
* **Split node:** a coordinate index $\delta \in \{1,\dots,8\}$ and an exact rational
  cut $c$; its children are the parent box intersected with $x_\delta \le c$ and with
  $x_\delta \ge c$. *Check:* the two closed child boxes cover the parent (they overlap
  on the cutting hyperplane; harmless).
* **McCormick-dual leaf:** exact rational multipliers $\mu \in \mathbb{Q}^{95}$
  ($\mu \le 0$) for the inequality rows and $\nu \in \mathbb{Q}^{42}$ for the equality
  rows, plus a stored rational bound $u$. *Check (exact rational arithmetic, no stored
  number trusted that can be recomputed):* rebuild the leaf LP of S31 for this box;
  verify hypothesis (i) of S33 (reduced cost of $t$ vanishes) and hypothesis (ii)
  (reduced costs of all 64 atom variables are $\le 0$); evaluate
  $\ell_0 + \max_{\mathrm{box}} \ell(x,y)$ at the sign-matching endpoints; verify the
  result equals the stored $u$ and $u \le \tau$. Conclusion by S33 + S32: every
  chamber configuration with profile in this box has $\min(B,W) \le u\,q^2$.
* **Exact empty leaf:** one of five reasons, each a pure interval-arithmetic
  contradiction with the chamber rows of S29 (never a solver infeasibility claim):
  `rsort`: $\max(l_{r_1}, l_{r_0}) > u_{r_1}$ (contradicts $r_0 \le r_1$);
  `csort`: likewise for columns;
  `rcsum`: $l_{r_0} + l_{r_1} > u_{c_0} + u_{c_1}$ (contradicts
  $r_0 + r_1 \le c_0 + c_1$);
  `dasum`: likewise for the diagonal families;
  `budget`: the sum over the four families of the family's minimum possible total on
  the box (i.e. $\sum_{i=1}^{8} l_i$, grouped by family) exceeds $4$.
  *Check:* re-evaluate the stated inequality on the box endpoints.
* **Plaid leaf (tree 1) / core leaf (tree 2):** an *exceptional* leaf.
  A plaid leaf asserts the box lies wholly inside one of the four rational plaid
  templates (choice of a square parity and a row parity); a box qualifies when,
  coordinate by coordinate, the template-$0$ coordinates have upper endpoint
  $\le \tfrac1{10}$, the template-$1$ coordinates have lower endpoint
  $\ge \tfrac{19}{20}$, and the two template-$s$ coordinates lie in
  $[\tfrac35, \tfrac78]$. A core leaf asserts the box lies wholly inside the aggregate
  core (S37): $l_{r_1} + l_{c_1} \ge \tfrac{36}{25}$,
  $u_{r_1} + u_{c_1} \le \tfrac{37}{25}$, $u_{r_0} + u_{c_0} \le \tfrac{9}{100}$,
  $u_{d_1} + u_{a_1} \le \tfrac{9}{200}$,
  $(1 - l_{d_0}) + (1 - l_{a_0}) \le \tfrac1{25}$ (normalized coordinates).
  *Check:* the endpoint inequalities.

The *canonical rational plaid neighbourhood* is
$$N:\quad 0 \le r_0, c_0, d_1, a_1 \le \tfrac1{10},\qquad
  \tfrac35 \le r_1, c_1 \le \tfrac78,\qquad \tfrac{19}{20} \le d_0, a_0 \le 1$$
(normalized); after the chamber restrictions it is the only surviving template, and
all four plaid leaves of tree 1 carry the template $(0,s,0,s,1,0,1,0)$, i.e. $N$.

**S35 (Branch-certificate inference — paper `lem:branchsound`).** `[ALG]`
If every terminal box of a branch certificate is either empty, contained in a declared
exceptional region, or carries a valid dual upper bound $u \le \tau$, then the root
box is covered by the union of the exceptional terminal boxes and boxes on which every
chamber configuration has $\min(B,W) \le \tau q^2$. *Proof:* upward induction from the
leaves; at each split the two closed children cover the parent.

**S36 (Global localization — paper `thm:cert1`).** `[CERT]`
Certified object: `even_c527_sym_mc.json.gz` (root box $[0,1]^8$; 6,929 nodes; 3,464
split nodes; 3,368 McCormick-dual leaves; 4 plaid leaves; 93 exact empty leaves
splitting as 1 `rsort`, 9 `csort`, 19 `rcsum`, 21 `dasum`, 43 `budget`; maximum depth
22; largest reconstructed leaf bound $\tfrac{527}{1000} - 1.92\cdot10^{-6}$).
*Statement certified (via S32–S35):* every chamber configuration whose normalized
profile lies outside $N$ has $\min(B,W) \le \tfrac{527}{1000} q^2$.

**S37 (Local core — paper `thm:cert2`).** `[CERT]`
Certified object: `even_local_core_mc.json.gz` (root box $N$; 4,423 nodes; 2,211 split
nodes; 1,639 McCormick-dual leaves; 563 core leaves; 10 exact empty leaves, all
`rcsum`; maximum depth 29; largest reconstructed leaf bound
$\tfrac{2329117}{4419584} = \tfrac{527}{1000} - 8.53\cdot10^{-7}$).
*Statement certified:* every chamber configuration with profile in $N$ has either
$\min(B,W) \le \tfrac{527}{1000} q^2$, or its unnormalized counts satisfy the four
*aggregate core* inequalities
$$\tfrac{36}{25} q \le r_1 + c_1 \le \tfrac{37}{25} q,\qquad
  r_0 + c_0 \le \tfrac{9}{100} q,\qquad
  d_1 + a_1 \le \tfrac{9}{200} q,\qquad
  (q - d_0) + (q - a_0) \le \tfrac{1}{25} q.$$

Both trees are already checked by two independently written exact-rational programs
(`verify_even_branch_certificate.py`, ending `ALL_EVEN_BRANCH_CERTIFICATES_OK`, and the
from-scratch `verify_even_finite_independent.py`, which re-derives the 42 rows from
torus incidence fibres at $n = 8,12,16,20$, re-validates them on 200 random colourings
at $n = 12,16,20,28$ — 8,400 equation checks — and rejects eight deliberately tampered
copies). A Lean verified checker replays exactly the per-node obligations of S34 and
concludes via S35; nothing beyond exact rational arithmetic is required.

**S38 (Escape corollary — paper `cor:escape`).** `[ALG]`
Let $q \ge 64$ and let a chamber configuration have $\min(B,W) \ge H(2q)$. Then its
normalized profile lies in $N$ and its counts satisfy the aggregate core of S37.
*Proof:* otherwise S36/S37 give $\min(B,W) \le \tfrac{527}{1000} q^2 < H(2q)$ by
S20(c), a contradiction.


## §8 Support cuts and the two cuts of the local finish

**S39 (Support duals and their inference — paper `lem:cutsound`).** `[ALG]`
A *support dual* is a pair $(\theta, \lambda)$ with $\theta \in \mathbb{Q} \cap [0,1]$
and $\lambda \in \mathbb{Q}^{42}$ such that, columnwise on all 64 atom columns of $E$
(S27),
$$\theta\,\mathbf 1[\varepsilon = (1,1,1,1)] + (1-\theta)\,\mathbf 1[\varepsilon =
  (0,0,0,0)] \ \le\ (\lambda^{\mathsf T}E)_{i,j,\varepsilon}.$$
If this holds, then every configuration satisfies
$$\min(B,W) \le \theta B + (1-\theta) W \le q^2\,\lambda^{\mathsf T} b(x)$$
at its own outer profile $x$. *Proof:* convex combination; multiply the columnwise
inequalities by the nonnegative atom counts and sum; $Ep = b(x)$ by S27. **No
relaxation, no branching, no chamber hypothesis is needed for this inference.**

**S40 (The certified cut library).** `[CERT]`
Certified object: 760 support cuts, stored as 684 delivered rational duals
(`new_dual_cuts.json`) and 76 legacy polynomials (`benders_cuts.json`) with rational
dual witnesses recovered by exact simplex. Per-cut data: $(\theta, \lambda)$ and the
induced multi-affine polynomial $P(x) = q^2 \lambda^{\mathsf T} b(x)$ (quadratic
monomials only among the 22 admissible products; never a square). Per-cut checks for a
verified checker: (i) the 64 columnwise inequalities of S39 in exact rational
arithmetic; (ii) the polynomial identity between $q^2\lambda^{\mathsf T}b(x)$ and the
stored coefficient list of $P$; (iii) multi-affinity (monomial support inside the 22
pairs). The existing verifier `verify_support_duals.py` performs exactly these checks
for all 760 cuts.

**S41 (Cuts 609 and 559 — paper `lem:cuts`).** `[CERT]`
Certified objects: entries 609 and 559 of the S40 library (shipped byte-identically as
`even_finite_support_cuts.json`; also checked by `verify_even_finite_algebra.py`).
Cut 609 has $\theta = 1$, cut 559 has $\theta = 0$. In the local coordinates of S42
their polynomials are, exactly,
$$B \ \le\ F_B := X - \beta\zeta + Q, \qquad\qquad W \ \le\ F_W := Y - \alpha\delta + Q,$$
for every configuration in the canonical chamber. *Verifier obligations:* the S40
checks for these two entries, plus the exact polynomial identity between each entry's
$P(x)$ and the displayed transported form. Write $T := \min(F_B, F_W)$; then
$\min(B,W) \le T$.


## §9 The local finish ($q \ge 130$)

Standing hypotheses for S42–S54: $q \ge 130$ where stated (only S54 needs it), the
configuration is in the canonical chamber (S29), its profile lies in $N$ (S34), and
the aggregate core (S37) holds. All variables are integers.

**S42 (Definition: local coordinates and aggregates).** `[ALG]`
Rename $u = r_0$, $R = r_1$, $v = c_0$, $C = c_1$, $e = d_1$, $g = q - d_0$,
$f = a_1$, $h = q - a_0$ (all in $\{0,\dots,q\}$; $u,v,e,f,g,h$ are small "defects",
$R, C$ are close to $sq$). Put
$$\sigma = R + C,\quad m = u + v,\quad \delta = e + f,\quad \zeta = g + h,\quad
  \alpha = 2q - \sigma - m,\quad \beta = \sigma - q,\quad Q = 2ef + 2gh,$$
$$X = uv + RC, \qquad Y = (q-u)(q-C) + (q-R)(q-v).$$
$(X,Y)$ are the two capacities of the $H$-profile $(r_0,r_1,c_0,c_1) = (u,R,C,v)$ —
the configuration's own quadruple with the two column parity counts *exchanged*, which
is again admissible in the definition of $H$ — hence
$$\min(X,Y) \ \le\ H(2q). \tag{S42.1}$$

**S43 (Core and chamber in local coordinates).** `[ALG]`
The core (S37) reads
$\tfrac{36}{25}q \le \sigma \le \tfrac{37}{25}q$, $m \le \tfrac{9}{100}q$,
$\delta \le \tfrac{9}{200}q$, $\zeta \le \tfrac{1}{25}q$; the chamber (S29) gives
$u \le R$, $v \le C$, $u + R \le v + C$, $e + h \le f + g$, and
$\sigma + m + \delta - \zeta \le 2q$. The neighbourhood $N$ gives in addition
$u, v, e, f \le \tfrac{q}{10}$ and $\tfrac{3q}{5} \le R, C \le \tfrac{7q}{8}$.
(Pure substitution; one Lean lemma.)

**S44 (Basic estimates — paper `lem:basic`).** `[ALG]`
Under S43: $\alpha \ge \tfrac{43}{100}q$, $\beta \ge \tfrac{11}{25}q$,
$\alpha > \delta$, $\beta > \zeta$.
*Reason:* $\alpha \ge 2q - \tfrac{37}{25}q - \tfrac{9}{100}q = \tfrac{43}{100}q$;
$\beta \ge \tfrac{36}{25}q - q = \tfrac{11}{25}q$; then
$\delta \le \tfrac{9}{200}q < \tfrac{43}{100}q$ and
$\zeta \le \tfrac{1}{25}q < \tfrac{11}{25}q$.

**S45 (Defect dichotomy — paper `lem:dichotomy`).** `[ALG]`
Under S43: $2Q = 4ef + 4gh \le \delta^2 + \zeta^2 \le \alpha\delta + \beta\zeta$,
hence $Q \le \max(\alpha\delta, \beta\zeta)$.
*Reason:* $4ef \le (e+f)^2$, $4gh \le (g+h)^2$ (AM–GM); then S44. This is the only
case distinction the local proof needs.

### Case $X \le Y$

**S46 (Easy branch).** `[ALG]`
If $Q \le \beta\zeta$ then $F_B \le X$ (by S41), so
$T \le X = \min(X,Y) \le H(2q)$ by (S42.1). For S47–S50 assume therefore
$Q > \beta\zeta$; S45 then gives $Q \le \alpha\delta$.

**S47 (Bounding $F_B$).** `[ALG]`
Since $\zeta \le q/25$: $2gh \le \tfrac{\zeta^2}{2} \le \tfrac{q\zeta}{50} \le
\beta\zeta$ (last step by S44), hence $F_B = X - \beta\zeta + 2ef + 2gh \le X + 2ef$.

**S48 (Four switched profiles).** `[ALG]`
Consider the four $H$-profiles
$(r_0,r_1,c_0,c_1) = (u+x,\ R,\ C,\ v+y)$ for
$(x,y) \in \{(e,2f), (2e,f), (f,2e), (2f,e)\}$.
(a) All coordinates lie in $[0,q]$: by S43, $u,v \le q/10$ and $e,f \le q/10$, so the
largest modified coordinate is $\le 3q/10$.
(b) Each has black capacity $(u+x)(v+y) + RC = X + uy + vx + xy \ge X + 2ef \ge F_B$
(each choice has $xy = 2ef$; then S47).
(c) Each has white capacity $Y - (x(q-C) + y(q-R))$; with $L := 2q - \sigma$, the
values of $x$ over the four choices sum to $3(e+f) = 3\delta$ and so do those of $y$,
so the *average* white loss is exactly $\tfrac34 \delta L$.

**S49 (The averaged loss is affordable).** `[ALG]`
Under the S46 assumption $Q > \beta\zeta$:
$$Q \ \le\ \delta\Bigl(\frac L4 - m\Bigr).$$
Chain, each step one lemma:
(a) $\tfrac L4 - m \ge \tfrac14(2 - \tfrac{37}{25})q - \tfrac{9}{100}q = \tfrac{q}{25}$;
(b) $2ef = Q - 2gh > \beta\zeta - \tfrac{q\zeta}{50} \ge \tfrac{11}{25}q\zeta -
    \tfrac{q\zeta}{50} = \tfrac{21}{50}q\zeta$;
(c) with $2ef \le \delta^2/2$: $\zeta < \tfrac{25\delta^2}{21q}$;
(d) $Q \le \tfrac{\delta^2 + \zeta^2}{2} \le \tfrac{\delta^2}{2} + \tfrac{q\zeta}{50}
    < \tfrac{\delta^2}{2} + \tfrac{q}{50}\cdot\tfrac{25\delta^2}{21q} =
    \tfrac{11}{21}\delta^2 \le \tfrac{11}{21}\cdot\tfrac{9q}{200}\delta =
    \tfrac{33}{1400}\delta q < \tfrac{1}{25}\delta q$
    (using $\zeta^2/2 \le q\zeta/50$, valid as $\zeta \le q/25$, and
    $\delta \le 9q/200$); compare with (a).

**S50 (First defect case — paper `prop:caseA`).** `[ALG]`
If $X \le Y$ then $T \le H(2q)$.
*Proof:* the easy branch is S46. Otherwise, since $\alpha = L - m$, S49 is equivalent
to $\tfrac34\delta L \le \alpha\delta - Q$; by S48(c) at least one of the four profiles
has white loss at most the average $\tfrac34\delta L$, hence white capacity
$\ge Y - (\alpha\delta - Q) = F_W$; by S48(b) its black capacity is $\ge F_B$. That
profile witnesses $H(2q) \ge \min(F_B, F_W) = T$.

### Case $Y \le X$

**S51 (Easy branch and the integrality step).** `[ALG]`
If $Q \le \alpha\delta$ then $F_W \le Y$ (by S41), so $T \le Y \le H(2q)$ by (S42.1).
Assume therefore $Q > \alpha\delta$; S45 gives $Q \le \beta\zeta$. Then $gh > 0$:
otherwise $Q = 2ef$, and $\delta > 0$ is forced ($\delta = 0$ would give $e = f = 0$,
hence $Q = 0$, contradicting $Q > \alpha\delta = 0$); but then
$Q = 2ef \le \tfrac{\delta^2}{2} \le \tfrac{9q}{400}\delta < \tfrac{43}{100}q\delta
\le \alpha\delta$ (using $\delta \le \tfrac{9}{200}q$ and S44), a contradiction. Since $g, h$ are **integer** counts, $g \ge 1$ and
$h \ge 1$, so
$$\zeta = g + h \ \ge\ 2.$$
This is the only point in the entire even proof where integrality of the counts is
used; the continuous relaxation is provably insufficient without it (it yields only
$t \le 43$ at $n = 18$ and $t \le 53$ at $n = 20$, against the true $42$ and $51$).

**S52 (Averaging the two cuts).** `[ALG]`
By S41, $T \le \tfrac{F_B + F_W}{2} = \tfrac{X+Y}{2} -
\tfrac{\alpha\delta + \beta\zeta - 2Q}{2}$. By S45 and S44,
$\alpha\delta + \beta\zeta - 2Q \ge \delta(\alpha - \delta) + \zeta(\beta - \zeta)
\ge \zeta(\beta - \zeta)$; on $2 \le \zeta \le q/25$ the map
$\zeta \mapsto \zeta(\beta-\zeta)$ is increasing (its derivative
$\beta - 2\zeta \ge \tfrac{11}{25}q - \tfrac{2}{25}q = \tfrac{9}{25}q > 0$), so by
S51's $\zeta \ge 2$:
$$\frac{\alpha\delta + \beta\zeta - 2Q}{2} \ \ge\ \beta - 2.$$

**S53 (Balanced-plaid baseline).** `[ALG]`
Under $Y \le X$ and profile in $N$: $\tfrac{X+Y}{2} \le \kappa q^2$.
*Reason:* apply S16 to the quadruple $(u, R, C, v)$; $N$ gives
$\rho \le \tfrac1{10} + \tfrac78 < 1$ and $\chi < 1$, so $\xi, \eta > 0$; the
assumption $X \ge Y$ yields $2\xi + 2\eta - \xi\eta \le 1$ exactly as in S17(c), so
$w = \sqrt{\xi\eta} \le 2 - \sqrt3$ and
$\tfrac{X+Y}{2q^2} = \tfrac{1+w^2}{2} \le \tfrac{1 + (2-\sqrt3)^2}{2} = \kappa$.

**S54 (Second defect case — paper `prop:caseB`).** `[ALG]`
If $Y \le X$ and $q \ge 130$ then $T \le H(2q)$.
*Proof:* the easy branch is S51's first sentence. Otherwise S52 + S53 +
$\beta \ge \tfrac{11}{25}q$ (S44) give $T \le \kappa q^2 - \tfrac{11}{25}q + 2$;
with $H(2q) \ge \kappa q^2 - \gamma q - \tfrac14$ (S19), $T \le H(2q)$ follows from
$$\Bigl(\tfrac{11}{25} - \gamma\Bigr) q \ \ge\ \tfrac94,$$
which at $q = 130$ reads $\tfrac{130}{\sqrt3} \ge \tfrac{1501}{20}$, i.e. the integer
comparison $6{,}760{,}000 \ge 6{,}759{,}003$; and the left side is increasing in $q$
because $\tfrac{11}{25} - \gamma = \tfrac{1}{\sqrt3} - \tfrac{14}{25} > 0$
(equivalently $625 \cdot 3 < 25^2 \cdot 3 \dots$ concretely: $\tfrac1{\sqrt3} >
\tfrac{14}{25} \iff 625 > 588$).

**S55 (Large even orders — paper `thm:q130`).** `[ALG]`
For every $q \ge 130$: $t(2q) \le H(2q)$.
*Proof:* suppose `HasPeaceable (2q) (H(2q)+1)`. By S9 there is a configuration with
$\min(B,W) \ge H(2q) + 1$; by S29 assume it is in the canonical chamber. Since
$q \ge 130 \ge 64$, S38 places its profile in $N$ and its counts in the aggregate
core. S41 gives $\min(B,W) \le T$, and S50 + S54 (covering both orderings of $X, Y$)
give $T \le H(2q)$ — a contradiction. Conclude with S7.


## §10 The finite range $q \le 129$: the cut-envelope ladder

**S56 (Box-discharge soundness — paper `lem:boxops`).** `[ALG]`
The ladder engine works over integer boxes $[l,u] \subseteq \{0,\dots,q\}^8$ (counts,
not normalized), with the five canonical inequalities of S29 in integer form
($r_0 \le r_1$, $c_0 \le c_1$, $r_0 + r_1 \le c_0 + c_1$, $d_0 + d_1 \le a_0 + a_1$,
$\sum \le 4q$; all coefficients in $\{0, \pm1\}$). Each of the following is one
soundness lemma:
(i) *Propagation.* A box is pruned only when the coordinatewise endpoint minimum of a
    row exceeds its right-hand side; a bound is tightened only to a value implied by
    the row for every point of the box satisfying it (integrality preserved since all
    coefficients are $\pm1$). No integer point satisfying the inequalities is ever
    discarded; the root is the full cube, so every canonical profile is covered
    (points violating the chamber are also covered, harmlessly).
(ii) *Multi-affinity.* Every cut polynomial is multi-affine: quadratic monomials only
    among the 22 admissible pairs, never a square (rejected at parse time otherwise).
(iii) *Corner maximum.* A multi-affine function attains its maximum over a real box at
    a vertex; enumerating all vertices in the cut's undetermined coordinates and
    finding none above the threshold bounds the cut on the whole box.
(iv) *Interval bound.* With $0 \le l \le x \le u$: each bilinear term $c_{ij}x_ix_j$
    is $\le c_{ij}u_iu_j$ for $c_{ij} > 0$ and $\le c_{ij}l_il_j$ for $c_{ij} < 0$;
    each linear term is bounded at its matching endpoint; the term-wise sum is a valid
    upper bound.
(v) *Splitting.* A split at $c = \lfloor (l_i + u_i)/2 \rfloor$ into $x_i \le c$ and
    $x_i \ge c + 1$ partitions the integer points of the parent box.
(vi) *Exactness of the arithmetic.* All comparisons are the exact integer test
    $s\,P(x) \le s\,H(2q) + s/2$ with $s = 12$ (the lcm of $2$ and all coefficient
    denominators of the library), so the threshold $H(2q) + \tfrac12$ is represented
    without rounding. The released engine uses signed 64-bit integers with the guard
    $Sq^2 < 2^{63}$, where $S = 360$ is the maximum absolute-coefficient sum of a
    scaled cut (recomputed before every run; every intermediate is bounded by
    $2Sq^2 \le 7.2\cdot10^8$ at the input cap $q \le 1000$). A Lean checker computing
    in ℤ needs no overflow guard; (vi) then degenerates to the scaling convention.

**S57 (Integer-box inference — paper `lem:boxsound`).** `[ALG]`
If such a search terminates with no survivor and every nonempty terminal box has a cut
of the S40 library bounded above by $H(2q) + \tfrac12$ throughout the box, then
$t(2q) \le H(2q)$.
*Proof:* by S56(v) splits partition integer points and by S56(i) pruning discards only
boxes without canonical profiles, so every canonical integer profile lies in a
discharged terminal box; there, S56(iii)/(iv) (or direct evaluation for one-point
boxes) bound the discharging cut by $H(2q) + \tfrac12$, and S39 gives
$\min(B,W) \le H(2q) + \tfrac12$; both sides integers, so $\min(B,W) \le H(2q)$.
Combine with S29 (reduction to the canonical chamber) and S9/S7.

**S58 (Ladder certificate: the finite object).** `[CERT]`
Per order $q$, the finite object a verified checker consumes is a *full discharge
tree*: header (order $q$; recomputed $H(2q)$ per S12/S15; the scaled integer cut
library of S40 with $s = 12$; root box $\{0,\dots,q\}^8$) and one record per node —
`SPLIT(i)` (children per S56(v)), `PRUNE(row)` (re-check per S56(i)),
`TIGHTEN(row, coord, bound)` (re-check per S56(i)), or
`DISCHARGE(cutId, mode ∈ {interval, corner, eval})` (re-check per S56(iii)/(iv)/direct
evaluation, against the exact threshold $12\,H(2q) + 6$). Every check is exact integer
arithmetic; the conclusion is the hypothesis of S57.
**Honest status of the released data:** the archived per-order files
(`records_q003_q020/`, `records_q021_q129/`) are *compact run summaries* (witnesses,
node counts, hashes), not node-by-node trees; in the paper, full coverage is
re-established by deterministically rerunning the audited C++17 engine
(`box_engine.cpp`, via `replay_finite_envelope.py`), with a separately written Python
engine agreeing exactly for all $q \le 129$ (same algorithm, so corroborative, not
independent). Emitting the full trees in the S58 format is the precisely delimited
remaining work for this component; the engine's operations are exactly those proved
sound in S56, so the tree format above is faithful to what the engine already does.

**S59 (The ladder — paper `prop:ladder`).** `[CERT]`
For every $q \in \{3,5\} \cup \{10, 11, \dots, 129\}$ (122 orders): the cut envelope
is at most $H(2q) + \tfrac12$ throughout the canonical integer domain, hence (S57)
$t(2q) \le H(2q)$, hence (S14) $t(2q) = H(2q)$. Recorded statistics of the runs: all
122 searches exhausted their stacks with no survivor, visiting 13,379,092 nodes in
total; every discharge used one of the 76 legacy cuts; the fallback sweep of the full
library at one-point boxes was never invoked.


## §11 Small orders and the exhaustive searches

**S60 ($t(2) = 0$ — `t_two`).** `[LEAN]`
`t 2 = 0 = H 1`. In Lean this is decided by finite evaluation of `lineMax 2` via S11
($(2^2)^4 = 256$ quadruples). (Paper's hand argument: any two distinct cells of the
$2\times2$ torus share a line.)

**S61 ($t(4) = 2$ — `t_four`).** `[LEAN]`
`t 4 = 2 = H 2`. Decided by finite evaluation of `lineMax 4` via S11
($(2^4)^4 = 65{,}536$ quadruples of subsets of `ZMod 4`, each requiring a count over
16 cells — comfortably within `native_decide`, and feasible for `decide` with a tuned
implementation). The paper instead gives a hand proof through the incidence and triple
identities; the Lean development replaces it by the direct decision, which is the
route recommended for any small order. $n = 6$ ($q = 3$, $t(6) = 4$) is covered by the
ladder (S59) in the paper; in Lean the same direct decision is possible in principle
($2^{24} \approx 1.7\cdot10^7$ quadruples) but is **not claimed as done** — see the
frontier table.

**S62 (Triple identity — paper Lemma 7).** `[ALG]`
Choose three line families with black-set sizes $x, y, z$, and let $U, U'$ count the
cells whose three chosen lines are all black resp. all white. Then
$$U + U' = n^2 - n(x + y + z) + I(X,Y) + I(X,Z) + I(Y,Z),$$
where $I(\cdot,\cdot)$ counts cells whose lines in both families are black.
*Reason:* sum the pointwise identity
$uvw + (1-u)(1-v)(1-w) = 1 - u - v - w + uv + uw + vw$ over all cells. Moreover
$\mathrm{blackCells} \subseteq U$ and $\mathrm{whiteCells} \subseteq U'$, so
$\min(B,W) \ge m$ forces the right side $\ge 2m$. Used only by the search filters
below (and by the paper's hand proof of $t(4) \le 2$, superseded in Lean by S61).

**S63 (Search reduction — paper §6.1, `lem:searchsound`, `lem:evensweep`).** `[COMP]`
For a target $M$, necessary profile conditions from S22, S23, S62 (budget
$\sum |{\cdot}| \le 2n$; pair products $\ge M$ on both sides; triple inequalities
$\ge 2M$; at even orders the parity-refined variants with
$J_{DA} = 2(d_0a_0 + d_1a_1)$, $\overline J_{DA} = 2((h-d_0)(h-a_0)+(h-d_1)(h-a_1))$,
$h = n/2$) yield a finite profile list; quotients use only explicit affine symmetries
(S28-type: transpose, $(r,c) \mapsto (r,-c)$, translations, unit multiplications, and
for odd $n$ also $(r,c) \mapsto (r+c, r-c)$), with Burnside audits of the orbit
counts; the last family is decided as an exact fixed-cardinality two-constraint subset
problem ($|\mathrm{Bl}| = \sum_{d \in D} p_d$, $|\mathrm{Wh}| = Q_0 - \sum_{d \in D}
q_d$). If the filter uses only necessary conditions, the fixed-pair list meets every
orbit, every third-family set is enumerated and the completion is decided exactly,
then all-UNSAT proves the target infeasible (paper `lem:searchsound`). These reductions are
formalizable, but the searches themselves are large computations audited (not
node-certified) in the release; they are *not* on the even theorem's critical path
except through S64.

**S64 (Remaining even orders — paper `prop:small-even`, `prop:t16sweep`).** `[COMP]`
$q \in \{4, 6, 7, 9\}$: the audited sweep campaigns at $n = 8, 12, 14, 18$ with
targets $9, 19, 26, 43$ (6 / 100 / 76 / 259 jobs; 720 / 5,111,848 / 70,259,455 /
228,644,005,008 third-family cases), all UNSAT. $q = 8$: the union-domain
verification at $n = 16$, target 33 (1,898 profiles; 159,551 fixed-pair
representatives; 3,226,530,570 $A$-masks tested, 2,951 surviving the scalar filter;
29,768 diagonal-cardinality cases; 38,830,322 $D$-masks), UNSAT, audit ending
`UNION_AUDIT_OK`. Together with S14 these give $t(2q) = H(2q)$ for
$q \in \{4,6,7,8,9\}$. **Lean alternative:** each of these five orders is also
decidable in principle by direct evaluation of `lineMax` (S11) or by a verified
replay of the S63 reduction; neither is claimed as done. Of the $n = 8,12,14,18$
sweeps, only $n = 17$ and $n = 15$ (below) were decided by two independently written
enumerators; $n = 8, 12, 14, 18$ rest on the single audited implementation
`general_sweep/solver_b.cpp`.

**S65 (Odd values — paper `thm:t15`, `thm:t17`; off the even critical path).** `[COMP]`
$t(15) = 20$: lower bound by explicit sets
$R = \{5,7,8,11,12,14\}$, $C = \{0,3,4,7,9,10,12,13\}$, $D = \{0,1,4,8,12,13,14\}$,
$A = \{1,2,3,9,10,12,14\}$ ($|\mathrm{Bl}| = 20$, $|\mathrm{Wh}| = 22$ — a checkable
finite fact); upper bound at target 21 via 247 canonical profiles, 43 fixed-pair orbit
types (Burnside-audited), and two independent enumerators (6,074,753,568 and
6,241,793,402 cases), both all-UNSAT.
$t(17) = 28$: lower bound by explicit sets
$R = \{0,1,2,4,5,7,8,9\}$, $C = \{0,1,2,4,5,7,8,9,13\}$,
$D = \{2,3,4,7,10,13,14,15\}$, $A = \{2,5,6,7,9,11,12,13,16\}$
($|\mathrm{Bl}| = |\mathrm{Wh}| = 28$); upper bound at target 29 via 316 jobs
(157,158,165,660 cases), independently confirmed by a second implementation
(158,802,287,408 cases), all UNSAT. The lower-bound witnesses are trivially
Lean-checkable (finite evaluation of `blackCells`/`whiteCells` cardinalities); the
upper bounds are audited computations, not certified objects.


## §12 Assembly

**S66 (Theorem 1).**
For every $q \ge 1$: $t(2q) = H(2q)$ (Lean: `t (2*q) = H q`).
*Proof by cases on $q$, each ingredient cited once:*
* $\ge$: S14, for all $q$. `[LEAN]`
* $\le$, $q \ge 130$: S55 (which consumes the certified S36, S37, S41 and the algebra
  S16–S20, S27–S33, S35, S38, S42–S54). `[ALG]`+`[CERT]`
* $\le$, $q \in \{3,5\} \cup \{10,\dots,129\}$: S59 (which consumes the certified S40
  ladder objects and the algebra S56, S57). `[CERT]`
* $\le$, $q \in \{1, 2\}$: S60, S61. `[LEAN]`
* $\le$, $q \in \{4,6,7,8,9\}$: S64. `[COMP]`

The Lean `Main` module isolates the entire upper bound as the single explicit
hypothesis `UpperBoundStatement` (`∀ q > 0, t (2*q) ≤ H q`) and proves
`evenTorusTheorem_of_upperBound : UpperBoundStatement → EvenTorusTheorem`; the
unconditional Lean theorems today are S14 (all $q$) and the complete instances
$q = 1, 2$.


## Formalization frontier

The companion Lean development (Lean 4, Mathlib v4.32.2 toolchain, modules
`PeaceableQueens/{Defs, LineColouring, LowerBound, Values, Main}`) fully proves the
definitional layer, the line-colouring equivalence, the lower bound $H(2q) \le t(2q)$
for **all** $q$, the Table-1 values of $H$, and the complete instances
$t(2) = H(2)$, $t(4) = H(4)$. Everything else in the upper bound reduces to (a) the
`[ALG]` statements — ordinary lemma-sized algebra with no new ideas, including every
$\sqrt3$ comparison as an explicit integer comparison — and (b) exactly **three
certified finite objects** plus their two soundness lemmas: the two branch trees
(S36, S37, checked per S34 against S33), the support-cut library entries 609/559
(S40, S41, checked per S39), and the per-order ladder trees (S58, S59, checked per
S56/S57 — the one component whose full node-by-node records still need to be emitted
by the existing engine; everything else about it is already specified). The five
`[COMP]` orders $q \in \{4,6,7,8,9\}$ can be removed from the trusted base either by
verified replay of S63 or, more simply, by direct `lineMax` decisions as in S60/S61.

| statements | tag | status today |
|---|---|---|
| S1–S15 | `[LEAN]` | proved in the companion development (defs, S9 `hasPeaceable_iff_lineSets`, S11 `t_eq_lineMax`, S14 `H_le_t`, S15 `H` value lemmas) |
| S60, S61 | `[LEAN]` | proved (`t_two`, `t_four`); $t(6)$ by the same `lineMax` decision is feasible but not claimed |
| S16–S20 | `[ALG]` | pen-and-paper; not yet in Lean |
| S21–S33, S35, S38 | `[ALG]` | pen-and-paper; not yet in Lean (S31/S32 replace the paper's $\mathrm{OPT}_{42}$, avoiding compactness) |
| S36, S37 | `[CERT]` | certified objects released (`even_c527_sym_mc.json.gz`, `even_local_core_mc.json.gz`), doubly checked in Python; Lean verified checker per S34 not yet written |
| S39–S41 | `[ALG]`/`[CERT]` | cut library released and doubly checked; Lean checker per S40 not yet written |
| S42–S55 | `[ALG]` | pen-and-paper; not yet in Lean; sole integrality use is S51 |
| S56, S57 | `[ALG]` | pen-and-paper; not yet in Lean |
| S58, S59 | `[CERT]` | engine + summaries + deterministic replay released; full node-by-node trees in the S58 format not yet emitted — the only data-side gap |
| S62 | `[ALG]` | pen-and-paper; only feeds `[COMP]` |
| S63–S65 | `[COMP]` | audited searches; off the critical path for even orders except S64, which is replaceable by direct decisions |
| S66 | — | assembles the above; unconditional in Lean today exactly for the S14 inequality and $q \in \{1,2\}$ |

Sources of record: `paper/peace_even_torus.tex` (Sections 2–6, Appendix A) and the
ancillary archive bound by `SHA256SUMS`, public immutable snapshot at
`github.com/jphme/math-problems`, directory `peaceable-queens-even-torus/anc/`
(one-command replay: `uv run --isolated --python 3.14.6 --with sympy==1.14.0 --with
mpmath==1.3.0 python verify_bundle.py`, ending
`PEACEABLE_QUEENS_RELEASE_BUNDLE_OK`).
