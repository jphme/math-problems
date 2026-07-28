# Refutation-certificate specification, format `erdos634-refutation-v1`

Status: normative. The exporter (a mode of `searcher2.py`) must produce exactly this
format; the independent checker (`check_refutation.py`) must validate exactly the
obligations in §5. The checker must be a fresh implementation: it must not import
from, or be written with reference to, `searcher2.py`, `searcher.py`, or
`independent/erdos634_exact_search.py`. Its only trusted inputs are this
specification and the mathematical lemmas cited in §6 (proved in the paper).

## 1. Purpose

A certificate is a finite proof object for a statement of the form

> the target polygon T admits no tiling by congruent copies of the tile R,

covering, in this first campaign:

- `N33`: target = triangle with sides (21, 21, 33), tile R = (5, 3, 7)
  (Group 2, `c^2 = a^2 + ab + b^2` with (a,b,c) = (5,3,7)), field D = 3;
- `N21`: target = triangle with sides (12, 12, 21), tile R = (2, 3, 4)
  (Group 1, (p,q) = (1,2)), field D = 15.

The certificate is a **tree**, not a DAG: the export run disables memoization and
canonicalization entirely, so every node carries its region in absolute
coordinates. No state-identification step needs to be trusted or checked.

The export run uses the **reduced pruning configuration** (the same flags as the
manifest's reduced-pruning replay): the only pruning rules are `budget`, `wedge`,
and `short_edge` as defined in §4. The segment-semigroup table and the
boundary-invariant pruning are disabled.

## 2. Number, point, and polygon encoding

- A rational is a string `"p/q"` or `"p"` with `gcd(p,q)=1`, `q>0`.
- A **coordinate** is `[x, w]` (two rational strings) denoting the real number
  `x + w*sqrt(D)`.
- A **point** is `[X, Y]` where `X` and `Y` are coordinates.
- A polygon is a list of >= 3 points, counterclockwise (positive signed area),
  simple (no repeated vertices, no self-intersection), with no three consecutive
  collinear vertices (every listed vertex is a genuine vertex: interior angle != pi).

## 3. File format

Gzipped JSONL (`.jsonl.gz`). Line 1 is the header; every subsequent line is one
node. Nodes appear in depth-first preorder; every node except the root is
referenced by exactly one `refuted_child` field of an earlier line.

### 3.1 Header

```json
{"type": "header",
 "format": "erdos634-refutation-v1",
 "instance": "N33",
 "D": 3,
 "tile_sides": ["5", "3", "7"],
 "target": [ <polygon> ],
 "config": {"prunes": ["budget", "wedge", "short_edge"]},
 "node_count": 22850}
```

`tile_sides` is the exact side-length triple of R (rationals). `target` must be in
**standard position**: longest side from (0,0) to (base,0), apex strictly above the
x-axis. `node_count` is the number of node lines that follow.

### 3.2 Node

```json
{"type": "node", "id": 17,
 "region": [ <polygon> ],
 "status": "branched" | "pruned",
 ...}
```

Node `id`s are consecutive integers starting at 0 (the root). The root's `region`
must equal the header `target` exactly.

**If `status = "pruned"`**, the node additionally has

```json
"prune": {"kind": "budget"}
"prune": {"kind": "wedge", "vertex": 4}
"prune": {"kind": "short_edge", "edge": 2}
```

- `budget` — claim: area(region)/area(R) is not a positive integer.
- `wedge` (vertex index i) — claim: the interior angle of `region` at vertex i is
  not a nonempty finite sum of tile angles of R.
- `short_edge` (edge index e, the edge from vertex e to vertex e+1) — claim: both
  endpoints of edge e are convex vertices (interior angle < pi) and the edge is
  strictly shorter than every side of R.

The witness data is intentionally minimal; the checker recomputes each claim from
`region` and the tile alone.

**If `status = "branched"`**, the node additionally has

```json
"corner": 3,
"ray": "succ" | "pred",
"candidates": [ <exactly 12 entries> ]
```

- `corner` is a vertex index; the vertex must be **convex** (interior angle < pi).
- `ray` selects the boundary ray at that vertex: `"succ"` = along the edge toward
  the next vertex (corner -> corner+1), `"pred"` = along the edge toward the
  previous vertex (corner -> corner-1).
- `candidates` is the complete 12-element placement list of §3.3, in the canonical
  order defined there. Each entry is

```json
{"tri": [P, Q, S], "verdict": "rejected"}
{"tri": [P, Q, S], "verdict": "expanded",
 "children": [ <polygon>, <polygon>, ... ],
 "refuted_index": 0,
 "refuted_child": 18}
```

`children` is a list of >= 1 polygons in absolute coordinates. `refuted_index`
selects one of them; `refuted_child` is the node id whose `region` equals
`children[refuted_index]` exactly. The other children get **no** node records
(they may or may not be tileable; the refutation does not need them). An
`expanded` entry with an empty `children` list is **invalid** (it would mean the
placement tiles the component, contradicting refutation).

### 3.3 The canonical 12-placement list

Given the corner point P, the unit direction u of the chosen ray (a vector with
coordinates in Q(sqrt(D)); the squared length of the ray edge must be the square
of a rational, so that u = edge/length is exactly computable — otherwise the
certificate is invalid),
and the tile R with sides (s1, s2, s3) and angle theta_i at the vertex opposite
side s_i:

For i in (1, 2, 3) — the tile angle placed at P is theta_i, whose adjacent sides
are the two sides other than s_i, say in fixed order (s_j, s_k) with j < k:

- for (along, other) in ((s_j, s_k), (s_k, s_j)) — which adjacent side lies on
  the ray:
  - for eps in (+1, -1) — chirality:
    - candidate triangle = ( P, P + along*u, P + other*Rot(eps*theta_i)*u ),

where Rot(phi) is the exact rotation matrix with entries cos(phi), sin(phi) in
Q(sqrt(D)), computed from the tile side lengths by the law of cosines
(cos theta_i rational) and sin theta_i = w*sqrt(D) with rational w. Order of the
list: i ascending, then (along, other) in the order above, then eps = +1 before
eps = -1. All 12 entries must be present, in this order, even when rejected.

Only candidates with eps such that the third vertex lies on the region's side of
the ray can be contained; both are still listed.

## 4. Claim semantics

The certificate claims: **the header target admits no tiling by congruent copies
of R** (reflections allowed, non-edge-to-edge allowed). A node claims: its
`region` admits no such tiling. The soundness chain is:

1. a `pruned` node's region is untileable because the recomputed witness claim
   holds and the corresponding lemma (§6) says the claim is impossible for a
   tileable region;
2. a `branched` node's region is untileable because (a) by the convex-corner
   branching lemma, any tiling of the region contains a tile with a vertex at the
   corner and a complete edge starting there along the chosen ray, i.e. one of the
   12 candidates, placed as a subset of the region; (b) every candidate the
   checker finds to be contained in the region is `expanded`; (c) for each
   expanded candidate, the recorded children together with the candidate triangle
   partition the region (checked by containment, pairwise interior-disjointness,
   and exact area additivity — the coverage lemma), so any tiling extending that
   placement induces a tiling of every child, in particular of the refuted child,
   which is untileable by induction on the tree.

## 5. Checker obligations

The checker must verify all of the following, in exact arithmetic over
Q(sqrt(D)), and reject the certificate on any failure:

 1. header well-formed; `instance` is one it knows; it **independently
    constructs** the target polygon of that instance in standard position from
    the published side lengths and checks exact equality with `target`; it
    independently checks the tile triple satisfies the instance's defining
    relation (e.g. 49 = 25 + 15 + 9);
 2. `node_count` matches; node ids are 0..n-1 in order; every node except 0 is
    referenced by exactly one `refuted_child`; every `refuted_child` refers to a
    later id (tree, preorder);
 3. every polygon (regions, children) is simple, CCW, positive area, no repeated
    or collinear-consecutive vertices;
 4. root region == header target;
 5. for each `pruned` node, the witness claim of §3.2 holds, recomputed by the
    checker from the region and tile alone:
    - `budget`: exact area ratio not a positive integer;
    - `wedge`: bounded exhaustive enumeration (sum of tile angles, each summand
      one of the three tile angles, total <= the corner angle bound pi) shows no
      nonempty combination matches the corner angle exactly (compare exact
      (cos, sin) pairs);
    - `short_edge`: both endpoints convex, exact length < min tile side;
 6. for each `branched` node: `corner` is a convex vertex; the ray edge's length
    has a rational value (else reject); the 12 candidates recomputed by the
    checker from §3.3 match the recorded `tri` lists exactly, in order;
 7. for each candidate, the checker decides containment itself:
    contained(tri, region) :<=> area(tri INTERSECT region) == area(tri), computed
    by exact polygon-intersection area (triangulate the region by ear clipping;
    clip each triangle against the convex candidate by half-plane clipping; sum
    signed areas). If contained but `verdict = "rejected"` -> reject the
    certificate. If not contained but `verdict = "expanded"` -> reject;
 8. for each `expanded` candidate: children all nonempty polygons; each child is
    contained in the region (same area criterion); the candidate triangle and the
    children are pairwise interior-disjoint (pairwise intersection area 0); the
    sum of the children's areas plus the tile area equals the region's area;
    **boundary support**: every edge of every child lies, as a point set,
    inside the union of the region's boundary and the candidate triangle's
    boundary.  Concretely: for each child edge, collect the closed edges of
    the region and of the triangle that are collinear with it, and verify by
    exact one-dimensional interval arithmetic on the common supporting line
    that their union covers the child edge (a child edge may straddle several
    collinear parent/tile edges, e.g. the exact union of a tile edge and a
    collinear region edge, so containment in a single edge must NOT be
    required).  Without this check a certificate could subdivide the true
    residual region along an artificial chord and "refute" a meaningless
    sliver, so its absence is unsound;
    `children[refuted_index]` equals the `refuted_child` node's region exactly;
 9. no `expanded` candidate anywhere has zero children;
10. after all nodes pass: report ACCEPT with the instance name, node count, and
    SHA-256 of the certificate file. Any warning path must be treated as REJECT;
    there is no "inconclusive-but-accepted" state.

Obligation 7 makes the checker, not the searcher, the arbiter of which
placements are legal; obligation 8 re-derives the child regions from scratch via
the coverage lemma, so the searcher's polygon-subtraction code is not trusted.

## 6. Trusted lemmas (proved in the paper)

- **Convex-corner branching**: in any tiling of a polygonal region, for any convex
  boundary vertex and either incident boundary ray, some tile has its vertex there
  and a complete edge along the ray. (Hence §3.3 is exhaustive.)
- **Coverage lemma**: finitely many closed polygons inside a region, pairwise
  interior-disjoint, with areas summing to the region's area, cover the region.
  (Hence obligation 8 certifies that children = closure of region minus tile, and
  every remaining tile of a hypothetical completion lies in exactly one child.)
- **Component induction**: given the coverage checks AND the boundary-support
  check of obligation 8, every child boundary lies in the union of the region
  boundary and the placed tile's boundary; a tile of a hypothetical completion
  has connected interior disjoint from the placed candidate and from that
  boundary union, hence lies in a single child; so untileability of one child
  kills the branch. (Boundary support is essential: without it the children
  could subdivide the true residual region and the induction would fail.)
- **Budget**: a tiled region's area is a positive integer multiple of the tile
  area.
- **Wedge**: every convex boundary vertex of a tiled region is filled by tile
  corners, so its angle is a nonempty sum of tile angles.
- **Short edge**: a boundary edge with two convex endpoints is partitioned by
  complete tile edges (each of length >= the minimum tile side).

## 7. Independence policy

The exporter may reuse any of `searcher2.py`; it only *produces* the object. The
checker must be written against this document only. Shared code between checker
and searcher: none. Shared code between checker and `verify_tiling.py`: none.
Python standard library only (`fractions`, `json`, `gzip`, `hashlib`). Run with
`uv run python`.

## 8. Artifacts and reporting

- Certificates: `computation/tiling_search/results/certificates/<instance>_refutation.jsonl.gz`
  (bulk machine output: untracked; SHA-256 recorded in `paper/verification_manifest.md`).
- Checker: `computation/tiling_search/check_refutation.py` (tracked).
- Exporter changes: inside `searcher2.py` (tracked), flag `--export-cert PATH`.
- Every run's exact command, interpreter version, node count, wall time, and
  SHA-256 of certificate and checker go into the manifest.
