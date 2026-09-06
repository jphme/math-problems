# Paper ↔ Lean correspondence

This document maps every numbered result of *Peaceable queens on even tori: an
exact parity formula* (`peace_even_torus.tex`, September 6, 2026) and every
obligation S1–S66 of [`FORMAL_PROOF.md`](FORMAL_PROOF.md) to its Lean
statement in `PeaceableQueens/`, and states exactly where the formalization is
narrower or wider than the paper. Paper results are cited by their stable LaTeX
labels; the shared theorem counter prints `thm:main` as Theorem 2, `lem:lines`
as Lemma 6 and `prop:lower` as Proposition 10.

The main even theorem is a complete formal proof under the disclosed native
trusted base (see [`VERIFICATION.md`](VERIFICATION.md)):

```
PeaceableQueens.evenTorusTheorem : ∀ q : ℕ, 0 < q → t (2 * q) = H q
```

where Lean's `H q` is the paper's `H(2q)`. The tables below record the
boundary of what is formalized; the formalization does not assert every
statement, experiment or conjecture in the paper.

## Load-bearing facts

* **The statement cannot succeed by changing the problem.** `Cell n` is
  `(ZMod n) × (ZMod n)`. The four attack relations use modular row, column,
  difference and sum labels. `IsPeaceable` prohibits only cross-army attacks;
  it also forces disjointness because `SharesLine p p` holds. `HasPeaceable`
  requires equal army sizes. `le_t_iff` establishes that the capped
  `Nat.findGreatest` really is the maximum for positive board orders.
* **The parity trap is handled.** The five non-D/A pair maps are bijections.
  D/A has two lifts for equal-parity labels and no lift for unequal-parity
  labels. `aggregateDAAtomCount_eq` counts the union of the two square-parity
  blocks, not each block separately, by an argument uniform in `q`; so the 42
  equations remain valid when `q` is even, including `4 ∣ n`.
* **Certificate indices are connected to geometry.** `MomentModel` defines
  semantic rows/atoms; `ModelCompatibility` checks every flat coefficient and
  right-hand-side component by kernel `decide`; `ConfigurationBridge` proves
  that the actual atom frequencies satisfy every LP equality, inequality and
  bound. The LP objective of a configuration is exactly `min(B,W)/q²`.
* **Neither feasibility nor certificate coverage is assumed.** The two large
  trees produce `CoverTree`s at the exact full-cube and neighbourhood roots.
  The finite checker constructs coverage from validated propagation, both
  split children and terminal discharge. A malformed or truncated encoded tree
  cannot replace a missing subtree with success. No producer's success flag is
  a Lean hypothesis.
* **The discrete finish is attached to real counts.** Column parities are
  deliberately exchanged in the `H` witness `(u,R,C,v)`. All natural
  subtractions are transported with the necessary `count ≤ q` bounds.
  `configuration_zeta_ge_two` returns to the natural defects before inferring
  `g + h ≥ 2`.

## Every numbered result of the paper

References such as `Main.evenTorusTheorem` identify a theorem and its source
file. Each file's namespace declaration gives the full Lean name; for example,
the main endpoint is `PeaceableQueens.evenTorusTheorem`.

“Direct” means the mathematical assertion is represented, allowing ordinary
changes of notation. “Specialized” means the version needed by the even
endpoint is proved. “Consequence” means existing theorems imply it, but no
separate exported theorem states it. “Outside” means no corresponding Lean
proof is supplied. Numbers follow the current LaTeX source.

| Paper number and stable label | Lean coverage and qualification |
|---|---|
| 1, `def:H` | Direct: `Defs.H`, `profileBlack`, `profileWhite`; range includes both 0 and `q`. |
| 2, `thm:main` | Direct: `Main.evenTorusTheorem`; all `q > 0`, no certificate premise. |
| 3, `cor:asym` | Direct: `Corollaries.even_bounds`, `even_asymptotic`, `even_density_limit`, using `UpperBound/Asymptotics`. The limit is along even orders indexed by `q`; the density is `κ/4 = (2-√3)/2`. |
| 4, `cor:values` | Direct: `Corollaries.t_sixteen`, `t_eighteen`, `t_twenty`, `t_forty`. Computability follows from finite `H` and the main theorem. |
| 5, `thm:oddmain` | Outside: neither `t(15)=20` nor `t(17)=28` is formalized. |
| 6, `lem:lines` | Direct, slightly more general: `hasPeaceable_iff_lineSets` also allows `m=0` and any nonzero board order. `t_eq_lineMax` gives its displayed consequence. |
| 7, `lem:inc` | Direct for the five non-D/A pairs and for even D/A fibres, in `Incidence`. Odd D/A bijectivity is outside. |
| 8, `lem:budget` | Specialized to even configurations in `Symmetry.budget_or_complement`; exact army exchange is proved. |
| 9, `lem:triple` | Outside: no exported triple-count identity. The even proof avoids it. |
| 10, `prop:lower` | Direct: `H_le_t`, `paritySeparated_counts`, `parityBlackCells_eq_lineCells` and `parityWhiteCells_eq_lineCells`. Arbitrary row/column sets have the displayed counts; first-label sets realize every admissible quadruple. |
| 11, `rem:plaid16` | Only the displayed `H` values are direct in Lean. `P`, `P(20)=50`, `P(24)=72`, the 200-order difference histogram and the finite confirmation of Conjecture 5.1 are outside Lean; `scripts/check_paper_values.cpp` reproduces these numerical comparisons and witnesses with exact integers. The conjecture for all even orders is explicitly unproved in the paper and remains unproved here. |
| 12, `lem:Hupper` | Direct over real profile coordinates: `profile_min_le_kappa_s17`; natural-floor consequence `H_le_floor_s18`. Its argument is nonnegative, so natural floor agrees with the paper's integer floor. |
| 13, `lem:Hlower` | Direct: `H_lower_s19`, with `m` and `m+1` both proved admissible. |
| 14, `lem:moments` | Direct for configurations: all normalization, four marginals, five block pairs, two aggregate D/A rows and both objective identities (`BlockMoments`, `ConfigurationMoments`). |
| 15, unlabelled D/A remark | The model correctly omits per-block D/A rows; the general formal counterexample to per-block independence is not a separate theorem. |
| 16, `def:OPT` | Outside as an optimum definition, nonemptiness/compactness/attainment theorem and real LP. Its needed configuration-feasibility consequence is direct: `configurationLPVector_leafFeasible`. |
| 17, `lem:chamber` | Direct for the objective: `Symmetry.exists_chamber`, with an actual transformed configuration. Preserves the unordered black/white pair; does not classify all configurations or all atom histograms. |
| 18, `lem:dualleaf` | Specialized to rational LP points: `linear_dual_upper_bound`. Dense, sparse and scaled implementations prove exact dual soundness with the correct multiplier signs. |
| 19, `lem:branchsound` | Direct rational-box coverage: `CoverTree.locate`, with checked split coverage in `BranchCertificate.splitNodeOK_coverTree`. |
| 20, `def:N` | `CertificateConsequences.localRoot` is the exact rational box. `InPlaid 0 1` describes it when combined with the unit cube. `InLargeOrderNeighborhood` retains only the inequalities used by the finish, omitting the two near-one constraints; the root/core supplies the localization. |
| 21, `thm:cert1` | Specialized: `global_tree_consequence`; the checked global tree bounds the configuration's own LP point or localizes it to `N`; no theorem about the real `OPT₄₂`. |
| 22, `thm:cert2` | Specialized: `local_tree_consequence`; the checked local tree gives the threshold/core alternative for configurations. `49/25 ≤ x₄+x₆` is exactly the last defect inequality. |
| 23, `rem:certverify` | Historical program independence, random checks and tampering statistics are not Lean theorems. The Lean coverage proof is independent of those audits' verdicts. |
| 24, `lem:escape` | Direct needed inequalities in `ProfileAlgebra`, culminating in `H_escape_s20` for `q ≥ 64`; the intermediate lower margin is derived in the proof. |
| 25, `cor:escape` | Direct configuration consequence of both checked trees and `H_escape_s20`: `configuration_escape_of_certificates`. |
| 26, `lem:cuts` | Direct, for every configuration (the paper's chamber hypothesis is not needed): `cut609_configuration_black` gives `B ≤ F_B`; `cut559_configuration_white` gives `W ≤ F_W`. Both minimum consequences remain available. |
| 27, `lem:basic` | Direct rational algebra: `Local.basic`, for positive `q` under the core inequalities. |
| 28, `lem:dichotomy` | Direct: `two_Q_le_squares`, `squares_le_weighted`, `defect_dichotomy`; the disjunction replaces the equivalent maximum bound. |
| 29, `prop:caseA` | Direct on actual configurations through the first branch of `configuration_local_finish`, using four valid integer `H` witnesses. Not exported as a standalone lemma; that branch does not use `q ≥ 130`. |
| 30, `prop:caseB` | Direct on actual configurations through the second branch of `configuration_local_finish`; the natural-defect gap, average bound and exact threshold comparison are connected. |
| 31, `rem:integrality` | The `q=130` comparison is direct. The reported continuous-relaxation numerical gaps at `n=18,20` are outside. |
| 32, `thm:q130` | Direct: `LargeOrderCertified.large_order_bound`, for every `q ≥ 130`. |
| 33, `lem:cutsound` | Direct: `support_weighted_dual_sound_indicator` exposes the weighted inequality; `support_dual_sound_indicator` derives its minimum-objective consequence. |
| 34, `lem:boxops` | Direct integer versions of propagation, multi-affinity, corner/interval discharge and splitting in `FiniteLattice`. Real-box extrema and the C++ 64-bit overflow analysis are outside; Lean uses mathematical `Int`. |
| 35, `lem:boxsound` | Direct via `validateCompleteBool_sound` and `finite_order_bound_of_tree_at`, with the exact `12b+6` threshold and `b ≤ H q` witness. |
| 36, `prop:ladder` | The upper-bound conclusion is direct for the larger full interval `3..129` (`Generated.Finite.finite_range_bound`); action-tree coverage plus the 76 sound cuts supplies the envelope consequence. The paper's runtime/node statistics are provenance, not premises. |
| 37, `lem:searchsound` | Outside: the profile/orbit/completion search reduction is not formalized. |
| 38, `thm:t15` | Outside, including the displayed odd lower-bound witness. |
| 39, `prop:t16sweep` | No `33+33` placement is a consequence of `Q008.upper_bound` and `Values.H_eight`. The union-domain algorithm and its statistics are not formalized. |
| 40, `lem:evensweep` | Outside: not needed by the action-tree proofs. |
| 41, `thm:t17` | Outside, including the displayed odd lower-bound witness. |
| 42, `prop:small-even` | All numerical conclusions covered: `SmallBoards.t_two`, `t_four`, and `Q004`, `Q006`, `Q007`, `Q008`, `Q009` plus the lower bound. The base cases use kernel decisions after translation; the five exceptions use action trees. Methods differ from the paper. |
| 43, `prop:lift` | Outside: no divisor-lifting theorem or its displayed odd examples. |

Table `tab:Hvals` is matched entry by entry by `SmallBoards.H_one`, `H_two`
and `Values.H_three` through `H_twenty`. Table `tab:certs`'s structural counts
agree with the generated tree declaration ranges: 6,929 and 4,423 nodes, with
3,464 and 2,211 splits, 3,368 and 1,639 dual leaves, 4 plaid and 563 core
leaves, 93 and 10 empty leaves. Maximum depths and leaf-bound decimal
approximations are certificate statistics, not exported theorems. The paper's
tables of search jobs/cases and `tab:finite-modes` describe its computations;
the Lean proof does not certify those programs' executions.

## Every obligation S1–S66

File names below are relative to `PeaceableQueens/`; `UB/` abbreviates
`UpperBound/`. Names are local to the namespace in the indicated file.
The prose statements are in [`FORMAL_PROOF.md`](FORMAL_PROOF.md).

| Obligation | File and theorem/definition | Exact correspondence |
|---|---|---|
| S1 | `Defs`: `SharesLine`, `sharesLine_refl`, `SharesLine.symm` | Four modular line equalities. |
| S2 | `Defs`: `IsPeaceable` | Only cross-colour attacks forbidden. |
| S3 | `Defs`: `IsPeaceable.disjoint` | Shared cells excluded by reflexivity. |
| S4 | `Defs`: `HasPeaceable` | Two finite armies of the same specified size. |
| S5 | `Defs`: `hasPeaceable_zero`, `HasPeaceable.le_sq`, `HasPeaceable.mono` | Empty, bounded and downward-closed sizes; bound assumes nonzero order. |
| S6 | `Defs`: `t` | Maximum up to `n²`. `ZMod 0` is infinite, but positive `q` excludes it. |
| S7 | `Defs`: `hasPeaceable_t`, `le_t_iff` | True maximum, with correct direction of the equivalence. |
| S8 | `Defs`, `LineColouring`: cell definitions and membership lemmas | White means complement in every family. |
| S9 | `LineColouring`: `hasPeaceable_iff_lineSets` | Both directions, including trimming to equal size. |
| S10 | `Defs`: `lineMax` | Maximum over all four finite line sets. |
| S11 | `LineColouring`: `t_eq_lineMax` | Both maxima agree for nonzero order. |
| S12 | `Defs`: `H`, `le_H`, `H_le` | Exactly the four-count maximum; natural subtraction is bounded. |
| S13 | `LowerBound`: `paritySeparated_counts`, `parityBlackCells_eq_lineCells`, `parityWhiteCells_eq_lineCells` | Arbitrary sets of the stated parity counts, including exact agreement with the homogeneous-cell construction. |
| S14 | `LowerBound`: `H_le_t` | All positive `q`. |
| S15 | `SmallBoards.H_one`, `H_two`; `Values.H_three` … `H_twenty` | All 20 table entries match. The optional table is outside Main's import closure. |
| S16 | `UB/ProfileAlgebra`: `profile_identities`, `profile_cross_term_abs_le` | Real algebra and absolute-value bound; `1+ξη` is an algebraic rewrite. |
| S17 | `UB/ProfileAlgebra`: `profile_min_le_kappa_s17` | Whole real domain, including mixed sums and complemented/swapped case. |
| S18 | `UB/ProfileAlgebra`: `profile_min_le_floor_s18`, `H_le_floor_s18` | Nonnegative natural-floor form. |
| S19 | `UB/ProfileAlgebra`: `H_ge_profile_floor_sq`, `floor_sq_cast_lower`, `H_lower_s19` | Floor/ceil construction, quarter-unit loss and two admissible choices. |
| S20 | `UB/ProfileAlgebra`: `kappa_escape_margin`, `gamma_lt_half`, `escape_quadratic_pos`, `H_escape_s20` | Exact comparisons and strict escape at `q ≥ 64`. |
| S21 | `UB/Configuration`: `card_parityClass`, `outerCount`, `normalizedProfile_range` | Eight counts in `0..q`, rational normalization by half-order. |
| S22 | `UB/Incidence`: five `*_bijective` lemmas, `diagonalAntidiagonal_mem_range_iff`, `card_diagonalAntidiagonalFibre_of_image` | Complete even incidence; odd D/A part outside. |
| S23 | `UB/Symmetry`: `budget_or_complement` | Even board budget `4q = 2n`, with army exchange. |
| S24 | `UB/BlockMoments`: `card_blockCells`, `atomFrequency_normalization`, four `atomCount_*_marginal` lemmas | Exactly `q²` cells per block and the four densities. |
| S25 | `UB/BlockMoments`: five `atomCount_*_pair` lemmas | All five determinant-one pairs; no per-block D/A claim. |
| S26 | `UB/BlockMoments`: `aggregateDAAtomCount_eq` | Aggregate count `2*d_e*a_e`, including even `q`. |
| S27 | `UB/ConfigurationMoments`: `configurationWeights_satisfiesMoments`, `configurationWeights_blackTotal`, `configurationWeights_whiteTotal` | All 42 equations and exact objective scaling. `MomentModel` checks dimensions. |
| S28 | `UB/Symmetry`: configuration transforms, `outerCount_*`, `objectiveEquivalent_*` | Complement, unit translations, transpose and reflection are proved board operations. |
| S29 | `UB/Symmetry`: `exists_chamber` | Ordered sequence preserves previous sorting and total budget. |
| S30 | `UB/CertificateCore`: four `mccormick_*`; `UB/ConfigurationBridge`: product-box bounds | All signs match; product endpoint bounds require nonnegative box. |
| S31 | `UB/LPModel`, `UB/DualLeaf.LeafFeasible` | 8+22+64+1 variables, 42 equalities, 7+88 inequalities over `ℚ`. |
| S32 | `UB/ConfigurationBridge`: `configurationLPVector_leafFeasible` | Feasible point constructed from the actual configuration, not a hypothesis. |
| S33 | `UB/CertificateCore`, `UB/DualLeaf`, `UB/SparseListDualLeaf`, `UB/ScaledIntDualLeaf/Sound` | Rational dual bound; positive scale and denominator checked before dividing. |
| S34 | `UB/BranchCertificate`, `UB/LeafChecks`, `UB/Generated/Even/*` | Bottom-up checked split/leaf obligations; the module/proof graph prevents circular evidence. |
| S35 | `UB/CertificateCore`: `CoverTree.locate`; `UB/BranchCertificate`: `splitNodeOK_coverTree` | Both closed children cover each rational parent point. |
| S36 | `UB/Generated/Even/C527LeafDispatcher`: `checked_tree`; `UB/LargeOrderCertified.global_tree` | Exact full-cube root, threshold `527/1000`, only canonical plaid exceptions. |
| S37 | `UB/Generated/Even/CoreLeafDispatcher`: `checked_tree`; `UB/LargeOrderCertified.local_tree` | Exact `N` root, core alternatives checked throughout exceptional boxes. |
| S38 | `UB/CertificateConsequences`: `threshold_contradicts_H`, `configuration_escape_of_certificates` | `q ≥ 64`, objective at least `H` rules out every safe threshold leaf. |
| S39 | `UB/CertificateCore`: `support_weighted_dual_sound_indicator`, `support_dual_sound_indicator` | Weighted inequality from nonnegative atom weights and moment equations; `0 ≤ θ ≤ 1` is needed only for the minimum consequence. |
| S40 | `UB/RecoveredFiniteCutSupport/Cuts_*.lean`, `CountBridge`, `Aggregate.cutSound` | All 76 used finite cuts formalized, plus the separate large cuts. Not all 760 reference cuts. |
| S41 | `UB/SupportCuts`, `UB/LargeOrderFinish`: individual black/white support bounds and polynomial identities | Both paper inequalities are exported; the finish keeps the minimum consequences. |
| S42 | `UB/LargeOrderAlgebra.Local`, `UB/LargeOrderConfiguration.localOfConfiguration`, `UB/LargeOrderFinish.local_min_le_H` | Correct coordinate assignment and exchanged column counts `(u,R,C,v)`. |
| S43 | `UB/LargeOrderConfiguration.localOfConfiguration_core`, `UB/LargeOrderFinish.local_neighborhood_transport` | Core transported exactly; the finish needs only a subset of `N` and no additional chamber assumption. |
| S44 | `UB/LargeOrderAlgebra.Local.basic` | `α ≥ 43q/100`, `β ≥ 11q/25`, both strict defect gaps. |
| S45 | `UB/LargeOrderAlgebra.Local.defect_dichotomy` | Uses squared differences to bound `2Q`; valid disjunction. |
| S46 | `UB/LargeOrderFinish.configuration_local_finish`, first easy branch | `Q ≤ βζ` gives `F_B ≤ X = min(X,Y) ≤ H`. |
| S47 | `UB/LargeOrderAlgebra.Local.two_gh_le_q_zeta_over_fifty`, `FB_le_X_add_two_ef` | Correct charge against `βζ`. |
| S48 | `UB/LargeOrderFinish`: `switch_losses_average`, `switched_coordinate_bounds`, `configuration_switched_profiles_H` | Four products equal `2ef`; all modified natural coordinates stay within `q`. |
| S49 | `UB/LargeOrderAlgebra.Local.large_defect_affordable` | Uses strict `Q > βζ` and core to pay the average loss. |
| S50 | `UB/LargeOrderFinish.s50_switch_exists`, first hard branch of `configuration_local_finish` | Chosen loss is at most the average; matching valid `H` witness closes the bound. |
| S51 | `UB/LargeOrderAlgebra.Local.gh_pos_of_Q_gt_alpha_delta`; `UB/LargeOrderFinish.configuration_zeta_ge_two` | Easy branch plus the actual natural-defect positivity argument. |
| S52 | `UB/LargeOrderAlgebra.Local.min_FB_FW_le_average_sub_beta_minus_two` | Same penalty bound; factors `(ζ-2)(β-ζ-2) ≥ 0` instead of differentiating. |
| S53 | `UB/LargeOrderFinish.s53_average_le_kappa` | Uses `Y ≤ X` and row/column total bounds from `N`. |
| S54 | `UB/LargeOrderFinish.s54_numeric`, `s54_finish` | Exact square-root comparison at 130; correct `9/4` deficit. |
| S55 | `UB/LargeOrderCertified.large_order_bound` | Both trees supplied; all positive even orders from `q=130` upward. |
| S56 | `UB/FiniteLattice`: propagation, `NoDiagonal`, corner/interval/eval checks, integer split | Five canonical rows, full cube, mathematical `Int`; real-box/C++ claims not formalized. |
| S57 | `UB/FiniteLattice.validateCompleteBool_sound`; `UB/FiniteCertificateConsequences.finite_order_bound_of_tree_at` | Coverage plus sound cuts implies `12m ≤ 12b+6`, hence `m ≤ b ≤ H`. |
| S58 | `UB/EncodedFiniteCertificate`, cached/fast equivalences, `UB/Generated/Finite/Q*.lean` | Complete checked action data. Threshold uses an explicit lower witness, not trusted external `H`. |
| S59 | `UB/Generated/FiniteRange.finite_range_bound` | All 127 orders `3..129`, stronger range than the paper's ladder. |
| S60 | `SmallBoards.t_two` | Every cell pair on the 2-torus shares a line; the finite lemma uses kernel decision. |
| S61 | `SmallBoards.t_four` | Translate one queen to the origin; check the four triples among the four cells available to the other army. Uses kernel decisions and the lower bound, not the paper's triple identity. |
| S62 | No corresponding Lean lemma | Triple identity outside the even proof. |
| S63 | No corresponding Lean proof | Profile/orbit/completion search reduction outside. |
| S64 | `UB/Generated/Finite/Q004`, `Q006`, `Q007`, `Q008`, `Q009` | Upper bounds direct; equality by `H_le_t`. The paper's sweep methods are outside. |
| S65 | No corresponding Lean proof | Odd witnesses and odd upper bounds outside. |
| S66 | `UB/Assembly`, `Main.upperBoundStatement`, `Main.evenTorusTheorem` | `1,2`; `3..129`; `≥130` cover every positive `q` without overlap issues or gaps. |

## Generated data and implementation layers

The generated branch sources have exactly one `tree_i` declaration for each
index `0..6928` (C527) and `0..4422` (Core). Their two dispatchers close the
root proofs. Scaled leaf data passes through `Coefficients`,
`RawCoefficients`, `ResidualScale`, `ResidualScaleFinal`, `EndpointScale`,
`BoundScale`, and `Sound` under `UB/ScaledIntDualLeaf/`: the integer
inequality coefficients scale by `S`, right-hand sides by `S²`, and the final
bound by `S³`. Positivity of `S` and the requested denominator is a checked
premise, so clearing denominators cannot reverse an inequality.

For finite orders there are 127 modules, each with the same three
declarations: `certificate_accepted`, `threshold_le_H`, and `upper_bound`.
Seven (`Q003`–`Q009`) use `acceptedCached`; 120 (`Q010`–`Q129`) use
`acceptedFast`. Both have proved equality to the specification checker
(`FastFiniteChecker.acceptedFast_eq`). `FastFiniteTables` proves the
cut/domain tables equal; `SparseCutEval` and `FastCutEval` preserve polynomial
evaluation; `ReducedCornerCheck` and `SupportReducedCornerCheck` remove
duplicate/unused coordinates; `IndependentCornerMax`, `IndependentCornerCheck`,
`IndependentCutMasks` and the fast adapters justify selecting independent
coordinates by their slopes. The independence mask is proved for each cut, not
trusted because the generator emitted it.

The support duals 609 and 559 of `UB/SupportCuts.lean` are transcribed from
the paper's certified cut library; their 64 columnwise support inequalities
are re-proved in the kernel and their expansions to the paper's polynomials
`F_B` and `F_W` are `ring` identities, so the transcription is checked rather
than trusted.

## Outside the formalization

Not formalized, and not claimed by any exported statement: the real optimum
`OPT₄₂(x)` of `def:OPT` with its compactness and attainment; the odd-order
results `thm:t15`, `thm:t17` and the search reductions `lem:searchsound`,
`lem:evensweep`; the triple identity `lem:triple`; divisor lifting `prop:lift`;
the plaid comparisons of `rem:plaid16` beyond the displayed `H` values; the
verification-program statistics of `rem:certverify`; and the all-orders
plaid-plus-two conjecture, which is open in the paper as well.
