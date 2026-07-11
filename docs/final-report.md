# Final Formalization Report

Date: 2026-07-11

## Outcome

This project reconstructs the central mathematics of Barenco et al.,
“Elementary Gates for Quantum Computation,” as a reusable Lean 4/mathlib
library. It does not transcribe circuit pictures as assertions. The completed
modules provide certified finite-register semantics, literal circuit syntax,
several inequivalent phase/measurement relations, syntax-derived resource
models, exact and approximate multi-control constructions, a rigorous lower
bound, and exact positive-width universality.

The headline result is
`Barenco.Universality.exact_oneQubitCNOT_universality`: for every register of
positive width and every certified unitary on that register, it constructs a
literal circuit of arbitrary one-qubit gates and CNOTs, proves exact evaluator
equality, and supplies an accepted finite cost. Width one has a direct one-gate
implementation. Exact width-zero universality is false: the state space is
one-dimensional and has arbitrary `U(1)` phases, while the restricted circuit
syntax `LowerBounds.BasicCircuit 0` has no legal primitive and reaches only
identity. General `Circuit 0` permits unclassified semantic nodes, but those are
outside the one-qubit/CNOT generator language and rejected by its cost model.

For the library's deliberately non-pruning synthesis schedule, writing

`B(k) = (k+1)^2 * 4^k`

for width `k+1`, the literal syntax satisfies

`2 * B(k) <= exactSynthesisCost k U <= 112 * B(k)`.

This yields a machine-checked `Theta(B(k))` theorem for that fixed schedule. It
is not a lower bound on arbitrary circuits and is not an optimal-synthesis
claim.

## Reproducible Project

- Lean: `leanprover/lean4:v4.31.0`
- mathlib: `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`
- Lake library target: `Barenco`
- Public umbrella import: `import Barenco`
- Project Lean files below `Barenco/`: 145, plus `Barenco.lean`
- Maintained kernel axiom checks: 480

The pinned inputs are in `lean-toolchain`, `lakefile.toml`, and
`lake-manifest.json`.

## Architecture

| Area | Main modules | Purpose |
|---|---|---|
| Finite semantics | `Basic`, `Semantics`, `Controlled` | qubit bases, certified unitaries, reindexing, local and controlled gates |
| Ordered two-wire gates | `TwoWire/Layout`, `TwoWire/Semantics`, `TwoWire/ControlledBridges`, `TwoWire/Circuit` | certified arbitrary-`U(4)` embeddings, spectator/orientation laws, trusted syntax, adjoints, and model-specific costs |
| Circuit syntax | `Circuit`, `Cost` | chronological primitive lists, exact evaluation, support, gate counts, named partial cost models |
| Exact fusion input | `Optimization/FusionIR`, `Optimization/FusionResources` | closed payload-preserving one-/two-wire syntax, exact lowering, explicit opaque barriers, and syntax-derived model-specific resources |
| Exact normalization | `Optimization/NormalizeCore`, `FusionLaws`, `FusionCommutation`, `Normalize`, `SymbolicCancellation`, `SymbolicExpose`, `SymbolicAdjoint`, `SymbolicSweep`, `SymbolicAvoids`, `NormalizeResources` | terminating exact rewrite policies, target-directed exposure, formal adjoints, certified wire schedules, cancellation across wire-avoiding syntax, barrier-separated programs, ordered-CNOT preservation, and conditional partial-cost nonincrease |
| Equivalence and error | `Equivalence/*` | exact global phase, basis-dependent phase, basis behavior, channel/all-measurement equality, L2 operator distance, event-probability bounds |
| One-qubit algebra | `OneQubit/*` | row/column convention bridge, Euler forms, Pauli/rotation identities, ABC factors, exact and coherent roots |
| Controlled gates | `ControlledCircuit/*` | target-block semantics, general and special controlled-U decompositions, controlled scalar phases, explicit expansions |
| Three-qubit gates | `ThreeQubit/*` | Lemma 6.1, exact primitive expansion, signed relative-phase Toffoli circuits, and the explicit three-`U(4)` Section 8 implementation |
| Multi-control | `MultiControl/*`, especially `Corollary74CompleteMergers` and `Corollary74MergerResources` | raw and coherently merged Gray circuits, dirty-wire ladders, four-block and recursive constructions, complete relative-phase Corollary 7.4 merging, clean ancillas, exact resources |
| Approximation | `MultiControl/Approximate*`, `ApproximationResources` | truncated coherent roots, exact residual formula, operator/event error, capacity-aware synthesis |
| Lower bounds | `LowerBounds/*` | restricted basic syntax, interaction graph, cut factorization, nonscalar obstruction, `n-1` CNOT lower bound |
| Exact universality | `Universality/*` | Givens elimination, finite reindex bridge, affine two-level circuits, diagonal synthesis, circuit-product chronology, exact assembly |
| Aggregate resources | `Universality/*Resources` | exact schedule lengths, quadratic component bounds, Section 8 pricing, finite and asymptotic synthesis bounds |

Files named `*Examples.lean`, including `Universality/ResourceExamples.lean` and
`MultiControl/Corollary74MergerExamples.lean`, are diagnostics and are
intentionally not imported by the public root.

## Main Public APIs

| API | Role |
|---|---|
| `Basis n`, `Gate n`, `UnitaryGate n`, `QubitUnitary` | finite qubit-state and certified-unitary types |
| `localUnitary`, `positiveControlledUnitary`, `cnotUnitary` | exact embedded gate semantics |
| `OrderedWirePair`, `twoWireUnitary`, `Primitive.twoQubit` | exact ordered arbitrary-two-wire semantics and trusted literal syntax |
| `Primitive`, `Circuit`, `Circuit.eval` | trusted primitive metadata and head-first chronological circuit syntax |
| `Circuit.gateCount`, `Circuit.kindCount`, `Circuit.touchedSupport`, `Circuit.cost` | syntax-derived resources |
| `Optimization.FusionPrimitive`, `FusionCircuit`, `FusionProgram` | optimizer-visible local payloads, exact compilation, and a lossless barrier path for unsupported existing syntax |
| `FusionCircuit.eval_lower`, `FusionCircuit.cost_lower`, `FusionProgram.lower_barriers` | exact semantic/resource compiler contracts |
| `normalizeEarly`, `section8Normalize` | exact visible passes for the one-qubit/CNOT-preserving and arbitrary-two-qubit policies |
| `normalizeEarlyProgram`, `section8NormalizeProgram` | exact maximal-run normalization with verbatim hard barriers |
| `SymbolicCircuit.normalize`, `SymbolicCircuit.normalizeAtWire`, `AcceptedCostNonincrease` | executable free-group inverse cancellation, certified target-directed exposure, and honest conditional partial-cost comparison |
| `CostModel.oneQubitCNOT`, `CostModel.arbitraryTwoQubit` | distinct Sections 3--7 and Section 8 cost conventions |
| `GlobalPhaseEq`, `BasisPhaseEq`, `SameBasisBehavior`, `BasisMeasurementEq`, `ChannelEq` | deliberately distinct relaxed target relations |
| `operatorDistance`, `eventProbability` | L2 induced operator distance and finite computational-basis event probabilities |
| `unitaryRoot`, `powerTwoRoot` | exact arbitrary roots and a coherent power-of-two root sequence |
| `controlledU2Circuit`, `doubleControlledRootCircuit`, `grayControlledCircuit` | selected controlled and multi-controlled circuits |
| `relativePhaseToffoliThreeGateCircuit`, `section8Normalize_relativePhaseToffoliAFusionCircuit` | named three-`U(4)` relative-phase Toffoli implementation and exact normalizer-output certificate |
| `eval_relativePhaseToffoliThreeGateCircuit`, `relativePhaseToffoliThreeGateCircuit_arbitraryTwoQubitCost` | exact signed-unitary evaluator and syntax-derived Section 8 cost three |
| `relativePhaseToffoliThreeGateCircuit_ne_toffoli`, `relativePhaseToffoliThreeGateCircuit_not_globalPhaseEq_toffoli` | explicit separation from exact and global-phase Toffoli |
| `mergedGrayControlledViaRootSymbolicCircuit`, `mergedGrayControlledViaRootNormalForm` | executable coherent Gray boundary merger and its exact emitted syntax |
| `eval_mergedGrayControlledCircuit`, `mergedGrayControlledFusionCircuit_profile` | exact arbitrary-register controlled-unitary semantics and syntax-derived post-merger counts |
| `completeMergedRelativeCorollary74SymbolicCircuit`, `completeMergedRelativeCorollary74Circuit` | transparent complete Corollary 7.4 merger and trusted lowering |
| `eval_completeMergedRelativeCorollary74Circuit`, `completeMergedRelativeCorollary74Circuit_basisAction_and_restoration` | exact full-register controlled-X semantics and explicit basis-wire restoration |
| `balancedCompleteMergedRelativeCorollary74Circuit_oneQubitCount`, `balancedCompleteMergedRelativeCorollary74Circuit_cnotCount`, `balancedCompleteMergedRelativeCorollary74Circuit_gateCount` | exact `(24n−102,24n−100,48n−202)` balanced profile for every `n≥7` |
| `cleanAncillaCircuit`, `expandedCleanAncillaCircuit_oneCleanAncillaContract`, `eval_expandedCleanAncillaCircuit_factorization` | clean-zero construction, structural one-ancilla contract, and semantic restoration/factorization |
| `decomposeFiniteUnitary` | arbitrary finite-index exact two-level decomposition with diagonal residual |
| `twoLevelCircuit`, `diagonalCircuit`, `exactSynthesisCircuit` | literal no-ancilla positive-width synthesis layers |
| `eval_exactSynthesisCircuit` | exact evaluator equality for the assembled circuit |
| `exactSynthesisCircuit_oneQubitCNOTCost`, `exactSynthesisCircuit_gateCount` | exact accepted cost and literal primitive count |
| `exactSynthesisCost_bounds`, `exactSynthesisCost_isTheta_fixedSchedule` | finite `2/112` sandwich and carefully scoped fixed-schedule asymptotics |
| `fullyControlled_cnotCount_lowerBound` | strengthened exact same-register lower bound for nonscalar controlled targets |

## Mathematical and Circuit Conventions

- `Basis n` is `Fin n -> Bool`. Wire indices are values of `Fin n`; no endianness
  is inferred from decimal labels.
- A circuit list is chronological: the head executes first. Under standard
  column-vector semantics, later gates multiply on the left.
- The paper's displayed matrices use row action. `fromPaper` transposes them into
  the library's column convention, reversing product order where required.
- Small gate identities are not silently promoted to larger registers. Local,
  target-block, controlled, reindex, spectator, and auxiliary-wire behavior is
  proved explicitly.
- Exact equality, one global scalar phase, basis-state-dependent phase, classical
  basis behavior, basis measurement equality, and all-measurement/channel equality
  are separate relations.
- Approximation uses mathlib's L2 induced matrix operator norm, not Frobenius or an
  entrywise norm. Operator error is connected to state error and finite
  computational-basis event probabilities by explicit inequalities.
- Resource theorems inspect circuit syntax. A matrix equality alone never supplies
  a gate count.
- `CostModel.oneQubitCNOT` accepts only one-qubit and CNOT nodes at unit cost.
  `CostModel.arbitraryTwoQubit` additionally accepts certified controlled-one-qubit
  nodes with zero or one control and the certified arbitrary-two-qubit metadata
  kind. It rejects larger controlled macros, Toffoli macros, and unclassified
  nodes.
- Repricing the same literal syntax does not merge gates. Merging requires a new
  circuit and an evaluator-preservation theorem. The relative-phase Toffoli merger
  meets this requirement with a distinct named three-node circuit; the original A
  and B source lists remain seven-node syntax. The Gray merger likewise counts
  only the exact normal form emitted by its executable boundarywise pass, never
  the semantically equal raw list.

See `docs/conventions.md` for the full specification.

## Circuit-Diagram Coverage

The repository source contains exactly sixteen extracted figures. Thirteen have
named circuit syntax and compiled semantics; the controlled-Z symmetry figure is
fully proved at its intended semantic-equality layer but has no separate circuit
wrapper or resource claim; the basic-notation figure is represented by the core
infrastructure; and the six-`U(4)` figure remains unresolved.

| # | Source figure | Final classification | Main Lean evidence |
|---:|---|---|---|
| 1 | `notation-basic-gates.png` | notation formalized; no circuit identity to prove | `Primitive`, `Circuit`, `localUnitary`, `positiveControlledUnitary`, `cnotUnitary` |
| 2 | `lemma-5-1-controlled-su2.png` | fully reconstructed, exact arbitrary-register equality and converse, exact cost | `controlledABCCircuit`, `eval_controlledABCCircuit_eq_iff`, `controlledSU2Circuit_correct_iff` |
| 3 | `lemma-5-2-controlled-phase.png` | fully reconstructed; controlled scalar is an exact local diagonal gate on the control | `controlledScalarUnitary_eq_localControl`, `eval_controlledPhaseCircuit` |
| 4 | `lemma-5-4-two-xor-special-case.png` | fully reconstructed with corrected iff classification and scalar endpoints | `eval_twoCNOTCircuit_eq_iff`, `twoCNOTFamily_iff` |
| 5 | `lemma-5-5-one-xor-special-case.png` | fully reconstructed with the omitted converse and phase normalization | `eval_oneCNOTCircuit_eq_iff`, `oneCNOTFamily_iff` |
| 6 | `controlled-z-symmetry.png` | fully reconstructed as exact arbitrary-register wire-swap equality | `controlledZRaw_swap`, `controlledZUnitary_swap` |
| 7 | `lemma-6-1-controlled-controlled-u.png` | fully reconstructed, including root selection, both inverse orders, spectators, restoration, and counts | `eval_doubleControlledRootCircuit`, expansion/cost theorems |
| 8 | `relative-phase-toffoli-a.png` | fully reconstructed as its exact signed unitary and `BasisPhaseEq` to Toffoli; source syntax costs seven, while a separate exactly evaluator-equivalent three-`U(4)` grouping has Section 8 cost three | `eval_relativePhaseToffoliACircuit`, `section8Normalize_relativePhaseToffoliAFusionCircuit`, `eval_relativePhaseToffoliThreeGateCircuit`, basis-action/phase/count/cost theorems |
| 9 | `relative-phase-toffoli-b.png` | fully reconstructed and proved exactly equal to the A circuit; its literal syntax costs seven under Section 8, and no separate B-normalizer-output claim is made | `eval_relativePhaseToffoliBCircuit`, `eval_relativePhaseToffoliACircuit_eq_BCircuit` |
| 10 | `four-bit-gray-code-construction.png` | fully reconstructed as the displayed 13-node chronology on arbitrary ambient width | `fourBitGrayCircuit`, `eval_fourBitGrayCircuit`, exact kind/cost theorems |
| 11 | `lemma-7-2-linear-multi-control.png` | fully reconstructed; dirty wires and spectators restored, exact Toffoli count | `inwardLadderCircuit`, `eval_inwardLadderCircuit`, support/resource theorems |
| 12 | `lemma-7-3-four-block-construction.png` | fully reconstructed; “by inspection” replaced by Boolean case algebra and exact full-register equality | `fourBlockCircuit`, `fourBlockUpdate_eq_update`, `eval_fourBlockCircuit` |
| 13 | `lemma-7-5-quadratic-general-control.png` | fully reconstructed through literal recursive primitive syntax with explicit base cases | `recursiveViaSquareCircuit`, `recursivePrimitiveCircuit`, evaluator/resource theorems |
| 14 | `lemma-7-9-linear-su2-control.png` | fully reconstructed and expanded to one-qubit/CNOT syntax | `linearABCCircuit`, `linearSU2Circuit`, `expandedLinearSU2Circuit` |
| 15 | `lemma-7-11-one-fixed-bit.png` | corrected and fully reconstructed on the clean-zero subspace; output closure and factorization prove restoration | `cleanAncillaCircuit`, clean-subspace evaluator and factorization theorems |
| 16 | `six-two-bit-gates-u8.png` | unresolved; diagram and parameter count do not prove surjectivity onto `U(8)` | no exported universality theorem; see C-012 |

The textual Section 8 repeated Gray walk is not one of the sixteen extracted
figures. Its path combinatorics, mixed-polarity adjacent block, endpoint
orientation, and restoration ingredients are proved, but the complete
`2m-3`-macro walk is not a named circuit. The main exact synthesizer instead uses
a proved affine X/CNOT endpoint normalization.

## Resource Results

| Construction or claim | Final result |
|---|---|
| Section 5 general controlled `U(2)` | exact constructed cost 6: four one-qubit and two CNOT gates |
| Section 5 special topologies | exact costs 4 and 3, with iff family classifications |
| Lemma 6.1 | exact five-node at-most-two-wire macro cost under Section 8; exact expansion cost 16 under one-qubit/CNOT |
| Relative-phase Toffoli | both source circuits remain seven nodes; the named A-derived merged syntax has exactly three certified `U(4)` nodes, exact full-register equality to the signed unitary, Section 8 cost `some 3`, and one-qubit/CNOT cost `none`; this is a constructive upper count, not a minimum |
| Four-bit Gray circuit | exact Section 8 cost 13: seven singly controlled roots and six CNOTs |
| General Gray expansion and merger | for `m>=1` controls, exact raw profile `4(2^m-1)` one-qubit, `3*2^m-4` CNOT, total `7*2^m-8`; the coherent executable merger emits exactly `2*2^m` one-qubit, the same `3*2^m-4` CNOTs, and total/cost `5*2^m-4`, verifying the paper's post-merger count as a constructive upper bound and yielding a syntax-linked fixed-construction `Theta(2^m)` theorem |
| Lemma 7.2 dirty ladder | for `m>=3` controls with stated ambient capacity, exact `4(m-2)` Toffoli occurrences and restoration |
| Corollary 7.4 | for logical width `n>=7`, exact macro total `8(n-5)`; selected raw expansion `32n-144` one-qubit + `24n-100` CNOT = `56n-244`; complete exact merger `24n-102` one-qubit + `24n-100` CNOT = `48n-202`, with both named costs accepted; the paper's `48n-204` is not recovered by this construction and is not refuted |
| Recursive exact multi-control | for width `n>=7`, with depth offset `d=n-7`: exact total `56d^2+364d+440`; construction-specific `IsBigOWith 56` in width |
| Lemma 7.7 lower bound | exact same-register implementation of a nonscalar fully controlled target needs at least `n-1` CNOTs, hence at least that many total accepted gates |
| Approximate multi-control | for width `n>=7` and `epsilon>0`, exact truncated component formulas, capacity-aware exact fallback, and operator/event error at most epsilon; the explicit logarithmic-regime bound assumes `epsilon<=1`; no optimal `Theta(n log(1/epsilon))` claim |
| Linear controlled SU(2) | for width `n>=7`, exact profile `(64n-279, 48n-194, 112n-473)` and construction-specific `O(n)` |
| One-clean-wire controlled U | for width `n>=7`, exact profile `(64n-284, 48n-198, 112n-482)` and construction-specific `O(n)` |
| General exact synthesis | for width `n=k+1>=1`, exact factor count `choose(2^n,2)`, exact diagonal-pattern count `2^(n-1)`, finite `2/112` benchmark sandwich, and fixed-schedule `Theta(B(k))` for `B(k)=(k+1)^2*4^k` |
| Section 8 numerical minima | excluded: the paper reports numerical evidence, not proofs |
| Six-`U(4)` and dimension lower claims | unresolved/excluded: no surjectivity or manifold/image-dimension proof |

All exact counts above are attached to named circuit syntax. Every `O` or `Theta`
result has a preceding finite natural-number inequality or exact recurrence.

## Corrections and Material Differences

The complete log contains 37 entries in `docs/corrections.md`. The most important
families are:

- **Matrix and execution conventions:** the source uses row action while the
  library uses standard columns; chronology and product reversal are explicit.
- **Controlled phase:** a scalar phase ceases to be globally ignorable when it is
  controlled; it becomes an exact diagonal gate on the control wire.
- **One-qubit degeneracies:** Euler choices and determinant normalization need
  explicit branches; the sentence excluding every `Rx(theta)` from the Lemma 5.4
  family has scalar endpoint exceptions.
- **Root assumptions:** square and iterated unitary roots are chosen and certified;
  inverse order and coherent approximation branches are not assumed informally.
- **Corollary 7.4:** the printed split fails at the smallest legal width and a
  remainder formula is arithmetically wrong. The repaired partition has four exact
  and `8n−44` relative occurrences. Two exact dirty-wire word fusions and one
  two-node formal inverse-pair cancellation yield the checked `48n−202` output,
  two gates above the printed number.
- **Relative phase:** basis-dependent signs are not global phase. Several
  cancellation arguments require an adjoint implementation, and controlled `W`
  carries its minus sign on a precisely identified input.
- **Auxiliary wires:** clean/dirty hypotheses, starting value, arbitrary spectator
  state, output closure, and restoration without residual entanglement are explicit.
- **Approximation:** the root estimate needs one shared principal spectral branch;
  all epsilon/capacity regimes are handled by a checked selector and exact fallback.
- **Lower bounds:** the rigorous invariant is CNOT connectivity across every cut,
  with an explicit tensor-factorization proof and a nonscalar target assumption.
- **Exact universality boundary:** zero-qubit unitaries form `U(1)`, while the
  restricted zero-wire circuit language reaches only identity.
- **Two-level implementation:** the source's final Gray edge can reverse the local
  block orientation. The main library uses a cleaner affine normalization and
  therefore has a different, stronger resource upper bound.
- **Asymptotics:** fixed-algorithm lower bounds caused by non-pruning are not target
  hardness. The exported `Theta` name says `fixedSchedule` and carries no
  optimality interpretation.
- **Section 8 model:** a singly controlled one-qubit macro is a certified two-wire
  operation and must be accepted; larger controlled macros remain rejected.
- **Section 8 relative-phase merger:** the source's omitted grouping is reconstructed
  as a distinct three-`U(4)` circuit with exact evaluator preservation. Its relation
  to Toffoli is the explicit `101` input-column `BasisPhaseEq`; exact and global-
  phase equality are formally refuted, and the count is not a minimality theorem.
- **General Gray merger:** independently chosen decompositions of `V` and `V⁻¹`
  do not justify inverse-factor cancellation. The repaired construction selects
  one factor package, uses literal adjoints for alternating Gray signs, and proves
  every executable boundary normalization, the emitted normal form, exact
  evaluator equality, CNOT chronology, and the printed count.
- **Historical efficiency:** “most efficient known” is time-dependent comparative
  context without a specified exhaustive circuit class or proof, not a formal
  optimality claim.

## Unresolved, Partial, and Intentionally Excluded Material

- The source-row lexicographic `Fin (2^n)` presentation of the initial controlled
  matrix definitions is not duplicated as a paper-shaped wrapper. The stronger
  arbitrary-target/control-set basis semantics is proved instead.
- The statement that “almost any” fixed controlled gate densely generates is
  cited by the paper from other work and is intentionally excluded. This library
  proves exact generation with arbitrary one-qubit primitives, not finite-set
  density or compilation.
- The paper's optimized Corollary 7.4 count `48n-204` is not obtained by the
  explicit checked normalization. The library exports both the raw `56n-244`
  expansion and an exact complete merger of cost `48n-202`. The latter's
  two-gate gap is a theorem about that named output, not a lower bound or a
  refutation of the paper's claimed upper bound.
- Numerical minimality of the five-, three-, and thirteen-operation Section 8
  circuits is not theoremized.
- The six-`U(4)` architecture for arbitrary `U(8)` is unresolved. Matching
  parameter dimension does not prove the multiplication map is surjective.
- The parameter-increment heuristic and `(4^n-3n-1)/9` lower conjecture are
  excluded pending a rigorous smooth/image-dimension argument.
- The paper's complete repeated Gray-walk `2m-3` syntax is partial; the main
  library uses the exact affine replacement.
- The historical claim that the Gray construction was “most efficient known” is
  intentionally excluded: it is time-dependent and has no specified exhaustive
  circuit class or proof. The separate post-merger count itself is now verified
  for the named coherent syntax.
- A physical POVM API is outside scope. The approximation result covers every
  finite computational-basis event. Separately, algebraic `AllMeasurementEq`
  quantifies over arbitrary matrices/effects and is equivalent to `ChannelEq`;
  the computational-basis rank-one probability relation is a proved consequence,
  not a converse physical-model theorem.
- The trusted `Primitive.twoQubit` constructor is now exported and its singleton
  syntax has proved exact semantics and Section 8 cost one. Existing generic
  primitives still do not expose recoverable local payloads; optimizer-visible
  payload retention belongs to the separate fusion IR rather than metadata
  inspection.

## Build and Axiom Audit

Stage 12 final verification before this report recorded:

- focused public/resource/diagnostic/audit build: 3,587 jobs;
- strict warning-as-error compilation of the public root, audit, and diagnostics;
- trust-zero warning-as-error compilation of the same;
- two consecutive full `lake build` runs: 3,585 jobs each;
- no `sorry`, `admit`, `by?`, custom `axiom`, `opaque`, `native_decide`, or
  `bv_decide` in project Lean sources;
- `git diff --check` clean;
- 319 maintained `#print axioms` checks at that Goal 1 release boundary.

The final Stage 13 release audit then ran `lake clean` followed by a build from
the empty project build tree; the clean build succeeded with 3,593 jobs. Strict
and trust-zero warning-as-error compilation of both the public root and maintained
axiom audit passed again afterward.

Goal 2 Stages 2–4 subsequently added certified ordered two-wire embeddings,
trusted arbitrary-two-qubit syntax, a separate closed fusion IR, exact
visible/mixed lowering, syntax-derived costs, and transparent selected
controlled-U, relative-phase, and Gray inputs. Stage 5 added the executable exact
normalization policies and symbolic inverse-provenance layer. Stage 6 reconstructed
the distinct three-`U(4)` relative-phase Toffoli output and its exact phase scope.
Stage 7 added target-directed symbolic exposure and the coherent Gray streaming
merger: the executable output is proved equal to its explicit normal form, exactly
equal to the established arbitrary-register evaluator, and counted from syntax.

Stage 8 added transparent selected exact-Toffoli expansion, formal symbolic
adjoints and wire-avoidance cancellation, optimizer-visible relative ladders, and
the complete corrected Corollary 7.4 merger. Two dirty-wire word fusions save one
node each, and deletion of a formal `A⁻¹/A` pair across final-target-avoiding syntax
saves two. The output preserves exact full-register semantics, restoration, and
the complete coherent mixed raw CNOT trace and has balanced profile
`(24n−102,24n−100,48n−202)` for every `n≥7`. Root-excluded diagnostics confirm
widths seven, eight, and nine as `(66,68,134)`, `(90,92,182)`, and
`(114,116,230)`. The existing recursive primitive construction still substitutes
the raw Corollary circuit, so its recurrence and quadratic counts remain unchanged.

The Stage 7 focused/adjacent/public/audit sweep passed with 3,608 jobs, all twelve
direct warning-as-error and trust-zero checks passed, and the integrated full build
passed with 3,606 jobs. Twenty-one representative Stage 7 checks raised the
maintained audit from 436 to 457. Stage 8 adds another 23 maintained checks, for
480 total: 21 use only `propext`, `Classical.choice`, and `Quot.sound`, while the
two structural symbolic-adjoint count/trace results use only `propext` and
`Quot.sound`. The audit source and documentation table both contain 480 entries;
the public tree contains 145 Lean files, and the Corollary merger diagnostics
remain root-excluded. The integrated Stage 8 resource/diagnostic/public/audit
build completed successfully with 3,617 jobs.

Every maintained headline result uses only the standard foundations reported by
Lean/mathlib: `propext`, `Classical.choice`, and `Quot.sound` (some arithmetic
results use a strict subset). There is no project-specific axiom.

Exact commands and declaration-by-declaration results are recorded in
`docs/axiom-audit.md`.

## Guidance for Future Projects

1. Import `Barenco` for the stable public surface. Import narrow modules such as
   `Barenco.Universality.ExactSynthesis` or
   `Barenco.Equivalence.OperatorNorm` when build isolation matters.
2. Reuse `UnitaryGate n` for certified semantics and `Circuit n` for resources.
   Do not use a semantic matrix as a stand-in for countable syntax.
3. Construct primitives through trusted smart constructors. An unclassified
   semantic primitive is intentionally rejected by both paper cost models.
4. State the target relation explicitly. Use exact equality unless the desired
   construction genuinely establishes `GlobalPhaseEq`, `BasisPhaseEq`, basis
   behavior, or a probability relation.
5. Use `TargetComplement`, `ControlSet`, and the layout structures instead of
   informal integer-wire arithmetic. They carry non-target and capacity facts in
   their types.
6. For auxiliary circuits, consume the clean/dirty subspace and factorization
   theorems rather than claiming full-unitary equality.
7. For approximation, open `Matrix.Norms.L2Operator` consistently and reuse the
   event-probability consequences rather than changing norms silently.
8. For a different primitive library or optimizer, define new syntax and prove
   evaluator preservation before attaching a new cost. The current fixed-schedule
   bound is a reusable baseline, not a claim that the circuit is optimized.
9. For exact local optimization, construct `FusionPrimitive` nodes directly or
   use the transparent paper builders. Lift unsupported existing `Circuit` syntax
   through `FusionProgram.barriers`; do not recover a local matrix from primitive
   kind/support metadata.

Low-dimensional checked examples are available in the root-excluded
`*Examples.lean` files. Paper-to-code navigation is maintained in
`docs/traceability.md`.
