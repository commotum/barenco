# 12-RESOURCES

Status: in progress (source, construction, and pinned-API audit complete; narrow
resource implementation beginning).

## Current Facts

- Stages 3 and 7--11 already attach exact syntax-derived costs to every selected
  controlled, multi-controlled, ancilla, approximation, lower-bound, and exact
  universality circuit. Stage 12 must aggregate those results; it must not infer
  resources from semantic equality or re-price an unsupported macro.
- `CostModel.oneQubitCNOT` accepts exactly arbitrary certified one-qubit primitives
  and CNOTs at cost one. `CostModel.arbitraryTwoQubit` accepts those two kinds,
  certified controlled-one-qubit macros with zero or one control, and the metadata
  kind `.arbitraryTwoQubit`; it rejects controlled macros with at least two controls.
  No trusted arbitrary-two-qubit smart constructor or embedding currently exists.
  The exact universality circuit uses only the stricter vocabulary, so its literal
  count agrees under both models, but this does not make the models interchangeable
  for other syntax.
- The Section 8 cost-model audit found and repaired one concrete defect:
  `.controlledOneQubit 1` is a certified two-wire primitive, but the named model
  had rejected every controlled-one-qubit kind. The repaired definition now gives
  the already verified five-node Lemma 6.1 circuit exact cost five and the displayed
  thirteen-node Lemma 7.1 circuit exact cost thirteen. It also exposed a hidden
  boundary in the recursive five-node circuit: prefix arities zero and one cost
  five, while rejection is valid only from prefix arity two onward.
- `decomposeFinUnitary` uses a fixed, non-pruning left-Givens schedule. At a
  successor dimension `d+1`, it adds exactly `d` factors to the recursively
  synthesized `d`-dimensional block. Therefore its factor-list length should be
  exactly `Nat.choose dimension 2`, independently of the input unitary. The
  generic `decomposeFiniteUnitary` only maps those factors through an equivalence,
  so it should preserve that length. This is a construction count, not a minimum.
- For an `n = controlCount+1` wire register, `Fintype.card (Basis n) = 2^n`.
  Consequently the fixed algebraic schedule has exactly `Nat.choose (2^n) 2`
  two-level factors. The diagonal circuit schedules one pattern for each assignment
  of the other `n-1` wires, hence `2^(n-1)` controlled blocks.
- `affinePairCircuit` has exact transport cost
  `trueBitCount first + (hammingDist first second - 1)`. The complete factor
  circuit pays for that transport and its adjoint around one adjacent block.
  Since both the true-bit count and Hamming distance are bounded by register width,
  transport is linear and the selected full-control block is quadratic. This
  supports a uniform quadratic-per-factor upper theorem, stronger than the
  source's repeated Gray-walk cubic upper route.
- `fullControlCircuitCost` is piecewise exact: explicit constants for zero through
  five controls, then `56*d^2 + 364*d + 440` at `d+6` controls. A simple uniform
  polynomial envelope (expected `<= 56*(controlCount+1)^2`) will make the general
  synthesis bound substantially easier to reuse than the shifted piecewise form.
- The completed construction and Lean audits give sharper boundary-safe envelopes. Writing
  `n=controlCount+1`, every full-control block and every synthesized two-level
  factor cost at most `56*n^2`; every diagonal pattern also costs at most
  `56*n^2`. The number of factor components plus diagonal-pattern components is
  exactly `2*4^controlCount`, so the clean total bound is
  `112*n^2*4^controlCount`, equivalently `28*n^2*4^n` in full-width notation.
- `exactSynthesisCost` is an exact finite sum of the actual factor circuit
  costs plus the actual diagonal-pattern schedule cost. It depends on factor
  endpoints and the chosen unitary, so Stage 12 needs a pointwise uniform upper
  bound before an asymptotic family theorem.
- The paper's path statement gives only `pathLength <= n+1`. Its conclusion that
  each factor has `Theta(n^3)` cost is false for adjacent endpoints and lacks a
  matching lower bound. The library's main affine circuit has a different schedule,
  so the paper's `2m-3` macro count cannot be attached to it.
- The paper's general `Theta(n^3 * 4^n)` wording is therefore not an optimality
  theorem. For the library construction, the proved uniform result is the stronger
  `O(n^2 * 4^n)` upper bound, with explicit natural-number constant `112` in
  control-count indexing.
- A matching `Theta(n^2*4^n)` statement is proved for the
  library's deliberately non-pruning *fixed syntax*: it emits all
  `choose(2^n,2)` factor circuits even for the identity, and every factor contains
  one quadratically priced full-control block. Such a theorem must be named as the
  complexity of `exactSynthesisCircuit`, never as optimal target complexity or a
  lower bound on arbitrary exact circuits.
- Section 8's five/thirteen-gate Toffoli upper counts, three-gate relative-phase
  count, six-`U(4)` claim for `U(8)`, and dimension-count conjecture require
  separate treatment. The last two remain unresolved/excluded from Stage 10;
  pricing metadata alone is insufficient to formalize the first three merged
  arbitrary-two-qubit circuits.
- More precisely, the five- and thirteen-node semantic circuits now have exact
  Section 8 cost theorems after the arity-one model repair. The
  three-gate relative-phase claim still requires an explicit grouping into three
  certified two-wire primitives; the existing seven-node one-qubit/CNOT syntax
  cannot be assigned cost three merely by changing its price.

## Updated Assumptions

- Register width is positive for general exact synthesis; write it as
  `controlCount+1` in circuit theorems and as `n` only after retaining `0<n`.
- Arbitrary one-qubit gates remain primitives. No fixed finite-set compilation or
  approximation cost is included in the exact general-unitary bound.
- The main synthesis uses no work wires. Its width is exactly the target unitary's
  width; no hidden reindexing, permutation, measurement, reset, or discarded
  subsystem is priced.
- Exact count, pointwise constructed upper bound, `IsBigOWith`, and optimal
  lower/`Theta` results are distinct declarations. Stage 12 will not use `Theta`
  for the general construction without a proved matching lower theorem.
- Natural-number resource arithmetic is authoritative. Real-valued asymptotic
  statements may cast those proved inequalities, but may not replace them.
- A theorem under the broader arbitrary-two-qubit cost model counts the literal
  one-qubit/CNOT syntax unchanged unless an explicit two-qubit merger circuit and
  evaluator-preservation theorem is supplied.

## Big Picture Objective

Connect the exact Stage 11 synthesis syntax to explicit structural counts and a
machine-checked uniform/asymptotic upper bound, while finishing the paper-facing
classification of Section 8 resource claims under both named cost models.

## Detailed Implementation Plan

1. Complete the source and pinned-API audit before Lean edits. Fix notation for
   width, Hilbert dimension, factor count, pattern count, exact cost, and the two
   named cost models; record any further correction before proving bounds.
2. Add a low-dependency elimination-resource leaf proving the exact fixed-schedule
   factor length on `Fin dimension`, preservation through `FiniteBridge`, and the
   qubit specialization `Nat.choose (2^n) 2`.
3. Add a circuit-resource leaf proving true-bit, Hamming, affine-transport,
   canonical adjacent, and arbitrary two-level cost bounds, plus a uniform
   polynomial bound for `fullControlCircuitCost`.
4. Prove the all-pattern schedule length and a reusable upper bound for the exact
   diagonal cost. Prove a closed exact sum only if its extra combinatorics improves
   downstream use; do not delay the uniform theorem for cosmetic normalization.
5. Aggregate the exact factor count, per-factor bound, and diagonal bound into a
   pointwise theorem for every `U : UnitaryGate n`. Target the checked bound
   `112*(controlCount+1)^2*4^controlCount`, then expose family-level
   `IsBigOWith`/`IsBigO` corollaries. Also prove the matching lower envelope and a
   carefully labeled `IsTheta` theorem for the non-pruning selected syntax if the
   lower proof remains as direct as the audit indicates.
6. Prove that the final literal synthesis cost is identical under
   `CostModel.oneQubitCNOT` and `CostModel.arbitraryTwoQubit`. Keep this statement
   construction-specific or derive it from a precise accepted-syntax lemma.
7. Correct `CostModel.arbitraryTwoQubit` to accept certified controlled-one-qubit
   primitives of control arity at most one. Prove exact Section 8 costs five and
   thirteen for the existing Lemma 6.1 and Lemma 7.1 circuits. Formalize the
   three-gate relative-phase claim only if three explicit grouped two-wire
   primitives and evaluator preservation are constructed; otherwise record that
   exact obstruction. Retain the six-`U(4)` and dimension lower claims as
   unresolved/excluded absent the required manifold/image proof.
8. Add root-excluded arithmetic examples, public imports, maintained axiom checks,
   traceability/correction/convention updates, strict and trust-zero compilation,
   focused builds, and two full builds.

## Build Structure

- Planned algebraic leaf:
  `Barenco/Universality/EliminationResources.lean`, importing only the elimination
  and finite-bridge declarations needed for factor-list lengths.
- Planned circuit leaves:
  `Barenco/Universality/TwoLevelResources.lean` for full-control, affine, and
  per-factor bounds; `DiagonalResources.lean` for pattern cardinality and schedule
  bounds; and `SynthesisResources.lean` for exact aggregation, model comparison,
  and Big-O/Theta statements.
- Planned Section 8 pricing leaf:
  `Barenco/Universality/Section8BasicResources.lean`, importing only the existing
  five- and thirteen-node semantic circuits plus the corrected cost model.
- Optional diagnostic leaf:
  `Barenco/Universality/ResourceExamples.lean`, excluded from `Barenco.lean`.
- `Barenco.lean` and `Barenco/AxiomAudit.lean` change only after theorem signatures
  and focused builds are stable. High-fanout `Semantics.lean`, `Circuit.lean`, and
  Stage 7 construction modules remain unchanged. `Cost.lean` is the one intentional
  high-fanout edit: the audit proved that its named Section 8 model incorrectly
  rejects certified arity-one controlled primitives. Focused and full consumer
  builds are mandatory after that correction.
- Initial focused commands:
  `lake build Barenco.Universality.EliminationResources` and
  `lake build Barenco.Universality.SynthesisResources`; adjacent builds will include
  the diagnostic leaf, public root, and maintained axiom audit after integration.

## Boundary Checks

- No count or bound may be concluded from `Circuit.eval` equality.
- A `some cost` theorem proves accepted syntax for one named model; it does not by
  itself classify primitive kinds under another model or prove asymptotics.
- `Nat.choose (2^n) 2` is the exact length of this fixed elimination schedule, not
  a lower bound on every decomposition and not a count of nonidentity factors.
- The factor endpoint-dependent cost is bounded pointwise; replacing it by a
  worst-case envelope must use proved true-bit/Hamming/control-cost inequalities.
- The diagonal residual and all global phases remain in the counted circuit.
- No algebraic `Fintype.equivFin` transport or matrix reindex operation is counted
  as a physical gate.
- The broader Section 8 cost model may price existing literal gates, but it may not
  retroactively merge them without explicit transformed syntax and exact semantics.
- `O(n^2*4^n)` for the selected affine construction is not an optimal-synthesis
  theorem and does not imply the source's conjectural lower bound.
- No `sorry`, `admit`, `by?`, custom `axiom`, `opaque`, `native_decide`, or
  `bv_decide` may occur in completed modules.

## Completion Requirements

- [ ] Exact factor-list lengths are proved for canonical Fin elimination, generic
  finite transport, and qubit dimensions.
- [ ] Exact component costs are connected to explicit pointwise polynomial and
  exponential natural-number upper bounds.
- [ ] The final exact synthesis has a proved uniform `C*n^2*4^n` bound and a
  correctly scoped asymptotic family theorem.
- [ ] If a matching lower envelope is exported, its `Theta` theorem is explicitly
  restricted to the fixed non-pruning `exactSynthesisCircuit` schedule and is not
  presented as optimal target complexity.
- [ ] The final literal synthesis is priced under both named cost models without
  conflating them or assuming an unproved merger.
- [ ] Every remaining Section 8 resource claim is proved, corrected, partially
  formalized, explicitly assumed, unresolved, or excluded with a precise reason.
- [ ] Public imports, representative diagnostics, maintained axiom entries,
  forbidden scans, strict/trust-zero checks, focused builds, and two full builds
  pass and are recorded.
- [ ] Traceability, corrections, conventions, and `0-plan.md` distinguish exact
  schedule counts, constructed upper bounds, asymptotics, lower bounds, and
  unresolved optimization/surjectivity claims.

## Stage Results

- Stage file created before Stage 12 Lean implementation. Initial evidence selects
  two narrow proof layers: exact elimination schedule lengths, then pointwise and
  asymptotic bounds for the already verified literal synthesis. The intended main
  correction is a construction-specific quadratic-times-`4^n` upper bound, not
  the paper's unsupported optimal `Theta(n^3*4^n)` wording.
- Independent source, construction, and pinned-API audits found no blocking API
  gap. They derive exact factor and pattern counts, a clean constant-112 upper
  envelope in control-count indexing, a matching fixed-schedule lower route, and
  the arity-one omission in `CostModel.arbitraryTwoQubit`. They also confirm that
  the five- and thirteen-gate Section 8 upper circuits are already semantically
  proved, while the three-gate grouping, six-`U(4)` surjectivity, and dimension
  lower bound still lack the necessary formal objects or proofs.
- `EliminationResources.lean` proves the exact non-pruning factor-list length
  `Nat.choose dimension 2`, preservation through finite reindexing, and the qubit
  specialization. `TwoLevelResources.lean` proves the quadratic full-control and
  factor envelopes. `DiagonalResources.lean` proves the `2^controlCount` schedule
  length and matching finite cost bounds.
- `SynthesisResources.lean` aggregates the literal syntax into the pointwise
  sandwich
  `2*(k+1)^2*4^k <= exactSynthesisCost <= 112*(k+1)^2*4^k`, plus explicit
  `IsBigOWith` and carefully named fixed-schedule `IsTheta` results. Compilation,
  public integration, documentation, and final audits remain in progress.
