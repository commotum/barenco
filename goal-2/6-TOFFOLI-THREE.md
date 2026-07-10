# 6-TOFFOLI-THREE

Status: in progress (2026-07-10).

## Current Facts

- The source's Section 8 cost model counts any certified at-most-two-wire unitary
  as one operation and states that three operations produce Toffoli “modulo
  phases” after merging the Section 6.2 construction. It does not claim or prove
  minimality.
- `relativePhaseToffoliAFusionCircuit` is the transparent chronological seven-node
  A diagram on an arbitrary ambient register. Its evaluator is exactly
  `relativeToffoliUnitary`; its literal profile is four one-qubit plus three CNOT
  nodes, and both named models charge seven before merging.
- `relativeToffoliUnitary` is not exact Toffoli and not globally phase-equivalent
  to Toffoli. Under pairwise-distinct wires it has the proved `101` input-column
  phase witness, exact signed basis action, `BasisPhaseEq`,
  `SameBasisBehavior`, and `BasisMeasurementEq` consequences.
- Stage 5's general `section8Normalize` promotes every CNOT to its certified local
  ordered-pair payload and fuses endpoint-compatible nodes exactly. On the
  pairwise-distinct relative-A input, the root-excluded diagnostic reduces seven
  nodes to three literal U(4) nodes with profile `(oneQ,CNOT,U4,total)=(0,0,3,3)`,
  Section 8 cost `some 3`, and early-model cost `none`.
- The three groups are structurally the two sandwiches on pair `(second,target)`
  around the middle canonical CNOT payload on pair `(first,target)`. Pairwise
  distinctness prevents the normalizer from fusing across the two pair changes.
- Exact evaluator equality already implies arbitrary spectator preservation. No
  ancilla is introduced, and no phase quotient is used by the optimizer.

## Updated Assumptions

- The paper's constructive upper count is recoverable from the A diagram. The
  source phrase “modulo phases” should be formalized as the existing
  input-column `BasisPhaseEq`, not as `GlobalPhaseEq`, exact equality, channel
  equality, or all-measurement equality.
- Export an explicit three-node list, not only the expression
  `section8Normalize input`. Prove that the general normalizer emits exactly that
  list under pairwise-distinct wires, then derive semantics and resources from
  the named syntax.
- The explicit three-node circuit may be defined using only control/target
  distinctness, but Toffoli-relative phase classification requires the two
  controls to be distinct as well.
- The B diagram need not be independently normalized: exact equality between the
  established A and B evaluators lets the A-derived three-node implementation
  serve the source's constructive claim without mispricing B's controlled-Z
  macro syntax.

## Big Picture Objective

Verify the paper's Section 8 constructive cost-three claim with a named explicit
three-U(4)-node circuit, exact arbitrary-register evaluator equality to the
seven-node relative-A circuit, the strongest correct phase/basis consequences,
and literal syntax-derived resources under the changed cost model.

## Detailed Implementation Plan

- Add `Barenco/ThreeQubit/RelativePhaseThreeGate.lean`:
  - define the local target-CNOT-target sandwich payload;
  - define an explicit chronological three-node `FusionCircuit` on ordered pairs
    `(second,target)`, `(first,target)`, `(second,target)`;
  - prove `section8Normalize relativePhaseToffoliAFusionCircuit` is exactly that
    list under pairwise-distinct wires;
  - define its trusted lowered `Circuit` and prove exact syntax/evaluator bridges;
  - prove exact equality to the original seven-node evaluator and to
    `relativeToffoliUnitary` on every ambient register;
  - transfer exact signed basis action, `BasisPhaseEq`, `SameBasisBehavior`, and
    `BasisMeasurementEq` to the named three-node circuit;
  - prove literal fusion and lowered component counts, total count three, Section
    8 cost `some 3`, and early-model rejection;
  - state explicitly that the theorem is a constructive upper count, not a
    minimality result or an exact/global-phase Toffoli implementation.
- Add root-excluded
  `Barenco/ThreeQubit/RelativePhaseThreeGateExamples.lean` with canonical width
  three and padded nonadjacent width five examples covering exact evaluator,
  signed action, ordered pairs, and both named costs.
- Integrate the stable leaf into `Barenco.lean`; add representative axiom checks.
- Update U6.2-A and U8-relToffoli3 traceability, C-032 and/or a new correction-log
  entry, conventions/final report, this stage file, and `goal-2/0-plan.md`.

## Build Structure

- `Barenco/ThreeQubit/RelativePhaseThreeGate.lean` — public paper-facing
  construction/proof/resource leaf importing `RelativePhaseFusion`, exact
  normalization/resources, and the existing phase equivalence API. It owns the
  named three-node syntax and claim classification.
- `Barenco/ThreeQubit/RelativePhaseThreeGateExamples.lean` — root-excluded
  concrete width/layout diagnostics; it may inspect definitional output but is
  not imported by `Barenco.lean` or the audit.
- `Barenco.lean`, `Barenco/AxiomAudit.lean`, and documentation — stable integration
  after focused verification.
- Existing `RelativePhase.lean`, `RelativePhaseFusion.lean`, optimizer runtime,
  `Primitive`, `Circuit`, and `CostModel` are intentionally unchanged unless a
  checked missing bridge forces a narrow documented migration.
- Focused build:
  `lake build Barenco.ThreeQubit.RelativePhaseThreeGate`, then the diagnostic.
- Adjacent builds include `RelativePhase`, `RelativePhaseFusion`,
  `Section8Normalize`, `NormalizeResources`, Corollary 7.4 relative-phase
  consumers, public root, and audit. Public integration requires direct strict
  and trust-zero checks plus a full build.

## Boundary Checks

- `first`, `second`, and `target` are pairwise distinct for every Toffoli-relative
  phase theorem. Ordered pair orientation remains control first, target second.
- The circuit is exact equal to `relativeToffoliUnitary`, not exact Toffoli.
  `BasisPhaseEq` is the strongest Toffoli relation exported. Do not claim
  `GlobalPhaseEq`, `ChannelEq`, `AllMeasurementEq`, or equality on arbitrary
  superpositions.
- The exact phase is the established `101` input-column sign. It is not discarded
  during fusion and is not basis-output dependent by convention accident.
- Three is a literal constructive upper count in `CostModel.arbitraryTwoQubit`.
  It is unsupported in `CostModel.oneQubitCNOT` because its U(4) payloads are not
  decomposed there. No theorem says three is minimal.
- Spectator preservation follows from exact full-register equality and certified
  two-wire embeddings; width-three matrix computation alone is not public
  evidence.
- The explicit list and normalizer-output theorem must be primary. A hard-coded
  arithmetic function or semantic equality alone cannot establish cost three.

## No-Cheating Checks

- The three output nodes must be `FusionPrimitive.twoQubit` values built from
  `OrderedWirePair` and certified local payloads, then lowered through
  `Primitive.twoQubit`; no ambient matrix or resource tag is forged.
- The normalizer equality must unfold the actual seven-node input and general
  rewrite policy. No branch may recognize this example by wire constants or
  theorem name.
- Resource theorems inspect the named three-element list and use established
  lowering bridges; they may not infer count from evaluator equality.
- Search the public leaf for `Primitive.unclassified`, `Classical.decEq`,
  `Classical.choice` used as runtime payload comparison, proof holes, custom
  axioms/opaque declarations, and phase-relaxed substitutions in exact proofs.
- Diagnostics remain absent from the public root and axiom audit.

## Completion Requirements

- [ ] A named explicit three-U(4)-node fusion circuit and trusted lowered circuit
  compile for arbitrary ambient width with pairwise-distinct classification
  assumptions.
- [ ] The general Section 8 normalizer emits exactly the named list, and exact
  visible/lowered evaluator equality to the seven-node A circuit is proved.
- [ ] Exact equality to `relativeToffoliUnitary`, signed computational-basis action,
  `BasisPhaseEq`, same classical basis behavior, and basis-measurement equality are
  transferred without claiming a stronger phase relation.
- [ ] Literal oneQ/CNOT/U4/total counts and both named partial costs are proved for
  the fusion and lowered syntax; Section 8 cost is exactly `some 3`.
- [ ] Width-three and padded nonadjacent-register diagnostics compile.
- [ ] Traceability marks the constructive cost-three claim verified but not
  minimal; correction/convention/final-report text records the precise phase and
  model scope.
- [ ] Public import, representative axiom checks, focused/adjacent/full builds,
  strict, trust-zero, forbidden/no-cheating scans, root exclusion, audit/table
  synchronization, and `git diff --check` pass.

## Stage Results

- Stage file created after Stage 5's complete requirement audit and before any
  Stage 6 Lean source change.
