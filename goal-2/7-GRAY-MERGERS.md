# 7-GRAY-MERGERS

Status: complete (2026-07-10).

## Current Facts

- The paper uses `n` total bits and `m=n-1>0` controls. In the Lean API,
  `m=tail+1`; the Gray schedule contains `r=2^m-1` nonempty masks/root blocks and
  `r-1=2^m-2` control-to-control Gray CNOT transitions.
- Public `grayFusionControlledViaRootCircuit` is transparent optimizer-visible
  syntax exactly equal to the checked Lemma 7.1 macro circuit on an arbitrary
  ambient register. Its raw literal profile is
  `4r = 4*(2^m-1)` one-qubit gates, `2r+(r-1)=3*2^m-4` CNOTs, and
  `7*2^m-8` total.
- The paper's post-merger claim keeps the same CNOT count but reports
  `2*2^m = 2r+2` one-qubit gates. Relative to the raw syntax, that requires
  deleting exactly `2(r-1)` one-qubit nodes: one two-node inverse pair at every
  internal root-block boundary. Ordinary pair fusion to one node would save only
  `r-1` and cannot establish the printed formula.
- The current transparent Gray builder independently applies
  `canonicalSelectedControlledU2FusionCircuit` to each signed payload `V` or
  `V⁻¹`. Because selected ABC factors are obtained by classical choice,
  factors selected independently for `V⁻¹` are not definitionally or
  theoremically the inverses of those selected for `V`; that builder is a valid
  raw regression input but cannot justify the desired boundary cancellations.
- The coherent transparent positive controlled-`V` block has chronology
  `A(target); phase(control); CNOT; B(target); CNOT; C(target)`. Its literal
  circuit adjoint implements controlled `V⁻¹` and exposes inverse provenance:
  `C⁻¹; CNOT; B⁻¹; CNOT; phase⁻¹; A⁻¹`.
- `GrayAdjacent.card_succ_or_succ_card` and its parity corollaries now prove that
  consecutive masks alternate signs. Named odd/even theorems connect this parity
  exactly to `signedGrayRoot mask V = V` or `V⁻¹` for nonempty masks.
- At a positive-to-negative boundary, `C` and `C⁻¹` are separated only by the
  control-register Gray CNOT. At a negative-to-positive boundary, `A⁻¹` and `A`
  are separated only by the Gray CNOT. A target-directed
  exact commutation pass can expose either pair without assuming any ambient wire
  ordering.
- Generic `normalizeEarly` preserves exact semantics and literal CNOT order, but
  it sorts distinct one-qubit gates by ambient `Fin` order and deliberately never
  recognizes a concrete matrix product as identity. Therefore it is not by itself
  sufficient evidence for layout-independent two-node inverse deletion.
- Public `SymbolicCircuit.exposeWire` and `normalizeAtWire` now provide the
  target-directed exposure pass across certified off-target one-qubit/CNOT nodes,
  with exact erased/lowered evaluators and exact ordered-CNOT-trace preservation.
- Stage 6 is complete: the maintained baseline is now 436 axiom checks, 132 Lean
  files below `Barenco/`, and a 3,604-job full build.

## Updated Assumptions

- Select the ABC/phase payloads once for `V`. Positive masks use the resulting
  controlled-`V` block; negative masks use its literal adjoint. Do not select
  unrelated factors for `V⁻¹`.
- Use exact symbolic inverse provenance or an equivalently checkable typed
  grammar. Do not decide equality of unitary matrices and do not assume the
  product of independently chosen factors is identity.
- Add a target-directed exposure policy that moves only a target one-qubit word
  across certified gates disjoint from the target. Its correctness must use the
  existing semantic commutation laws, not metadata cardinality.
- The source formula is verified for the named coherent output: the general
  executable output, exact evaluator bridge, ordered CNOT trace, and
  constructor-derived formulas all compile.
- If the coherent construction or general count proof fails, retain the strongest
  checked normal form and classify the source claim as not recovered; failure of
  one policy is not a refutation.

## Big Picture Objective

Reconstruct the paper's omitted general Gray merger as a coherent, executable,
exactly sound transformation with a named literal output circuit, then determine
whether its actual one-qubit/CNOT profile is the printed
`(2*2^m, 3*2^m-4, 5*2^m-4)` for every positive control count.

## Detailed Implementation Plan

- Prove the Gray sign infrastructure:
  - every runtime mask is nonempty;
  - Gray adjacency flips mask-cardinality parity;
  - the first mask has positive sign and consecutive indexed masks alternate;
  - odd masks give `signedGrayRoot mask V = V`, while even masks give `V⁻¹`.
- Define one finite decidable atom grammar for the selected `phase/A/B/C` payloads
  and a valuation determined by a single selected factor package for `V`.
- Define coherent positive and negative symbolic controlled-root blocks, with the
  negative block literally the reverse/inverse syntax of the positive block.
  Prove erasure gives the positive controlled-`V` circuit or its exact adjoint and
  hence the required signed-root macro semantics.
- Rebuild the full Gray root/transition schedule from public masks, pivots, and
  CNOT edges using those coherent blocks. Prove exact equality to
  `grayControlledViaRootCircuit layout V`, then specialize to the selected exact
  root for arbitrary controlled `U`.
- Add or reuse a target-directed symbolic exposure pass. Prove exact arbitrary-
  register evaluation, literal CNOT trace/count preservation, component-count
  preservation before cancellation, and independence from ambient wire order.
- Run symbolic normalization after exposure. Prove the general emitted structure
  deletes exactly one inverse pair at each of the `2^m-2` internal boundaries and
  nothing needed for the evaluator.
- Define the named erased `FusionCircuit` and trusted lowered `Circuit`. Derive
  exact evaluator theorems, one-qubit/CNOT/U4/total counts, and accepted
  `oneQubitCNOT` cost from the actual normalized syntax.
- Add root-excluded diagnostics at control counts one, two, and three, including a
  nonconsecutive/reversed ambient layout, checking profiles `(4,2,6)`, `(8,8,16)`,
  and `(16,20,36)` plus exact semantics and CNOT order.
- Update L7.1/C-035, conventions, final report, axiom audit, this stage file, and
  `goal-2/0-plan.md` only after the output formula is checked.

## Build Structure

- Prefer a narrow generic symbolic target-exposure leaf under
  `Barenco/Optimization/` only if the proof is genuinely target-independent and
  reusable; otherwise keep the policy private to a new
  `Barenco/MultiControl/GrayMergers.lean` leaf.
- `Barenco/MultiControl/GrayMergers.lean` will own Gray-cardinality sign lemmas,
  coherent symbolic block/schedule syntax, the named optimized circuit, exact
  evaluator bridges, and general resource theorems. It may import `GrayFusion`,
  symbolic cancellation/exposure, and normalization resources, but must not edit
  the high-fanout `Primitive`/`Circuit` trust core.
- `Barenco/MultiControl/GrayMergerExamples.lean` will be root-excluded diagnostic
  code for low-control and nonadjacent-layout boundaries.
- If the symbolic exposure layer is split, build it first and keep it free of
  paper-specific masks or factor atoms.
- Focused builds: the exposure leaf if added, then `GrayMergers`, then diagnostics.
- Adjacent builds include `GrayCode`, `Lemma71`, `GrayFusion`, `GrayExpansion`,
  normalization leaves/resources, recursive consumers if imports change, public
  root, and audit. Public integration requires strict/trust-zero and a full build.

## Boundary Checks

- Public controlled-unitary results use `m=tail+1>=1` controls; the distinct
  zero-control local-gate case is not smuggled into the Gray generator.
- `OrderedControlLayout` carries injective controls and target distinctness.
  Proofs must hold for arbitrary ambient positions and spectators, not only the
  consecutive layout used by diagnostics.
- All optimization equalities are exact. Scalar/global phase is retained; no
  phase-relaxed relation is used to justify a cancellation.
- Every output node remains a symbolic/erased one-qubit node or literal CNOT.
  Generic U(4), controlled macros, Toffoli macros, and unclassified barriers are
  absent, so the early named cost must be accepted.
- The ordered Gray CNOT trace is unchanged. No CNOT self-cancellation or
  reorientation is part of the claimed count.
- The negative block is the literal adjoint of the chosen positive block, not a
  separately selected implementation of `V⁻¹`.
- Target exposure may commute only across one-qubit nodes on a distinct wire and
  CNOTs whose two endpoints differ from the target. Touching CNOTs are hard stops.
- `2*2^m` is a constructive upper count for the named syntax, never a minimum or
  a claim that all equivalent circuits normalize to the same result.

## No-Cheating Checks

- Search the new runtime leaves for matrix equality decisions, whole-circuit
  `Classical.choice`, `Primitive.unclassified`, forged
  `.arbitraryTwoQubit`/`Primitive.mk`, paper-specific low-width branches, hard-
  coded count outputs, proof holes, custom axioms/opaque declarations, and
  forbidden decision shortcuts.
- Inspect that resource functions fold the emitted list and that formulas are
  derived from constructors/recurrences; do not define a disputed formula and
  reuse it as evidence for list length.
- Prove the real exposure/normalization output relation. A separately hand-written
  short circuit with only semantic equality is insufficient evidence for a
  merger count.
- Prove the coherent raw schedule equals the established macro evaluator before
  transferring full controlled-`U` semantics.
- Keep diagnostics absent from `Barenco.lean` and `Barenco/AxiomAudit.lean`.

## Completion Requirements

- [x] Named coherent raw and normalized Gray circuit families compile for every
  positive control count and arbitrary ambient layout.
- [x] Gray sign alternation and positive/adjoint block semantics are explicitly
  proved; no unrelated inverse factor choices are used.
- [x] The executable target-exposure/cancellation result preserves exact visible
  and lowered evaluators and the complete ordered CNOT trace.
- [x] Literal component, total, and early-model accepted-cost formulas are proved
  from the normalized syntax.
- [x] The paper's formula receives a verified/refuted/not-recovered status with
  scope matching the checked grammar; no optimizer limitation is overstated.
- [x] One-, two-, and three-control profiles and a padded/reordered ambient layout
  compile and agree with the general statements.
- [x] Traceability, correction log, conventions, final report, public import, and
  representative axiom checks are synchronized.
- [x] Focused/adjacent/full builds, strict, trust-zero, forbidden/no-cheating
  scans, root exclusion, audit/table synchronization, and `git diff --check` pass.

## Stage Results

- Stage file created after the requirement-by-requirement Stage 6 audit and before
  any Stage 7 Lean source change.
- `Barenco/Optimization/SymbolicExpose.lean` adds an exact target-directed
  exposure/cancellation pass. It commutes a selected-wire word only across a
  distinct-wire one-qubit node or a CNOT whose endpoints are both distinct from
  the selected wire. Exact erased/lowered evaluator, length/component, and ordered
  CNOT trace/count theorems compile.
- `Barenco/MultiControl/GrayMergers.lean` selects one phase/A/B/C package for `V`,
  uses the literal formal adjoint for negative roots, proves Gray parity
  alternation, and reconstructs the full coherent raw schedule exactly against
  the established Lemma 7.1 macro.
- Each actual three-node boundary is passed through `normalizeAtWire`; the local
  output theorem emits the unchanged Gray CNOT. A streaming prefix applies this
  executable pass at all boundaries. Literal regrouping proves that the unmerged
  boundary form is exactly the raw schedule, and a separate syntax theorem proves
  that the streaming merger emits the named direct normal form.
- Exact arbitrary-register evaluator preservation holds at every local segment,
  prefix, full fusion circuit, and trusted lowered circuit. The selected-root
  wrapper implements `positiveControlledUnitary` exactly. The complete ordered
  CNOT trace is identical to the coherent raw schedule.
- For `m=tail+1>0` controls, the actual emitted symbolic/fusion/lowered syntax has
  exactly `2*2^m` one-qubit nodes, `3*2^m-4` CNOTs, no generic U(4) nodes, and
  total `5*2^m-4`. Both named cost models return that literal total. This verifies
  the paper's post-merger formula as a constructive upper count, not a minimum.
- Root-excluded `GrayMergerExamples` proves profiles `(4,2,6)`, `(8,8,16)`, and
  `(16,20,36)` and checks exact semantics, normal-form output, and CNOT chronology
  on the width-six reordered/padded control embedding `![4,0,5]` with target `2`.
- The focused/adjacent/public/audit build passed with 3,608 jobs; the separate
  root/audit integration passed with 3,607 jobs; the full build passed with 3,606
  jobs. All six warning-as-error and all six trust-zero direct compilations passed.
- Eighteen new audit checks raise the synchronized source/table total to 454 and
  use only `propext`, `Classical.choice`, and `Quot.sound` (one append theorem uses
  a strict subset). The public tree has 135 Lean files. Proof-hole,
  custom-declaration, runtime-choice/matrix-decision/constructor-forgery,
  low-width-branch, root-exclusion, and diff scans are clean.
