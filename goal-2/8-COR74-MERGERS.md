# 8-COR74-MERGERS

Status: in progress (2026-07-10).

## Current Facts

- The paper's `n` is the full network width. Its construction simulates the
  `(n-1)`-wire gate `wedge_(n-2)(X)` while using one dirty borrowed wire, so the
  public balanced Lean family is indexed by the same `sourceWidth = n >= 7`.
- The repaired floor partition is already encoded by `balancedLayout`. It
  satisfies the smallest legal width, keeps the final target out of A's borrowed
  prefix, and yields `balancedLeftTail + balancedRightTail + 7 = sourceWidth`.
- The exact macro count is `8(n-5)=8n-40`. Four occurrences touching the final
  target remain exact and the other `8n-44` occurrences use the checked
  relative-phase circuit. The source's intermediate `8n-36` is arithmetically
  false.
- Exact contextual correctness already requires the repaired chronology
  `Arel; Bhybrid; adjoint(Arel); Bhybrid`. Replacing the adjoint by a second
  forward A circuit leaves a real basis-dependent sign. B consists of two exact
  outer Toffolis and two identical relative smaller halves; two B copies therefore
  contain all four exact occurrences.
- `balancedExpandedRelativeCorollary74Circuit` replaces each exact macro by a
  selected sixteen-node witness but deliberately performs no cross-occurrence
  normalization. Its literal early-model profile is
  `(32n-144, 24n-100, 56n-244)`, including `(80,68,148)` at width seven, and its
  evaluator is exactly the intended full-register controlled X.
- `exactToffoliExpansionCircuit` is a `Classical.choose` of an entire circuit.
  Its specification exposes only evaluator and aggregate resource facts, so it is
  forbidden as optimizer-visible input.
- `doubleControlledExpansion16Circuit` is the needed transparent oriented
  schedule. It contains eight one-qubit and eight CNOT nodes parameterized by one
  shared `delta,A,B,C` package. `selectedColumnABCFactors` supplies transparent
  checked factors for `specialUnitaryPart (unitarySquareRoot pauliX)`, and the
  existing product theorem proves the explicit schedule implements exact Toffoli.
- The Stage 5 early normalizer preserves every literal CNOT and exact scalar phase.
  Its ordinary matrix-payload mode fuses one-qubit nodes but does not infer that a
  concrete product is identity. Stage 7 symbolic inverse provenance and
  target-directed exposure are available when exact syntactic adjoints occur.
- If the CNOT count remains `24n-100`, the paper's final `48n-204` requires
  `24n-104` one-qubit nodes and hence exactly `8n-40` one-qubit deletions from the
  raw circuit. One deletion for each of the `8n-44` relative occurrences leaves
  four additional required deletions. Width seven would have to normalize from
  `(80,68,148)` to `(64,68,132)`; widths eight and nine target totals 180 and 228.
- A successful count must come from the emitted list of a named executable pass.
  A semantic short circuit, an arithmetic count function, or inspection of one
  low-width trace is insufficient.

## Updated Assumptions

- Preserve the repaired partition, hybrid-B semantics, adjoint-A occurrence,
  target-free capacity bound, arbitrary dirty-wire input, and exact restoration.
- Select the square root and A/B/C factors coherently once for every explicit
  exact-Toffoli orientation used by the family. Do not replace a transparent
  factor schedule by the opaque whole-circuit witness.
- Begin with the established sixteen-node orientation and the exact early-model
  grammar. Explore alternative orientations only as separately named exact
  constructions with evaluator proofs.
- Preserve every CNOT unless a distinct exact rewrite explicitly emits and proves
  a smaller CNOT trace. The paper-facing diagnostic initially targets the known
  `24n-100` CNOT profile.
- Use symbolic inverse cancellation only where literal provenance proves an
  inverse pair. Never decide equality of arbitrary unitary matrices or erase a
  scalar/global phase.
- The four extra one-qubit savings demanded by the printed total are an obligation
  to discover and certify, not an assumption. If the verified pass reaches a
  different stable profile, classify the printed count as not recovered for the
  named orientation and calculus. Refutation would require a matching completeness
  or lower-bound theorem and is not presumed.

## Big Picture Objective

Translate the complete corrected Corollary 7.4 construction into transparent
payload-preserving syntax, run a real exact normalization pass across every
relative and exact occurrence boundary, and export the strongest checked
arbitrary-width evaluator/restoration/resource result. Determine honestly whether
that named construction realizes the paper's `48n-204` count.

## Detailed Implementation Plan

- Define a transparent selected exact-Toffoli factor package for `pauliX` from
  `unitarySquareRoot`, `determinantPhaseAngle`, `specialUnitaryPart`, and
  `selectedColumnABCFactors`; prove its inactive, active, phase, and square laws.
- Reify `doubleControlledExpansion16Circuit` in `FusionCircuit` or the symbolic
  exact grammar with its complete chronological one-qubit/CNOT payloads. Prove
  literal lowering equality and exact arbitrary-register Toffoli semantics.
- Reify relative base/outer/half/inward ladder builders without changing their
  chronology. Preserve A's literal adjoint and B's two exact outer plus two
  relative-half structure.
- Assemble the full corrected `FourBlockLayout` circuit in transparent syntax and
  prove its lowering/evaluator equality to
  `expandedRelativeCorollary74Circuit` or directly to
  `relativeCorollary74Circuit` plus the explicit exact-expansion bridge.
- Apply `normalizeEarly` and, where literal adjoint provenance is essential, the
  exact symbolic target-exposure/cancellation layer. Record the actual emitted
  boundary forms before choosing any specialized reusable pass.
- If a recurring legal boundary is missed by the generic pass, add the narrowest
  target-independent exact rewrite justified by certified locality and inverse
  provenance. Do not add a Corollary-specific arithmetic shortcut.
- Name the normalized fusion circuit and trusted lowered circuit. Prove exact
  evaluator equality, preservation/restoration through the existing full-register
  semantics, complete CNOT trace or an explicitly proved replacement trace, and
  syntax-derived component/total/accepted-cost formulas.
- Prove general balanced-width formulas for every `n>=7`, plus literal width
  seven, eight, and nine diagnostics. Compare the theoremized result with both the
  raw profile and the printed target.
- Recompute recursive dependent counts only if the emitted Corollary circuit
  changes their substitution syntax. Otherwise retain the existing results and
  state why no dependency changes.
- Update public imports, axiom checks, traceability, correction C-004, conventions,
  final report, this stage file, and `0-plan.md` after the result is verified.

## Build Structure

- Add the narrow reusable public leaf
  `Barenco/ThreeQubit/ExpansionFusion.lean` for the transparent selected
  sixteen-node generic double-controlled-`U` expansion, exact lowering/evaluator
  bridge, and literal resource facts. This declaration belongs beside Corollary
  6.2 rather than inside a Corollary 7.4-specific namespace.
- Add `Barenco/MultiControl/Corollary74Mergers.lean` for the relative-ladder
  fusion/symbolic builders, named normalized family, exact evaluator bridges, and
  general Corollary resource theorems. It may import the existing Corollary
  expansion, the new exact-expansion fusion leaf, fusion resources, early
  normalizer, and symbolic exposure, but must not edit the `Primitive`/`Circuit`
  trust core.
- Keep width-seven/eight/nine traces and alternative-orientation probes in the
  root-excluded diagnostic leaf
  `Barenco/MultiControl/Corollary74MergerExamples.lean`.
- Add a generic optimizer leaf only if an uncovered rewrite is demonstrably
  target-independent and has another real consumer; otherwise keep the proof
  local to the Corollary leaf.
- Runtime/public API: transparent builders and named normalized circuits.
  Proof-side public API: lowering/evaluator/restoration/resource theorems.
  Diagnostic: low-width traces and negative orientation probes. No fallback or
  temporary declaration enters `Barenco.lean`.
- Focused builds: exact-expansion fusion leaf, Corollary public leaf, then
  diagnostic leaf. Adjacent builds:
  `Corollary74Expansion`, `RelativePhase`, recursive primitive consumers,
  normalization leaves/resources, public root, and axiom audit. Public integration
  requires strict, trust-zero, and full-build verification.

## Boundary Checks

- Domain is every balanced `sourceWidth >= 7`; widths below seven are excluded by
  the constructor proof, not padded or handled by a low-width branch.
- All optimizer soundness statements are exact full-register equality. The later
  relative-Toffoli phase theorem may explain ingredients but never substitutes for
  exact contextual correctness.
- `FourBlockLayout` supplies the distinct controls, dirty wire, final target, and
  capacity facts. Arbitrary ambient spectators and arbitrary initial dirty-wire
  values remain covered by the established evaluator theorem; no clean-ancilla
  hypothesis is introduced.
- Ordered CNOT orientation and head-first chronology are preserved. The local
  product for gates applied `U` then `V` is `V*U`.
- Output syntax remains one-qubit/CNOT-only for the early model. Generic U(4),
  controlled macros, exact-Toffoli macros, unclassified gates, and opaque barriers
  cannot be silently assigned early cost.
- The Section 8 arbitrary-two-qubit model may be reported additionally, but it is
  not the source model for `48n-204` and cannot justify that count.
- The source result is a constructive upper bound. No theorem may say minimal,
  canonical, globally optimal, or refuted without a separately matched proof.

## No-Cheating Checks

- Search new runtime code for the whole-circuit `exactToffoliExpansionCircuit`,
  `Primitive.unclassified`, forged `Primitive.mk`/`.arbitraryTwoQubit`, matrix
  equality decisions, hard-coded paper count branches, fixed low-width runtime
  cases, phase-relaxed substitutions, and forbidden proof shortcuts.
- Inspect that every exact node is constructed from the explicit sixteen-node
  factor schedule and that every relative node retains its literal four-one-qubit/
  three-CNOT payload or a proved normalizer output.
- Prove lowering/evaluator equality before transferring semantics. Prove resource
  formulas by folding the named emitted list, never from matrix equality or a
  separately defined arithmetic function.
- Preserve or explicitly theoremize the complete CNOT chronology. A claimed
  one-qubit-only merger must not silently delete, reverse, or fuse CNOTs.
- Distinguish: a successful named circuit verifies the source count; a fixed point
  of the declared pass supports only not recovered; a matching completeness or
  lower-bound theorem would be required for refutation.
- Keep diagnostics absent from `Barenco.lean` and `Barenco/AxiomAudit.lean`.

## Completion Requirements

- [ ] A transparent exact-Toffoli expansion with selected factors lowers to the
  established sixteen-node chronology and has exact arbitrary-register semantics.
- [ ] The corrected full Corollary family is available as optimizer-visible syntax
  without opaque whole-circuit choices and is exactly equal to the established
  phase-safe evaluator.
- [ ] A named executable normalized/stable output exists for every `n>=7`, with
  exact full-register semantics and dirty-wire/spectator restoration inherited
  through an explicit evaluator bridge.
- [ ] One-qubit, CNOT, total, and accepted early-model costs are derived from the
  literal output syntax; the CNOT trace or any exact change to it is theoremized.
- [ ] Width-seven/eight/nine examples compile and agree with the general formula.
- [ ] `48n-204` receives a scoped verified/refuted/not-recovered status with named
  evidence; no optimizer limitation is overstated.
- [ ] Every affected recursive/resource theorem is rederived or explicitly shown
  to remain based on the unchanged raw substitution.
- [ ] Stable declarations are publicly integrated and representative headline
  theorems enter the maintained axiom audit; diagnostics remain root-excluded.
- [ ] Focused/adjacent/public/full builds, strict, trust-zero, forbidden/no-cheating
  scans, documentation/table synchronization, and `git diff --check` pass with
  exact evidence recorded below.

## Stage Results

- Stage file created and Stage 8 arithmetic/current facts folded into `0-plan.md`
  before any Stage 8 Lean source edit.
