# 3-TWO-PRIMITIVE

Status: complete (2026-07-10).

## Current Facts

- Stage 2 publicly exports `OrderedWirePair`, `twoWireUnitary`, exact certified
  basis/arbitrary-state/spectator/algebra/orientation theorems, and exact bridges
  to established local, singleton-controlled, and CNOT semantics. Its integrated
  build passed with 3,590 jobs and the maintained audit now has 335 checks.
- `Primitive n` stores only `kind`, `support`, and a certified full-register
  `denotation`; its `mk` constructor is private to `Barenco/Circuit.lean`. A trusted
  arbitrary-two-qubit smart constructor must therefore be added in that file.
- `PrimitiveKind.arbitraryTwoQubit` already exists. No current smart constructor
  inhabits it, and `Primitive.unclassified` deliberately has full support and kind
  `.other`; it is not a legal shortcut.
- Existing smart constructors establish the intended pattern: a public definition
  fixes kind/support/denotation together, followed by definitional kind/support/
  denotation lemmas and a proved support-cardinality theorem.
- `Primitive.adjoint` preserves kind and support and replaces denotation by group
  inverse. `Circuit.eval_singleton`, `gateCount`, `kindCount`, `touchedSupport`, and
  generic adjoint theorems already operate on any trusted primitive.
- `CostModel.oneQubitCNOT` rejects `.arbitraryTwoQubit`; the Section 8
  `CostModel.arbitraryTwoQubit` assigns it `some 1`. Cost is a partial fold over
  literal primitive syntax, so singleton cost facts can be derived without
  changing either model.
- `Primitive` cannot recover the originating local matrix after construction.
  Stage 3 proves compatibility for an explicitly constructed node; Stage 4's
  separate payload IR remains responsible for retaining optimizer-visible local
  payloads.

## Updated Assumptions

- The only required high-fanout edit is an import plus the trusted constructor and
  cheap structural/denotation lemmas in `Barenco/Circuit.lean`. There is no public
  `Primitive.ext`, but external proof leaves may eliminate existing primitives;
  compiled probes therefore keep whole-record swap/adjoint equalities, basis
  action, singleton evaluation, counts, and costs in the narrow
  `Barenco/TwoWire/Circuit.lean` consumer.
- The constructor will be named `Primitive.twoQubit`, take exactly
  `(pair : OrderedWirePair n)` and `(U : TwoQubitUnitary)`, declare support
  `{pair.first, pair.second}`, and use `twoWireUnitary pair U` as denotation.
- Structural support is an upper bound, not minimal semantic support: identity and
  scalar `U` still have the declared two-wire support and Section 8 singleton cost
  one. The finset `{pair.first,pair.second}` is necessarily unordered; pair
  orientation survives in the constructor argument and certified denotation, not
  in support metadata.
- The expected adjoint law is exact syntax equality
  `(Primitive.twoQubit pair U).adjoint = Primitive.twoQubit pair U⁻¹`; it must use
  `twoWireUnitary_inv`, not phase relaxation or metadata inference.
- Literal singleton syntax should yield gate count one, arbitrary-two-qubit kind
  count one, touched support `{first,second}`, Section 8 cost `some 1`, and strict
  one-qubit/CNOT cost `none`.

## Big Picture Objective

Connect the certified ordered two-wire semantic embedding to trusted, countable
circuit syntax without weakening the private-constructor boundary, then prove all
structural, evaluator, adjoint, and model-specific resource facts from that literal
syntax.

## Detailed Implementation Plan

- Edit `Barenco/Circuit.lean` narrowly:
  - import `Barenco.TwoWire.Semantics` alongside the existing controlled semantics;
  - add `Primitive.twoQubit pair U` using the private constructor;
  - prove exact kind, support, support-cardinality, denotation, and raw-denotation
    projection lemmas.
- Add `Barenco/TwoWire/Circuit.lean` importing the trusted syntax and cost layer:
  - prove whole-primitive pair-swap and exact compatibility with
    `Primitive.adjoint` and local inverse by eliminating existing records, never
    manufacturing a private-constructor value;
  - bridge certified basis action and arbitrary spectator-zero to the primitive;
  - prove singleton evaluator and basis-action theorems;
  - prove singleton gate count, arbitrary-two-qubit kind count, touched support,
    Section 8 cost one, and one-qubit/CNOT rejection;
  - expose only syntax-derived resource theorems.
- Add root-excluded `Barenco/TwoWireCircuitExamples.lean` covering canonical width
  two, nonadjacent width five, swapped orientation, adjoint, singleton evaluation,
  and both cost-model boundaries.
- Run existing one-qubit/CNOT/controlled/Toffoli and lower-bound adjacent consumers
  after the high-fanout edit. Integrate only the stable leaf into `Barenco.lean` and
  add representative maintained axiom checks after focused verification.
- Synchronize conventions, Section 8 traceability, axiom documentation, this stage
  file, and `goal-2/0-plan.md`; then run the required full build.

## Build Structure

- `Barenco/Circuit.lean` — public runtime trust boundary; only the constructor and
  cheap projections requiring private `Primitive.mk` belong here.
- `Barenco/TwoWire/Circuit.lean` — public proof/resource consumer; imports
  `Barenco.Cost` and owns adjoint/evaluator/basis/count/cost consequences.
- `Barenco/TwoWireCircuitExamples.lean` — diagnostic and root-excluded.
- `Barenco/Cost.lean` — intentionally unchanged unless an actual missing generic
  theorem prevents the narrow leaf; cost-model definitions already classify the
  new kind.
- `Barenco.lean` and `Barenco/AxiomAudit.lean` — public export and maintained audit
  only after focused leaves pass.
- Documentation files — `docs/conventions.md`, `docs/traceability.md`, and
  `docs/axiom-audit.md`.
- Focused build:
  `lake build Barenco.Circuit Barenco.TwoWire.Circuit Barenco.TwoWireCircuitExamples`.
- Adjacent regression build:
  `lake build Barenco.Cost Barenco.ControlledCircuit.Decomposition`
  `Barenco.LowerBounds.BasicCircuit Barenco.ThreeQubit.RelativePhase`
  `Barenco.TwoWireCircuitExamples Barenco.AxiomAudit Barenco`.
- Because `Circuit.lean` is high-fanout, completion also requires a full
  `lake build` after public integration, plus direct strict and trust-zero
  compilation of the changed public leaves, root, and audit.

## Boundary Checks

- `Primitive.twoQubit` is constructed only from a certified local
  `TwoQubitUnitary` and an ordered distinct pair. No caller supplies the ambient
  denotation, kind, or support independently.
- No use of `Primitive.unclassified`, no direct constructor bypass outside
  `Circuit.lean`, and no arbitrary full-register unitary receives a two-wire tag.
- Pair orientation is retained exactly. Swapping pair endpoints without locally
  reindexing `U` is not identified with the original primitive.
- Support `{first,second}` is structural and may overapproximate identity/scalar
  semantics. No theorem claims minimal affected support.
- Adjoint compatibility is exact and retains local payload only in the theorem
  about an explicit constructor call; no inverse payload is reconstructed from an
  arbitrary existing primitive.
- Every count and cost theorem inspects literal singleton circuit syntax. Semantic
  equality alone never supplies a resource result.
- `oneQubitCNOT` rejection and `arbitraryTwoQubit` acceptance remain separate.
- No optimizer, fusion rule, disputed paper count, or payload-recovery function is
  introduced in this stage.

## No-Cheating Checks

- Search the implementation for `Primitive.unclassified` and direct `.other`
  construction; both must be absent from new runtime code.
- Confirm the smart constructor's only denotation expression is
  `twoWireUnitary pair U` and its only support is the endpoint finset.
- Confirm resource theorems reduce `Circuit.gateCount`, `kindCount`,
  `touchedSupport`, and `cost` on the actual singleton list.
- Confirm the one-qubit/CNOT result is `none`; do not manufacture or assume an
  explicit decomposition of a generic `U(4)`.
- Repository scans reject proof holes, custom axioms/opaque declarations, and
  forbidden decision shortcuts.

## Completion Requirements

- [x] Trusted `Primitive.twoQubit` compiles with exact kind, two-endpoint structural
  support, support card two, certified denotation, and raw denotation theorems.
- [x] Adjoint compatibility, primitive/singleton basis action, exact singleton
  evaluator, and spectator-zero consequences compile for arbitrary ambient width.
- [x] Literal singleton gate count, kind count, touched support, Section 8 cost one,
  and one-qubit/CNOT rejection theorems compile; generic adjoint costs remain exact.
- [x] Width-two, swapped-orientation, and nonadjacent diagnostics exercise semantics,
  adjoint, syntax, support, counts, and both model boundaries.
- [x] Existing primitive/cost/controlled/Toffoli/lower-bound consumers retain their
  behavior after the high-fanout edit.
- [x] Stable public imports and representative maintained axiom checks are added;
  diagnostics remain root-excluded and all new checks use accepted foundations.
- [x] Focused, adjacent, full, strict, trust-zero, forbidden/no-cheating, and diff
  checks pass with exact results recorded.
- [x] Conventions, traceability, axiom docs, this stage file, and `0-plan.md` are
  folded forward with Stage 3 marked complete and Stage 4 resumable.

## Stage Results

- Stage file created before any Stage 3 Lean source change.
- The high-fanout edit to `Barenco/Circuit.lean` is limited to the low
  `TwoWire.Semantics` import, trusted `Primitive.twoQubit pair U`, and definitional
  kind/support/denotation plus support-cardinality facts. Its body fixes kind
  `.arbitraryTwoQubit`, unordered endpoint support, and certified
  `twoWireUnitary pair U`; callers cannot independently supply any of those fields.
- Added public proof/resource leaf `Barenco/TwoWire/Circuit.lean`. It proves exact
  primitive pair reversal with local bit-swap reindexing, exact adjoint as the same
  pair carrying `U⁻¹`, primitive and singleton basis/four-term/spectator-zero
  action, singleton evaluation, gate/kind/touched-support results, early-model
  rejection, Section 8 cost one, and specialized adjoint resource preservation.
  `Barenco/Cost.lean` required no edit.
- An initial assumption that whole-record equalities required private-constructor
  access was disproved by a strict/trust-zero external elimination probe. The
  swap/adjoint proofs therefore remain in the narrow leaf, preserving the frozen
  minimal high-fanout boundary. This does not expose a payload extractor or permit
  construction around `Primitive.mk`.
- Added root-excluded `Barenco/TwoWireCircuitExamples.lean`: canonical width-two
  singleton evaluation recovers arbitrary `U(4)`; the same local CNOT on the
  reversed pair is ambient `1 → 0`; nonadjacent `(4,1)` syntax has exact symbolic
  action and spectator preservation; adjoints carry inverse payloads; structural
  support/counts and both model outcomes are checked literally.
- `Barenco.lean` exports `Barenco.TwoWire.Circuit` but not either diagnostic leaf.
  Thirteen representative Stage 3 checks raise the maintained audit from 335 to
  348; every new result uses only `propext`, `Classical.choice`, and `Quot.sound`.
- Focused builds passed with 2,363 jobs for the core constructor, 2,365 for the
  proof/resource leaf, and 2,368 for diagnostics. The adjacent cost/controlled/
  lower-bound/relative-phase build passed with 2,938 jobs; a broader reverse-
  dependency sweep passed with 3,508. The final integrated public/audit regression
  passed with 3,593 jobs and the post-integration full `lake build` passed with
  3,589 jobs.
- Direct warning-as-error and trust-zero warning-as-error compilation passed for
  `Circuit.lean`, the public two-wire circuit leaf, diagnostics, public root, and
  axiom audit. Repository proof-hole/custom-declaration/forbidden-decision scans,
  scoped constructor/no-fallback/root-exclusion/import-layer scans, and
  `git diff --check` were clean. The only scoped `Primitive.mk` scan hit is an
  explanatory docstring, not use of the private constructor.
- `docs/conventions.md`, `docs/traceability.md`, `docs/axiom-audit.md`, and
  `docs/final-report.md` now describe the trusted constructor, unordered support
  versus ordered denotation, literal cost boundaries, 348-check audit, and current
  build results. Stage 4 remains responsible for a separate payload-preserving IR;
  no local payload is reconstructed from arbitrary existing primitive metadata.
