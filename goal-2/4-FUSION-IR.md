# 4-FUSION-IR

Status: complete (2026-07-10).

## Current Facts

- Stages 2–3 provide the exact semantic and trusted syntax boundaries needed by a
  compiler layer: `localUnitary`/`Primitive.oneQubit`, certified CNOT syntax, and
  `twoWireUnitary`/`Primitive.twoQubit` all have arbitrary-width evaluator,
  support, adjoint, and named-cost facts.
- `Primitive` intentionally stores only `kind`, `support`, and ambient denotation.
  Even a trusted `Primitive.twoQubit pair U` does not expose `pair` or `U` after it
  is erased to an arbitrary `Primitive`. Reconstructing optimizer payloads from
  kind/support/denotation is therefore unavailable and forbidden.
- `Circuit n` is a chronological `List (Primitive n)` and evaluates the head first.
  `Circuit.append first second` lowers to list append and evaluates as
  `eval second * eval first`.
- Both named cost models are partial folds over literal primitive kinds.
  `oneQubitCNOT` accepts only one-qubit and CNOT syntax;
  `arbitraryTwoQubit` additionally accepts trusted generic two-wire nodes and
  zero/one-control macros. Unsupported nodes produce `none`.
- The seven-node relative-phase A circuit is already transparent literal syntax:
  four target rotations and three CNOTs. It can be rebuilt directly in an
  optimizer-visible grammar and lowered definitionally to the existing circuit.
- `expandedGrayControlledCircuit` has exact semantics and raw profile
  `(4(2^m-1), 3*2^m-4, 7*2^m-8)`, but each six-node controlled-root block is the
  opaque `selectedControlledU2Circuit` chosen only by an aggregate spec. Its
  boundary chronology is unavailable to an optimizer.
- The ingredients for a transparent replacement are public:
  `selectedColumnABCFactors (specialUnitaryPart U)` exposes checked `A/B/C`,
  `determinantPhaseAngle U` and `controlPhaseUnitary` expose the scalar correction,
  and parameterized `controlledU2Circuit` proves the exact six-node evaluator.
  Gray masks, pivots, edges, signed roots, and layout wire proofs are also public.
- Stage 3's final high-fanout regression passed with 3,593 jobs, the full build with
  3,589 jobs, and the maintained audit has 348 standard-foundation checks.

## Updated Assumptions

- Keep `FusionPrimitive n` closed and fully inspectable with exactly explicit
  one-qubit, CNOT, and ordered two-qubit payloads; `FusionCircuit n` is its
  chronological list. Put opaque existing primitives in a separate mixed
  `FusionStep`/`FusionProgram` layer whose alternatives are a visible fusion gate
  or an exact barrier. This prevents barriers from inhabiting the local grammar.
- Visible lowering is `List.map` through trusted smart constructors; mixed-program
  lowering maps a visible step through that compiler and a barrier to its original
  primitive unchanged. Evaluator equality and append chronology should be
  definitional or proved by short induction.
- A total barrier lift from `Circuit n` to `FusionProgram n` should preserve every
  unsupported input exactly and satisfy an exact lowering round trip. Transparent
  builders, rather than metadata recovery, create optimizable nodes.
- IR structural kind/support/gate-count/kind-count/touched-support and partial cost
  should be executable folds that provably equal the corresponding established
  `Circuit` quantities after lowering. The two named models remain separate.
- A strict/trust-zero disposable prototype confirms that payload-preserving
  adjoints stay inside the visible grammar. Local-gate and two-wire branches use
  exact inverse payloads; the CNOT branch follows from its arbitrary-width basis
  action and self-inverse Boolean update. The mixed barrier branch delegates to
  the established exact `Primitive.adjoint`.
- Replace the opaque controlled-U choice for optimizer inputs with one coherent
  transparent selected-factor schedule. The existing opaque circuit remains a
  semantic/resource reference, never an optimizer input.

## Big Picture Objective

Introduce a small compiler IR that retains exactly the local payload needed for
future fusion, lowers only through trusted circuit constructors, preserves exact
full-register semantics and syntax-derived resources, and can represent the
relative-phase and Gray inputs without inspecting opaque primitive metadata.

## Detailed Implementation Plan

- Add `Barenco/Optimization/FusionIR.lean`:
  - define closed explicit `oneQubit`, `cnot`, and `twoQubit` nodes/circuits;
  - define a separate visible-step/barrier mixed program layer;
  - define trusted node/circuit/program lowering, chronological evaluation,
    append, and barrier lifting with an exact round trip;
  - prove kind/support/denotation projections agree with lowering;
  - add payload-preserving adjoints with exact lowering and evaluator
    compatibility for visible circuits and mixed programs.
- Add `Barenco/Optimization/FusionResources.lean`:
  - define literal gate count, kind count, touched support, and partial cost folds
    for visible circuits and mixed programs;
  - prove equality to `Circuit.gateCount`, `kindCount`, `touchedSupport`, and
    `cost` on the lowered syntax;
  - prove append and barrier-lift resource bridges and both named-model boundaries.
- Add `Barenco/ControlledCircuit/CanonicalSelected.lean`:
  - construct one transparent six-node fusion circuit from the selected
    determinant phase and column-chronological `A/B/C` factors;
  - prove its lowering is the parameterized `controlledU2Circuit`, its evaluator is
    the desired singleton-controlled `U`, and its literal profile is `(4,2,6)`.
- Add `Barenco/ThreeQubit/RelativePhaseFusion.lean`:
  - rebuild relative-phase A in fusion syntax;
  - prove exact lowering equality to the existing seven-node circuit, exact
    evaluator transfer, and literal pre-normalization profile `(4,3,7)`.
- Add `Barenco/MultiControl/GrayFusion.lean` at the smallest useful generality:
  - use the public Gray mask/pivot/edge schedule and the transparent controlled-U
    fusion block, never `selectedControlledU2Circuit`;
  - prove exact full-register evaluator equality to the checked Gray macro target;
  - prove literal raw profile matching Goal 1. If the full parameterized schedule
    exposes a new proof dependency, finish at least the one-control and one indexed
    transition blocks and record the exact remaining general constructor rather
    than substituting the opaque witness.
- Add root-excluded `Barenco/FusionExamples.lean` covering lowering chronology,
  barrier round trip, model separation, relative A, and a Gray boundary.
- Integrate only stable public leaves into the root/audit after focused builds;
  update conventions, traceability, axiom docs, stage results, and the master plan.

## Build Structure

- `Barenco/Optimization/FusionIR.lean` — public runtime plus exact lowering/eval
  core; imports the trusted two-wire circuit layer but no paper construction.
- `Barenco/Optimization/FusionResources.lean` — public proof/resource leaf;
  imports the IR and established `Cost` API.
- `Barenco/ControlledCircuit/CanonicalSelected.lean` — public noncomputable
  transparent factor schedule and exact compiler bridge.
- `Barenco/ThreeQubit/RelativePhaseFusion.lean` — public paper-input bridge.
- `Barenco/MultiControl/GrayFusion.lean` — public schedule-aware transparent Gray
  input bridge at the achieved checked generality.
- `Barenco/FusionExamples.lean` — diagnostic and root-excluded.
- `Barenco.lean`, `Barenco/AxiomAudit.lean`, and documentation — stable integration
  only after narrow leaves compile.
- High-fanout `Primitive`, `Circuit`, and `CostModel` definitions are intentionally
  unchanged in this stage.
- Focused sequence:
  `lake build Barenco.Optimization.FusionIR`, then
  `lake build Barenco.Optimization.FusionResources`, then
  `lake build Barenco.ControlledCircuit.CanonicalSelected`,
  `Barenco.ThreeQubit.RelativePhaseFusion`,
  `Barenco.MultiControl.GrayFusion`, and `Barenco.FusionExamples`.
- Adjacent/public sequence includes existing selected controlled-U, relative-phase,
  Gray expansion, lower-bound restricted syntax, root, and audit consumers.

## Boundary Checks

- Every visible node lowers through `Primitive.oneQubit`, `Primitive.cnot`, or
  `Primitive.twoQubit`; callers cannot independently label an ambient unitary.
- A mixed-program `barrier p` lowers to exactly `p`, retains no inferred local
  payload, and blocks every future local rewrite. Barrier lifting is a preservation
  path, not an optimizer claim.
- No function attempts to translate an arbitrary existing `Primitive` into a
  visible node by inspecting `kind`, `support`, support cardinality, or denotation.
- All compiler/evaluator statements are exact full-register equalities. No scalar
  or basis-dependent phase is discarded.
- Head-first chronology is preserved. A later Stage 5 fusion of chronological
  local gates `U;V` must eventually use payload `V*U`.
- Resource equalities are derived from lowering and literal IR folds; a semantic
  evaluator equality never supplies a count.
- `oneQubitCNOT` and `arbitraryTwoQubit` costs remain distinct and Option-valued.
  A barrier retains its original syntax cost when priced and remains unsupported
  when its original kind is unsupported; neither outcome makes it fusion-visible.
- The opaque selected controlled-U circuit may be compared semantically and by
  aggregate profile, but its factors are never used as optimizer-visible nodes.
- Stage 4 does not implement normalization, claim a fixed point, or test the
  disputed post-merger formulas beyond constructing honest transparent inputs.

## No-Cheating Checks

- Search new runtime code for construction of `Primitive.unclassified`, direct
  primitive field assignments, and arbitrary ambient-unitary parameters; all must
  be absent. A mixed barrier may store an already existing `Primitive` verbatim.
- Confirm all visible lowering branches invoke trusted smart constructors and the
  barrier branch returns its stored primitive unchanged.
- Confirm resource bridge proofs inspect IR syntax/lowering rather than semantic
  matrices.
- Confirm relative/Gray builders construct their factor lists explicitly and do
  not call `selectedControlledU2Circuit` or an opaque whole-circuit choice.
- Repository scans reject proof holes, custom axioms/opaque declarations, and
  forbidden decision shortcuts.

## Completion Requirements

- [x] Closed payload-preserving node/circuit syntax plus the separate mixed barrier
  program and trusted lowering compile with exact kind, support, denotation,
  chronology, append, and barrier round-trip theorems.
- [x] Executable IR gate count, kind count, touched support, and partial cost agree
  exactly with the lowered `Circuit` under both named models.
- [x] Visible one-qubit/CNOT/two-qubit nodes retain every payload needed by Stage 5;
  unsupported existing primitives can enter only through exact mixed barriers and
  never inhabit `FusionPrimitive`.
- [x] A transparent selected arbitrary controlled-U fusion circuit lowers to the
  parameterized six-node circuit, has exact evaluator, and literal profile
  `(oneQubit,CNOT,total) = (4,2,6)`.
- [x] Relative-phase A lowers exactly to its existing seven-node syntax with profile
  `(4,3,7)` and exact evaluator transfer.
- [x] At least one checked Gray fusion input uses the transparent factor schedule,
  has an exact evaluator bridge, and matches the corresponding Goal 1 raw counts;
  any remaining parameterized schedule work is recorded precisely.
- [x] Barrier, width-two/nonadjacent, chronology, model-boundary, relative, and Gray
  diagnostics compile without entering the public root.
- [x] Stable public imports and representative axiom checks are integrated; focused,
  adjacent, strict, trust-zero, forbidden/no-cheating, and diff checks pass.
- [x] Conventions, traceability, axiom docs, this stage file, and `0-plan.md` are
  folded forward with Stage 4 marked complete and Stage 5 resumable.

## Stage Results

- Stage file created before any Stage 4 Lean source change.
- Added public runtime leaf `Barenco/Optimization/FusionIR.lean`. Its closed
  `FusionPrimitive` grammar retains explicit one-qubit, ordered CNOT, and ordered
  certified `U(4)` payloads and lowers only through the three trusted smart
  constructors. `FusionCircuit` has independent exact evaluation, append,
  structural support, and payload-preserving adjoint APIs with exact lowering
  bridges.
- The separate `FusionStep`/`FusionProgram` layer admits arbitrary existing
  primitives only as exact barriers. Fully visible lifting and total all-barrier
  lifting both have exact lowering/evaluator theorems; mixed append, support, and
  adjoint preserve the established chronology and never recover local payloads
  from metadata. The first focused build passed with 2,364 jobs.
- Added proof/resource leaf `Barenco/Optimization/FusionResources.lean` with
  executable literal gate/kind/component counts, structural support, and generic
  Option-valued costs for visible circuits and mixed programs. Every quantity has
  an exact lowering bridge. The visible Section 8 model costs precisely literal
  length; the early model accepts exactly circuits with zero generic `U(4)` nodes;
  unsupported visible nodes and stored barriers propagate `none`. Its first
  focused build passed with 2,366 jobs.
- Added `Barenco/ControlledCircuit/CanonicalSelected.lean`: the transparent
  chronological schedule `phase(control); A; CNOT; B; CNOT; C` uses the checked
  selected factors of `specialUnitaryPart U`, lowers definitionally to the
  parameterized `controlledU2Circuit`, and has exact singleton-controlled-`U`
  semantics. Literal visible syntax proves profile `(4,2,0,6)` for
  `(oneQubit,CNOT,generic-U(4),total)` and cost six in both pre-normalization
  models; no opaque whole-circuit witness is an optimizer input.
- Added `Barenco/ThreeQubit/RelativePhaseFusion.lean`: the paper's A diagram is a
  transparent seven-node visible circuit, lowers exactly to the established
  `relativePhaseToffoliACircuit`, transfers its exact arbitrary-width evaluator,
  and proves literal profile `(4,3,0,7)` plus cost seven in both models. The
  combined canonical/relative focused build passed with 2,942 jobs.
- Added `Barenco/MultiControl/GrayFusion.lean` for the full parameterized positive-
  control family, not merely a low-dimensional probe. It rebuilds every root block
  from the public Gray masks/pivots, the transparent canonical factor circuit, and
  literal generated CNOT edges; it never imports or inspects the opaque selected
  expansion. Prefix induction proves exact equality with the checked Lemma 7.1
  macro evaluator on arbitrary ambient width. Literal syntax proves raw profile
  `4(2^m-1)` one-qubit nodes, `3*2^m-4` CNOTs, and `7*2^m-8` total/early-model
  cost for every `m=tail+1>0`, with explicit one-, two-, and three-control checks.
  Its focused build passed with 3,469 jobs.
- Added root-excluded `Barenco/FusionExamples.lean`. It checks canonical width two,
  oriented nonadjacent width five, exact `U;V ↦ V*U` chronology, lossless Toffoli
  barriers and both-model rejection, generic-`U(4)` model separation, transparent
  controlled-U and relative-A profiles, the general Gray formulas, and the
  one-control `(4,2,6)` boundary. Its combined focused verification passed with
  3,478 jobs; the public root and audit contain no diagnostic import.
- `Barenco.lean` now exports the five stable Stage 4 leaves. Twenty-nine maintained
  checks raise `Barenco/AxiomAudit.lean` from 348 to 377 entries; every new result
  reports only `propext`, `Classical.choice`, and `Quot.sound`. Public/audit builds
  passed with 3,595 jobs, and the combined public/diagnostic regression passed with
  3,596 jobs.
- Direct warning-as-error and trust-zero warning-as-error compilation passed for
  every new public leaf, the diagnostic, root, and audit. The adjacent regression
  against selected controlled-U, existing relative phase, Lemma 7.1/Gray
  expansion, cost, and lower-bound consumers passed with 3,481 jobs; final
  `lake build` passed with 3,594 jobs.
- Repository proof-hole, forbidden-decision, custom-axiom/opaque, constructor-
  forgery, opaque-input, semantic-to-count, and root-exclusion scans were clean.
  Canonical/Gray runtime code contains no use of `selectedControlledU2Circuit`,
  `GrayExpansion`, unclassified primitives, or barrier shortcuts. Audit source and
  documentation both contain exactly 377 entries, and `git diff --check` passed.
- `docs/conventions.md`, `docs/traceability.md`, `docs/axiom-audit.md`, and
  `docs/final-report.md` now record the visible/barrier boundary, transparent paper
  inputs, raw Gray profile, current public API, build evidence, and explicit fact
  that no disputed merger has yet been claimed. Stage 5 can start from a fully
  compiled exact IR and must implement the executable rewrite layer itself.
