# 5-NORMALIZE

Status: in progress (2026-07-10).

## Current Facts

- Stage 4 publicly exports a closed, fully inspectable `FusionPrimitive` grammar
  with explicit one-qubit, ordered CNOT, and ordered certified `U(4)` payloads.
  `FusionCircuit` is chronological and has exact lowering, evaluation, append,
  support, and payload-preserving adjoint bridges.
- `FusionProgram` keeps arbitrary existing primitives only as exact barriers.
  Visible lifting and all-barrier lifting preserve syntax, evaluation, support,
  adjoint, and partial costs exactly; no local payload is reconstructed from
  `Primitive.kind` or `Primitive.support`.
- `FusionResources` proves literal component counts and generic Option-valued cost
  agreement after lowering. `oneQubitCNOT` accepts exactly visible circuits with
  no generic `U(4)` node; `arbitraryTwoQubit` charges every visible node one.
- Head-first chronology is fixed: replacing chronological `U;V` by one local
  payload must use `V * U`.
- Existing semantic bridges identify a one-qubit gate on local bit `0`/`1` and
  canonical CNOT `0 -> 1` inside any ordered pair. `twoWireUnitary_mul` and the
  proof-irrelevance/orientation laws provide the exact ambient algebra required by
  Section 8 fusion.
- Finite wire indices have executable equality, but arbitrary certified complex
  unitary payloads do not have a justified computable `DecidableEq`. A normalizer
  may compare wires and syntax tags; it must not decide matrix equality or use
  `Classical.decEq` as a fake executable identity/inverse test.
- Equality-free adjacent fusion is sufficient to combine same-wire one-qubit
  nodes, same-oriented-pair `U(4)` nodes, CNOT with endpoint-local gates, and the
  three relative-A groups. Automatic deletion of an arbitrary payload followed by
  its inverse requires additional honest syntactic provenance or a supplied
  certificate; the raw payload value alone does not retain that provenance.
- Stage 4's transparent controlled-U, relative-A, and Gray inputs remain raw:
  `(4,2,6)`, `(4,3,7)`, and
  `(4(2^m-1), 3*2^m-4, 7*2^m-8)`. No disputed merger count is yet established.
- A strict/trust-zero disposable Section 8 prototype against the actual API
  reifies CNOT as ordered local `0 -> 1`, greedily fuses endpoint-compatible
  nodes, proves every supported branch has denotation
  `second.denotation * first.denotation`, and reduces the generic relative-A input
  definitionally from seven nodes to three `U(4)` nodes.
- A second compiled prototype supplies a reusable tail-first adjacent-rewrite
  engine with results `blocked`, `deleted`, or `fused gate`. From executable
  identity/combination functions plus semantic soundness certificates it proves
  exact chronological evaluation, length nonincrease, a precise `Stable`
  predicate, fixed points, and unconditional idempotence.

## Updated Assumptions

- Separate two deterministic policies. The early policy may fuse compatible
  one-qubit syntax and perform proved disjoint commutations but must retain every
  CNOT literally. The Section 8 policy may reify a CNOT and endpoint-local gates
  into one ordered `U(4)` node and fuse compatible ordered-pair nodes.
- Operate on visible runs and lift the pass across `FusionProgram` barriers without
  moving, deleting, relabeling, or repricing a barrier. A barrier splits all local
  rewrite context.
- Use constructor-specific semantic theorems for commutation and absorption.
  Unordered support metadata may help state a normal-form predicate but is never
  sufficient evidence for a rewrite.
- Prove cost monotonicity conditionally in the partial model: if input cost is
  `some inputCost`, output has `some outputCost` with
  `outputCost <= inputCost`. Unsupported inputs remain unsupported unless a
  separately proved policy theorem states otherwise.
- Generic raw-payload normalization never tests arbitrary matrix identity. Add an
  honest symbolic cancellation layer whose one-qubit payload is
  `FreeGroup Atom`, parameterized by `[DecidableEq Atom]` and one valuation
  `Atom -> QubitUnitary`. Free-group reduction makes identity and inverse
  cancellation executable; `FreeGroup.lift` proves the exact denotation. Fresh
  keys reify arbitrary unrelated payloads conservatively, while coherent future
  builders may deliberately share one key with opposite polarity.
- A useful stable result may be a deterministic pass with a proved local
  fixed-point/stability predicate rather than a globally canonical or minimal
  circuit. Idempotence is required only if it follows from the actual pass.

## Big Picture Objective

Implement a terminating, target-independent exact normalization layer over the
payload IR. Prove every local rewrite in arbitrary ambient width, compile the
complete passes exactly, preserve barriers and scalar phase, and derive
model-specific nonincreasing costs from literal output syntax.

## Detailed Implementation Plan

- Add `Barenco/Optimization/NormalizeCore.lean`:
  - define generic `CombineResult := blocked | deleted | fused gate`;
  - define structurally recursive insertion and tail-first normalization;
  - prove exact group-valued chronological soundness, length nonincrease,
    stability, fixed points, and idempotence from explicit local certificates.
- Add `Barenco/Optimization/FusionLaws.lean`:
  - prove exact same-wire one-qubit chronological multiplication;
  - prove exact same-oriented-pair `U(4)` chronological multiplication;
  - define local-bit `0`/`1` embeddings and canonical local CNOT payloads;
  - prove all four left/right endpoint-local absorption laws;
  - prove exact conversion of an explicit CNOT to its ordered-pair `U(4)` payload;
  - prove only the constructor-specific disjoint commutations consumed by the
    normalizer;
  - prove exact identity and inverse-cancellation laws at the strongest executable
    syntactic/proof-carrying level actually supported.
- Add `Barenco/Optimization/SymbolicCancellation.lean`:
  - define decidable free-group one-qubit words and certified atom valuation;
  - erase symbolic one-qubit/CNOT syntax exactly into `FusionCircuit`;
  - instantiate the generic engine so same-wire words compose chronologically and
    inverse words/empty identity delete without matrix equality;
  - prove evaluator preservation, literal count nonincrease, stability, and
    idempotence; retain CNOT nodes literally.
- Add `Barenco/Optimization/Normalize.lean`:
  - define deterministic visible-run passes for the early and Section 8 policies;
  - compare only decidable wire/orientation/provenance data;
  - lift normalization across mixed programs with barriers as hard separators;
  - prove termination structurally and exact `FusionCircuit.eval`/lowered
    `Circuit.eval` preservation for every pass and complete normalizer;
  - state and prove the actual normal-form or stability predicate and idempotence
    only if achieved.
- Add `Barenco/Optimization/NormalizeResources.lean`:
  - prove literal gate/component count changes for every rewrite;
  - prove early-policy preservation of CNOT count and accepted-cost nonincrease;
  - prove Section 8 accepted-cost/gate-count nonincrease;
  - prove mixed-program conditional cost nonincrease and exact barrier retention;
  - keep unsupported model results as `none` rather than assigning a fabricated
    decomposition cost.
- Extend root-excluded `Barenco/FusionExamples.lean` (or add a narrower
  `Barenco/NormalizeExamples.lean` if imports become heavy) with nonadjacent,
  reversed-orientation, append-boundary, scalar-phase, explicit inverse,
  model-separation, and unsupported-barrier diagnostics. Include the generic
  seven-node relative-A input as a regression input without yet claiming the
  paper-facing Stage 6 classification.
- Integrate only stable normalization leaves into `Barenco.lean` and add
  representative maintained axiom checks after focused/adjacent verification.
  Synchronize conventions, traceability, axiom docs, this stage file, and
  `goal-2/0-plan.md`.

## Build Structure

- `Barenco/Optimization/NormalizeCore.lean` — low public generic runtime/proofs;
  depends only on group/list infrastructure.
- `Barenco/Optimization/FusionLaws.lean` — public proof-side exact local algebra;
  imports the narrow two-wire controlled bridges plus Fusion IR/NormalizeCore.
- `Barenco/Optimization/FusionCommutation.lean` — narrow proof-only wrappers around
  exact disjoint local/CNOT laws; isolates the heavier `ThreeQubit.Lemma61` import.
- `Barenco/Optimization/SymbolicCancellation.lean` — public executable certified
  free-group cancellation layer; imports NormalizeCore and Fusion IR/resources.
- `Barenco/Optimization/Normalize.lean` — public runtime pass and exact semantic
  soundness; imports FusionLaws but no paper-specific construction.
- `Barenco/Optimization/NormalizeResources.lean` — public proof/resource leaf;
  imports Normalize and FusionResources/Cost.
- Optional narrow provenance module if compiled experiments show it must sit below
  Normalize; it may not widen `Primitive` or hide a noncomputable equality test.
- `Barenco/FusionExamples.lean` or `Barenco/NormalizeExamples.lean` — diagnostic,
  exhaustive, and negative boundary checks; root-excluded.
- `Barenco.lean`, `Barenco/AxiomAudit.lean`, and documentation — stable integration
  only after focused leaves compile.
- High-fanout `Circuit`, `Primitive`, `CostModel`, and Stage 4 IR definitions are
  intentionally unchanged unless a checked missing law forces a documented narrow
  migration.
- Focused sequence:
  `lake build Barenco.Optimization.NormalizeCore`,
  `Barenco.Optimization.FusionLaws`, and
  `Barenco.Optimization.SymbolicCancellation`, then
  `Barenco.Optimization.Normalize`, `Barenco.Optimization.NormalizeResources`, and
  the diagnostic leaf.
- Adjacent sequence includes Stage 4 canonical/relative/Gray inputs, existing
  controlled expansion, relative phase, cost/lower-bound consumers, root, and
  audit. Public integration requires direct strict/trust-zero root/audit checks and
  a full build.

## Boundary Checks

- Every fused `U(4)` node is constructed from an `OrderedWirePair` and a certified
  local product through `FusionPrimitive.twoQubit`; no ambient unitary, kind, or
  support is supplied independently.
- Reversing an ordered pair is not same-pair fusion. A swap is legal only through
  the explicit local bit-swap reindexing theorem.
- Chronological `first;second` always forms local payload `second * first`.
- Exact equality is the only optimizer relation. Global, basis-dependent, or
  measurement phase quotients are not used, and scalar phases are retained.
- Disjoint rewrites use proved constructor semantics, never support metadata alone.
- Barriers are neither crossed nor converted to visible gates. All-barrier input is
  an exact fixed preservation path.
- The early policy never emits a generic `U(4)` node or consumes a CNOT into one;
  the Section 8 policy may do so and must state that the early cost then becomes
  unsupported.
- No theorem infers a resource result from evaluator equality. Counts and costs are
  folds over the actual normalized output list.
- A locally stable result is not described as globally optimal, complete, minimal,
  or canonical.

## No-Cheating Checks

- Search runtime code for `Classical.decEq`/`Classical.choice` used to compare
  payloads, `Primitive.unclassified`, direct primitive fields, ambient-unitary
  rewrite outputs, and example-specific branch constants; all are forbidden.
- Confirm every visible output branch calls only visible constructors and every
  barrier branch preserves its stored primitive verbatim.
- Inspect multiplication order in every same-wire/same-pair/absorption branch and
  test it with noncommuting symbolic payloads.
- Confirm early-policy output contains no `.twoQubit` when its input contains none,
  and Section 8 cost reduction is linked to emitted literal `.twoQubit` syntax.
- Confirm inverse cancellation consumes explicit syntactic provenance or a theorem
  argument; it may not test semantic equality of arbitrary unitary matrices.
- Repository scans reject proof holes, custom axioms/opaque declarations,
  forbidden decision shortcuts, and root imports of diagnostics.

## Completion Requirements

- [ ] Exact local fusion, pair embedding/absorption, required disjoint commutation,
  and honest identity/inverse-cancellation laws compile for arbitrary ambient width.
- [ ] Executable deterministic early and Section 8 passes terminate and preserve
  exact visible and lowered evaluators, with correct chronological multiplication.
- [ ] Mixed-program normalization treats every barrier as an exact hard separator
  and preserves all-barrier programs definitionally or by an exact round trip.
- [ ] The output satisfies a precisely stated normal-form/stability predicate;
  idempotence is proved only if the implementation establishes it.
- [ ] Early accepted cost is nonincreasing while CNOT syntax/count is preserved;
  Section 8 accepted cost is nonincreasing; partial/unsupported cases remain honest.
- [ ] Diagnostics cover width-two, nonadjacent, reversed pair, append boundary,
  scalar phase, inverse provenance, model separation, relative A, and barriers.
- [ ] Stable public imports and representative axiom checks are integrated; focused,
  adjacent, strict, trust-zero, forbidden/no-cheating, full, and diff checks pass.
- [ ] Conventions, traceability, axiom docs, this stage file, and `0-plan.md` are
  folded forward with Stage 5 marked complete and Stage 6 resumable.

## Stage Results

- Stage file created after Stage 4's requirement-by-requirement audit and before
  any Stage 5 Lean source change.
