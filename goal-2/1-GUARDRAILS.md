# 1-GUARDRAILS

Status: complete (2026-07-10).

## Current Facts

- Goal 1 is complete and the working tree began this stage clean at commit
  `aaef54f`. The pinned baseline is Lean 4.31.0 with mathlib commit
  `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`; the maintained audit currently has
  319 `#print axioms` entries.
- `Circuit n` is `List (Primitive n)` in chronological order. Its evaluator is
  `eval (primitive :: tail) = eval tail * primitive.denotation`, so a chronological
  pair `[U,V]` fuses to local product `V * U`.
- `Primitive` has a private constructor and only three stored fields: `kind`, an
  unordered structural `support`, and a certified full-register `denotation`.
  There is no retained target/control/pair/local-matrix payload and no generic
  theorem that disjoint support metadata implies commuting denotations.
- `PrimitiveKind.arbitraryTwoQubit` and its Section 8 unit price already exist, but
  no trusted smart constructor currently inhabits that kind. The only general
  semantic wrapper is `Primitive.unclassified`, which has full support and is
  rejected by both named models.
- `Primitive.adjoint` retains kind/support and inverses the denotation. A new
  inspectable optimization layer must retain enough payload to express its local
  inverse rather than trying to recover it from the full-register matrix.
- Existing semantic infrastructure includes certified reindex, block-diagonal,
  and Kronecker unitary constructors; `splitTarget` and target-block algebra handle
  one selected wire. The precise lowest-dependency ordered-pair construction is
  still being audited.
- `selectedControlledU2Circuit` and the selected exact-Toffoli expansion use
  `Classical.choose` witnesses whose specs retain semantics and aggregate counts
  but not optimizer-visible boundary factors. Transparent factor and explicit
  expansion APIs exist below those selection layers and must be used instead.
- The relative-phase A circuit is the literal chronology
  `A(target); CNOT(second,target); A(target); CNOT(first,target);`
  `A†(target); CNOT(second,target); A†(target)`. Its existing exact evaluator and
  `BasisPhaseEq` consequences are arbitrary-width; its literal Section 8 cost is
  seven. The paper's three-gate statement is a constructed upper-count target, not
  a minimality claim.
- For `m=n-1>=1` controls, the existing raw Gray expansion has exactly
  `4*(2^m-1)` one-qubit nodes and `3*2^m-4` CNOTs. The source prints post-merger
  counts `2*2^m` and `3*2^m-4` respectively but supplies no merger syntax.
- For logical width `n>=7`, the corrected balanced Corollary 7.4 circuit has raw
  profile `(32n-144,24n-100,56n-244)`. The source's `48n-204` target would require
  one-qubit count `24n-104` if the checked CNOT count is unchanged. The phase-safe
  chronology uses `Arel; Bhybrid; adjoint(Arel); Bhybrid`; neither the source's
  invalid smallest split nor two forward A copies may be restored for a lower
  number.

## Updated Assumptions

- The architecture is frozen as a separate payload-preserving
  `FusionPrimitive`/`FusionCircuit` IR lowering into the stable
  `Primitive`/`Circuit` core. A direct payload refactor is rejected: `Circuit` has
  a 77-module reverse source-import closure, the extra field would create a
  permanent coherence invariant, and it would not make whole-circuit classical
  choices inspectable.
- The semantic local type is `UnitaryGate 2`, with local bit zero equal to the
  ordered pair's first ambient wire and local bit one equal to its second. Thus
  standard `Basis 2` order is exactly `00,01,10,11` for `(first,second)`.
- A trusted `Primitive.twoQubit` constructor requires a narrow edit to
  `Barenco/Circuit.lean`, because the private constructor prevents a later module
  from manufacturing a correctly tagged primitive. Its semantic embedding must
  live below `Circuit` to avoid a cycle.
- The relative-phase cost-three target appears constructively reachable without
  commutation by grouping nodes `1–3`, `4`, and `5–7`, each on one ordered pair.
- A coherent Gray expansion that chooses factors once and uses the literal adjoint
  for opposite signs may expose one inverse one-qubit pair at every internal block
  boundary. Sign alternation, chronology, and boundary arithmetic remain proof
  obligations rather than accepted facts.
- Corollary 7.4 may remain not recovered even if generic normalization is sound.
  One normalizer result cannot refute the source number without a scoped
  completeness or lower-bound theorem.
- Executable normalization will branch only on decidable wire, ordered-pair, and
  explicit syntax tags. It will not test equality of arbitrary complex unitary
  payloads. Generic inverse cancellation remains proof-side unless a later
  symbolic atom/environment layer makes the inverse relationship syntactic.

## Frozen API Inventory

- `Barenco.Basic` owns `Basis`, `Gate`, `UnitaryGate`, `QubitUnitary`, and the
  head-first evaluator convention.
- `Barenco.Semantics` owns `reindexUnitary` and its entry/one/mul/equivalence laws,
  `blockDiagonalUnitary`, `kroneckerUnitary`, `basisKet`, and
  `matrix_eq_iff_mulVec_basisKet_eq`. It is the sole required import for the
  Stage 2 core.
- Mathlib's `Equiv.piSplitAt`, `Equiv.prodAssoc`, `Equiv.prodCongr`, and
  `Equiv.piEquivPiSubtypeProd` are owned by `Mathlib.Logic.Equiv.Prod`;
  `finTwoArrowEquiv` is owned by `Mathlib.Logic.Equiv.Fin.Basic`;
  `Matrix.reindexAlgEquiv` is owned by
  `Mathlib.LinearAlgebra.Matrix.Reindex`; block-diagonal algebra is owned by
  `Mathlib.Data.Matrix.Block`; and Kronecker algebra, including
  `Matrix.mul_kronecker_mul`, is owned by
  `Mathlib.LinearAlgebra.Matrix.Kronecker`.
- A strict and trust-zero disposable prototype importing only
  `Barenco.Semantics` compiled an explicit `OrderedWirePair`, direct complement,
  `splitTwoWire : Basis n ≃ Basis 2 × PairComplementBasis`, raw/certified
  `U ⊗ I` embedding, entry/locality formula, identity, multiplication, monoid-hom,
  inverse, and pair-reversal law. No `Controlled`, `Circuit`, `Universality`, or
  `LowerBounds` import is needed by the core.
- `Barenco.Controlled` owns `localUnitary`, controlled/CNOT semantics, and
  one-target basis/spectator proof patterns. These belong only in a later
  `TwoWire.ControlledBridges` proof leaf.
- `Barenco.LowerBounds.PartitionFactorization.wireSplit` is a useful proof pattern
  but imports the circuit/lower-bound stack and is therefore forbidden as a
  downward dependency. `Barenco.Universality.TwoLevel` is likewise semantically
  different and too high in the import graph.
- There are no existing `kroneckerUnitary_one/mul/inv` wrappers. Stage 2 will prove
  the narrow fixed-identity laws with `Matrix.mul_kronecker_mul`, package the
  embedding as a monoid hom, and derive inverse preservation via `map_inv`.
- Pair reversal uses the local `Basis 2` permutation obtained by lifting
  `Equiv.swap 0 1`; entry extensionality avoids transporting between the
  propositionally equivalent but syntactically different reversed complements.

## Frozen Source and Test Boundaries

- **Cost three:** `relativePhaseToffoliACircuit` is
  `A;CNOT(second,target);A;CNOT(first,target);A†;CNOT(second,target);A†`.
  `eval_relativePhaseToffoliACircuit` is exact for arbitrary width under the two
  target inequalities. The Toffoli-relative consequence
  `relativePhaseToffoliACircuit_basisPhaseEq_toffoli` additionally requires
  `first≠second`; the sign is input-basis-dependent, not global. The current
  Section 8 cost theorem is
  `relativePhaseToffoliACircuit_arbitraryTwoQubitCost = some 7`. A verified Goal 2
  result must emit three literal pair nodes, prove exact equality to this seven-node
  evaluator, and only then inherit `BasisPhaseEq`. It remains an upper count.
- **Gray mergers:** the source states `n≥3`, `m=n-1≥2`; Lean strengthens the
  construction to `m=tail+1≥1` via `OrderedControlLayout`, keeping zero controls a
  separate local-gate case. `grayControlledViaRootCircuit` has `2^m-1` signed
  controlled roots and `2^m-2` Gray CNOTs;
  `eval_grayControlledViaRootCircuit` proves exact semantics. The literal
  `expandedGrayControlledCircuit` and its evaluator/count theorems give raw profile
  `(4*(2^m-1),3*2^m-4,7*2^m-8)`. The source target is
  `(2*2^m,3*2^m-4,5*2^m-4)`.
- The Gray candidate requires one transparent controlled-root block, its literal
  adjoint for the opposite sign, a theorem that adjacent Gray signs alternate,
  and exact target-vs-control-only commutations. At positive-to-negative boundaries
  `C/C†` cancel after crossing the Gray CNOT; at negative-to-positive boundaries
  terminal `A†` must cross its control phase, the Gray CNOT, and the next control
  phase before canceling `A`. Independent `selectedControlledU2Circuit` choices
  cannot justify either identity.
- **Corollary 7.4:** the repaired domain is `n≥7`, with the floor split from C-003.
  `balancedRelativeCorollary74Circuit` uses the exact phase-safe chronology
  `Arel;Bhybrid;adjoint(Arel);Bhybrid`, giving four exact and `8n-44` relative
  occurrences. `balancedExpandedRelativeCorollary74Circuit` has exact evaluator and
  raw profile `(32n-144,24n-100,56n-244)`, including `(80,68,148)` at width seven.
  The source target `48n-204`, if CNOTs remain fixed, requires profile
  `(24n-104,24n-100,48n-204)` and `(64,68,132)` at width seven.
- Corollary 7.4's generic phase prerequisites are the two balanced-capacity bounds
  plus the stronger target-free A bound. The dirty auxiliary has arbitrary initial
  state and must be restored. A verified result must use transparent oriented
  sixteen-node exact expansions; the opaque `exactToffoliExpansionCircuit` witness
  cannot be normalized structurally.
- `verified`, `refuted`, and `not recovered` retain the definitions in
  `goal-2/0-plan.md`. In particular, exact normalized output plus a gap is only
  “not recovered”; “refuted” requires a same-grammar/domain/relation/model
  impossibility theorem.

## Big Picture Objective

Freeze Goal 2's representation, equality, locality, cost, source-claim, module,
and verification boundaries before any Lean implementation begins.

## Detailed Implementation Plan

- Complete a declaration-level inventory of the local/mathlib APIs usable for an
  ordered two-wire split, full-register embedding, unitarity, multiplication,
  inverse, swap orientation, and basis action.
- Compare the separate optimizer IR and direct-`Primitive`-refactor designs using
  actual dependency ownership and optimizer-input requirements.
- Inspect the exact source passages, corrections C-003/C-004/C-025/C-032/C-035,
  current selected-factor APIs, and theorem signatures for all three test families.
- Freeze the ordered pair convention, supported optimizer grammar, exact equality
  relation, two normalization policies, opaque/unsupported barrier behavior, and
  verified/refuted/not-recovered status discipline.
- Freeze tentative Stage 2–5 module ownership, declaration classifications, and
  focused/adjacent build commands.
- Run the cached focused baseline, strict and trust-zero root/audit compilation,
  forbidden-source scans, and `git diff --check` before any Lean source change.
- Fold final facts and the completed design decision into `goal-2/0-plan.md`.

## Build Structure

- Stage 1 changes documentation only: this stage file and the current-facts/status
  portions of `goal-2/0-plan.md`.
- Stage 2 runtime/public leaves are `Barenco/TwoWire/Layout.lean` for the ordered
  pair/direct basis split and `Barenco/TwoWire/Semantics.lean` for raw/certified
  `U⊗I` embedding and algebra. A proof-side
  `Barenco/TwoWire/ControlledBridges.lean` owns local/CNOT/single-control/swap laws;
  `Barenco/TwoWireExamples.lean` is root-excluded. The core imports no `Circuit`,
  `Cost`, optimizer, lower-bound, universality, or paper-specific module.
- Expected Stage 3 high-fanout but narrow edit: `Barenco/Circuit.lean` gains only
  the trusted constructor and cheap structural/denotation lemmas; cost consequences
  remain in `Barenco/Cost.lean` or a narrow consumer leaf.
- Stage 3 adds the unavoidable trusted constructor and cheap simp lemmas directly
  inside `Barenco/Circuit.lean`; `Barenco/TwoWire/Circuit.lean` owns evaluator,
  adjoint, basis-action, and cost bridges. `CostModel` itself needs no change.
- Stage 4 public runtime/proof leaves are
  `Barenco/Optimization/FusionIR.lean` and `FusionResources.lean`. Transparent
  higher inputs belong in `ControlledCircuit/CanonicalSelected.lean`,
  `ThreeQubit/RelativePhaseFusion.lean`, and `MultiControl/GrayFusion.lean`.
- Stage 5 separates `Optimization/FusionLaws.lean`, `Normalize.lean`, and
  `NormalizeResources.lean`; `Barenco/FusionExamples.lean` remains root-excluded.
- Stage 1 focused baseline command:
  `lake build Barenco.Circuit Barenco.Cost Barenco.ThreeQubit.RelativePhase`
  `Barenco.MultiControl.GrayExpansion Barenco.MultiControl.Corollary74Expansion`
  `Barenco.AxiomAudit Barenco`.
- Stage 1 strict/trust commands compile `Barenco.lean` and
  `Barenco/AxiomAudit.lean` directly with `-DwarningAsError=true`, with and without
  `-t0`.
- Frozen Stage 2 focused build:
  `lake build Barenco.TwoWire.Layout Barenco.TwoWire.Semantics`
  `Barenco.TwoWire.ControlledBridges Barenco.TwoWireExamples`, followed by strict
  `Semantics` and trust-zero `ControlledBridges` compilation.
- Frozen Stage 3 adjacent build includes `Barenco.Circuit`, `Barenco.TwoWire.Circuit`,
  `Barenco.Cost`, `ControlledCircuit.Decomposition`, `LowerBounds.BasicCircuit`,
  `ThreeQubit.RelativePhase`, the root, and audit, followed by a full build because
  `Circuit.lean` is high-fanout.
- Frozen Stage 4 and 5 builds cover their generic leaves first, then the transparent
  selected/relative/Gray consumers, `LowerBounds.BasicCircuit`, root, and audit;
  strict/trust-zero compilation targets the runtime and resource leaves.

## Boundary Checks

- Stage 1 defines architecture and evidence only. It does not add a semantic
  constructor, optimizer runtime, test-case circuit, or resource theorem.
- Ordered wire pairs remain ordered even though structural support is a finset.
  Equal wires are rejected by a proof argument; widths below two have no such
  input.
- Exact equality is the optimizer soundness target. Existing basis-phase results
  are inherited only after an exact bridge to the original circuit.
- Structural support is an upper bound and not a proof of minimal semantic support.
  Scalar and identity two-wire matrices remain legal without being relabeled as
  smaller gates.
- The early policy may fuse/cancel one-qubit nodes while retaining literal CNOTs;
  the Section 8 policy may absorb eligible operations into a `U(4)` node. The two
  output costs are never conflated.
- Opaque chosen circuits and unsupported generic primitives are barriers until a
  transparent proved expansion is supplied.
- No ancilla is introduced by the two-wire embedding or normalizer. Test-case
  existing dirty/clean contracts must be preserved by exact evaluator equality.

## No-Cheating Checks

- Search confirms that Stage 1 introduces no `Primitive.unclassified` use, no
  arbitrary-two-qubit smart constructor, no optimizer, and no count theorem.
- The selected design must never infer a local matrix from `.kind`, `.support`, or
  support cardinality.
- Every future fused node must lower through a trusted constructor built from a
  certified local unitary and ordered wires.
- Every future count must inspect the actual normalized syntax; no disputed formula
  is accepted as a definition or arithmetic postulate.
- No global phase is deleted in exact normalization.
- Optimizer failure is classified as not recovered unless a theorem proves a
  same-scope impossibility result.
- Baseline forbidden scans cover all project Lean files for proof holes, custom
  axioms, opaque declarations, and forbidden decision shortcuts.

## Completion Requirements

- [x] Local/mathlib two-wire API inventory is recorded with exact declaration and
  import owners.
- [x] Separate-IR versus direct-refactor decision is frozen using dependency and
  trust-boundary evidence.
- [x] Source chronologies, formulas, equality relations, distinctness assumptions,
  widths, and current theorem names are independently recorded for all test cases.
- [x] Ordered-pair convention, optimizer grammar, exact soundness target, cost
  policies, barrier semantics, and result-status vocabulary are frozen.
- [x] Stage 2–5 module ownership, declaration classifications, and focused/adjacent
  commands are recorded.
- [x] Cached focused baseline, strict/trust-zero root and audit, forbidden scans,
  and `git diff --check` pass with exact results recorded.
- [x] `goal-2/0-plan.md` is folded forward and agrees with this completed stage.

## Stage Results

- Stage file was created before any Lean source change. Three independent read-only
  audits and two disposable compiled probes informed the frozen architecture.
- The selected design is the low-dependency direct ordered split and certified
  `U⊗I` reindex embedding, followed by a separate payload IR and trusted lowering.
  The sequential `splitTarget` prototype also compiled but was rejected because it
  unnecessarily imports `Controlled` and produces a nested complement type.
- Strict and trust-zero disposable prototypes confirmed the complete Stage 2 core,
  including swapped orientation, under the pinned toolchain without repository
  source edits.
- `lake build Barenco.Circuit Barenco.Cost Barenco.ThreeQubit.RelativePhase
  Barenco.MultiControl.GrayExpansion Barenco.MultiControl.Corollary74Expansion
  Barenco.AxiomAudit Barenco` passed with 3,586 jobs.
- Direct warning-as-error compilation passed for `Barenco.lean` and
  `Barenco/AxiomAudit.lean`; trust-zero warning-as-error compilation passed for
  both again. The maintained audit contains exactly 319 checks, all previously
  recorded within the standard `propext`/`Classical.choice`/`Quot.sound` set.
- Repository-wide Lean scans found no forbidden proof term, custom `axiom`, or
  `opaque`. Existing `Primitive.unclassified` references are only the deliberate
  named-model rejection theorems in `Cost.lean`. `git diff --check` passed.
- No Lean project source was changed in Stage 1. The next stage can begin directly
  with `Barenco/TwoWire/Layout.lean` and `Semantics.lean`.
