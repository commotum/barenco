# 6-THREE-QUBIT

Status: in progress.

## Current Facts

- The original PDF, local transcription, and extracted images
  `lemma-6-1-controlled-controlled-u.png`, `relative-phase-toffoli-a.png`, and
  `relative-phase-toffoli-b.png` are available. All three diagrams execute
  left-to-right; the library's circuit lists are chronological and their matrix
  products therefore appear in reverse order under standard column semantics.
- Lemma 6.1 has three pairwise distinct wires: first control, second control, and
  target. Its chronological macro circuit is:
  controlled-`V` from second to target; CNOT first-to-second; controlled-`V†`
  from second to target; the same CNOT; controlled-`V` from first to target.
  The two CNOTs restore the second control exactly. No auxiliary wire occurs.
- For input control bits `x₁,x₂`, chronological action selects `V` under `x₂`,
  `V†` under `x₁ xor x₂`, and `V` under `x₁`; the standard-column matrix product
  reverses those factors. The four Boolean cases give identity except at
  `x₁=x₂=true`, where the target receives `V*V`. Thus the exact theorem should
  assume/provide `V^2=U`.
- `Barenco.OneQubit.unitarySquareRoot` is a certified principal-branch choice for
  every finite unitary, and `unitarySquareRoot_pow_two` proves its square is the
  input. It is semantic infrastructure only; the Stage 6 circuit must contain
  explicit controlled primitives.
- `Primitive.positiveControlled`, `Primitive.cnot`, `Circuit.eval`,
  `Circuit.gateCount`, `Circuit.kindCount`, and partial `Circuit.cost` already
  separate syntax, denotation, and resources. The five-node Lemma 6.1 macro has
  three unsupported controlled-one-qubit nodes plus two CNOT nodes, so its
  `oneQubitCNOT` cost must remain `none` until expansion.
- Section 5's `targetBlockRaw` proves products pointwise when every operation
  preserves the complement of one selected target. The Lemma 6.1 CNOTs instead
  alter the second control, so a reusable parity/conjugation lemma or a complete
  basis-extensional proof is required before reducing the remaining target
  factors to four Boolean cases.
- Expanding each of the three controlled gates independently with Corollary 5.3
  gives `3*(4 one-qubit + 2 CNOT) + 2 CNOT = 20` primitives. Corollary 6.2's
  claimed `8+8=16` bound uses coordinated decompositions of controlled-`V` and
  controlled-`V†` and removes two adjacent inverse pairs, i.e. four one-qubit
  occurrences. A semantic equality or informal merge cannot certify that count.
- The first Section 6.2 circuit is chronological
  `A; CNOT(second,target); A; CNOT(first,target); A†;`
  `CNOT(second,target); A†`, where the paper writes `A=Ry(pi/4)`.
- The second Section 6.2 circuit uses the paper's two-square notation for the
  already formalized symmetric controlled-Z gate and is chronological
  `B; CZ(second,target); B†; CZ(first,target); B; CZ(second,target); B†`, where
  the paper writes `B=Ry(3*pi/4)`.
- The source's congruence symbol means computational-basis-dependent signs, not
  exact equality or one global phase. The manuscript claims the first topology
  reverses the sign of input basis state `|101⟩`; it separately observes that
  doubly controlled `W`, for paper matrix `W=[[0,1],[-1,0]]`, differs from
  Toffoli on `|111⟩`. These are distinct constructions and both sign tables
  must be checked in the library's column convention.
- Independent evaluation of the extracted diagrams confirms that both seven-node
  circuits have the same exact signed permutation: `|101⟩` alone receives `-1`,
  `|110⟩` and `|111⟩` are swapped with positive amplitude, and every other basis
  state is fixed. Doubly controlled paper `W` instead maps `|110⟩` to `|111⟩`
  and `|111⟩` to `-|110⟩`; neither diagram is literally controlled-`W`.
- Stage 5 is complete and the public root and 64-declaration axiom audit build
  with only `propext`, `Classical.choice`, and `Quot.sound`. Stage 6 must preserve
  that baseline and add no `sorry`, `admit`, custom axiom, or unclassified gate.

## Updated Assumptions

- Exact circuit theorems quantify arbitrary ambient width `n` and three pairwise
  distinct `Fin n` wires. A concrete three-qubit instantiation is diagnostic,
  not the public result.
- The primary Lemma 6.1 API should expose both a parameterized theorem assuming
  `V^2=U` and a root-selected theorem using `unitarySquareRoot U`. This separates
  reusable circuit algebra from the particular noncomputable root choice.
- A two-control target should use the existing `ControlSet target`; membership
  and enabled-branch simplification must prove that both distinct controls are
  true, not rely on an ordered pair convention.
- Full-register evaluator equality proves untouched spectator wires and exact
  restoration of the second control. A separate statement about basis states may
  be exported for diagnostics, but is not a substitute for operator equality.
- Corollary 6.2 must name `CostModel.oneQubitCNOT`, exhibit the exact expanded
  circuit syntax, and prove evaluator equality to Lemma 6.1. An upper bound of
  `16` may be stated as exact equality for the selected syntax plus `≤ 16` for
  the implemented unitary.
- Relative-phase constructions should first receive an exact basis-action or
  exact signed-permutation theorem. `BasisPhaseEq`, `SameBasisBehavior`, and
  `BasisMeasurementEq` should be derived only after the exact sign witness is
  known. No all-measurement equivalence follows.
- The paper's row-oriented `Ry` labels must be translated through `fromPaper` or
  the already proved `paperRy`/`ry` bridge. The sign table, not visual similarity
  of a diagram, decides the semantic angle.
- The later paired-cancellation requirement will be attempted only for the exact
  relative-phase constructions on which Section 7 relies; no blanket congruence
  cancellation theorem will be asserted.

## Big Picture Objective

Reconstruct all Section 6 diagrams as explicit arbitrary-width circuits, prove
the exact doubly controlled-unitary construction and its stated primitive upper
bound, and replace the source's informal phase congruence by exact, exhaustively
checked computational-basis phase behavior suitable for later Section 7 proofs.

## Detailed Implementation Plan

- Add a narrow Lemma 6.1 leaf with:
  a two-control-set constructor; the five-node chronological macro circuit;
  structural macro counts; a reusable CNOT/parity conjugation or basis-action
  lemma; exact evaluator equality from `V^2=U`; and the selected-square-root
  corollary.
- Keep any parity helper local to the Stage 6 leaf until the Gray-code stage
  demonstrates a second consumer. Promote it only when its statement matches
  the later schedule algebra without weakening Lemma 6.1.
- Add a Corollary 6.2 expansion leaf after inspecting the exact Section 5
  `controlledU2Circuit` factors. Choose coordinated factors for `V` and `V†`,
  construct the post-cancellation 16-node syntax, prove evaluator equality by
  explicit append/adjoint/merge laws, and prove eight one-qubit plus eight CNOT
  occurrences and cost `some 16`.
- Add a relative-phase leaf defining the paper's `W`, the exact doubly controlled
  `W` gate, both seven-node circuits, and exact signed basis actions. Derive the
  strongest valid phase/basis/measurement relations and prove the two diagrams'
  exact relationship only if their independently computed sign witnesses agree.
- Add a diagnostic `Barenco/ThreeQubitExamples.lean` excluded from the public
  root. Exhaust all eight three-qubit basis inputs for Lemma 6.1 and each
  relative-phase circuit, check non-adjacent embeddings in a wider register, and
  evaluate all resource projections.
- After leaves stabilize, import only public theorem leaves from `Barenco.lean`,
  add headline declarations to `Barenco/AxiomAudit.lean`, and update conventions,
  traceability, corrections, and the stage/goal plans with exact source status.

## Build Structure

- `Barenco/ThreeQubit/Lemma61.lean`: runtime/public two-control set and macro
  circuit; proof-side/public evaluator, restoration-through-equality, root, and
  macro-count theorems. Narrow imports: controlled semantics, circuit, roots, and
  only the Section 5 multiplication/block API actually used.
- `Barenco/ThreeQubit/Expansion.lean`: runtime/public 16-node expanded circuit;
  proof-side/public semantic bridge and exact named-model resources. Imports
  `Lemma61`, the precise Section 5 expansion leaves, and `Cost`.
- `Barenco/ThreeQubit/RelativePhase.lean`: runtime/public `W` and the two diagram
  circuits; proof-side/public exact signed actions and phase consequences. Imports
  controlled-Z, certified rotations, and equivalence relations as narrowly as
  possible.
- `Barenco/ThreeQubitExamples.lean`: diagnostic only, excluded from the public
  root and axiom surface.
- `Barenco.lean` and `Barenco/AxiomAudit.lean` remain untouched until the new
  public leaves compile. Existing high-fanout `Basic`, `Controlled`, `Circuit`,
  `Cost`, and equivalence modules remain unchanged unless a checked reusable gap
  cannot live in a Stage 6 leaf.
- Declaration classifications: circuit and gate constructors are runtime/public;
  exact evaluator, algebra, phase, and cost theorems are proof-side/public;
  concrete `Fin 3` tables are diagnostic; no fallback or temporary declaration
  may enter the root.
- Initial focused build:
  `lake build Barenco.ThreeQubit.Lemma61`.
  Adjacent builds grow to `Barenco.ThreeQubit.Expansion`,
  `Barenco.ThreeQubit.RelativePhase`, `Barenco.ThreeQubitExamples`,
  `Barenco.AxiomAudit`, and `Barenco` as each layer becomes public.

## Boundary Checks

- Matrix identities, circuit evaluator equality, restoration/untouched-wire
  behavior, syntax counts, and cost-model results remain separate theorem layers.
- The two controls and target are explicitly pairwise distinct. No hidden choice
  of wire `0`, `1`, or `2` occurs in a public theorem.
- The Lemma 6.1 macro's controlled primitives are not assigned a Section 3–7
  basic-gate cost. Only the explicit Corollary 6.2 expansion may have
  `oneQubitCNOT` cost.
- The two intermediate CNOTs must be shown to restore the second control in the
  full semantic theorem; target-only multiplication that ignores their action is
  forbidden.
- `V†` is the certified inverse/adjoint of the same selected `V`, not an
  independently chosen square root or an unconstrained unitary witness.
- Controlled-`W`, the A-based relative-phase circuit, and the B/CZ-based circuit
  are three separately named exact operators. Similar reversible behavior does
  not identify their phase witnesses.
- Exact equality, global phase, basis-dependent phase, reversible basis behavior,
  and basis-measurement equality use the established distinct relations.
- Any later phase cancellation theorem must exhibit exact circuit composition or
  exact pointwise cancellation of its phase witnesses.

## No-Cheating Checks

- No hard-coded eight-by-eight matrix calculation substitutes for the
  arbitrary-width Lemma 6.1 evaluator theorem.
- No truth-table proof is promoted to operator equality without a proved basis
  extensionality/linearity bridge.
- No use of `Primitive.unclassified`, semantic-only dummy gates, or metadata tags
  to obtain a resource count.
- No count is inferred from the paper diagram or a semantically equivalent
  shorter matrix expression; all counts inspect the named `Circuit` syntax.
- No controlled macro receives cost zero or one under `oneQubitCNOT`.
- No global-phase theorem is used for a basis-state-dependent sign.
- No `sorry`, `admit`, `by?`, custom `axiom`, `opaque`, `native_decide`, or
  `bv_decide` in completed Stage 6 modules.

## Completion Requirements

- [x] Lemma 6.1 has a named five-node circuit, a parameterized exact evaluator
  theorem from `V^2=U`, a selected-root exact theorem, structural macro counts,
  and arbitrary-width/pairwise-distinct wire quantification.
- [x] Full-register equality covers all spectator wires and exact restoration of
  the second control; representative `Fin 3` and wider-register cases compile.
- [x] Corollary 6.2 has a named explicit expansion, evaluator equality, exactly
  eight one-qubit and eight CNOT nodes, and `some 16` cost under
  `CostModel.oneQubitCNOT`.
- [x] Paper `W` versus Toffoli and both Section 6.2 diagrams have complete exact
  eight-input sign tables generalized to arbitrary ambient width, followed by
  the strongest justified phase/basis/measurement theorems.
- [x] Any Section 7 dependency on paired relative-phase cancellation is either
  proved exactly here or recorded with a precise pending theorem statement and
  no premature downstream use.
- [ ] Focused builds, adjacent diagnostic builds, warning-as-error checks, two
  consecutive full builds after root changes, forbidden-shortcut scans,
  `git diff --check`, and the headline axiom audit all pass and are recorded.
- [ ] Conventions, traceability, correction log, axiom audit, this stage file,
  and `0-plan.md` state exact theorem names, source locations, costs, phase
  witnesses, corrections, and unresolved claims.

## Stage Results

- `Barenco/ThreeQubit/Lemma61.lean` now defines the exact five-node chronological
  macro `doubleControlledViaSquareCircuit`, selected-root wrapper
  `doubleControlledRootCircuit`, and arbitrary-width evaluator theorems
  `eval_doubleControlledViaSquareCircuit_pow_two`,
  `eval_doubleControlledViaSquareCircuit_of_sq_eq`, and
  `eval_doubleControlledRootCircuit`. The proof conjugates a complementary-wire
  CNOT through target blocks and checks all four control cases; it is not an
  eight-by-eight sample.
- The same leaf exports the genuinely reused disjoint-wire laws
  `cnotRaw_commute_localRaw`, `cnotUnitary_commute_localUnitary`,
  `localRaw_commute_of_ne`, and `localUnitary_commute_of_ne`. Macro resources are
  exactly three singleton-controlled nodes plus two CNOTs, gate count five, with
  `oneQubitCNOT` cost deliberately `none`.
- `Barenco/ThreeQubit/Expansion.lean` defines the coordinated twenty-node circuit
  `S(second); K; S(second)†; K; S(first)` and the reduced explicit sixteen-node
  syntax. `eval_doubleControlledExpansion20Circuit_eq_16` proves the two source
  cancellation groups by commuting them across control-only gates; the gates are
  not treated as syntactically adjacent.
- `eval_doubleControlledExpansion16Circuit_of_products` reuses one shared Section
  5 factorization, `doubleControlledExpansion16Circuit_exists` selects the exact
  square root once, and `doubleControlledUnitary_has_sixteenPrimitiveCircuit`
  proves Corollary 6.2 as an exact existence/resource theorem. The final syntax
  has gate count sixteen, exactly eight one-qubit plus eight CNOT nodes, and cost
  `some 16`; the unmerged syntax has twelve plus eight and cost `some 20`.
- Focused builds `lake build Barenco.ThreeQubit.Lemma61` and
  `lake build Barenco.ThreeQubit.Lemma61 Barenco.ThreeQubit.Expansion` succeeded
  with 2,928 and 2,929 jobs respectively. Direct warning-as-error compilation of
  both leaves succeeded. A temporary seven-theorem axiom audit reports only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Correction entries C-019 and C-020 record the source's unproved root choice,
  omitted `V†*V` branch, implicit commutation, and coordinated-witness requirement.
  Their exact Lean evidence is now part of the maintained public modules.
- `Barenco/ThreeQubit/RelativePhase.lean` translates paper
  `W=[[0,1],[-1,0]]` to standard-column `Ry(pi)`, defines the exact common
  `I,I,Z,X` block unitary, and reconstructs both seven-node diagrams. Theorems
  `eval_relativePhaseToffoliACircuit` and
  `eval_relativePhaseToffoliBCircuit` prove each evaluator exactly, while
  `eval_relativePhaseToffoliACircuit_eq_BCircuit` proves the diagrams are the
  same unitary, not merely measurement-equivalent.
- `relativePhaseToffoliACircuit_mulVec_basisKet` and its B analogue prove the
  exact Toffoli permutation with a Circle-valued minus sign precisely on input
  `101`. `controlledWUnitary_mulVec_basisKet` proves the distinct minus sign on
  `111`. Separate `BasisPhaseEq`, `SameBasisBehavior`, and
  `BasisMeasurementEq` consequences are exported; no global-phase or
  all-measurement statement is made.
- The A circuit is seven early-basic primitives, exactly four one-qubit plus
  three CNOT, with cost `some 7`. The B source syntax is four one-qubit plus
  three controlled-Z macros; its gate count is seven but `oneQubitCNOT` cost is
  correctly `none`. Its exact equality with the A circuit supplies a separate
  seven-basic implementation semantically without miscounting the macro syntax.
- `relativeToffoliUnitary_sq` and the two
  `eval_append_relativePhaseToffoli*Circuit_self` theorems prove exact adjacent
  identical-pair cancellation. The stronger contextual claim used by Corollary
  7.4 remains a Stage 7 obligation: after defining the exact and relative
  Corollary 7.4 circuits, prove their full evaluators equal by showing that the
  product of `relativeToffoliPhase` witnesses along every ordered computational-
  basis path is one. No generic “occurs in pairs” shortcut is permitted.
- `Barenco/ThreeQubitExamples.lean` now exhausts all eight concrete three-bit
  inputs in quantified A, B, and controlled-W truth-table theorems, checks a
  non-adjacent five-wire embedding with two spectators, and validates macro and
  basic costs. Direct warning-as-error compilation succeeds.
- The public root imports `Expansion` and `RelativePhase`. The combined focused,
  diagnostic, root, and audit build succeeded with 2,947 jobs. The maintained
  audit now prints 80 headline declarations; all sixteen new Stage 6 checks use
  only `propext`, `Classical.choice`, and `Quot.sound`. Direct warning-as-error
  compilation of the root and audit succeeds.
- Correction C-021 records the original PDF's erroneous “latter” attribution and
  the distinct `101`/`111` witnesses. Documentation synchronization, two full
  builds, and final scans remain before Stage 6 closes.
