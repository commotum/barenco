# Goal 1 — Barenco Lean Library

Shorthand: `BARENCO`

Status: active. The goal is complete only when the central mathematical claims of
“Elementary Gates for Quantum Computation” have been independently checked,
formalized to the documented scope, and audited as a reusable Lean library.

## Big-Picture Objective

Build a pinned Lean 4/mathlib library that reconstructs the paper's useful
mathematics rather than transcribing its diagrams. The library must separate
finite-register semantics, circuit syntax, equivalence relations, approximation,
and resource accounting; prove the central decompositions and universality
results at the strongest justified level; and document every material repair,
extra assumption, omission, or unresolved obstruction.

## Non-Negotiable Constraints and No-Cheating Rules

- `BUILD-PLAN.md` is an authoritative execution requirement for every Lean-changing
  stage, alongside this plan and `goal-1/0-loop.md`. Each such stage records module
  ownership/layers, focused and adjacent builds, declaration classifications, and
  boundary checks before implementation.
- Completed public modules contain no `sorry`, `admit`, `by?`, or unexplained
  project-specific axioms. Any deliberately conditional theorem exposes its
  assumptions in its type and traceability entry.
- Circuit diagrams are evidence to reconstruct, not proof terms. Every claimed
  circuit equivalence is proved from explicit semantics with a documented
  wire-indexing and execution-order convention.
- Matrix equality on a small subsystem is not silently promoted to equality on
  a larger register. Local embeddings, untouched wires, and ancilla restoration
  are proved where claimed.
- Exact equality, equality up to one global phase, computational-basis-dependent
  phase, reversible basis behavior, computational-basis measurement equivalence,
  and equality of all measurement distributions are distinct definitions and are
  never conflated.
- Resource theorems are derived from countable circuit syntax under a named cost
  model. Semantic equality alone is not evidence for a gate count.
- “Basic operation” is versioned by cost model, because Section 8 changes the
  paper's convention from arbitrary one-qubit gates plus CNOT to arbitrary
  two-qubit gates.
- Exact synthesis and approximation are separate. Approximation uses a precisely
  defined norm, with proved composition/error and measurement-probability bounds.
- Upper bounds, lower bounds, exact counts, asymptotic bounds, and heuristic
  dimension counts are labeled separately.
- Existence and choices of unitary roots are proved or stated as explicit
  hypotheses; no root is selected merely because a diagram names one.
- Ancilla theorems state initialization, ownership, non-entanglement expectations,
  and restoration explicitly, including boundary cases for controls and width.
- Existing mathlib APIs are preferred only after their assumptions and
  conventions are checked. The Lean and mathlib revisions remain pinned.
- The original objective is not narrowed silently. An unprovable claim receives
  an exact obstruction, the strongest useful nearby theorem, and dependency
  impact in the correction/traceability documentation.
- Work proceeds in small compiling increments. Existing unrelated user files and
  changes are preserved.
- Prefer narrow leaf modules and focused builds; avoid high-fanout/umbrella imports,
  experimental declarations in shared cores, and broad global simp/instance changes.
  A green build of an unused abstraction is not evidence that a stage goal is met.

## Current Facts

- The source is local as `Barenco/barenco-1995.pdf`, a structured transcription
  at `Barenco/barenco-1995.md`, and sixteen extracted circuit images under
  `Barenco/images/`.
- The repository began with a minimal Python package and no Lean project. Stage 1
  has now added an exact Lean 4.31.0 toolchain pin, exact mathlib commit pin,
  resolved manifest, root/smoke modules, documentation, and this `goal-1` scaffold.
- Git started on `master` with an unrelated untracked `.DS_Store`; it remains
  preserved. Generated `.lake/` and PDF-render scratch are ignored.
- `BUILD-PLAN.md` is the repository-wide Lean build protocol. It remains generic;
  goal-specific ownership, commands, and evidence live in each stage file.
- Stage 2 now provides certified basis transport, block/Kronecker semantics,
  arbitrary-target local and positive multi-controlled gates, Pauli-X/CNOT truth
  tables, trustworthy chronological circuit syntax, adjoints, and structural smart
  constructors. Diagnostic boundary examples compile for widths 0–3.
- Stage 3 now provides exact/global/input-column phase relations, coarse basis
  behavior, computational-basis probabilities, conjugation-channel and algebraic
  all-effect equality, the scoped L² operator distance with a single-outcome
  factor-two probability bound, and syntax-only width/count/support/partial-cost
  projections under two distinct paper cost models.
- Stage 4 now provides the paper's displayed one-qubit matrices and their
  standard-column transposes, certified U(2)/SU(2) gates, all Lemma 4.2 identities,
  exact SU(2) and U(2) Euler surjectivity including degenerate entry cases, both
  orientations of Lemma 4.3's A/B/C algebra, and exact certified positive `k`-th
  roots for every finite-dimensional complex unitary. The A/B/C results are still
  matrix-level; their explicit circuit semantics and counts begin in Stage 5.
- Stage 5 now provides arbitrary-register target-block circuit semantics, exact
  reconstructions of all four controlled-gate diagrams, both directions of the
  Lemmas 5.1/5.4/5.5 characterizations, controlled scalar phase and controlled-Z
  identities, and syntax-derived costs. Corollary 5.6 is repaired by separating
  its six-node controlled-V macro library from its ten-primitive expansion and
  six-primitive post-merge CNOT circuit.
- The paper's main numbered chain is Lemmas 4.1–4.3; Lemmas/Corollaries 5.1–5.6;
  Lemmas/Corollaries 6.1–6.2; Lemmas/Corollaries 7.1–7.12; and the general
  synthesis/resource discussion in Section 8.
- The paper explicitly says diagrams execute left-to-right. Lean matrix products
  conventionally act right-to-left, so the circuit evaluator must resolve this
  mismatch deliberately and test it.
- Section 6.2 uses basis-dependent signs, Lemma 7.8 in Section 7.3 uses an induced
  Euclidean operator distance and a stated `2ε` probability consequence, and Section 8
  contains both constructive upper bounds and informal dimension-counting claims.

## Current Assumptions and Decisions

- The selected semantic core is `Fin n → Bool` indexed complex matrices, with raw
  algebraic gates and certified unitaries separated; circuit syntax is a later layer.
- `basisIndex` fixes the paper's big-endian lexicographic bridge. The implemented
  Gray layer uses finite masks and Boolean functions directly; `BitVec` remains
  optional diagnostic/interchange infrastructure rather than the core basis.
- The pinned matrix, unitary-group, Kronecker, reindexing, permutation, wire-split,
  and L² operator-norm APIs compile in `Barenco/ApiSmoke.lean`.
- `AllMeasurementEq` intentionally quantifies arbitrary matrices/effects and is
  algebraically equivalent to channel equality. It is not a declaration that every
  such matrix is a physical state or POVM effect.
- Clean/dirty ancilla contracts are now explicit rather than inferred from numeric
  resource fields: Stage 7 proves exact full-register dirty-wire restoration, and
  Stage 8 proves clean-zero subspace correctness, output closure, and literal
  fixed-wire factorization.
- Lemma 4.1's existential Euler decomposition is now proved by a canonical
  `SU(2)` entry form plus explicit determinant-phase normalization. General exact
  finite-dimensional unitary roots are now proved by finite-spectrum functional
  calculus. Stage 9 now names one coherent principal power-of-two sequence, proves
  exact adjacent squaring and `pi/2^m` L² operator-distance decay, and connects
  those analytic facts to literal truncated one-qubit/CNOT circuits. The selected
  epsilon construction uses truncation only when its certified natural depth fits
  and otherwise uses an exact fallback; no continuity of root choice or optimal
  approximation-cost theorem is claimed.
- Some Section 8 “lower bounds” are heuristic parameter counts rather than proved
  topological lower bounds and may need to remain explicitly non-theorem claims.
- The core Lemma 7.7 lower-bound stack is now implemented for a proof-carrying
  syntax containing exactly arbitrary one-qubit gates and distinct-wire CNOTs.
  A duplicate-safe interaction graph, explicit arbitrary-cut Kronecker
  factorization, and a separated-control scalar obstruction prove the stronger
  exact no-ancilla bound of `n-1` CNOT occurrences. The source's total-basic-gate
  and named-cost forms are corollaries; scalar, approximate, phase-relaxed,
  measurement, and ancilla-assisted targets are outside the theorem.

## Success Metrics and Final Verification

- `lake build` succeeds from a clean checkout using only pinned versions.
- Every Lean-changing stage follows `BUILD-PLAN.md`: narrow dependency layers,
  smallest sufficient focused builds, adjacent-consumer builds when APIs move, and
  broader builds only when required by fanout or explicit completion criteria.
- Focused tests cover basis action, execution order, control/target indexing,
  embeddings, phase relations, ancilla behavior, and representative 1–4 qubit
  examples.
- Repository-wide audits find no forbidden proof holes in completed Lean modules.
- `#print axioms` (or a maintained equivalent audit) records the axioms of every
  headline export and explains standard classical/propext/quotient usage.
- Every important paper claim has a row in the traceability map with a Lean name,
  source location, formalization level, status, assumptions, and dependency notes.
- Every discovered mathematical or expository issue has a correction-log entry.
- Exact resource claims evaluate over circuit syntax and named cost models;
  asymptotic claims follow from proved recurrences or inequalities.
- Approximation results specify the norm and connect operator error to state and
  measurement error with proved constants.
- Computational-basis observational equivalence and all-input/all-measurement
  observational equivalence are separate, with only justified implications.
- Public modules have module-level documentation and stable names suitable for a
  later circuit/synthesis project.
- The final report lists fully reconstructed diagrams, proved resource claims,
  unresolved/excluded material, build results, axiom results, and reuse guidance.

## Stage Index

- [x] `1-GUARDRAILS` — pin the project, audit sources/APIs, and freeze conventions.
- [x] `2-SEMANTICS` — finite registers, unitary gates, local embeddings, circuits.
- [x] `3-EQUIVALENCE` — phase relations, basis behavior, approximation, costs.
- [x] `4-ONE-QUBIT` — Section 4 identities, Euler forms, and unitary roots.
- [x] `5-CONTROLLED` — Section 5 controlled-one-qubit decompositions and counts.
- [x] `6-THREE-QUBIT` — Section 6 exact and relative-phase constructions.
- [x] `7-MULTICONTROL` — Section 7 exact multi-control/Gray-code constructions.
- [x] `8-ANCILLA` — linear constructions with fixed/restored auxiliary wires.
- [x] `9-APPROXIMATION` — truncated roots, norm bounds, and measurement effects.
- [ ] `10-LOWER-BOUNDS` — rigorous dependency and cost lower bounds.
- [ ] `11-UNIVERSALITY` — two-level unitary synthesis and exact universality.
- [ ] `12-RESOURCES` — recurrences, asymptotics, and cost-model separation.
- [ ] `13-AUDIT` — coverage closure, examples, build/axiom audit, final report.

## 1-GUARDRAILS

### Big Picture Objective

Create a reproducible Lean baseline and enough source/API evidence to make the
foundational representation choices deliberately.

### Detailed Implementation Plan

- Inventory the paper, diagrams, numbered claims, existing repo, installed Lean,
  and locally available mathlib revisions.
- Add `lean-toolchain`, `lakefile.toml`, a root module, and an initial smoke module
  using an exact compatible mathlib pin.
- Probe candidate mathlib APIs with compiling examples; record names, imports,
  conventions, and missing infrastructure.
- Write convention documentation for basis indexing, wire numbering, diagram and
  multiplication order, matrix entries, controls/targets, phase, norm, and costs.
- Create living traceability, correction, and axiom-audit documents with all paper
  claims inventoried rather than only the easiest claims.
- Keep `lake-manifest.json` as a versionable project artifact, ignore generated `.lake/` and render scratch, and
  verify generated artifacts do not enter source audits.
- Establish focused/full build and proof-hole/diff audit commands.

### Completion Requirements

- The pinned project resolves and `lake build` passes twice without source edits.
- The root library imports a smoke module with no proof holes.
- The conventions document makes every choice listed above explicit and includes
  sanity examples for execution and basis order.
- Traceability contains every numbered Section 4–7 claim; important unnumbered
  definitions, external universality claims, phase/Gray constructions, terminology
  changes, all sixteen diagrams; and each distinct Section 8 construction/bound,
  initially marked planned/excluded/unresolved as warranted.
- The correction and axiom-audit logs exist with their evidence format defined.
- The stage file records commands, outputs, risks, and the chosen Stage 2 model.

## 2-SEMANTICS

### Big Picture Objective

Implement a small reusable semantic and syntactic core for finite qubit circuits.

### Detailed Implementation Plan

- Define register bases, states, gates, unitarity predicates/structures, basis
  vectors, and the encoding relation to `Fin (2^n)` where needed.
- Define typed primitive/local gates, sequential circuits, evaluation, identity,
  append/composition, inverse/adjoint, and execution order.
- Define arbitrary wire embeddings (including permutations), controlled and
  multiply controlled one-qubit gates, CNOT, X, and untouched-wire predicates.
- Prove evaluator algebra, embedded unitarity, basis action, control/target
  behavior, and low-dimensional matrix sanity checks.

### Completion Requirements

- All foundational modules compile with no proof holes or custom axioms.
- Evaluation of append/composition is proved with the documented order.
- Local gates and multi-controls have extensional basis-action theorems and proven
  unitarity; invalid/duplicate wire choices are ruled out in types or hypotheses.
- Tests cover 0, 1, 2, and 3-qubit boundary cases and non-adjacent embeddings.
- Traceability and conventions link the formal definitions to Sections 2–3.

## 3-EQUIVALENCE

### Big Picture Objective

Separate the semantic relations and resource observations needed by later claims.

### Detailed Implementation Plan

- Define exact circuit equivalence, global-phase equivalence, basis-dependent
  phase equivalence, reversible basis behavior, and equality of computational
  basis measurement distributions.
- Define an all-input/all-measurement observational relation (via channels,
  density operators, or quantified effects) separately from computational-basis
  observation.
- Prove equivalence-relation/congruence properties only where mathematically true,
  plus implications and counterexample documentation between relations.
- Define operator-norm distance through a checked mathlib representation and prove
  unitary invariance, sequential error accumulation, state error, and the exact
  single-computational-basis-outcome probability consequence available at this
  layer.
- Define structural gate counts, ambient width, touched support, and named cost
  models for Sections 3–7 versus Section 8. Defer clean/dirty ancilla semantic
  contracts to Stage 8, where actual initialization/restoration constructions exist.

### Completion Requirements

- Each relation has reflexive/symmetric/transitive results and composition rules
  appropriate to it; invalid implications are covered by examples or corrections.
- The appropriate implications into all-measurement equivalence are proved, and a
  relative/basis-dependent phase counterexample prevents a false implication.
- The exact norm and its finite-matrix/operator bridge are documented and tested.
- Resource projections compute on representative circuits and never inspect only
  semantic matrices.
- Phase and cost entries in the traceability map cite these definitions.

## 4-ONE-QUBIT

### Big Picture Objective

Independently verify the one-qubit algebra in Section 4 and supply reusable roots.

### Detailed Implementation Plan

- Define the paper's phase and axis-rotation matrices with precise angle/sign
  conventions; prove unitarity, determinant, adjoint, and multiplication laws.
- Prove Lemmas 4.2 and 4.3 as concrete matrix identities, including all degenerate
  angle cases.
- Prove the strongest supported version of the U(2)/SU(2) Euler decomposition in
  Lemma 4.1, splitting parameterized reconstruction from existential surjectivity
  if the latter requires a deeper argument.
- Prove existence and properties of the square roots/iterated roots actually used
  later, with choices isolated behind proved theorems.

### Completion Requirements

- Every Section 4 displayed identity is machine checked under documented signs.
- Lemmas 4.1–4.3 have traceability statuses and no hidden nonzero assumptions.
- Root theorems give unitarity and the exact power equation needed by Sections 6–9.
- Numerical/symbolic examples validate X, rotations, phase, and special-unitary
  boundary cases.

## 5-CONTROLLED

### Big Picture Objective

Reconstruct all Section 5 controlled-one-qubit networks semantically and count them
from syntax.

### Detailed Implementation Plan

- Translate every Section 5 diagram into the circuit syntax with explicit control,
  target, and left-to-right execution order.
- Prove Lemmas 5.1, 5.2, 5.4, and 5.5, including both directions of every claimed
  “if and only if” and exact characterization of phase/determinant conditions.
- Derive Corollaries 5.3 and 5.6 from constructed circuits and structural counts;
  record whether adjacent one-qubit gates are merged in each count.

### Completion Requirements

- Each diagram has a named circuit, exact evaluator theorem, basis-case proof, and
  source image/location in traceability.
- The iff converses are independently proved or explicitly corrected with impact.
- Published upper bounds compute under the Sections 3–7 cost model.

## 6-THREE-QUBIT

### Big Picture Objective

Verify Section 6 exact controlled-controlled gates and the precise relative-phase
Toffoli behavior.

### Current Facts

- The Lemma 6.1 diagram executes left-to-right as controlled-`V` from the second
  control to the target; CNOT from the first control to the second; controlled-
  `V†` from the second control; the same CNOT restoring the second wire; and
  controlled-`V` from the first control. Its proof requires three pairwise
  distinct named wires and no auxiliary wire.
- `OneQubit.unitarySquareRoot` provides a certified exact square root with
  `unitarySquareRoot_pow_two`; `doubleControlledRootCircuit` and
  `eval_doubleControlledRootCircuit` now connect that selected root to the
  explicit five-node Lemma 6.1 circuit.
- The Section 5 target-block algebra applies directly to all gates sharing the
  final target, but the two intermediate CNOTs change a complementary/control
  assignment. `eval_doubleControlledViaSquareCircuit_pow_two` resolves this with
  proved disjoint-wire CNOT conjugation and all four control cases, yielding
  arbitrary-width full-register equality rather than a small truth-table proof.
- Corollary 6.2's published `8` one-qubit plus `8` XOR upper bound is not the
  naive expansion count: three six-primitive controlled-unitary expansions plus
  two CNOTs give `20`. `eval_doubleControlledExpansion20Circuit_eq_16` proves the
  source's nonliteral “adjacent” cancellations using coordinated Section 5
  witnesses, and `doubleControlledUnitary_has_sixteenPrimitiveCircuit` certifies
  the explicit sixteen-node syntax and `oneQubitCNOT` cost `some 16`.
- The first relative-phase Toffoli diagram is chronological
  `A(target); CNOT(second,target); A(target); CNOT(first,target); A†(target);`
  `CNOT(second,target); A†(target)`, with `A = Ry(pi/4)` in the paper convention.
  The second replaces the three CNOTs by symmetric controlled-Z gates and uses
  `B; CZ(second,target); B†; CZ(first,target); B; CZ(second,target); B†`, with
  `B = Ry(3*pi/4)`. Independent diagram evaluation gives the same exact signed
  permutation for both: `|101⟩` alone receives `-1`, while `|110⟩` and `|111⟩`
  are swapped positively and every other basis state is fixed.
- Section 6.2 does not establish global-phase equality. Controlled-`W` with
  `W = [[0,1],[-1,0]]` instead maps `|111⟩` to `-|110⟩`; it has a different
  exact sign witness from both displayed seven-node circuits. All three must
  remain distinct before deriving weaker `BasisPhaseEq`, reversible-basis, or
  basis-measurement consequences.
- Both diagrams now have exact arbitrary-width evaluator and signed basis-action
  theorems, are proved exactly equal to one another, and derive only the justified
  `BasisPhaseEq`, `SameBasisBehavior`, and `BasisMeasurementEq` consequences.
  `lemma61Toffoli_threeBit_truthTable` and the A, B, and controlled-W diagnostics
  exhaust all eight concrete inputs without replacing the public operator proofs.
- Stage 6 is complete under `BUILD-PLAN.md`. Its combined 2,948-job build, two
  consecutive 2,946-job full builds, warning-as-error checks, 84-declaration axiom
  audit, forbidden-shortcut scan, and documentation synchronization are recorded
  in `goal-1/6-THREE-QUBIT.md` and the maintained docs. Stage 7 has now discharged
  the related contextual obligation by computing the phases along the actual
  corrected Corollary 7.4 path; Stage 6 itself still claims only exact
  cancellation of adjacent identical copies.

### Detailed Implementation Plan

- Formalize Lemma 6.1 using a proved square root and explicit embedded gates.
- Derive Corollary 6.2's count from the Section 5 expansion.
- Encode both relative-phase Toffoli circuits, calculate their basis-dependent
  phases, and state their strongest valid equivalence relation.
- Prove when paired relative-phase constructions cancel phases in later circuits.

### Completion Requirements

- Exact evaluator equality and untouched-wire behavior hold for Lemma 6.1.
- The sixteen-operation upper bound is syntactically checked under its stated
  primitive expansion.
- Every affected basis state and sign in both Section 6.2 diagrams is proved; no
  global-phase wording is used for a relative-phase fact.

## 7-MULTICONTROL

### Big Picture Objective

Formalize the exact multi-control constructions and their Gray-code semantics from
Section 7, including their dirty/borrowed workspace contracts.

Current implementation facts:

- The source/diagram audit is complete in `goal-1/7-MULTICONTROL.md`, including
  exact chronologies, C-003–C-010, and new corrections C-022–C-024.
- `MultiControl.Parity` proves the exact alternating subset-XOR exponent identity.
  `MultiControl.GrayCode` proves reflected coverage, uniqueness, adjacency, pivot
  alignment, and singleton-before-strict-pivot-rise. `GrayAccumulator` proves the
  two local CNOT accumulator update rules, exact `2^m-2` edge count, every-edge
  validity, the prefix invariant, and exact full restoration at all widths.
- `OrderedControlLayout` supplies arbitrary nonadjacent ambient embeddings.
  `grayControlledViaRootCircuit` now interleaves the signed roots with the
  certified CNOT schedule and proves exact full-register Lemma 7.1 semantics.
  `grayControlledCircuit` selects the exact root. The theorem includes one
  positive control, keeps zero controls as a separate local base, and derives
  exact controlled-root/CNOT/total macro counts from syntax.
- `fourBitGrayCircuit` is proved exactly equal to the generated width-three
  syntax and reconstructs the source's seven-root/six-CNOT chronology. Strict
  checks and its selected-root/count audits pass.
- Lemma 7.2 now has a trusted pairwise-distinct Toffoli primitive, arbitrary-wire
  `InwardLadderLayout`, exact recursive syntax, Boolean-ring dirty restoration,
  full-register evaluator equality, `4(m−2)` syntax count, capacity/support
  bounds, rejected unexpanded paper costs, and exact `m=3`/`n=9,m=5`
  diagnostics.
- Lemma 7.3 now has arbitrary-wire `FourBlockLayout`, exact `A;B;A;B` syntax,
  explicit Boolean-ring dirty restoration, full-register operator equality, four
  macro occurrences, and checked A/B substitution with exact doubled counts. The
  latest focused root/audit build has 3,485 jobs and all 112 maintained axiom
  prints are standard; two post-root full builds have 3,484 jobs each.
- Corrected Corollary 7.4 now has explicit shared-register ladder substitution,
  exact arbitrary-placement semantics, a canonical exact-width circuit for every
  `n≥7`, `n−2` controls, exact `8(n−5)` Toffoli count, the `n=7` boundary, honest
  unexpanded cost rejection, and a target-free A theorem. `RelativeHalf` now
  proves the exact signed recursive phase formula and `RelativePhase` proves the
  corrected `Arel;Bhybrid;adjoint(Arel);Bhybrid` circuit exactly on the full
  register, with four exact and `8n−44` relative occurrences. Both new leaves pass
  focused and warning-as-error checks. `Corollary74Expansion` now proves exact
  evaluator preservation and literal counts `32n−144` one-qubit,
  `24n−100` CNOT, and `56n−244` total/cost. The source's optimized `48n−204`
  remains unresolved because no explicit evaluator-preserving normalization
  establishes it. Lemma 7.5 now has an exact arbitrary-width five-node evaluator,
  selected square-root wrapper, explicit zero/one-control boundaries, and a
  generic checked substitution theorem. Its complete primitive recursion now
  embeds corrected Corollary 7.4 circuits into arbitrary ambient layouts while
  borrowing/restoring the unitary target, and proves exact evaluator equality.
  For `d=n−7`, its checked one-qubit/CNOT/total profiles are
  `32d²+200d+252`, `24d²+164d+188`, and `56d²+364d+440`. The corrected
  Corollary 7.6 API proves the Nat-safe width formula
  `56n²+636−420n`, exact increment `112n−364`, and a construction-specific
  `IsBigOWith 56`/`O(n²)` theorem. No optimal `Θ(n²)` claim is exported.
- Stage 7 is complete. Its final public root and 175-entry axiom audit pass direct
  warning-as-error and trust-zero compilation; the integrated focused build has
  3,495 jobs, two final full builds have 3,493 jobs each, and forbidden/diff
  scans are clean. Later claims 7.7–7.12 remain explicitly routed to Stages 8–10.

### Detailed Implementation Plan

- Define Gray codes/parity schedules suitable for Lemma 7.1 and prove their
  coverage, adjacency, parity, and cancellation properties.
- Reconstruct Lemmas 7.1–7.5, including wire partitions, all boundary inequalities,
  recursive calls, and relative-phase cancellation dependencies.
- State which wires are logical data versus borrowed/dirty workspace, prove
  correctness for arbitrary (even entangled) borrowed-wire inputs where claimed,
  prove restoration/no residual entanglement, and count total width.
- Derive Corollaries 7.4 and 7.6 from structural costs and explicit recurrences.

### Completion Requirements

- All exact diagrams through Lemma 7.5 have evaluator proofs on arbitrary states.
- Recursive circuits are total only on proved-valid index ranges and cover smallest
  legal `n` examples.
- Dirty-wire theorems establish full-register equality; “no workspace” is used only
  when no wire is borrowed, not merely because no wire lies outside the n-wire
  network.
- Exact and asymptotic upper bounds cite circuit counts/solved recurrences, with
  constants and phase-gate accounting made explicit.

## 8-ANCILLA

### Big Picture Objective

Verify the paper's linear exact constructions and state their auxiliary-wire
contracts without ambiguity.

### Current Results

- Lemma 7.9 now has the exact five-macro chronology on arbitrary ambient
  registers, a selected special-unitary ABC witness, a literal one-qubit/CNOT
  expansion, and exact logical-width profile
  `(64n−279,48n−194,112n−473)` for `n≥7`. The source's special `W` example has
  an explicit input-column sign and separate `BasisPhaseEq`, basis-behavior, and
  basis-measurement theorems.
- Lemma 7.11 now has an exact arbitrary-auxiliary basis formula, equality on the
  entire clean-zero subspace for arbitrary superpositions, clean-zero output
  closure, and an explicit fixed-wire factorization witness. Its primitive
  expansion declares exactly one clean wire and has profile
  `(64n−284,48n−198,112n−482)` for `n≥7`.
- Both numeric count families are linked exactly to their named circuit syntax
  and have construction-specific `IsBigOWith 112`/`O(n)` theorems. Corollary
  7.10's dropped control and both corollaries' unsupported optimal `Θ(n)` reading
  are corrected in C-022 and C-026.
- Root-excluded width-seven/eight diagnostics confirm every component count,
  prove a vector-level auxiliary-one counterexample for Pauli-X, and specialize
  arbitrary-state factorization. Stage 8 is publicly integrated: strict and
  trust-zero root/audit checks pass with 206 standard-only axiom entries, the
  focused build passes with 3,505 jobs, and two final full builds pass with 3,503
  jobs each.

### Detailed Implementation Plan

- Reconstruct Lemma 7.9 and Corollary 7.10 for SU(2), including the control split
  and any relative-phase dependencies.
- Formalize Lemma 7.11/Corollary 7.12 as a subspace/input-contract theorem: the
  chosen auxiliary wire starts in zero, is restored, and the data transformation
  is exact even on superpositions satisfying the contract.
- Distinguish clean ancillas from borrowed/dirty ancillas and document which notion
  the paper actually establishes.

### Completion Requirements

- Linear circuits have exact semantic proofs and structural linear upper bounds.
- Initialization and restoration theorems quantify over arbitrary data states,
  not only individual classical inputs, and prove no residual entanglement.
- Invalid smallest widths and alternate ancilla initial states are documented.

## 9-APPROXIMATION

### Big Picture Objective

Repair and formalize Lemma 7.8 with an unambiguous metric and rigorous error/cost
dependence.

### Current Results

- `powerTwoRoot` is one coherent principal-spectrum sequence for every finite
  unitary. Its zeroth member, adjacent square equation, and
  `operatorDistance≤pi/2^m` decay are proved without claiming continuous
  dependence on the input matrix.
- Target-block/reindex semantics are isometric in the scoped L² induced operator
  norm. Positive-controlled distance to identity therefore reduces exactly to
  the corresponding one-qubit distance.
- `truncatedRecursiveCircuitFrom` is literal macro syntax retaining the first
  four Lemma 7.5 nodes per level. It has an exact arbitrary-register residual
  factorization and exact residual-root distance. The primitive expansion uses
  only one-qubit and CNOT syntax and preserves that evaluator and error.
- For residual exact depth `r` and retained depth `k`, exact syntax-derived counts
  are `32k²+(64r+200)k` one-qubit, `24k²+(48r+164)k` CNOT, and
  `56k²+(112r+364)k` total/accepted cost. Exact completion recovers the established
  full-recursion profile at combined depth `r+k`.
- `principalRootBoundDepth` is the natural ceiling of `logb 2 (pi/epsilon)` and
  exactly characterizes the certified root bound for `epsilon>0`.
  `epsilonSynthesisPrimitiveCircuit` uses the truncation when this depth fits and
  otherwise selects the exact recursive circuit. It meets every positive
  tolerance, links exactly to selected structural counts/cost, has the uniform
  bound `440+112n*min(principalRootBoundDepth epsilon,n−7)` for `n≥7`, and has an
  explicit construction-specific logarithmic upper under `0<epsilon≤1`.
- Finite computational-basis event probabilities on unitary images of a common
  norm-at-most-one pure input obey a stronger cardinality-free constant-one bound;
  the paper's constant-two statement is an immediate corollary. No arbitrary-POVM
  claim is made.
- Boundary examples cover the empty, exact-fallback, maximum one-shell, and exact
  completion cases. Stable modules are publicly integrated; strict/trust-zero,
  focused, forbidden-token, diff, 235-entry axiom-audit, and two full-build
  checks pass. Stage 9 is complete.

### Detailed Implementation Plan

- Match the paper's “induced Euclidean” distance to the operator norm and prove the
  block/control distance formula used by the truncation argument.
- Bound iterated roots in operator norm with explicit dependence on phase/eigenangle
  choices; verify all logarithmic regimes and `ε` boundary cases.
- Prove the truncated recursive circuit error and a precise upper bound in
  `n` and `log (1/ε)`; distinguish fixed-ε from two-parameter asymptotics.
- Derive state-vector and finite computational-basis-event probability bounds,
  checking the paper's `2ε` constant and keeping arbitrary POVMs outside the
  theorem unless separately formalized.

### Completion Requirements

- Lemma 7.8 has a corrected, quantified theorem with explicit norm and integer
  depth; the all-positive-epsilon selector and the separate `0<ε≤1` logarithmic
  regime are stated explicitly.
- Error accumulation and resource count are separate proved lemmas.
- The probability claim is proved with its hypotheses or corrected in the log.

## 10-LOWER-BOUNDS

### Big Picture Objective

Formalize every rigorous lower bound supported by the paper while quarantining
heuristic parameter counts.

### Detailed Implementation Plan

- Retain the implemented `BasicPrimitive`/`BasicCircuit` restricted syntax and
  exact erasure, evaluator, occurrence-count, total-count, and accepted-cost
  bridges to the generic library.
- Retain the duplicate-safe CNOT interaction graph and the explicit
  selected-wires-first `wireSplit`/`partitionReindex` Kronecker semantics for
  arbitrary, possibly noncontiguous cuts.
- Retain the proved target-component factorization and separated-control scalar
  obstruction, which combine into the stronger `n-1` CNOT-occurrence theorem and
  its weaker total-gate and named-cost corollaries.
- Add boundary examples, public-root imports, maintained axiom entries, and the
  required strict/trust-zero, forbidden-token, diff, focused, and full-build
  checks before marking the stage complete.
- Preserve the Section 5/6 named-topology classifications and constructive counts
  without promoting them to global minimum claims. Preserve Section 8 dimension
  counting as excluded evidence unless a future manifold/image theorem supplies
  the missing assumptions.

### Completion Requirements

- Every exported lower bound names its primitive set and semantic target relation.
- Lemma 7.7's `n - 1` bound follows from a mechanized invariant, not prose.
- The arbitrary-cut tensor convention, exact/no-ancilla scope, nonscalar
  hypothesis, and width-one/zero boundaries are documented explicitly.
- Heuristic/excluded bounds have exact obstruction and no theorem-shaped claim.
- Examples, public imports, axiom audit, and all required builds/checks pass before
  the Stage Index box is checked.

## 11-UNIVERSALITY

### Big Picture Objective

Prove exact universality of arbitrary one-qubit gates plus CNOT by a verified
finite-dimensional synthesis, without bundling approximation or efficiency.

### Detailed Implementation Plan

- Define two-level unitaries and prove a finite complex-unitary elimination or
  decomposition theorem over arbitrary finite dimensions/index types, including
  diagonal phases; only then specialize it to dimensions `2^n`.
- Formalize Gray-code conjugation that implements any two-level basis rotation via
  modified multi-control gates and restores all permuted basis states.
- Combine Sections 5–8 constructions into exact generation of arbitrary
  `2^n × 2^n` unitaries; separately state primitive availability and no-ancilla
  conditions.
- Document relationships, but not false implications, to dense generation by a
  fixed finite gate set.

### Completion Requirements

- A headline theorem constructs a circuit for every finite-qubit unitary and proves
  exact evaluator equality under arbitrary one-qubit plus CNOT primitives.
- A reusable algebraic theorem decomposes arbitrary finite-dimensional complex
  unitary matrices independently of the qubit specialization.
- Two-level decomposition, Gray path, diagonal handling, and `n = 0/1` boundaries
  are individually tested.
- Exact generation, dense generation, and efficiency appear as distinct APIs.

## 12-RESOURCES

### Big Picture Objective

Prove the justified exact and asymptotic resource statements across both of the
paper's cost models.

### Detailed Implementation Plan

- Solve the recurrences generated by the concrete constructions and connect each
  closed form/`O`/`Θ` statement to structural counts.
- Formalize two-level/Gray-code general-unitary upper bounds, including the number
  and length of paths, and determine whether `Θ(n^3 4^n)` is an upper bound only or
  a true tight bound under a specified algorithm/cost model.
- Track width, clean/dirty ancillas, arbitrary one-qubit gates, CNOT, Toffoli,
  arbitrary two-qubit gates, and gate merging separately.

### Completion Requirements

- Every resource theorem names its syntax, cost projection, allowed simplification,
  and exact/upper/lower/asymptotic status.
- Section 8's changed primitive convention cannot be substituted accidentally for
  the earlier one.
- Claimed asymptotics have machine-checked finite inequalities/recurrences or are
  explicitly documented as unresolved.

## 13-AUDIT

### Big Picture Objective

Close coverage honestly and deliver a reusable, reproducible library with a final
paper-to-Lean and axiom audit.

### Detailed Implementation Plan

- Reconcile every traceability row, correction dependency, diagram, theorem,
  example, and public module against the paper and actual compiled code.
- Run clean/focused/full builds, proof-hole searches, formatting/diff checks,
  documentation checks, and axiom prints for headline exports.
- Add a library guide and final report covering architecture, conventions,
  corrections, unresolved claims, diagram/resource coverage, and future reuse.

### Completion Requirements

- No traceability item is silently absent; every item has a final status and reason.
- All sixteen source diagrams are individually classified as fully reconstructed,
  partial, excluded, or unresolved; every exact/asymptotic resource claim receives
  the same explicit final classification.
- All completed modules build with no forbidden holes; axiom output is recorded and
  explained.
- The final report contains every deliverable requested in the original objective
  and gives concrete import/examples for downstream projects.
