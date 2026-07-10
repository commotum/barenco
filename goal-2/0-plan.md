# Goal 2 — Certified Two-Wire Fusion and Paper Optimization Tests

Shorthand: `TWOFUSE`

Status: active. Stages 1–3 are complete; Stage 4 payload-preserving fusion IR is
the first incomplete stage.

## Big-Picture Objective

Extend the Barenco Lean library with a trustworthy representation of arbitrary
two-wire unitary gates inside an ambient register, a payload-preserving circuit
optimization layer with exact semantics-preservation proofs, and syntax-derived
resource theorems. Exercise that infrastructure on the paper's disputed
three-two-qubit relative-phase Toffoli construction and its omitted post-merger
Gray/Corollary 7.4 counts.

The goal is not to force the paper's advertised counts to be true. Each test case
must end with one of three honest outcomes:

- **verified:** an explicit output circuit, exact evaluator theorem, and count
  theorem establish the source claim;
- **refuted:** a theorem in the same stated model proves the source claim false;
- **not recovered:** the verified normalizer reaches a precisely stated result or
  fixed point without the advertised count, but no global impossibility theorem is
  claimed. The paper claim remains explicitly unresolved.

The completed work should be reusable as compiler infrastructure rather than a
collection of hand-simplified paper examples.

## Non-Negotiable Constraints and No-Cheating Rules

- `BUILD-PLAN.md` is an authoritative execution requirement alongside this plan
  and `goal-2/0-loop.md`. Every Lean-changing stage must record module ownership,
  declaration classification, focused and adjacent builds, boundary checks, and
  exact verification evidence before completion.
- Preserve the completed Goal 1 API and its mathematical conventions unless a
  checked incompatibility forces a documented migration. Avoid a broad refactor of
  the high-fanout `Primitive`/`Circuit` core when a narrow layered representation
  can provide the needed payloads.
- Do not wrap an arbitrary full-register unitary, label it `.arbitraryTwoQubit`,
  and assert that it acts on two wires. A two-wire node must be constructed from an
  ordered pair of distinct wires and a certified local `UnitaryGate 2`, with its
  full-register denotation and locality derived by trusted code.
- Do not reconstruct a local gate from `Primitive.kind` or `Primitive.support`.
  Existing metadata is not, by itself, a semantic locality certificate, and the
  current `Primitive` structure does not retain the originating local matrix.
- Optimizer input must retain the local one- or two-wire payload needed for
  composition. Unsupported or opaque existing primitives are barriers unless an
  explicit, proved translation is supplied.
- Exact evaluator equality is the default optimizer correctness relation. Never
  discard global phase: a later control can turn it into relative phase. Any
  phase-relaxed optimization must be separately named, specified, and proved and
  is not required by this goal.
- Circuit chronology remains head-first. If `U` runs before `V`, their fused local
  matrix is `V * U` in the library's standard-column convention.
- Resource claims come from literal output syntax. Matrix equality, a semantic
  support theorem, an arithmetic function, or a cost tag alone cannot justify a
  reduced gate count.
- Keep `CostModel.oneQubitCNOT` and `CostModel.arbitraryTwoQubit` distinct. A
  generic `U(4)` node costs one in the latter and is unsupported in the former
  unless an explicit one-qubit/CNOT decomposition is present.
- Prove arbitrary-ambient-register equality and spectator preservation. A
  calculation only at width two or three is a diagnostic, not the public theorem.
- Do not infer commutation from disjoint metadata alone. Every generic commutation
  rule must consume a semantic locality certificate or be proved for the concrete
  trusted constructors involved.
- A normalizer may be deterministic and locally stable without being globally
  canonical, complete, or optimal. Do not advertise minimality, completeness, or a
  lower bound without a separate theorem.
- Optimizer failure is not a disproof. A failed advertised count receives the
  strongest checked normalized circuit and a scoped status, not an invented
  impossibility conclusion.
- Do not use the opaque classical-choice circuit selected by an existence theorem
  as though its factor chronology were available to an executable optimizer.
  Supply a transparent canonical factor schedule and prove it implements the same
  target operation.
- Completed modules contain no `sorry`, `admit`, `by?`, `native_decide`,
  `bv_decide`, custom `axiom`, `opaque`, `sorryAx`, or `implemented_by`. No new
  project-specific axiom is permitted.
- Maintain the public/diagnostic boundary: stable declarations may enter
  `Barenco.lean`; examples, exhaustive probes, and negative tests remain in
  root-excluded diagnostic modules unless explicitly promoted.
- Existing user changes are preserved. No destructive Git operations are part of
  this goal.

## Current Facts

- Goal 1 is complete at its audited scope. The baseline uses Lean 4.31.0 and
  mathlib commit `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`, has 319 maintained
  `#print axioms` checks, and passed a 3,593-job clean build.
- `Circuit n` is a chronological `List (Primitive n)`. `Circuit.eval` evaluates
  the head first, so later gate denotations multiply on the left.
- `Primitive` has a private constructor and stores only `kind`, `support`, and a
  certified full-register `denotation`. Its trusted one-qubit, controlled, CNOT,
  and Toffoli smart constructors prevent arbitrary metadata forgery.
- `PrimitiveKind.arbitraryTwoQubit` and
  `CostModel.arbitraryTwoQubit` already exist, but there is no trusted public smart
  constructor embedding an arbitrary local `U(4)` on an ordered wire pair.
- `Primitive.unclassified` deliberately has full support and is rejected by both
  named paper cost models. It is not an acceptable implementation shortcut.
- The existing `Primitive.adjoint` preserves kind and support and inverts the
  certified denotation. New two-wire syntax must connect this generic operation to
  the inverse local payload.
- The optimizer cannot safely pattern-match an existing `Primitive` back into its
  local matrix. Stage 1 therefore selected a richer proof-carrying
  optimization IR with explicit one-wire/two-wire payloads and a proved lowering
  into `Circuit`.
- `selectedControlledU2Circuit` and the selected exact Toffoli expansion use
  classical choice to obtain witnesses whose specs retain semantics and aggregate
  counts but not boundary chronology. The local controlled-U factor data are
  separately available through transparent selected-column ABC factors; the
  explicit sixteen-node exact-Toffoli constructor is also available before the
  opaque selection layer.
- The two explicit relative-phase Toffoli circuits each have seven syntax nodes,
  exact arbitrary-register evaluator/basis-phase theorems, and Section 8 cost
  seven. The source claims that local merging produces cost three.
- For `m = n - 1 > 0` controls, the checked raw Gray expansion has exactly
  `4 * (2^m - 1)` one-qubit gates, `3 * 2^m - 4` CNOT gates, and total
  `7 * 2^m - 8`. The paper reports the same CNOT count but only `2 * 2^m`
  one-qubit gates after omitted mergers.
- For logical width `n >= 7`, the corrected phase-safe Corollary 7.4 expansion has
  exactly `32n - 144` one-qubit gates, `24n - 100` CNOT gates, and total
  `56n - 244`. The paper prints the unresolved optimized total `48n - 204`.
- No existing result claims that costs three, five, or thirteen are minimal. Goal
  2 concerns constructive upper counts and evaluator-preserving optimization, not
  global minimality.
- Stage 1 selected a direct low-dependency ordered split and certified `U⊗I`
  reindex embedding. Strict/trust-zero prototypes import only `Barenco.Semantics`
  and cover entries, spectators, algebra, inverse, and swapped orientation.
- Stage 2 implemented that design as public `TwoWire.Layout`, `Semantics`, and
  `ControlledBridges` leaves. Exact entry, certified basis/four-term/arbitrary-
  state action, spectator-zero, algebra, inverse, proof-irrelevance, orientation,
  local-gate, singleton-control, and CNOT theorems compile for arbitrary ambient
  width. Width-two, reversed, and nonadjacent width-five diagnostics are root-
  excluded. The integrated 3,590-job build, strict/trust-zero checks, scans, and
  335-entry maintained axiom audit pass.
- Stage 3 added trusted `Primitive.twoQubit pair U` at the private-constructor
  boundary and a narrow `TwoWire.Circuit` proof/resource leaf. Explicit nodes have
  exact swap/adjoint/basis/evaluator laws, literal endpoint support, gate/kind
  counts, early-model rejection, and Section 8 cost one. Root-excluded diagnostics,
  the 3,593-job integrated regression, 3,589-job full build, strict/trust-zero
  checks, scans, and 348-entry audit pass. `Primitive` still does not retain an
  optimizer-readable payload; Stage 4's separate IR must do so.
- The optimizer architecture is a separate payload-preserving IR lowering through
  trusted smart constructors. `Primitive` changed only by the completed trusted
  two-wire constructor inside its private-constructor file; no normalizer will
  infer payloads from metadata or decide equality of arbitrary unitary matrices.

## Remaining Assumptions to Test
- The relative-phase A circuit appears to split chronologically into three groups
  supported on two wire pairs: `A; CNOT; A`, the middle CNOT, and
  `A†; CNOT; A†`. This must be checked under the exact wire/order convention.
- The paper's Gray count may follow from same-target one-qubit mergers across
  transparent controlled-U expansion boundaries. Boundary gates and selected
  factors may prevent the naive formula; no count is trusted before syntax exists.
- A specific candidate is to select one transparent controlled-`V` circuit, use
  its literal adjoint for the opposite Gray sign, prove that consecutive Gray
  masks alternate sign, and cancel one inverse target-gate pair at each of the
  `2^m - 2` boundaries. If correct, the normalized profile is
  `(2 * 2^m, 3 * 2^m - 4, 5 * 2^m - 4)`.
- The Corollary 7.4 constant may require rewrites beyond the general Gray mergers.
  Its source arithmetic and phase errors remain corrected regardless of whether a
  lower count is found.

## Success Metrics and Final Verification

The goal is complete only when all of the following hold:

- A stable public API embeds every certified `UnitaryGate 2` on any ordered pair of
  distinct ambient wires, with exact basis action, spectator preservation,
  algebraic laws, and unitarity.
- A trusted arbitrary-two-qubit circuit constructor has exact kind, support,
  denotation, adjoint, and named-cost theorems. The private-constructor trust
  boundary remains intact.
- A payload-preserving optimizer syntax lowers to the established `Circuit` model
  with exact chronology, evaluator, support, and resource bridges.
- An executable, terminating normalization pass implements the supported fusion,
  cancellation, absorption, and proved commutation rules. Its exact semantic
  soundness and the relevant model-specific cost nonincrease theorem are proved.
- The relative-phase cost-three example and both parameterized merger families
  are run through the real infrastructure. Each receives a named output circuit,
  exact evaluator theorem, syntax-derived counts, and an honest verified/refuted/
  not-recovered status.
- Any changed dependent resource theorem is derived from the new output syntax;
  no old constant is edited arithmetically without a circuit proof.
- Representative width-two, nonadjacent-wire, swapped-orientation, three-wire,
  one-control, and smallest Corollary 7.4 boundary examples compile.
- Public documentation, traceability, correction statuses, and the final report
  explain the optimizer's exact scope and every material difference from Goal 1.
- Focused and adjacent builds, strict warning-as-error compilation, trust-zero
  compilation, the maintained axiom audit, repository-wide forbidden scans, full
  verification appropriate to the import changes, and `git diff --check` pass.

## Stage Index

- [x] `1-GUARDRAILS` — freeze architecture, source claims, models, and proof boundaries.
- [x] `2-TWO-WIRE` — certified ordered-pair semantic embeddings and algebra.
- [x] `3-TWO-PRIMITIVE` — trusted circuit constructor, support, adjoint, and costs.
- [ ] `4-FUSION-IR` — payload-preserving optimizer syntax and lowering bridges.
- [ ] `5-NORMALIZE` — executable exact fusion/normalization and cost monotonicity.
- [ ] `6-TOFFOLI-THREE` — certify or precisely delimit the cost-three claim.
- [ ] `7-GRAY-MERGERS` — normalize the general Gray family and settle its checked count.
- [ ] `8-COR74-MERGERS` — test the optimized Corollary 7.4 count and dependencies.
- [ ] `9-AUDIT` — public integration, documentation, builds, and axiom audit.

## 1-GUARDRAILS

### Big Picture Objective

Freeze the semantic, syntactic, cost-model, and source-claim boundaries before a
high-fanout representation decision is made.

### Detailed Implementation Plan

- Re-read `BUILD-PLAN.md`, this plan, `goal-2/0-loop.md`, the relevant source
  passages, Goal 1 corrections C-003/C-004/C-025/C-032/C-035, and the existing
  circuit, cost, relative-phase, Gray, and Corollary 7.4 modules.
- Inventory reusable mathlib and local APIs for finite reindexing, product bases,
  block diagonals, Kronecker products, unitary subgroups, and wire complements.
- Compare a narrow payload-preserving optimization IR with a direct refactor of
  `Primitive`. Record dependency fanout, interoperability, trusted-constructor
  implications, and how each design exposes transparent local factors.
- Freeze the ordered-pair convention, exact optimizer relation, supported gate
  grammar, cost-policy modes, unsupported-gate barrier behavior, and boundary
  widths.
- Translate every disputed source formula into the library's `m`/`n` variables and
  record the exact existing chronology and theorem names.
- Specify the status criteria for verified, refuted, and not-recovered outcomes.
- Choose narrow module ownership and list focused/adjacent build commands for
  Stages 2–5 before implementation.

### Completion Requirements

- The Stage 1 file records the selected architecture and why it respects the
  existing trust boundary and incremental-build plan.
- The source chronologies, formulas, wire assumptions, equality relations, and
  legal width domains are explicit and independently checked.
- The optimizer grammar retains every payload required for executable fusion; no
  later stage depends on reconstructing a local gate from metadata.
- Public, proof-side, runtime, diagnostic, and temporary declarations are
  classified, with expected files and focused builds recorded.
- Baseline focused root/audit builds and forbidden scans pass before Lean changes.

### Stage Results

- Selected `Barenco/TwoWire/Layout`, `Semantics`, and `ControlledBridges` as the
  low public layers, with a root-excluded examples leaf. A strict/trust-zero
  disposable prototype compiled the ordered split, `U⊗I` embedding, entry/locality,
  identity/multiplication/inverse, monoid-hom, and swapped-orientation results using
  only `Barenco.Semantics`.
- Rejected a `Primitive` payload refactor in favor of a separate
  `FusionPrimitive`/`FusionCircuit` IR. The trusted two-wire smart constructor will
  be the only narrow high-fanout edit and must live in `Circuit.lean` because
  `Primitive.mk` is private.
- Froze exact chronology, domains, current theorem names/counts, and resolution
  criteria for cost-three relative Toffoli, Gray post-mergers, and corrected
  Corollary 7.4. Opaque whole-circuit choices are barriers; transparent selected
  factors and explicit oriented expansions are required.
- Baseline focused/root/audit build passed with 3,586 jobs; strict and trust-zero
  root/audit compilation, the 319-entry axiom audit, forbidden scans, and
  `git diff --check` passed. No Lean source changed in this stage.

## 2-TWO-WIRE

### Big Picture Objective

Construct the reusable semantic foundation for applying an arbitrary certified
two-qubit unitary to an ordered pair of distinct wires in any ambient register.

### Detailed Implementation Plan

- Define an ordered two-wire layout or equivalent basis equivalence that separates
  the selected bits from the complementary assignment without assuming adjacency.
- Define raw and certified embeddings of `UnitaryGate 2` into `UnitaryGate n`.
- Prove entry and computational-basis action formulas, exact preservation of every
  spectator wire, and equality on arbitrary superpositions through the full
  operator theorem.
- Prove identity, chronological multiplication, inverse/adjoint, and reindexing or
  swapped-orientation laws needed by fusion.
- Prove the concrete locality bridges needed by the optimizer: a gate on the first
  selected wire as `A ⊗ I`, a gate on the second as `I ⊗ A`, canonical CNOT and
  singleton-controlled matrices, and pair reversal by explicit swap conjugation.
- Add width-two, reversed-order, and padded nonadjacent-wire diagnostics.

### Completion Requirements

- The embedding accepts exactly an ordered pair with a proof of distinctness;
  widths zero and one are impossible by construction rather than handled by an
  arbitrary fallback.
- Full-register unitarity and the advertised algebraic laws compile without a
  project axiom or postulated locality fact.
- Basis order for the local `00,01,10,11` states is documented and tested; swapping
  the ordered wires is not silently treated as the same local matrix.
- Distinctness-witness proof irrelevance and the fact that declared structural
  support is an upper bound for identity/scalar local gates are documented or
  proved at the appropriate layer.
- At least one nonadjacent ambient-register example proves target action and
  spectator preservation.
- Focused leaf, adjacent semantic consumer, strict, trust-zero, and forbidden-token
  checks required by the stage file pass.

### Stage Results

- Public `Barenco.TwoWire.Layout` defines the ordered pair, direct complement
  split, reconstruction/update/agreement API, and explicit local bit-swap
  equivalence. Public `Barenco.TwoWire.Semantics` defines raw/certified `U⊗I`
  embeddings with exact entry, basis, arbitrary-state, algebra, inverse, proof-
  irrelevance, chronology, and pair-reversal laws.
- `Barenco.TwoWire.ControlledBridges` proves exact arbitrary-width first/second
  local-gate, singleton-controlled-U, and canonical CNOT bridges. Root-excluded
  `Barenco.TwoWireExamples` checks canonical width two, reversed CNOT, and
  nonadjacent width-five target action with three symbolic spectators.
- Stable leaves are exported publicly and sixteen representative declarations are
  in the maintained 335-check axiom audit. Focused builds, the 3,590-job integrated
  build, strict/trust-zero compilation of leaves/root/audit, forbidden/no-cheating
  scans, documentation synchronization, and `git diff --check` pass. No circuit
  syntax or resource claim was introduced; that trust-boundary work remains Stage 3.

## 3-TWO-PRIMITIVE

### Big Picture Objective

Expose arbitrary two-wire semantics through trusted countable circuit syntax and
connect it to both named paper cost models.

### Detailed Implementation Plan

- Add a trusted `Primitive` smart constructor from an ordered distinct wire pair
  and a certified local `UnitaryGate 2`, using the Stage 2 embedding.
- Prove exact `.arbitraryTwoQubit` kind, two-wire support, support cardinality,
  denotation, basis action, and singleton-evaluator theorems.
- Prove compatibility with `Primitive.adjoint`, including the local inverse and
  ordered-wire payload.
- Prove Section 8 cost `some 1` and explicit rejection by the one-qubit/CNOT model
  for a generic arbitrary-two-qubit node.
- Add public imports only after narrow consumers and root-excluded examples build.

### Completion Requirements

- No use of `Primitive.unclassified`, no direct access around the private
  constructor, and no arbitrary full-register denotation labeled local appears in
  the implementation.
- Kind, support, denotation, adjoint, gate-count, kind-count, and both cost-model
  boundary theorems are syntax-derived and compile.
- Existing one-qubit, CNOT, controlled, and Toffoli APIs retain their behavior and
  all adjacent cost tests pass.
- New headline declarations are added to the maintained axiom audit and use only
  the accepted standard foundations.
- Focused, adjacent, strict, trust-zero, root, audit, and diff checks specified by
  the stage file pass.

### Stage Results

- `Primitive.twoQubit` is the sole trusted generic two-wire smart constructor. It
  accepts only an `OrderedWirePair` and certified local `U(4)`, fixes kind,
  unordered endpoint support, and `twoWireUnitary` denotation together, and has
  exact support-cardinality/projection facts.
- Public `Barenco.TwoWire.Circuit` proves exact pair-swap, adjoint/inverse,
  primitive/singleton basis and spectator behavior, singleton evaluation, literal
  counts/support, early-model rejection, and Section 8 cost one. `Cost.lean` and
  the `Primitive` representation were otherwise unchanged; optimizer payloads are
  deliberately deferred to Stage 4.
- Canonical width-two, reversed-CNOT, and nonadjacent width-five diagnostics pass.
  Thirteen new checks bring the maintained audit to 348. Focused, adjacent,
  3,593-job integrated, 3,589-job full, strict/trust-zero, forbidden/no-cheating,
  root-exclusion, documentation, and diff checks all pass.

## 4-FUSION-IR

### Big Picture Objective

Introduce optimizer-visible circuit syntax that retains local payloads and lowers
exactly into the established trusted `Circuit` representation.

### Detailed Implementation Plan

- Define a small reified gate grammar, expected to include explicit one-qubit,
  CNOT, and ordered arbitrary-two-qubit nodes, plus a chronological circuit list.
- Define lowering/compilation of every reified node to trusted `Primitive` syntax
  and prove exact chronology and evaluator preservation for lists and append.
- Define structural support and both relevant costs on the IR, then prove they
  agree with the lowered circuit whenever the selected model accepts the node.
- Treat unsupported existing primitives as barriers; do not infer missing payloads
  from kind/support fields. If a partial bridge from existing circuits is useful,
  its success conditions and round-trip theorem must be explicit.
- Provide transparent IR builders and evaluator bridges for the relative-phase A
  circuit and the expanded Gray/Corollary inputs. Replace any opaque chosen witness
  used as optimizer input with a transparent canonical factor schedule based on
  proved selected factors.

### Completion Requirements

- Every IR node lowers through trusted constructors, and every lowering theorem is
  exact full-register equality.
- The IR contains sufficient data to multiply same-wire and same-pair local
  unitaries without inspecting full-register matrices or metadata.
- Relative-phase and at least one Gray expansion compile through the bridge with
  an evaluator theorem and literal pre-normalization counts matching Goal 1.
- Unsupported nodes cannot be silently dropped, relabeled, or assigned a local
  payload; barrier behavior has a diagnostic test.
- Focused IR/compiler, adjacent test-input, strict, trust-zero, audit, and hygiene
  checks pass.

## 5-NORMALIZE

### Big Picture Objective

Build an executable exact normalizer from reusable fusion laws and prove that its
output is semantically sound and no more expensive under its declared cost policy.

### Detailed Implementation Plan

- Prove local laws for same-wire one-qubit multiplication, identity deletion,
  syntactic inverse cancellation, same-ordered-pair two-qubit multiplication, and
  absorption of adjacent one-qubit operations into a two-qubit node.
- Prove only those disjoint commutations justified by the IR's semantic locality
  theorem and needed to expose supported mergers.
- Implement a terminating deterministic pass or sequence of passes. Separate the
  early one-qubit/CNOT policy, which must preserve CNOT syntax, from the Section 8
  policy, which may absorb local gates into arbitrary `U(4)` nodes.
- Prove exact lowering/evaluator soundness for every pass and the complete
  normalizer, with the correct reversed local multiplication order.
- Prove a precise normalized/fixed-point property for the supported rules and
  model-specific cost nonincrease. Prove idempotence only if the implementation
  actually establishes it.
- Add nonadjacent, reversed-pair, append-boundary, phase-carrying, and unsupported-
  barrier examples.

### Completion Requirements

- The normalizer is executable and target-independent; test circuits are inputs,
  not hard-coded branches in the algorithm.
- `eval (lower (normalize circuit)) = eval (lower circuit)` holds on arbitrary
  ambient registers exactly, with no phase quotient.
- A theorem ties the output's literal syntax to nonincreasing accepted cost under
  each supported policy. Unsupported conversions remain unsupported rather than
  being assigned a fabricated cost.
- The output satisfies the declared local normal-form predicate or a documented
  weaker stability property. No global completeness, minimality, or canonical-form
  statement appears without proof.
- Focused optimizer, representative diagnostics, adjacent consumers, strict,
  trust-zero, audit, full-root-if-needed, and hygiene checks pass.

## 6-TOFFOLI-THREE

### Big Picture Objective

Use the real Section 8 fusion infrastructure to determine whether the paper's
seven-node relative-phase circuit has a literal three-two-qubit implementation.

### Detailed Implementation Plan

- Reconstruct the relative-phase A chronology in the optimizer IR under explicit
  pairwise-distinct wire assumptions.
- Apply general fusion/absorption rules to the candidate three groups
  `A; CNOT(second,target); A`, `CNOT(first,target)`, and
  `A†; CNOT(second,target); A†`, checking chronological multiplication exactly.
- Emit a literal three-node lowered circuit using trusted two-wire syntax.
- Prove exact evaluator equality to the existing seven-node A circuit on every
  ambient register and transfer its basis-phase, basis-behavior, and measurement
  consequences to Toffoli.
- Derive gate count and Section 8 cost three from syntax; record the stricter-model
  boundary. Investigate the B circuit only if it follows from the same general API
  without distorting the stage.

### Completion Requirements

- A verified outcome includes an explicit three-node circuit, exact equality to
  the original evaluator, inherited phase classification, and literal cost
  `some 3` under `CostModel.arbitraryTwoQubit`.
- If the advertised grouping fails, the stage records the exact failed obligation
  and either supplies a theorem refuting that grouping or marks the broader claim
  not recovered; optimizer failure alone is not labeled a disproof.
- No theorem calls cost three minimal or equates basis-dependent phase with global
  phase or exact Toffoli equality.
- A concrete three-wire example and a padded nonadjacent-register example compile.
- Traceability/correction status, axiom checks, focused/adjacent builds, strict,
  trust-zero, and hygiene checks are updated and pass.

## 7-GRAY-MERGERS

### Big Picture Objective

Run exact early-model normalization across the general Gray expansion and
determine the real post-merger one-qubit/CNOT profile.

### Detailed Implementation Plan

- Produce a transparent optimizer-IR Gray expansion for every positive control
  count and prove exact equality to the existing checked Gray construction.
- Select the controlled-root factors coherently once: positive signs use the
  transparent circuit, negative signs use its literal circuit adjoint. Prove the
  required Gray-sign alternation rather than choosing unrelated inverse witnesses.
- Normalize within controlled-U decompositions and across block boundaries while
  retaining literal CNOT nodes and exact phase.
- Prove syntax-derived one-qubit, CNOT, total, and accepted-cost formulas for the
  output by induction over the actual Gray schedule.
- Treat the one-control case, the first and final block, adjoints, and arbitrary
  spectator width explicitly.
- Test the candidate boundary calculation that removes two one-qubit nodes at each
  of `2^m - 2` internal boundaries, yielding source profile
  `(2 * 2^m, 3 * 2^m - 4, 5 * 2^m - 4)` if every cancellation is certified.
- Compare the proved formula with the paper's `2 * 2^m` one-qubit and
  `3 * 2^m - 4` CNOT counts. If they differ, characterize the remaining normal-
  form boundaries and state only the obstruction proved for the declared rewrite
  system.
- Derive asymptotic consequences only after the exact output count is linked to
  syntax.

### Completion Requirements

- A named normalized Gray circuit and exact evaluator-preservation theorem exist
  for all `m >= 1` controls in arbitrary ambient width.
- Every resource formula is proved from that circuit's literal node list; no
  hard-coded count function or semantic equality substitutes for syntax.
- The source formula is marked verified only if the named output circuit realizes
  it. Otherwise the achieved formula and scope of the checked obstruction are
  documented without a global impossibility claim.
- Low-control sanity checks agree with the general theorem and the existing raw
  construction remains available as a regression baseline. In particular, test
  `(oneQubit,CNOT,total) = (4,2,6)`, `(8,8,16)`, and `(16,20,36)` at
  control counts one, two, and three.
- Focused Gray/optimizer, adjacent recursive consumers if changed, strict,
  trust-zero, axiom, traceability, and hygiene checks pass.

## 8-COR74-MERGERS

### Big Picture Objective

Apply the verified merger machinery to the corrected phase-safe Corollary 7.4
construction and test the paper's optimized total `48n - 204`.

### Detailed Implementation Plan

- Translate the balanced corrected chronology into optimizer IR without reverting
  the repaired partition, adjoint-A requirement, hybrid-B semantics, or smallest
  legal width.
- Replace the opaque selected exact-Toffoli witnesses with explicit oriented
  sixteen-node expansions before attempting cross-occurrence normalization.
- Normalize the literal one-qubit/CNOT expansion and prove exact evaluator equality
  and preservation of borrowed wires and spectators.
- Prove exact component, total, and accepted-cost formulas from the output syntax
  for every logical width `n >= 7`, including a width-seven sanity theorem.
- Compare the result with both the Goal 1 raw profile
  `(32n - 144, 24n - 100, 56n - 244)` and the source total `48n - 204`.
- Record that the printed total, if CNOTs remain `24n - 100`, requires exactly
  `24n - 104` one-qubit nodes. Test the width-seven target profile `(64,68,132)`
  and diagnostic widths eight and nine before accepting a symbolic formula.
- Update dependent recursive exact counts and asymptotic constants only if a new
  optimized circuit and its substitution/evaluator theorem actually justify them.

### Completion Requirements

- The optimized or stable output is a named circuit family with exact full-
  register semantics, restoration, and syntax-derived resource theorems.
- The printed `48n - 204` is exported only if realized by literal checked syntax.
  Otherwise the final status states the strongest proved count and why the source
  merger was not recovered.
- A refutation requires a completeness/maximality or lower-bound theorem for a
  precisely stated merger calculus and orientation class. One stalled normalizer
  run or one chosen exact-gate orientation can establish only “not recovered.”
- No source arithmetic error, invalid smallest-width split, or false relative-
  phase cancellation is reintroduced to obtain a better number.
- All affected recursive/resource theorems either remain unchanged with a stated
  reason or are rederived from the new circuit family.
- Focused Corollary/recursive builds, boundary examples, strict, trust-zero, axiom,
  documentation, and hygiene checks pass.

## 9-AUDIT

### Big Picture Objective

Integrate the stable optimization surface, close every test-case status honestly,
and deliver release-grade documentation and verification.

### Detailed Implementation Plan

- Reconcile public imports, theorem names, diagnostics, traceability rows,
  correction entries, README guidance, and `docs/final-report.md` against the
  compiled source.
- Document ordered-wire, chronology, exact-phase, optimizer-IR, unsupported-
  barrier, normalization-scope, and model-specific cost conventions.
- Add representative examples for two-wire embedding, fusion, the cost-three
  circuit, Gray boundaries, and Corollary 7.4 boundaries; keep diagnostics outside
  the public root.
- Add maintained `#print axioms` entries for all headline exported results and
  audit their exact dependency sets.
- Run focused and adjacent builds, public-root and audit builds, strict warning-as-
  error and trust-zero compilation, repository-wide forbidden scans, and a full or
  clean build appropriate to the final public import changes.
- Run `git diff --check`, verify documentation links and source-count formulas, and
  ensure this plan, all stage files, and the final report agree.

### Completion Requirements

- The public API is usable without importing diagnostic or paper-specific test
  modules, and examples show the intended downstream workflow.
- Every disputed claim has one final verified/refuted/not-recovered status backed
  by named Lean evidence; no optimizer limitation is overstated as a mathematical
  impossibility.
- All completed Lean modules are free of forbidden proof holes and project axioms;
  maintained axiom output is recorded and explained.
- Required focused, adjacent, full/clean, strict, trust-zero, and diff checks pass
  with exact commands and results recorded.
- `goal-2/0-plan.md`, the completed stage files, traceability/corrections, and the
  final project report agree on what was achieved and what remains open.
