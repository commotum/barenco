# 7-MULTICONTROL

Status: in progress (Lemma 7.1 and the displayed Gray circuit complete; Lemma 7.2 next).

## Current Facts

- Section 7 is available in the original PDF, the maintained Markdown
  transcription, and six extracted diagrams:
  `four-bit-gray-code-construction.png`,
  `lemma-7-2-linear-multi-control.png`,
  `lemma-7-3-four-block-construction.png`,
  `lemma-7-5-quadratic-general-control.png`,
  `lemma-7-9-linear-su2-control.png`, and
  `lemma-7-11-one-fixed-bit.png`. As in Sections 5–6, every diagram executes
  left-to-right and must be stored as a chronological circuit list.
- The established semantic target is `positiveControlledUnitary target controls U`
  for a `ControlSet target`. It already supports arbitrary ambient width, empty
  control sets, certified unitarity, and exact computational-basis action.
  `Primitive.positiveControlled` retains a multi-control gate only as an
  unexpanded `.controlledOneQubit controls.card` macro; it cannot receive a
  `oneQubitCNOT` cost before an explicit expansion.
- Stage 6 supplies exact arbitrary-width Lemma 6.1 and Corollary 6.2 circuits,
  disjoint-wire commutation laws, the exact signed action of both relative-phase
  Toffoli diagrams, and syntax-derived costs. In particular,
  `relativeToffoliPhase` is negative exactly on the input pattern `101`; this is
  the witness that a Corollary 7.4 contextual cancellation proof must track.
- `OneQubit.unitaryRoot (2^m) U` and `unitaryRoot_pow_two_pow` provide the exact
  positive power-of-two root required by Lemma 7.1. This is a semantic root
  choice, not a circuit synthesis or a resource theorem.
- No Gray-code API exists in the project or the pinned mathlib. Batteries exposes
  `BitVec.ofFnLE`/`ofFnBE` and their indexing laws, but the library's semantic
  basis remains `Fin n → Bool`. The first combinatorial layer should therefore
  use finite masks/Boolean assignments and add a `BitVec` bridge only when it
  simplifies executable diagnostics.
- `Circuit.eval`, `gateCount`, `kindCount`, and partial `cost` already separate
  full-register denotation from syntax resources. Exact dirty-wire restoration
  should be stated as evaluator equality; a classical truth table is diagnostic
  evidence only.
- `Barenco.MultiControl.Parity` now proves the representation-independent signed
  nonempty-subset XOR identity, including empty and singleton boundaries and the
  symmetric-difference update law needed by Gray transitions.
- `Barenco.MultiControl.GrayCode` constructs the exact bit-reversed reflected
  order, proves coverage/no duplicates/length/one-bit adjacency, pairs every mask
  with its maximum pivot, and proves that a strict pivot-rank rise can occur only
  after a singleton mask.
- `Barenco.MultiControl.GrayAccumulator` defines the generated CNOT edges and
  their Boolean action, proves the fixed-pivot and pivot-transfer update laws,
  reconstructs the six CNOT edges of the displayed four-bit circuit, proves a
  prefix accumulator invariant, certifies every generated edge as nondegenerate,
  and proves exact full-schedule restoration at every width, including zero.
- `Barenco.MultiControl.Layout` packages an ordered injective control embedding
  disjoint from an arbitrary ambient target and bridges it to `ControlSet`, CNOT,
  and singly controlled target primitives.
- `Barenco.MultiControl.Lemma71` now proves the signed target-root product, the
  selected power-of-two-root formula, the arbitrary-width basis semantics of
  certified embedded CNOT lists, exact restoration by the generated CNOT-only
  circuit, the target-local-state prefix invariant for the interleaved syntax,
  and exact full-register Lemma 7.1 semantics. The selected-root wrapper is valid
  for every positive control count; the zero-control local-gate case is kept
  separate. Exact root/CNOT/total macro counts are syntax-derived, while the
  unexpanded circuit correctly has no `oneQubitCNOT` cost.

## Source Claim Audit

| Claim | Source content | Audited status and routing |
|---|---|---|
| Four-bit Gray example | For `V^4=U`, seven controlled `V`/`V†` gates and six CNOTs realize `∧₃(U)` using parity masks `100,110,010,011,111,101,001`. | Exact chronology is recoverable and all three controls are restored. Formalize first as the smallest circuit consumer of the Gray API. |
| Lemma 7.1 | For `n≥3`, `∧_{n−1}(U)` uses `2^(n−1)−1` controlled `V`/`V†` gates and `2^(n−1)−2` CNOTs, with `V^(2^(n−2))=U`; proof omitted. After expansion/merging the paper claims `3·2^(n−1)−4` CNOTs and `2·2^(n−1)` one-qubit gates. | The macro count is plausible but needs a constructed schedule, accumulator invariant, root equation, and exact evaluator proof. The expanded count needs coordinated Section 5 decompositions and explicit merges; it does not follow from the semantic theorem. Stage 7. |
| Lemma 7.2 | For `n≥5` and `3≤m≤⌈n/2⌉`, a `∧ₘ(X)` gate uses `4(m−2)` three-bit Toffolis while borrowing `m−2` arbitrary wires and restoring them. | Recoverable as exact full-register equality. The inequalities encode `2m−1≤n`, ensuring enough distinct wires. The prose covers classical dirty bits; Lean must prove the induced permutation equality, hence correctness for superposition and entanglement. Stage 7. |
| Lemma 7.3 | For `n≥5` and `2≤m≤n−3`, a `∧_{n−2}(X)` gate is `A;B;A;B`, where `A=∧ₘ(X)` computes into one borrowed wire and `B=∧_{n−m−1}(X)` uses it with the remaining controls. Proof is only “by inspection.” | Recoverable by four Boolean cases/full basis action. The borrowed wire begins arbitrarily and is restored. Stage 7. |
| Corollary 7.4 | For `n≥7`, compose Lemmas 7.2–7.3 to obtain `8(n−5)` Toffolis and allegedly `48n−204` early-basic operations; four Toffolis are exact and the rest may be relative-phase implementations. | The `8(n−5)` macro count is repairable with the partition in C-003. The paper's intermediate remainder is wrong (C-004), and the final basic count remains unproved until exact contextual phase cancellation and all one-qubit merges are represented in syntax. Stage 7. |
| Lemma 7.5 | A fully controlled `U` is built recursively from a square root `V`, two singly controlled `V`/`V†` gates, two `∧_{n−2}(X)` gates, and one recursively smaller controlled `V`. | Exact generalization of Lemma 6.1 is recoverable. The statement omits a lower bound on `n`; the displayed recursive form requires at least one control (`n≥2`) or an explicit base case. Stage 7. |
| Corollary 7.6 | Recurrence `C_{n−1}=C_{n−2}+Θ(n)` is reported as a `Θ(n²)` simulation, with `48n²+O(n)` after detailed counting. | Export an exact recurrence and an `O(n²)` upper bound for the named construction. Do not claim optimal quadratic synthesis; see C-005. Its leading constant depends on the unresolved Corollary 7.4 count. Stage 7 for the construction/upper recurrence; final asymptotic packaging may continue in Stage 12. |
| Lemma 7.7 | A nonscalar fully controlled `U` needs at least `n−1` basic operations, argued by connectivity of the CNOT interaction graph. | The proof actually establishes a CNOT lower bound even with arbitrary one-qubit gates. It needs a tensor-factorization theorem up to wire reindexing and an exact definition `¬∃δ, U=Ph(δ)I`. Routed to Stage 10. |
| Lemma 7.8 | Recursive roots give an alleged `Θ(n log(1/ε))` approximation in induced Euclidean operator norm, with outcome-event error at most `2ε`. | Routed to Stage 9. The source has the wrong recursive cross-reference, missing eigenphase branch, unrestricted epsilon/depth problems, and an unproved arbitrary-event consequence; see C-006–C-008. |
| Lemma 7.9 | For `W∈SU(2)`, an ABC circuit with two large controlled-X operations realizes fully controlled `W`. | Recoverable from the exact Stage 4 ABC products plus full-register macro semantics. Its expanded linear cost uses a contextual borrowed-wire instance of Corollary 7.4. Routed to Stage 8 after Stage 7. |
| Corollary 7.10 | The printed statement says `∧_{n−2}(W)` has linear cost, although Lemma 7.9 and its diagram construct `∧_{n−1}(W)` and the next paragraph claims an n-bit Toffoli analogue. | Material index mismatch not covered by C-003–C-010. The useful intended result appears to be the stronger fully controlled `∧_{n−1}(W)` upper bound; record a new correction before formalizing it in Stage 8. |
| Lemma 7.11 | Compute the conjunction of `n−2` controls into a zero-initialized auxiliary wire, apply controlled `U`, then uncompute; proof is “by inspection.” | Recoverable only as a clean-zero subspace theorem, not equality of the full unitary with the target gate for arbitrary auxiliary inputs. The auxiliary must be restored and factorized for arbitrary data superpositions. Routed to Stage 8. |
| Corollary 7.12 | The Lemma 7.11 construction has claimed `Θ(n)` basic cost and a reusable fixed auxiliary bit. | State an explicit constructed upper bound under a clean-zero contract and threshold; no optimal `Θ(n)` claim follows without a lower bound in that model. Routed to Stage 8/12. |

## Exact Diagram Chronologies

- The four-bit Gray circuit, with controls `x₁,x₂,x₃` and target `t`, is:
  `C(x₁,V,t); CNOT(x₁,x₂); C(x₂,V†,t); CNOT(x₁,x₂);`
  `C(x₂,V,t); CNOT(x₂,x₃); C(x₃,V†,t); CNOT(x₁,x₃);`
  `C(x₃,V,t); CNOT(x₂,x₃); C(x₃,V†,t); CNOT(x₁,x₃);`
  `C(x₃,V,t)`.
  Immediately before the seven target gates, the selected control wire contains
  the parities `100,110,010,011,111,101,001`, respectively. The masks are the
  nonzero bit-reversed reflected Gray path; the final CNOT restores `x₃`, and the
  first two controls have already been restored.
- In the illustrated Lemma 7.2 case `n=9,m=5`, write
  `q₁=T(5,8→9)`, `q₂=T(4,7→8)`, `q₃=T(3,6→7)`, and
  `q₄=T(1,2→6)`. The exact chronology is
  `q₁;q₂;q₃;q₄;q₃;q₂;q₁;q₂;q₃;q₄;q₃;q₂`.
  In general, for the inward chain `q₁,…,q_{m−1}`, the schedule is
  `q₁,…,q_{m−1}; q_{m−2},…,q₁; q₂,…,q_{m−1}; q_{m−2},…,q₂`,
  of length `4(m−2)`. The first part toggles the logical target correctly while
  disturbing borrowed wires; the final part restores every borrowed wire.
- In the illustrated Lemma 7.3 case `n=9,m=5`, `A` has controls wires `1–5`
  and target borrowed wire `8`; `B` has controls wires `6,7,8` and target wire
  `9`. The chronology is exactly `A;B;A;B`. The first and third `A` occurrences
  restore wire `8`; the two `B` occurrences cancel its unknown initial value and
  retain only the conjunction of all logical controls on the final target.
- The Lemma 7.5 chronology partitions the controls into `prefix` and the last
  control `c`: `C(c,V,target); MCX(prefix,c); C(c,V†,target);`
  `MCX(prefix,c); MC-V(prefix,target)`, with `V²=U`. The last operation is the
  recursively smaller multi-controlled `V`, not a local target gate.
- The Lemma 7.9 chronology partitions the controls into `prefix` and last control
  `c`: `C(c,A,target); MCX(prefix,target); C(c,B,target);`
  `MCX(prefix,target); C(c,C,target)`. Under standard-column chronology its
  inactive and active target products are the already established
  `C*B*A=I` and `C*X*B*X*A=W` identities.
- Lemma 7.11 uses data controls `prefix`, clean auxiliary `a=0`, and target `t`:
  `MCX(prefix,a); C(a,U,t); MCX(prefix,a)`. This circuit is intentionally not
  claimed correct when `a` begins in an arbitrary state.

## Known Corrections and New Audit Findings

- C-003: the printed Corollary 7.4 choice
  `m₁=⌈n/2⌉`, `m₂=n−m₁−1` gives `m₂=2` at `n=7`, outside Lemma 7.2. Use
  `m₁=⌊n/2⌋`, `m₂=n−m₁−1`; both are at least three for `n≥7` and the total
  `8(n−5)` is unchanged.
- C-004: from `8(n−5)=8n−40` total Toffolis and four exact occurrences, the
  relative-phase remainder is `8n−44`, not the paper's `8n−36`. Consequently
  `48n−204` must be independently reconstructed and is not accepted by algebraic
  correction alone.
- C-005: Corollary 7.6 gives the cost of a displayed recursive algorithm, not a
  quadratic lower bound on optimal synthesis. Use exact counts/upper bounds for
  the named syntax.
- C-006: the original PDF says the `Vₖ` occur in recursive applications of
  Lemma 7.3; this must be Lemma 7.5. The Markdown transcription silently uses
  the corrected reference.
- C-007: `‖Dₖ-I‖≤π/2^k` needs principal eigenangles (or an equivalent coherent
  branch), not arbitrary arguments of the eigenvalues. Existing exact roots do
  not yet prove adjacent-root coherence or this norm estimate.
- C-008: the unrestricted `ε>0` statement makes `log(1/ε)` nonpositive for large
  epsilon and may choose more recursive levels than controls. Stage 9 needs an
  integer-depth theorem, a restricted logarithmic corollary, and exact fallback.
- C-009: “congruent modulo phase shifts” is not one relation. Stage 6 now has the
  exact `101` input-column phase witness and adjacent-pair cancellation. Stage 7
  must still prove cancellation in the ordered Corollary 7.4 basis paths; mere
  even occurrence counts are insufficient.
- C-010: Lemmas 7.2–7.3 use dirty borrowed wires; Lemma 7.11 uses a clean-zero
  wire. Restoration prose must become full-register equality in the dirty case
  and a quantified zero-subspace/factorization theorem in the clean case.
- New correction candidate: Corollary 7.10 is misindexed as `∧_{n−2}(W)`. Its
  stated dependency, Lemma 7.9 diagram, and the n-bit Toffoli discussion all
  point to `∧_{n−1}(W)`. Formalize the strongest checked version and record the
  source discrepancy before closing Stage 8.
- New boundary clarification: Lemma 7.5 states no condition on `n`. Its recursive
  syntax needs a last control and a prefix, so the theorem must use `n≥2` with an
  explicit smallest case or state a stricter recursive threshold and separate
  base circuits.

## Updated Assumptions

- A Gray schedule is more than a list of adjacent masks. Each mask needs a
  distinguished pivot wire holding its parity, every intervening CNOT must be
  proved to update that parity, and the final schedule must restore all controls.
  For the bit-reversed reflected path, masks with maximum set index `r` form one
  block: only wire `r` accumulates a parity and all lower wires are raw.
- Lemma 7.1 should expose a parameterized theorem for any `V` satisfying the
  required power equation and a selected-root wrapper using
  `unitaryRoot (2^(n−2)) U`. The power exponent is positive only after the
  statement's `n≥3` boundary is made explicit.
- Multi-control APIs should quantify named, pairwise distinct wire lists or
  embeddings and derive their `ControlSet`s. Cardinality equations alone do not
  identify control order, borrowed wires, or the target.
- Dirty-wire correctness means equality of full permutation/unitary matrices,
  not only restoration on individual classical assignments. This automatically
  covers arbitrary superpositions and external entanglement.
- The Stage 7 public scope is the opening Gray construction, Lemmas 7.1–7.5,
  Corollary 7.4, and the corrected construction-specific part of Corollary 7.6.
  Lemma 7.7 remains Stage 10, Lemma 7.8 remains Stage 9, and Lemmas/Corollaries
  7.9–7.12 remain Stage 8. Their source audits stay here for dependency control.
- All Section 7 resource statements continue to use `CostModel.oneQubitCNOT`.
  Macro counts for controlled gates or Toffolis are separately named structural
  counts and cannot be called early-basic costs.

## Big Picture Objective

Build reusable Gray/parity and multi-control circuit infrastructure, prove the
exact full-register semantics and restoration properties of the paper's
no-clean-ancilla constructions through Lemma 7.5, and derive only those exact and
asymptotic resource upper bounds justified by explicit circuit syntax.

## Detailed Implementation Plan

1. Add pure parity and Gray leaves. Define nonempty finite masks, Boolean XOR parity,
   the signed parity exponent, and the bit-reversed reflected Gray schedule with
   its pivot/update information. Prove nonemptiness, no duplicates, coverage of
   every nonempty mask, length `2^m−1`, consecutive one-bit transitions, pivot
   validity, initial/final singleton masks, and restoration of the linear control
   state.
2. Prove the mathematical core before circuit syntax:
   the alternating signed sum of nonempty subset parities is
   `2^(m−1)` exactly when every input bit is true and zero otherwise. The cleanest
   proof pairs subsets differing by a false input; the all-true case counts odd
   subsets. This independently checks the paper's inclusion-exclusion identity.
   **Implemented:** `parityInclusionExclusionSum_formula` and its all-true,
   false-witness, singleton, and finite-type specializations compile.
3. Define the alternating Gray controlled-root circuit and prove the exact n=4
   diagram first. Generalize to Lemma 7.1 using the pivot invariant and signed
   parity identity, then add the selected power-of-two-root wrapper. Prove macro
   counts before attempting the coordinated Section 5 primitive expansion.
4. Define an ordered-wire partition type carrying data controls, borrowed wires,
   and target with disjointness proofs. Construct the Lemma 7.2 ladder schedule,
   prove its Boolean update/restoration theorem, lift it to full-register circuit
   equality, and derive the exact `4(m−2)` Toffoli count.
5. Define the Lemma 7.3 four-block circuit. Prove `A;B;A;B` by explicit Boolean
   algebra for an arbitrary borrowed bit, then use Lemma 7.2 expansions and the
   repaired floor partition to obtain Corollary 7.4's `8(n−5)` macro count.
6. Construct separate exact and relative-phase expanded Corollary 7.4 circuits.
   Prove exact evaluator equality by multiplying the Stage 6
   `relativeToffoliPhase` witnesses along every ordered basis path. Only after
   that proof, formalize local-gate mergers and decide whether `48n−204` is true;
   otherwise state and prove the strongest corrected explicit count.
7. Define Lemma 7.5 as a five-macro chronological circuit and prove its evaluator
   equality by the same parity/conjugation structure as Lemma 6.1, with exact
   boundary/base cases. Expand recursive calls only in a separate syntax layer.
8. Define a natural-number recurrence from the constructed circuits, prove an
   exact finite upper formula and `O(n²)`, and label any two-sided `Θ` theorem as
   the count of this algorithm only. Do not import the later lower-bound claim.
9. Add low-dimensional diagnostics: the seven-mask n=4 sequence, all sixteen
   basis inputs for the diagram, smallest legal Lemma 7.2/7.3 instances, dirty
   borrowed wires in both basis values, the repaired `n=7` partition, nonadjacent
   embeddings, counts, and costs.
10. After public leaves stabilize, update the root, axiom audit, conventions,
    traceability, corrections, and `0-plan.md`; run focused/adjacent builds first,
    then warning-as-error and two full builds after root integration.

## Recommended First Theorem

The first public proof target should be a representation-independent theorem of
the following form: for a nonempty finite control set and Boolean assignment,
the sum over nonempty subsets of `(-1)^(|S|+1)` times the XOR parity on `S` is
`2^(m−1)` when all controls are true and zero otherwise. It is the exact exponent
identity behind Lemma 7.1, has no circuit/indexing dependencies, exposes boundary
cases immediately, and gives the subsequent Gray circuit proof a small stable
semantic target. The next theorem should certify the bit-reversed reflected-Gray
pivot invariant, not merely Hamming adjacency.

## Build Structure

- `Barenco/MultiControl/Parity.lean`: representation-independent XOR parity,
  symmetric-difference bridges, signed subset contributions, and the exact
  inclusion-exclusion closed form.
- `Barenco/MultiControl/GrayCode.lean`: low-dependency runtime/public mask and
  schedule definitions plus proof-side/public coverage, adjacency, pivot, and
  pivot theorems. Avoid importing circuit semantics.
- `Barenco/MultiControl/GrayAccumulator.lean`: pure Boolean CNOT schedules,
  accumulator states, local fixed-pivot/transfer update laws, and eventual full
  schedule restoration. It imports `Parity` and `GrayCode`, but no circuit layer.
- `Barenco/MultiControl/Layout.lean`: ordered control embeddings and the narrow
  bridges to existing `ControlSet` and primitive syntax.
- `Barenco/MultiControl/Lemma71.lean`: runtime/public Gray circuit constructors
  and proof-side/public four-bit/general evaluators, root wrapper, and macro
  counts. Import `GrayCode`, narrow controlled circuit semantics, roots, and cost.
- `Barenco/MultiControl/Borrowed.lean`: runtime/public wire-partition and Lemma 7.2
  ladder syntax; proof-side/public Boolean update, restoration, evaluator, and
  Toffoli-count theorems.
- `Barenco/MultiControl/FourBlock.lean`: runtime/public Lemma 7.3 and repaired
  Corollary 7.4 macro circuits; proof-side/public full-register correctness,
  partition inequalities, and `8(n−5)` count.
- `Barenco/MultiControl/RelativePhase.lean`: heavy proof-side/public contextual
  phase cancellation and explicit early-basic expansion/count. Keep it out of
  the Boolean/runtime leaves.
- `Barenco/MultiControl/Recursive.lean`: runtime/public Lemma 7.5 constructor and
  proof-side/public exact evaluator and root-selected theorem.
- `Barenco/MultiControl/Resources.lean`: construction-specific recurrences and
  upper bounds only after all counted syntax exists.
- `Barenco/MultiControlExamples.lean`: diagnostic exhaustive cases, excluded from
  the public root and axiom surface.
- Existing high-fanout `Basic`, `Controlled`, `Circuit`, and `Cost` modules remain
  unchanged unless a second checked consumer proves a genuinely foundational gap.
  The Stage 6 CNOT/local commutation API should be reused from its current public
  leaf rather than duplicated.
- Runtime/public declarations are schedules, wire partitions, and circuit
  constructors. Proof-side/public declarations are combinatorial identities,
  evaluator/restoration theorems, phase cancellation, and resource equations.
  Concrete small-width checks are diagnostic. No fallback or temporary theorem
  enters `Barenco.lean`.
- Initial focused build: `lake build Barenco.MultiControl.GrayCode`. Adjacent
  builds grow one leaf at a time through `Barenco.MultiControl.Lemma71`,
  `Borrowed`, `FourBlock`, `RelativePhase`, `Recursive`, `Resources`, and
  `Barenco.MultiControlExamples`. Root/audit/full builds occur only after stable
  public integration.

## Boundary Checks

- Every theorem states ambient width, ordered logical wires, target, borrowed
  wires, and all disjointness/cardinality hypotheses. No implicit top-to-bottom
  numbering from a diagram enters a public theorem.
- The Gray circuit proves both the target product and restoration of every
  control. A list containing every parity mask is not by itself a circuit proof.
- Lemma 7.2/7.3 dirty-wire theorems quantify arbitrary initial borrowed bits and
  prove full-register equality. Lemma 7.11's later clean wire is never silently
  treated as dirty or vice versa.
- Exact macro semantics, explicit primitive expansion, exact structural count,
  and asymptotic upper bound remain four separate theorem layers.
- Corollary 7.4 does not use basis-phase equivalence as a congruence. The exact
  phase product is proved in the actual ordered surrounding circuit.
- `V†` occurrences use the inverse of the same selected `V`; repeated controlled
  expansions share coordinated witnesses whenever cancellation or merging needs
  them.
- Lemma 7.5 and every recurrence have explicit smallest widths and base cases.
  No subtraction such as `n−2` is used to hide an invalid index range.
- Section 7 uses the one-qubit+CNOT model. Toffoli and controlled-one-qubit macros
  remain unsupported until replaced by named explicit circuits.

## No-Cheating Checks

- No hard-coded `16×16` matrix proof substitutes for the arbitrary-width Gray
  evaluator or dirty-wire restoration theorem.
- No classical truth-table theorem is promoted to operator equality without a
  proved permutation/basis-extensionality bridge.
- No `Primitive.unclassified`, semantic dummy gate, or relabeled macro occurs in
  a resource-counted circuit.
- No resource count is inferred from semantic equality, a diagram, or prose.
  Counts inspect the exact named syntax after every expansion and merge.
- No phase cancellation is inferred from an even number of relative Toffolis;
  the ordered input phase at each occurrence is computed.
- No `Θ(n²)` or `Θ(n)` optimality claim is exported from an upper-bound recurrence.
- No `sorry`, `admit`, `by?`, custom `axiom`, `opaque`, `native_decide`, or
  `bv_decide` in completed Stage 7 modules.

## Completion Requirements

- [x] The signed subset-parity identity and an executable Gray schedule compile
  with coverage, uniqueness, adjacency, pivot/update, length, and restoration
  theorems, including zero/one-control boundary diagnostics.
- [x] The four-bit diagram and general Lemma 7.1 have named chronological circuits,
  exact arbitrary-width evaluators, selected-root wrappers, exact macro counts,
  and any claimed expanded counts proved from coordinated syntax.
- [ ] Lemmas 7.2 and 7.3 have named circuits and full-register dirty-wire
  correctness/restoration theorems for all legal widths, plus exact Toffoli counts.
- [ ] Corollary 7.4 uses the repaired partition, proves `8(n−5)` Toffoli macros,
  proves contextual relative-phase cancellation, and either proves or explicitly
  corrects `48n−204` from an expanded circuit.
- [ ] Lemma 7.5 has exact evaluator/root theorems with explicit base cases, and
  Corollary 7.6 is replaced by an exact construction recurrence and justified
  quadratic upper bound.
- [ ] Later claims 7.7–7.12 retain explicit routing and dependency assumptions;
  no Stage 9/10 theorem or clean-ancilla theorem is claimed prematurely.
- [ ] Focused and adjacent builds, warning-as-error checks, two full post-root
  builds, forbidden-shortcut scans, `git diff --check`, and headline axiom audits
  pass and are recorded.
- [ ] Conventions, traceability, corrections (including the Corollary 7.10 index
  issue), axiom audit, this stage file, and `0-plan.md` are synchronized before
  Stage 7 is marked complete.

## Stage Results

- Source audit completed against the original PDF, Markdown transcription, all
  six Section 7 diagram images, current Lean APIs, and correction entries
  C-003–C-010. No Lean, root, audit, or documentation file was changed during
  this audit.
- The first implementation slice is fixed as the signed subset-parity identity,
  followed by the reflected-Gray pivot invariant and the exact four-bit circuit.
- Open source issues carried into implementation are Corollary 7.4's contextual
  phases/basic count, Lemma 7.5's omitted width boundary, Corollary 7.10's index
  mismatch, and every clean/dirty auxiliary contract described above.
- `Parity.lean` exports `xorParity`, `xorParity_symmDiff`,
  `xorParity_eq_add_of_symmDiff_eq_singleton`, `signedParityContribution`,
  `nonemptySubsets`, `parityInclusionExclusionSum`, and
  `parityInclusionExclusionSum_formula`. The proof is order-independent and gives
  exactly `2^(card-1)` on the all-true branch and zero otherwise.
- `GrayCode.lean` exports `fullGrayCode`, `grayCode`, `fullGrayToggles`,
  `grayToggles`, `grayPivots`, exact length/coverage/no-duplicate laws,
  `fullGrayCode_isChain`, `grayCode_isChain`, `grayCode_pivots`,
  `grayPivots_isChain`, and
  `grayCode_previous_singleton_of_pivotRank_lt`. The executable width-three
  schedule is exactly `100,110,010,011,111,101,001`.
- `GrayAccumulator.lean` exports `grayCNOTEdges`, `xorWireUpdate`,
  `parityAccumulatorState`, the two local accumulator transition theorems, and
  exact edge count `2^width-2`, generated-edge validity, a prefix invariant, and
  exact full restoration for every width.
- `Layout.lean` exports `OrderedControlLayout`, its exact-cardinality `controlSet`,
  ordered restriction, and certified embedded CNOT/controlled-target primitives.
  `MultiControlExamples.lean` checks the source's three-control signed identity,
  masks/toggles/pivots/CNOT chronology, and restoration on all eight inputs.
- Direct warning-as-error checks passed for all four public leaves and the
  diagnostic module. The combined focused build
  `lake build Barenco.MultiControl.Parity Barenco.MultiControl.GrayCode
  Barenco.MultiControl.GrayAccumulator Barenco.MultiControl.Layout
  Barenco.MultiControlExamples` passed with 3,060 jobs. Eight representative
  axiom checks use only `propext`, `Classical.choice`, and `Quot.sound`; the
  transfer theorem needs only `propext` and `Quot.sound`. The forbidden-shortcut
  scan and `git diff --check` passed.
- Corrections C-022 and C-023 now record Corollary 7.10's control-count mismatch
  and Lemma 7.5's omitted recursive boundary/base cases.
- `Lemma71.lean` additionally exports the order-independent target product
  formula, a selected exact root, the ordered-control ambient CNOT evaluator,
  certified generated CNOT syntax, its full-register restoration theorem,
  `grayControlledViaRootCircuit`, the exact interleaved prefix evaluator,
  `eval_grayControlledViaRootCircuit`, `grayControlledCircuit`, and
  `eval_grayControlledCircuit`. For `tail+1` controls the exact syntax has
  `2^(tail+1)-1` controlled-root macros, `2^(tail+1)-2` CNOTs, and
  `2^(tail+2)-3` total nodes. Its early-basic cost remains `none` pending the
  explicit coordinated expansion.
- `fourBitGrayCircuit` is exactly the source's 13-node chronology; the generated
  width-three syntax is proved equal to it. Its arbitrary-width evaluator,
  parameterized fourth-root theorem, seven-root/six-CNOT counts, and rejected
  unexpanded early-basic cost compile. The one-control boundary is exactly one
  controlled root and no CNOT; C-024 records why zero controls require a separate
  local circuit.
- Strict compilation passed for every new public/diagnostic module and the root.
  The focused root/audit build passed with 3,482 jobs; two consecutive full builds
  passed with 3,480 jobs each. The maintained audit now prints 96 headline
  declarations; all use only `propext`, `Classical.choice`, and `Quot.sound`
  (with `nodup_grayCode` not requiring choice). Forbidden-shortcut scans and
  `git diff --check` passed.
