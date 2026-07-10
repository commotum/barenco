# 11-UNIVERSALITY

Status: complete.

## Current Facts

- Section 8 changes its cost model before the universality discussion, but exact
  generation by arbitrary one-qubit gates and CNOT is a semantic/syntactic claim
  independent of pricing arbitrary two-qubit gates. Stage 11 will prove exact
  generation first; Stage 12 will attach only justified structural and asymptotic
  costs.
- The paper invokes the Reck decomposition without supplying an elimination
  algorithm or a product order. Its displayed formula says an arbitrary unitary
  is a product of two-level transformations followed by a diagonal unitary, and
  says the diagonal is itself a product of two-dimensional rotations. Those are
  mathematical obligations, not imported facts.
- A two-level transformation acts nontrivially on exactly two computational-basis
  states. The Section 8 Gray path first conjugates those two states to an adjacent
  pair, applies a one-qubit block conditioned on every other wire having a
  prescribed Boolean pattern, and reverses the conjugating swaps. Exact proof must
  show its action on every basis state, including states not on the named path.
- The paper's “modified” fully controlled gates include both positive and negative
  controls. The existing semantic core has positive controls; local Pauli-X
  conjugation can turn each zero-pattern condition into a positive control and
  restore the affected wires. A temporary basis relabeling is not itself a circuit
  theorem.
- Endpoint orientation cannot be inferred from the path display. In the paper's
  own example the final transition changes the target bit from `true` to `false`.
  Applying a canonical `false,true` one-qubit matrix without transporting the
  ordered endpoint pair would implement `X U X`, not `U`, on that two-state
  subspace. The construction must carry an explicit endpoint equivalence or insert
  the corresponding conjugation.
- `Basis n = Fin n → Bool` is the circuit-semantic index. The pinned matrix APIs
  support simultaneous reindexing. The current `basisIndex` is only a descriptive
  natural-number function with four width-two checks; it has no proved range,
  injectivity, or equivalence with `Fin (2^n)`. Algebraic elimination should remain
  reusable over a general finite index (ideally directly `Basis n`); any later
  lexicographic `Fin (2^n)` bridge is a separate theorem, not an existing API.
- The project already has chronological `Circuit.append`/`Circuit.eval`, certified
  arbitrary one-qubit primitives, CNOT primitives, circuit adjoints, finite-mask
  Gray-code facts, and exact positive multi-control constructions. A direct
  duplicate-free shortest Hamming path has now been proved for source
  traceability. The main exact circuit theorem instead uses a smaller affine
  conjugation: translate the first endpoint to zero with local X gates, then use
  CNOTs from one differing pivot to clear every other differing bit of the second
  endpoint. This sends the ordered pair to zero and a singleton without ancillas.
- The pinned mathlib audit confirms there is no Givens, Householder/QR,
  two-level-unitary, or unitary-triangular decomposition API. The general
  transvection factorization is unusable because its factors are nonunitary.
  Reindexing, `fromBlocks`, unitary-group, diagonal, and finite-induction APIs are
  sufficient for a custom construction.
- Boundary dimensions matter. On zero qubits the Hilbert space has one basis
  state and hence arbitrary `U(1)` phases, but the allowed one-qubit/CNOT syntax
  has no legal primitive and evaluates only to identity. Exact universality is
  therefore false at width zero: the headline must assume positive width and a
  separate theorem must characterize the zero-wire obstruction. On one qubit the
  entire target is an allowed primitive. A two-level object requires two distinct
  basis indices and is empty in dimensions below two.
- The Section 8 claims that six arbitrary two-qubit gates realize every `U(8)` and
  that dimension counting yields a general lower bound remain unresolved or
  excluded under Stage 10. They are not prerequisites for exact universality.
- The source's per-factor `Theta(n^3)` and total `Theta(n^3 4^n)` claims are also
  overstated. The Gray path only satisfies `m <= n+1`; adjacent endpoints have
  `m=2` and one fully controlled gate, so that displayed construction supports a
  uniform `O(n^3)` upper bound, not a per-instance lower bound. The affine
  conjugation needs only linearly many X/CNOT transport gates around one quadratic
  fully controlled block, giving the formal library a stronger uniform `O(n^2)`
  construction per two-level factor. Stage 12 must state this as an upper bound,
  not promote either schedule to `Theta` without a matching lower theorem.

## Updated Assumptions

- Exact arbitrary one-qubit `U(2)` gates are primitives; no fixed finite gate-set
  approximation theorem is assumed.
- CNOT is the only required entangling primitive in the final headline circuit.
- The construction uses the same `n` data wires throughout, with no work bit,
  measurement, reset, or discarded subsystem.
- Matrix equality is exact, including global phase. Diagonal and zero-qubit phases
  therefore require real circuit factors and cannot be erased observationally.
- A finite-dimensional algebraic decomposition may first return certified
  two-level unitaries and diagonal phases. Completion requires constructing those
  factors and proving their chronological product, not merely proving generation
  as an abstract subgroup membership proposition.
- Efficiency and exact generation remain separate. Stage 11 may record exact list
  lengths needed by Stage 12, but no `Theta` theorem follows without a matching
  lower bound in the same model.

## Big Picture Objective

Construct and verify an exact, no-ancilla circuit over arbitrary one-qubit gates
and CNOT for every positive-width finite-qubit unitary. Supply a reusable
finite-dimensional two-level decomposition independently of the qubit
specialization, then connect each two-level factor to a fully explicit affine
X/CNOT conjugation circuit. Retain the verified shortest Hamming path as a direct
formal reconstruction of the paper's Gray-path reasoning.

## Detailed Implementation Plan

1. **Complete.** The source and pinned-API audit fixes the multiplication and
   endpoint-order hazards, requires a direct shortest Hamming path, retains exact
   diagonal phases, and corrects the headline to positive register width.
2. **Complete.** Add a low-dependency algebraic two-level module: define the embedded `U(2)`
   block on two distinct finite indices, certify unitarity, prove entries/basis
   action, inverse and multiplication facts actually needed by elimination.
3. **Complete.** Prove a constructive finite-unitary elimination/decomposition theorem. Keep
   the chronological factor list explicit, include the residual diagonal phases,
   and prove the product equation with all zero/singleton boundary cases.
4. **Complete.** Add qubit-path infrastructure: construct a duplicate-free shortest Hamming path
   between distinct basis assignments, prove adjacent states differ at one named
   wire, and specify the exact fixed values required of every other wire.
5. **Complete.** Define pattern-controlled one-qubit circuits via local-X conjugation of the
   existing positive-control implementation. Prove exact full-register semantics,
   negative-control restoration, and primitive expansion to one-qubit/CNOT syntax.
6. **Complete.** Construct a two-level circuit by affine-conjugating the two endpoints to zero
   and a singleton, applying the desired ordered block on that adjacent pair, and
   reversing the X/CNOT transport. Prove evaluator equality using the general
   certified-unitary transport theorem. The shorter Hamming path remains a proved
   alternative/source model rather than the assembly dependency.
7. **Complete.** Map every algebraic factor to its circuit and concatenate chronologically with
   the order required by `Circuit.eval_append`. Prove exact universality for
   positive register width, the direct one-qubit specialization, and the exact
   zero-wire identity-only obstruction.
8. **Complete.** Add root-excluded examples in dimensions one, two, and four, public imports,
   traceability/correction/convention updates, maintained axiom checks, and focused
   plus full verification. Leave structural/asymptotic aggregation to Stage 12.

## Build Structure

- Algebraic layer: `Barenco/Universality/Givens.lean`,
  `Barenco/Universality/TwoLevel.lean`, and one or more narrow elimination leaves.
  These are public algebraic APIs and must not import circuit syntax.
- Circuit layer: narrow full-control, pattern-control, basis-path, adjacent-pair,
  affine-pair, and two-level transport modules importing only the semantic/circuit
  and established multi-control leaves they use.
- Assembly layer: a universality leaf importing both algebraic and circuit
  synthesis. `Barenco.lean` changes only after stable theorem signatures compile.
- Planned diagnostic leaf: `Barenco/Universality/UniversalityExamples.lean`, excluded
  from the public root.
- High-fanout `Semantics.lean`, `Circuit.lean`, and established Section 4–10 theorem
  leaves are not to be edited unless the audit demonstrates a genuinely shared
  missing lemma.
- Runtime/public declarations: constructive factor and circuit definitions.
  Proof-side declarations: elimination invariants and entrywise path lemmas.
  Diagnostic declarations: concrete low-width examples and API probes. No fallback
  or temporary semantic primitive may enter the public theorem.
- Focused commands will be recorded after module ownership is fixed; every new
  leaf is built directly before adjacent assembly/root/audit builds.

## Boundary Checks

- A theorem about a two-level matrix does not by itself establish a circuit on a
  larger register; the bridge must prove exact evaluator equality.
- The path circuit must be a conjugation, so all intermediate basis permutations
  and all negative-control X gates are explicitly reversed.
- “Adjacent” means exactly one differing wire, with a named target and a proof
  that all other controls are distinct from it.
- The selected `U(2)` block orientation must agree simultaneously with matrix
  columns, basis-ket action, path endpoint order, and chronological evaluation.
  In particular, a final `true`-to-`false` target transition is not silently read
  in canonical `false,true` order.
- Diagonal phases at positive width are synthesized exactly, not removed as
  global phase. At zero width, prove that the restricted syntax reaches only
  identity and explicitly record the resulting failure of exact universality.
- The final circuit contains only trusted arbitrary one-qubit and CNOT primitives;
  controlled-one-qubit macros, Toffoli macros, arbitrary-two-qubit primitives, and
  unclassified semantic gates may occur only in separately named intermediate
  syntax with a proved primitive expansion.
- Exact universality, dense generation by a fixed finite set, and efficient
  synthesis are different theorem families. Only the first is a Stage 11 target.

## No-Cheating Checks

- No `Primitive.unclassified` wrapper or hard-coded full-register denotation may
  stand in for a synthesized circuit.
- No permutation or reindex equivalence may be counted as a gate unless a circuit
  implementing it is constructed and evaluated.
- No basis-state sample or finite-width computation may replace the general matrix
  proof; basis action is acceptable only with a proved extensionality bridge.
- No diagonal residual may be silently dropped up to phase.
- No existence theorem is called constructive unless it returns enough factor or
  circuit data for the evaluator theorem.
- No `sorry`, `admit`, `by?`, custom `axiom`, `opaque`, `native_decide`, or
  `bv_decide` may occur in completed modules.

## Completion Requirements

- [x] A reusable finite-dimensional theorem decomposes every certified complex
  unitary into explicit two-level and/or diagonal certified factors with a proved
  ordered product equation.
- [x] Every algebraic two-level factor on a qubit basis has an exact no-ancilla
  circuit implementation on the full register.
- [x] Pattern controls, source-path combinatorics, adjacent endpoint orientation,
  affine forward/adjoint restoration, and exact action on the complete register
  are all machine checked.
- [x] The headline theorem returns a circuit containing only arbitrary one-qubit
  and CNOT primitives and proves exact evaluator equality for every positive `n`,
  with a direct width-one case and a separate exact width-zero obstruction theorem.
- [x] Exact generation is not conflated with approximation, fixed-set dense
  generation, arbitrary-two-qubit pricing, or an efficiency theorem.
- [x] Representative low-dimensional examples, public imports, maintained axiom
  entries, forbidden-token/diff checks, strict/trust-zero compilation, focused
  builds, and two full builds pass and are recorded.
- [x] Traceability, corrections, and conventions document every material repair
  to Section 8's decomposition, Gray path, diagonal, ordering, and boundary claims.

## Stage Results

- Stage file created before Lean implementation. The initial audit isolates two
  independent obligations: finite-dimensional two-level elimination and exact
  qubit-circuit realization. It rejects the paper's dimension-count argument and
  six-`U(4)` surjectivity claim as prerequisites, and makes diagonal/global phases,
  negative controls, chronology, no-ancilla scope, and width-zero/one behavior
  explicit.
- The completed independent source/API audits found no reusable unitary
  decomposition in pinned mathlib, rejected nonunitary transvections, identified
  the paper's reversed final-edge block hazard and false per-factor `Theta(n^3)`
  inference, and selected a shortest differing-wire path instead of the Section 7
  reflected Gray traversal.
- `Barenco/Universality/Givens.lean` now supplies a total certified complex Givens
  block. It exactly sends `(a,b)` to
  `(0,sqrt(normSq a + normSq b))`, including the zero pair, and passes strict and
  trust-zero compilation.
- `TwoLevel.lean`, `EliminationCore.lean`, `Elimination.lean`, and
  `FiniteBridge.lean` now give a reusable constructive decomposition over every
  finite decidable index type. Exact left-Givens elimination returns an explicit
  ordered list of certified two-level factors and a certified diagonal residual,
  with a proved product equation and no lost phase; the finite zero- and
  one-dimensional cases are included.
- `FullControl.lean`, `PatternFlip.lean`, `PatternControl.lean`, and
  `AdjacentTwoLevel.lean` now compile. They expand mixed-polarity pattern controls
  to literal arbitrary one-qubit/CNOT syntax, prove exact full-register semantics
  and restoration, and repair reversed endpoint order by using `X U X` precisely
  when the first endpoint has target bit `true`.
- `BasisPath.lean` proves a duplicate-free shortest differing-wire path, exact
  endpoints, one-wire adjacency, length `hammingDist + 1`, and the bound `<= n+1`.
  `TwoLevelTransport.lean` proves the stronger algebraic conjugation theorem that
  any certified unitary with the two required basis-ket images transports the
  corresponding ordered two-level block; no unsupported claim about the remaining
  basis permutation is needed.
- `DiagonalCircuit.lean` now turns every certified positive-width diagonal
  unitary into literal one-qubit/CNOT syntax. It constructs one certified
  two-entry diagonal block for each complementary basis pattern, proves that the
  duplicate-free schedule contributes exactly the matching phase on every basis
  ket, and derives an exact finite-sum accepted cost from the circuit syntax.
- `ZeroWidth.lean` proves that every proof-carrying one-qubit/CNOT circuit at
  width zero is literally empty, evaluates to identity, and has gate count zero.
  Its explicit certified scalar `-1` unitary proves the exact headline cannot be
  extended to zero wires; this is not hidden by global-phase relaxation.
- `WidthOne.lean` separately proves the positive boundary without invoking
  elimination: `Basis 1` is explicitly equivalent to `Bool`, every certified
  width-one unitary reindexes to one arbitrary qubit primitive, and the singleton
  circuit has exact evaluator equality, gate count one, and accepted cost one.
- `CircuitProduct.lean` isolates chronological order from algebraic order. Given
  component circuits in conventional left-to-right matrix-product order, it
  executes them right-to-left and proves that the evaluator is exactly the
  `List.prod` of their evaluators, with additive gate-count and accepted-cost
  theorems derived from syntax.
- A smaller affine implementation was discovered after the path layer compiled:
  X gates translate the first endpoint to zero and pivot-controlled CNOTs reduce
  the second endpoint's difference mask to one bit. This improves the construction
  targeted by the library from the source route's cubic worst-case upper bound to
  a quadratic upper bound per two-level factor; the matching asymptotic theorem is
  deliberately deferred to Stage 12 even though the exact structural counts now
  compile.
- `AffinePair.lean` and `TwoLevelCircuit.lean` now complete that implementation.
  The transport sends the ordered endpoints exactly to all-zero and a canonical
  singleton, uses exactly `hammingDist - 1` clearing CNOTs, and has literal
  one-qubit/CNOT count and accepted-cost theorems. The chronological circuit
  `P; Q; P†` is independently audited to evaluate as `P⁻¹ * Q * P`; the general
  unitary transport theorem then proves exact equality to every algebraic
  two-level factor on the full register.
- `ExactSynthesis.lean` now completes the corrected Section 8 assembly. Its
  component list is the conventional-order two-level factors followed by the
  diagonal residual; `orderedCircuitProduct` executes that list right-to-left,
  so evaluation is exactly `finiteFactorProduct factors * residual`. The
  successor-width headline constructs literal accepted syntax for every unitary,
  proves exact evaluator equality, and returns the exact finite cost consisting
  of all factor-circuit costs plus the diagonal schedule cost. It makes no
  asymptotic or optimality claim.
- `UniversalityExamples.lean` instantiates the direct width-one theorem, a
  nonadjacent width-two `|00>`/`|11>` affine two-level block (including basis
  action and exact accepted cost), and full width-two synthesis of trusted CNOT.
  The public root imports the exact synthesis and both boundary leaves.
- Final verification passed: strict and trust-zero compilation of the root,
  maintained axiom audit, and diagnostics; a focused 3,582-job build; two
  consecutive unchanged 3,580-job full builds; repository-wide forbidden-token,
  unclassified-universality, whitespace, and diff checks. The maintained audit
  now covers 285 declarations, including 32 Stage 11 exports, and every Stage 11
  result uses only `propext`, `Classical.choice`, and `Quot.sound`.
