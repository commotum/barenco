# 11-UNIVERSALITY

Status: in progress (source and pinned-API audit; no Stage 11 Lean implementation
has begun).

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
  support simultaneous reindexing, and `basisIndex` supplies the already-fixed
  big-endian equivalence with `Fin (2^n)`. Algebraic elimination should remain
  reusable over a general finite index or `Fin d`, with an explicit reindex bridge
  to qubit bases.
- The project already has chronological `Circuit.append`/`Circuit.eval`, certified
  arbitrary one-qubit primitives, CNOT primitives, circuit adjoints, finite-mask
  Gray-code facts, and exact positive multi-control constructions. Whether the
  most reusable Section 8 path should reuse the reflected Gray enumeration or a
  direct Hamming path remains under audit.
- The pinned mathlib version has no previously identified ready-made unitary
  Givens decomposition. Available finite-unitary, reindexing, finite-product, and
  orthogonality APIs are being checked before selecting a custom elimination
  invariant.
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
  `m=2` and one fully controlled gate, so the displayed construction supports a
  uniform `O(n^3)` upper bound, not a per-instance lower bound. Stage 12 must not
  promote this into `Theta` without an aggregate matching theorem.

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
and CNOT for every finite-qubit unitary. Supply a reusable finite-dimensional
two-level decomposition independently of the qubit specialization, then connect
each two-level factor to a fully explicit Gray-path circuit.

## Detailed Implementation Plan

1. Finish the source and pinned-API audit. Fix the algebraic index type,
   multiplication order, two-level block orientation, diagonal treatment, direct
   path convention, and the precise boundary APIs before writing proofs.
2. Add a low-dependency algebraic two-level module: define the embedded `U(2)`
   block on two distinct finite indices, certify unitarity, prove entries/basis
   action, inverse and multiplication facts actually needed by elimination.
3. Prove a constructive finite-unitary elimination/decomposition theorem. Keep
   the chronological factor list explicit, include the residual diagonal phases,
   and prove the product equation with all zero/singleton boundary cases.
4. Add qubit-path infrastructure: construct a duplicate-free Hamming/Gray path
   between distinct basis assignments, prove adjacent states differ at one named
   wire, and specify the exact fixed values required of every other wire.
5. Define pattern-controlled one-qubit circuits via local-X conjugation of the
   existing positive-control implementation. Prove exact full-register semantics,
   negative-control restoration, and primitive expansion to one-qubit/CNOT syntax.
6. Construct a two-level circuit by moving one endpoint along the path, applying
   the desired block on the final adjacent pair, and reversing the moves. Prove
   evaluator equality on all computational basis states and then as matrices.
7. Map every algebraic factor to its circuit and concatenate chronologically with
   the order required by `Circuit.eval_append`. Prove exact universality for
   positive register width, the direct one-qubit specialization, and the exact
   zero-wire identity-only obstruction.
8. Add root-excluded examples in dimensions one, two, and four, public imports,
   traceability/correction/convention updates, maintained axiom checks, and focused
   plus full verification. Leave structural/asymptotic aggregation to Stage 12.

## Build Structure

- Planned algebraic layer: `Barenco/Synthesis/TwoLevel.lean` and one or more narrow
  elimination leaves. These are public algebraic APIs and must not import circuit
  syntax.
- Planned circuit layer: narrow pattern-control and basis-path modules importing
  only the semantic/circuit and established multi-control leaves they use.
- Planned assembly layer: a universality leaf importing both algebraic and circuit
  synthesis. `Barenco.lean` changes only after stable theorem signatures compile.
- Planned diagnostic leaf: `Barenco/Synthesis/UniversalityExamples.lean`, excluded
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

- [ ] A reusable finite-dimensional theorem decomposes every certified complex
  unitary into explicit two-level and/or diagonal certified factors with a proved
  ordered product equation.
- [ ] Every algebraic two-level factor on a qubit basis has an exact no-ancilla
  circuit implementation on the full register.
- [ ] Pattern controls, Gray/Hamming path movement, endpoint rotation, reverse
  restoration, and untouched off-path states are all machine checked.
- [ ] The headline theorem returns a circuit containing only arbitrary one-qubit
  and CNOT primitives and proves exact evaluator equality for every positive `n`,
  with a direct width-one case and a separate exact width-zero obstruction theorem.
- [ ] Exact generation is not conflated with approximation, fixed-set dense
  generation, arbitrary-two-qubit pricing, or an efficiency theorem.
- [ ] Representative low-dimensional examples, public imports, maintained axiom
  entries, forbidden-token/diff checks, strict/trust-zero compilation, focused
  builds, and two full builds pass and are recorded.
- [ ] Traceability, corrections, and conventions document every material repair
  to Section 8's decomposition, Gray path, diagonal, ordering, and boundary claims.

## Stage Results

- Stage file created before Lean implementation. The initial audit isolates two
  independent obligations: finite-dimensional two-level elimination and exact
  qubit-circuit realization. It rejects the paper's dimension-count argument and
  six-`U(4)` surjectivity claim as prerequisites, and makes diagonal/global phases,
  negative controls, chronology, no-ancilla scope, and width-zero/one behavior
  explicit.
