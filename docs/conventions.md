# Mathematical and Circuit Conventions

This document fixes the conventions of the Lean library. Changes here are breaking
changes: every diagram theorem, phase statement, and resource theorem depends on
them.

## Source Authority and Translation

The supplied 31-page arXiv manuscript `Barenco/barenco-1995.pdf`
(`quant-ph/9503016v1`) is the primary source. `Barenco/barenco-1995.md` is a useful
structural index, and the PNG crops under `Barenco/images/` are visual aids. When a
sign, gate label, order, hypothesis, or count matters, it is checked against the PDF.

The paper is not treated as a formal specification. A paper matrix is translated to
the library convention before a diagram is encoded. Material differences are
recorded in `docs/corrections.md`, and coverage is recorded in
`docs/traceability.md`.

## States, Basis, and Matrix Entries

- The computational basis of an `n`-qubit register is `Fin n → Bool`.
- Wire `0` is the top wire in a paper diagram and the leftmost bit in a displayed
  ket `|x₀,…,xₙ₋₁⟩`.
- `false` is computational value `0`; `true` is value `1`.
- A semantic gate is a square complex matrix indexed by basis assignments.
- `basisKet x` is the amplitude function `Pi.single x 1`; matrix action on it is
  exactly the `x`-column (`mulVec_basisKet`). Matrix equality can therefore be
  proved by equality on every computational-basis ket.
- The public semantics uses standard column vectors. `U row col` is the amplitude
  of output basis state `row` from input basis state `col`; hence
  `U.mulVec ψ` represents applying `U` to state `ψ`.
- No theorem relies on Lean's arbitrary `Fintype` enumeration of function-valued
  bases. A later bridge to `Fin (2^n)` will use the explicit big-endian encoding
  `Σ i, bit(i)·2^(n-1-i)`, matching the paper's lexicographic order.

### The paper's opposite action convention

On manuscript p. 6 the paper defines

`|y⟩ ↦ u[y,0]|0⟩ + u[y,1]|1⟩`.

Thus its basis states behave as row vectors acted on from the right. Its diagram
proofs consequently multiply gates in chronological, left-to-right order. This is
not the column-vector meaning normally suggested by ket notation.

The library does **not** inherit that convention. If `P` is a paper matrix, its
standard-column semantic matrix is

`fromPaper(P) = Pᵀ`.

This works because `e_y P`, transposed, is `Pᵀ e_y`; transposition also converts a
paper chronological product `P₁ P₂ … Pₖ` into the standard semantic product
`Pₖᵀ … P₂ᵀ P₁ᵀ`. Mathlib proves that transpose preserves matrix unitarity via
`Matrix.transpose_mem_unitaryGroup_iff`.

Each paper-specific algebra module must say whether a displayed matrix name denotes
the source matrix or its translated semantic matrix. Core/public gates use semantic
matrices; paper-facing bridge theorems use `fromPaper` explicitly.

## Sequential Circuits and Execution Order

- Circuit syntax is chronological: the head/leftmost primitive executes first,
  matching the diagrams.
- Semantic matrix multiplication remains standard. Executing `g₁` and then `g₂`
  yields `eval [g₁,g₂] = eval g₂ * eval g₁`.
- Evaluation folds a chronological list by left-multiplication,
  starting at identity.
- Circuit append means chronological concatenation. Its evaluator theorem
  exposes the reversal: `eval (c₁ ++ c₂) = eval c₂ * eval c₁`.
- Adjoint/inverse circuits reverse the list and adjoint every primitive.

`Circuit.eval` proves these equations directly in the unitary group:
`eval_append`, `eval_adjoint`, and the cancellation theorems establish composition
and inverse behavior. `Barenco.SemanticsExamples` contains a noncommuting
two-primitive sanity theorem; comments or diagram order are not its evidence.

`Primitive` has a module-private raw constructor. Resource-relevant values are
created by trusted smart constructors (`Primitive.oneQubit`,
`Primitive.positiveControlled`, and `Primitive.cnot`) whose kind, exact support,
support cardinality, and certified denotation are fixed together. The only generic
wrapper is `Primitive.unclassified`: it receives kind `.other` and full-register
support, so later cost models must reject or explicitly price it. Toffoli and
arbitrary-two-qubit kinds deliberately have no smart constructor until their
certified semantics exists.

## Wires, Controls, Targets, and Embeddings

- Wire indices are `Fin n` and increase from top to bottom.
- Positive controls trigger when their bit is `true`. Negative controls, used in
  Section 8, trigger when their bit is `false`.
- A target must be distinct from every control. Repeated controls are forbidden.
  These facts are represented in data or hypotheses, never assumed by simplifier
  accidents.
- A one-qubit local gate acts on the selected target and preserves every other bit.
  Its matrix is characterized by computational-basis action.
- A multiply controlled local gate acts on the target exactly when every signed
  control predicate holds.
- Arbitrary-wire embeddings are semantic operations in their own right. A small
  matrix identity is not automatically an equality after embedding.
- Kronecker products may be used for contiguous constructions, but tensor
  associativity and wire reordering use explicit `Matrix.reindex` equivalences;
  they are not definitional equalities.

The implemented target split is
`splitTarget target : Basis n ≃ Bool × ComplementBasis target`. A
`ControlSet target` is a `Finset` of subtype indices carrying proofs that each
control differs from the target, so duplicate controls and control/target aliasing
are impossible. `localUnitary`, `controlledUnitary`, and
`positiveControlledUnitary` are certified constructors; their raw matrices have
entry and complete basis-column action theorems. `cnotUnitary control target h`
requires `h : control ≠ target`, and its truth-table theorem quantifies over every
basis assignment and register width.

## Unitary Gates

The initial raw matrix type is useful for algebra, while certified gates use
`Matrix.unitaryGroup (Fin n → Bool) ℂ`. The membership predicate is mathlib's
two-sided unitary condition; relevant entry points are:

- `Matrix.mem_unitaryGroup_iff` and `Matrix.mem_unitaryGroup_iff'`;
- `Matrix.UnitaryGroup.star_mul_self`, `.toLinearEquiv`, `.transpose`;
- `Matrix.kronecker_mem_unitary`;
- `Matrix.reindexRingEquiv` / `Matrix.reindexAlgEquiv` plus
  `Matrix.conjTranspose_reindex`.

Definitions should accept certified unitary gates when later conclusions need
unitarity. Pure matrix identities may remain generalized over weaker rings when that
improves reuse without obscuring the quantum statement.

## Section 4 One-Qubit Matrices, Euler Forms, and Roots

### Paper-row displays and semantic-column gates

`Barenco.OneQubit.Matrix` preserves the manuscript's displayed matrices under
paper-facing names: `paperRy`, `paperRz`, `paperPhase`, and `paperX`. In particular,

`paperRy θ = [[cos(θ/2), sin(θ/2)],[-sin(θ/2), cos(θ/2)]]`.

These are raw row-action displays, not the library's semantic gates.
`Barenco.OneQubit.Certified` defines the standard-column matrices explicitly by
translation:

- `ry θ = fromPaper (paperRy θ) = paperRy (-θ)`;
- `rz α = fromPaper (paperRz α) = paperRz α`;
- `phaseShift δ = fromPaper (paperPhase δ) = paperPhase δ`;
- `sigmaX = fromPaper paperX = paperX`.

Only `Ry` changes its displayed entries under transposition. `sigmaX` is also proved
equal, as a certified unitary, to the Boolean-permutation `pauliX`; their
`localUnitary` embeddings agree on every target. This bridge is still a semantic
matrix equality, not a `Primitive` or `Circuit` construction.

`QubitSpecialUnitary` abbreviates
`Matrix.specialUnitaryGroup Bool ℂ`. The Y and Z rotations are packaged both as
ordinary certified unitaries and as special unitaries. Scalar phase and Pauli-X are
packaged as unitaries; their determinants are respectively `cis (2 * δ)` and `-1`.

All six identities in Lemma 4.2 are proved both for the raw paper displays and for
the semantic matrices: addition of Y angles, addition of Z angles, addition of
scalar phases, `X²=I`, and the two X-conjugation laws. These are exact matrix
identities for every real parameter. They do not by themselves construct or count
a circuit.

For Lemma 4.3, the paper-facing definitions are

- `paperA α θ = paperRz α * paperRy (θ/2)`;
- `paperB α θ β = paperRy (-θ/2) * paperRz (-(α+β)/2)`;
- `paperC α β = paperRz ((β-α)/2)`.

Each factor has a special-unitary certificate. The parameterized raw theorems prove
`A B C = I` and `A X B X C = paperEuler α θ β`. Transposing gives the explicitly
reversed column products `Cᵀ Bᵀ Aᵀ = I` and
`Cᵀ Xᵀ Bᵀ Xᵀ Aᵀ = columnEuler α θ β`. After exact SU(2) Euler existence,
`specialUnitary_exists_paperABC` and
`specialUnitary_exists_columnChronologicalABC` quantify over certified SU(2)
witnesses. These remain matrix-only results. The separately proved
`controlledABCCircuit`, `eval_controlledABCCircuit_eq_iff`, and
`controlledABCCircuit_oneQubitCNOTCost` supply the circuit and resource layers of
Lemma 5.1; they are not consequences of the matrix identity alone.

### Exact SU(2) and U(2) Euler decompositions

The SU(2) proof first establishes the canonical entry form and then uses the total
`Complex.arg` function, so zero entries do not introduce an undefined phase.
`specialUnitary_exists_paperEuler` proves exact paper-row `Rz Ry Rz` existence with
the middle angle in `[0,π]`. `specialUnitary_exists_columnEuler` records the
transposed outer-factor order, while `specialUnitary_exists_rz_mul_ry_mul_rz`
renames the outer witnesses to expose the usual semantic product
`rz α * ry θ * rz β`.

For an arbitrary `QubitUnitary U`,
`determinantPhaseAngle U = Complex.arg (det U) / 2` selects the half-open principal
representative `(-π/2,π/2]`. Because a scalar two-by-two phase has determinant
`cis (2 * δ)`, this choice gives the determinant of `U` exactly. Removing the phase
produces `specialUnitaryPart U`, and `phaseShift_mul_specialUnitaryPart` reconstructs
`U` exactly. The choice is discontinuous across the principal-argument branch cut;
no continuity is claimed.

This determinant calculation repairs an imprecision in the paper: determinant one
does not force the scalar representative to be `1`; `-I` is also possible. The
formal SU(2) theorem absorbs that representative into a Z angle, and
`paperPhase_pi_mul_paperRz` records the corresponding `2π` shift. The exported U(2)
theorems are `unitary_exists_paperPhase_mul_paperEuler` and
`unitary_exists_phaseShift_mul_rz_mul_ry_mul_rz`, both exact and both retaining a
middle angle in `[0,π]`.

### Exact finite-index unitary roots and their boundary

For every finite index type `ι`, positive natural `k`, and
`U : Matrix.unitaryGroup ι ℂ`, `unitaryRoot k U` is a certified exact root and
`unitaryRoot_pow` proves `(unitaryRoot k U)^k = U`. The public API also includes
`exists_unitary_pow_eq`, `unitarySquareRoot`, and the power-of-two specialization
`unitaryRoot_pow_two_pow`. The implementation applies principal-argument scalar
roots to the finite spectrum using continuous functional calculus. Correctness is
asserted only for `0 < k`; the total definition at `k=0` is not a zeroth-root theorem.

The selected scalar branch is noncanonical and is not globally continuous as the
matrix varies. More importantly for Lemma 7.8, the current API proves each
power-of-two root equation independently but does not yet prove a coherent sequence
`V_{m+1}² = V_m`, nor the operator-distance estimate
`operatorDistance V_m I ≤ π / 2^m`. Those theorems must use the already fixed L²
operator norm and a shared eigenphase choice. Section 6 now embeds the selected
square root into the exact Lemma 6.1 circuit and its explicit sixteen-primitive
expansion. The later coherent-root circuits of Lemmas 7.5 and 7.8 and their
syntax-based counts remain separate circuit/resource obligations.

## Section 5 Controlled-Gate Conventions

`Barenco.ControlledCircuit.targetBlockRaw` exposes the existing arbitrary-target
semantics as a reindexed block-diagonal matrix. Multiplication is pointwise on
target blocks, and `targetBlockRaw_injective` lets a full-register equality be
proved or recovered from all complementary-wire assignments. This is proof-side
infrastructure, not a circuit representation or a resource counter.

The four Section 5 diagrams are represented by chronological lists whose first
element executes first:

- Lemma 5.1: `A; CNOT; B; CNOT; C`, with column-semantic branches
  `C * B * A` and `C * X * B * X * A`;
- Lemma 5.2: the single control-wire gate
  `E(delta) = Rz(-delta) * Ph(delta/2) = diag(1,cis delta)`;
- Lemma 5.4: `A; CNOT; B; CNOT`, with branches `B * A` and
  `X * B * X * A`;
- Lemma 5.5: `A; CNOT; B`, with branches `B * A` and `B * X * A`.

All evaluator theorems quantify an arbitrary ambient width and distinct named
control and target wires. Thus their equality is equality of the complete register
unitaries, including every other wire; no two-qubit coordinate check is promoted to
a larger-register theorem. There are no auxiliary wires in these constructions.

Controlling the scalar matrix `Ph(delta)` does not produce an ignorable global
phase. It produces a relative phase between the two control branches and is exactly
equal to applying `E(delta)` on the control wire. Corollary 5.3 uses the exact
determinant-phase split from Section 4 and has a constructed syntax cost of four
one-qubit gates plus two CNOTs under `CostModel.oneQubitCNOT`.

For Lemmas 5.4 and 5.5, define
`symmetricEuler alpha theta = rz alpha * ry theta * rz alpha`. In standard-column
orientation the two-CNOT family is `symmetricEuler alpha theta`, while the
one-CNOT family is `sigmaX * symmetricEuler alpha theta`. The latter is equivalent
to the paper's displayed row-action family after transposition and renaming the
unrestricted parameters. The classification chooses `theta` with `Real.arcsin`
and the phase with total `Complex.arg`; zero off-diagonal entries require no
division or nonzero assumption. Lemma 5.5's arbitrary U(2) witnesses are normalized
to `specialUnitaryPart` only after the inactive branch proves `B = A⁻¹`; the
opposite scalar phases then cancel exactly around Pauli-X.

The paper's one-sentence proof of Lemma 5.5 starts with the Lemma 5.4 construction,
appends an XOR, and cancels the adjacent XOR pair. That proves sufficiency only as
written. The formal converse instead starts from an arbitrary one-CNOT circuit,
extracts `B * A = I`, and performs the U(2)-to-SU(2) normalization just described.

The blanket source remark that `Rx(theta)` is not in the Lemma 5.4 family has scalar
exceptions. If `sin(theta/2) = 0`, equivalently `theta = 2*pi*k` for an integer `k`,
then `Rx(theta) = (-1)^k I`; both `I` and `-I` occur in `symmetricEuler alpha 0`.
When `sin(theta/2) ≠ 0`, the imaginary off-diagonal entries of `Rx(theta)` rule out
membership in the real-off-diagonal symmetric-Euler family.

Corollary 5.6 has three deliberately separate syntax/resource layers:

- the unexpanded macro circuit has six nodes—four `.oneQubit` and two
  `.controlledOneQubit 1` occurrences—and `CostModel.oneQubitCNOT` returns `none`;
- expanding both controlled-`V` macros as `D; CNOT; F` gives ten primitives—eight
  one-qubit and two CNOT occurrences—with cost `some 10`;
- under `D * F = I`, the three proved adjacent local merges give evaluator equality
  with the existing six-primitive `controlledU2Circuit`; that distinct syntax has
  four one-qubit and two CNOT occurrences and cost `some 6`.

The expansion/macro evaluator equality additionally assumes `D * F = I` and
`V = F * X * D`; the expanded/merged equality needs `D * F = I`. Semantic equality
never serves as the count proof: the ten-node and six-node lists remain distinct,
and every count and cost is evaluated on its own syntax.

The unnumbered controlled-Z diagram is exact wire-swap symmetry, not merely a
graphical convention or phase equivalence. `controlledZUnitary_swap` proves it for
arbitrary ambient width; the shared matrix contributes `-1` exactly when both named
wires are true.

## Section 6 Three-Bit Conventions

All three Section 6 diagrams are stored as chronological lists: the first list
element executes first, while the corresponding standard-column matrix product is
written in reverse order. The Lemma 6.1 macro is

`controlled-V(second,target); CNOT(first,second);`
`controlled-V†(second,target); CNOT(first,second); controlled-V(first,target)`.

`doubleControlledViaSquareCircuit` quantifies an arbitrary ambient width and three
pairwise distinct named wires. `eval_doubleControlledViaSquareCircuit_pow_two`
proves that its complete-register evaluator is the doubly controlled `V^2`; the
two CNOTs therefore restore the second control and every spectator wire is fixed.
`eval_doubleControlledRootCircuit` selects the certified `unitarySquareRoot U` and
obtains exact doubly controlled `U`. The five syntax nodes are three
controlled-one-qubit macros and two CNOTs, so their structural gate count is five
but `CostModel.oneQubitCNOT` returns `none` before expansion.

Corollary 6.2 uses one coordinated Section 5 factorization `S`, not three
independent existential choices. Its twenty-node expansion is
`S(second); K; S(second)†; K; S(first)`, with `K = CNOT(first,second)`; it contains
twelve one-qubit gates and eight CNOTs and has cost `some 20`. The source's two
“adjacent” inverse pairs are separated in chronological syntax by operations on
the control wires. `eval_doubleControlledExpansion20Circuit_eq_16` explicitly
commutes those target-local factors across the disjoint-wire operations before
cancelling them. The resulting `doubleControlledExpansion16Circuit` has exactly
eight one-qubit gates and eight CNOTs, cost `some 16`, and the same full-register
evaluator. `doubleControlledUnitary_has_sixteenPrimitiveCircuit` packages this as
an exact existence-and-resource theorem for every one-qubit unitary `U`.

The two Section 6.2 source circuits are also chronological:

- `A; CNOT(second,target); A; CNOT(first,target); A†;`
  `CNOT(second,target); A†`, with `A = ry (pi/4)`;
- `B; CZ(second,target); B†; CZ(first,target); B; CZ(second,target); B†`,
  with `B = ry (3*pi/4)`.

Both evaluate exactly to `relativeToffoliUnitary`, whose target blocks for control
bits `00`, `01`, `10`, and `11` are respectively `I`, `I`, `Z`, and `X`.
`eval_relativePhaseToffoliACircuit_eq_BCircuit` therefore proves exact equality of
the two diagrams, stronger than phase-relaxed equality. Their Toffoli permutation
has a negative input-column phase exactly on `101`. The separately discussed
doubly controlled paper matrix `W`, translated to `wMatrix = ry pi`, instead has
its negative Toffoli-relative phase exactly on `111`. These are distinct exact
operators and neither relation is promoted to global-phase or all-measurement
equality.

The A circuit is an explicit seven-basic-gate syntax: four one-qubit gates and
three CNOTs, with `oneQubitCNOT` cost `some 7`. The B source syntax has four
one-qubit gates and three controlled-Z macros. Its structural node count is also
seven, but its `oneQubitCNOT` cost is `none`; exact semantic equality with the A
circuit does not transfer the A circuit's resource count to that different syntax.

`relativeToffoliUnitary_sq` proves the common signed permutation is an involution,
and the two `eval_append_relativePhaseToffoli*Circuit_self` theorems consequently
cancel two immediately adjacent identical copies. This does not prove the stronger
Section 7 claim that relative-phase gates separated by other operations cancel
merely because they occur in pairs; that use still requires an ordered basis-path
phase calculation.

## Semantic Relations

The implemented relations are deliberately noninterchangeable:

1. **Exact circuit equality:** `ExactCircuitEq c d` means equality of the certified
   evaluator outputs.
2. **Global phase:** `GlobalPhaseEq U V` is oriented as
   `V = (phase : ℂ) • U` for one `phase : Circle`, independent of the input.
3. **Input-basis-dependent phase:** `BasisPhaseEq U V` means
   `V row input = (phase input : ℂ) * U row input`. Thus each input column may
   receive its own unit scalar. Common postcomposition, represented by multiplying
   both matrices on the left, preserves this relation. Arbitrary precomposition on
   the right mixes columns and is intentionally not exposed as a congruence law.
4. **Reversible basis behavior:** `SameBasisBehavior` records the same phased
   basis-to-basis transitions. For non-monomial matrices it is intentionally a
   coarse classical relation, not equality of quantum action.
5. **Computational-basis measurement behavior:** `BasisMeasurementEq U V` compares
   `Complex.normSq (U output input)` entrywise. `BasisPhaseEq` implies this.
6. **Channel/all-effect behavior:** `ChannelEq U V` compares
   `U * input * Uᴴ` and `V * input * Vᴴ` for every square complex matrix `input`.
   `AllMeasurementEq` compares
   `BornWeight effect state = trace (effect * state)` for every input matrix and
   every effect matrix. Matrix-unit effects prove these two relations equivalent.
   A global phase implies them, and channel equality implies
   `BasisMeasurementEq`; basis-dependent phase generally does not imply channel
   equality.

The conjugation and Born-weight definitions are algebraic on arbitrary matrices.
They do **not** yet define physical density matrices, positive effects, trace-one
normalization, real-valued probabilities, or the interval bounds `0 ≤ p ≤ 1`.
Those restrictions require separate structures and theorems. Quantifying over all
matrices/effects is intentionally stronger and makes the trace pairing separating.

Section 6's `≅` diagrams establish the explicit basis-dependent `101` sign described
above, not a global phase. The resulting `BasisPhaseEq`, `SameBasisBehavior`, and
`BasisMeasurementEq` theorems are proved; no channel/all-measurement equivalence is
claimed.

## Approximation and Probability

- `operatorDistance A B = ‖A - B‖` uses mathlib's scoped L² induced operator norm
  (spectral/operator norm), not a Frobenius, entrywise, or unspecified matrix norm.
- `Barenco.Equivalence.OperatorNorm` alone opens
  `Matrix.Norms.L2Operator`; the norm instance is not opened in the algebraic phase,
  measurement, circuit, or cost modules.
- The compiled API proves nonnegativity, separation, symmetry, the triangle
  inequality, left/right multiplication bounds, invariance under certified unitary
  multiplication, additive error for a product of two unitary factors, the
  Euclidean state-action bound, a per-coordinate amplitude bound, and distance at
  most two between certified unitaries on a nonempty finite index type.
- `Matrix.l2_opNorm_mul`, `.l2_opNorm_mulVec`, `Matrix.toEuclideanCLM`, and C*-unitary
  norm facts are the exact mathlib bridge used by those proofs.
- `operatorDistance_basisOutcomeProbability_le` proves the paper's `2ε` constant
  for one computational-basis outcome: for certified unitaries and a state with
  Euclidean norm at most one, the absolute difference of the two squared output
  amplitudes is at most twice the operator distance. This is not silently promoted
  to a bound for a multi-outcome event, coarse-graining, or arbitrary POVM effect;
  those require a separately stated physical measurement theorem.

Exact and approximate synthesis have different theorem names and result types.
Bounds in two variables (`n` and `ε`) state their domains, integer recursion depth,
and whether they are uniform, worst-case, or for a particular construction.

## Auxiliary Wires

- A **clean ancilla** starts in a named basis state (usually zero). A theorem over a
  clean ancilla is equality on the corresponding input subspace, not equality of
  full-register unitaries.
- A **dirty** or **borrowed ancilla** may start in an arbitrary state and may be
  entangled with the data. Correct borrowing requires full semantic equality that
  restores the wire and all correlations.
- Restoration includes absence of residual entanglement, not only equality of a
  classical output bit.
- Width is the total number of wires. Ancilla count and initialization assumptions
  are separate resource fields.

Lemmas 7.2–7.3 are expected to use dirty borrowed wires. Lemma 7.11 uses one clean
zero ancilla and must be stated as a subspace/input-contract theorem.

## Circuit Syntax and Cost Models

Resource claims are computed from syntax before semantic evaluation erases the
construction.

Named cost models:

- **`CostModel.oneQubitCNOT` (Sections 3–7):** kinds `.oneQubit` and `.cnot`
  cost one. Controlled one-qubit, Toffoli, arbitrary-two-qubit, and `.other` kinds
  are unsupported rather than silently treated as free.
- **`CostModel.arbitraryTwoQubit` (Section 8):** `.oneQubit`, `.cnot`, and the
  certified `.arbitraryTwoQubit` kind cost one. Controlled-one-qubit, Toffoli, and
  `.other` kinds remain unsupported. This deliberately changes the earlier ground
  rules; no arbitrary-two-qubit smart constructor or paper decomposition theorem is
  thereby supplied.
- Additional diagnostic models may count one-qubit, CNOT, controlled-one-qubit,
  Toffoli, arbitrary two-qubit gates, swaps, or negative-control conjugations in
  separate coordinates.

`Circuit.registerWidth`, `gateCount`, `kindCount`, and `touchedSupport` inspect
typed syntax only; `touchedSupport_card_le_registerWidth` proves the named support
fits inside the ambient width.
`Circuit.cost` returns `Option ℕ`: one unsupported occurrence makes the complete
cost `none`. Append and adjoint theorems prove the structural count/cost laws, and
`Primitive.namedModels_reject_unclassified_of_mem` proves that both named models
reject any circuit containing `.unclassified`. Semantic matrix equality is never
used to infer a resource count.

Counts distinguish exact equality from phase-relaxed targets, allow gate merging
only through an explicit syntactic optimization theorem, and label exact count,
constructed upper bound, optimal lower bound, and asymptotic statement separately.
The word `Θ` is not exported for an optimal synthesis problem unless both bounds are
proved for the same cost model and target relation.

## API Evidence and Representation Decision

The following APIs were checked against the pinned mathlib 4.31.0 source and/or a
compiling smoke module:

- `Matrix`, `Matrix.ext`, `Matrix.mul_apply`, `Matrix.mulVec_mulVec`;
- `Matrix.unitaryGroup` and the membership/transpose APIs listed above;
- `Matrix.kronecker`, `Matrix.mul_kronecker_mul`,
  `Matrix.kronecker_mem_unitary`;
- `Matrix.reindex`, `Matrix.reindexAlgEquiv`, `Equiv.Perm.permMatrix`;
- `Equiv.piSplitAt` for arbitrary-target wire splitting and reconstruction;
- `Circle`, `Complex.normSq_mul`, `Matrix.trace`, and
  `Matrix.trace_single_mul` for phase and measurement algebra;
- `BitVec` XOR/get/equivalence APIs for later Gray-code support;
- `Matrix.toEuclideanCLM`, `Matrix.l2_opNorm_mulVec`, and
  `Matrix.l2_opNorm_mul` under the scoped L² norm;
- `CStarMatrix`, finite matrix spectra, and continuous functional calculus on a
  finite spectrum for the exact `unitaryRoot` construction.

Mathlib 4.31.0 contains no quantum-circuit or Gray-code framework and no ready
unitary Givens decomposition. Exact finite-matrix roots are now supplied by
`Barenco.OneQubit.Roots` through a proved finite-spectrum functional-calculus
construction, so root existence is no longer an outstanding stage. Coherent
recursive roots with norm decay, circuit synthesis, Gray-code infrastructure, and
Givens-style general-unitary elimination remain explicit project stages.

The selected core basis is `Fin n → Bool`, rather than `Fin (2^n)` or `BitVec n`:
it makes arbitrary controls, wire updates, and untouched-wire proofs direct.
`BitVec n` will be bridged in for Gray codes; `Fin (2^n)` will be bridged only for
lexicographic matrices and finite-dimensional decomposition APIs. This avoids bit
arithmetic in the foundational gate semantics while retaining later synthesis tools.
