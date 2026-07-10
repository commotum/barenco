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
- Evaluation will therefore fold a chronological list by left-multiplication,
  starting at identity.
- Circuit append means chronological concatenation. Its evaluator theorem will
  expose the reversal: `eval (c₁ ++ c₂) = eval c₂ * eval c₁`.
- Adjoint/inverse circuits reverse the list and adjoint every primitive.

The first semantics module must prove these equations and include a noncommuting
two-gate sanity example. Comments or diagram order alone are not verification.

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

## Semantic Relations

The library will keep at least these relations separate:

1. **Exact equality:** equal linear operators/matrices.
2. **Global phase:** `A = z • B` for one `z : Circle`, independent of input.
3. **Basis-dependent phase:** each computational-basis column differs by its own
   unit scalar; the phase may depend on the basis state.
4. **Reversible basis behavior:** the same permutation of computational basis
   labels, ignoring phases.
5. **Computational-basis measurement behavior:** the same probability distribution
   after computational-basis inputs/measurements.
6. **All-measurement behavior:** operational equivalence for arbitrary states and
   measurements; global phase implies this, basis-dependent phase generally does
   not.

Section 6's `≅` diagrams establish basis-dependent signs, not global phase. A later
use may be exact only after an explicit cancellation theorem.

## Approximation and Probability

- Matrix approximation uses the L² induced operator norm (spectral/operator norm),
  not a Frobenius, entrywise, or unspecified matrix norm.
- Approximation modules enable mathlib's scoped instance with
  `open scoped Matrix.Norms.L2Operator` and use `Matrix.toEuclideanCLM` as the bridge
  to continuous linear maps.
- `Matrix.l2_opNorm_mul`, `.l2_opNorm_mulVec`, and unitary norm facts support error
  propagation. Scoped norm instances stay out of unrelated algebra modules to avoid
  ambiguous norm inference.
- The paper's claim that operator error `≤ ε` gives event-probability error `≤ 2ε`
  will be proved from normalized states and orthogonal projections/events. The
  constant and hypotheses are not assumed merely because the source states them.

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

- **`OneQubitCNOT` (Sections 3–7):** an arbitrary one-qubit unitary costs one and a
  CNOT costs one. Controlled arbitrary gates are composite unless a theorem
  explicitly studies a different intermediate alphabet.
- **`ArbitraryTwoQubit` (Section 8):** any gate supported on at most two wires costs
  one. This deliberately changes the paper's earlier ground rules.
- Additional diagnostic models may count one-qubit, CNOT, controlled-one-qubit,
  Toffoli, arbitrary two-qubit gates, swaps, or negative-control conjugations in
  separate coordinates.

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
- `Equiv.piEquivPiSubtypeProd` and `Function.update` for wire splitting/action;
- `BitVec` XOR/get/equivalence APIs for later Gray-code support;
- `Matrix.toEuclideanCLM`, `Matrix.l2_opNorm_mulVec`, and
  `Matrix.l2_opNorm_mul` under the scoped L² norm.

Mathlib 4.31.0 contains no quantum-circuit or Gray-code framework, no directly
usable general-unitary spectral theorem/root constructor, and no ready unitary
Givens decomposition. Those remain explicit project stages.

The selected core basis is `Fin n → Bool`, rather than `Fin (2^n)` or `BitVec n`:
it makes arbitrary controls, wire updates, and untouched-wire proofs direct.
`BitVec n` will be bridged in for Gray codes; `Fin (2^n)` will be bridged only for
lexicographic matrices and finite-dimensional decomposition APIs. This avoids bit
arithmetic in the foundational gate semantics while retaining later synthesis tools.

