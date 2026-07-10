# Barenco Lean

This repository is a reusable Lean 4 formalization inspired by Barenco et al.,
*Elementary Gates for Quantum Computation* (1995). It provides exact semantics
for finite qubit registers, circuit syntax and resource accounting, controlled
and multiply controlled constructions, phase-sensitive equivalences,
approximation bounds, lower-bound infrastructure, and an exact positive-width
one-qubit/CNOT synthesis pipeline.

The staged formalization is complete for its declared scope. It is not a
line-by-line certification of every claim in the paper: unsupported or false
claims are corrected, scoped, or explicitly excluded in the project
documentation. The stable public surface is exported by `import Barenco`;
diagnostic example files remain outside that root import.

## Toolchain and build

- Lean: `v4.31.0`
- mathlib: `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`

Build the maintained library with:

```sh
lake build
```

## Quick start: exact positive-width synthesis

For `controlCount = k`, the synthesis API acts on a register of width `k + 1`.
It constructs literal syntax accepted by `CostModel.oneQubitCNOT`, proves exact
evaluation—including diagonal and global phases—and bounds the cost of the
selected non-pruning schedule.

```lean
import Barenco

open Barenco
open Barenco.Universality

noncomputable section

variable (k : ℕ) (U : UnitaryGate (k + 1))

example :
    Circuit.eval (exactSynthesisCircuit k U) = U :=
  eval_exactSynthesisCircuit k U

example :
    Circuit.cost CostModel.oneQubitCNOT (exactSynthesisCircuit k U) =
      some (exactSynthesisCost k U) :=
  exactSynthesisCircuit_oneQubitCNOTCost k U

example :
    2 * exactSynthesisBenchmark k ≤ exactSynthesisCost k U ∧
      exactSynthesisCost k U ≤ 112 * exactSynthesisBenchmark k :=
  exactSynthesisCost_bounds k U
```

Here
`exactSynthesisBenchmark k = (k + 1)^2 * 4^k`. The sandwich is an exact finite
bound for this particular generated circuit family. It is not an optimality
claim or a lower bound on arbitrary implementations of `U`.

## Module map

| Area | Main modules | Purpose |
|---|---|---|
| Core semantics | `Barenco.Basic`, `Barenco.Semantics`, `Barenco.Controlled` | Basis states, matrices, local embeddings, controlled operations, and full-register action |
| Ordered two-wire gates | `Barenco.TwoWire.*` | Certified ordered `U(4)` embeddings, spectator/orientation laws, and trusted arbitrary-two-qubit syntax |
| Circuit syntax and costs | `Barenco.Circuit`, `Barenco.Cost` | Chronological syntax, evaluation, gate counts, and named partial cost models |
| Exact normalization | `Barenco.Optimization.*` | Payload-preserving fusion syntax, exact lowering, executable model-specific passes, barriers, and syntax-derived cost behavior |
| One-qubit algebra | `Barenco.OneQubit.*` | Certified rotations, Euler decompositions, determinant phases, roots, and selected factors |
| Controlled circuits | `Barenco.ControlledCircuit.*` | Target-block reasoning and exact Section 5 circuit decompositions |
| Three and many qubits | `Barenco.ThreeQubit.*`, `Barenco.MultiControl.*` | Controlled-controlled gates, relative phases, recursive constructions, ancillas, approximation, and resources |
| Equivalence and error | `Barenco.Equivalence.*` | Exact/global/basis-phase relations, measurement consequences, and operator-distance bounds |
| Lower bounds | `Barenco.LowerBounds.*` | Restricted basic syntax, interaction graphs, tensor-factor obstructions, and CNOT lower bounds |
| Exact universality | `Barenco.Universality.*` | Givens elimination, two-level and diagonal circuits, positive-width exact synthesis, and implementation costs |
| Trust audit | `Barenco.AxiomAudit` | Maintained `#print axioms` checks for exported headline results |

## Critical conventions

- `Basis n` is `Fin n → Bool`. Wires are named by `Fin n`; the core semantics do
  not silently identify bit strings with a particular little- or big-endian
  natural-number encoding.
- A `Circuit n` is chronological: its head executes first. With column vectors,
  later gates multiply on the left, so `[A, B]` evaluates as `B * A`.
- Exact matrix equality, `GlobalPhaseEq`, and input-column `BasisPhaseEq` are
  distinct. The library also keeps classical basis behavior, computational-basis
  transition probabilities, and channel/all-effect behavior separate rather than
  treating every phase as global.
- `operatorDistance A B` uses mathlib's induced L2 operator norm (the spectral
  norm), not a Frobenius or entrywise norm.
- Resource theorems come from literal syntax. `CostModel.oneQubitCNOT` accepts
  only arbitrary one-qubit gates and CNOTs. `CostModel.arbitraryTwoQubit` also
  accepts certified arbitrary two-qubit gates and controlled one-qubit nodes
  with at most one control. Unsupported primitives make `Circuit.cost` return
  `none`; semantic equality alone never supplies a gate count.

## Documentation

- [Mathematical and implementation conventions](docs/conventions.md)
- [Paper-to-Lean traceability matrix](docs/traceability.md)
- [Corrections and clarifications](docs/corrections.md)
- [Axiom audit and build ledger](docs/axiom-audit.md)
- [Final formalization report](docs/final-report.md)

## Deliberate exclusions and boundaries

- Exact one-qubit/CNOT universality is proved for every positive width. At width
  zero, the restricted one-qubit/CNOT `BasicCircuit` syntax can express only the
  empty circuit, while the semantic unitary group is `U(1)`; exact width-zero
  universality is therefore false. General `Circuit 0` still permits conservative
  unclassified semantic nodes, which the named cost models reject.
- The paper's merged relative-phase Toffoli claim is reconstructed as the distinct
  named `relativePhaseToffoliThreeGateCircuit`: it contains three certified `U(4)`
  nodes, is exactly equal to the seven-node A evaluator on the full ambient
  register, and has Section 8 cost `some 3`. Relative to exact Toffoli, the strongest
  exported relation is the explicit `101` input-column `BasisPhaseEq`, with only
  classical-basis and computational-basis measurement consequences. This is a
  constructive upper count; no exact-Toffoli, `GlobalPhaseEq`, arbitrary-input
  measurement-equivalence, or minimality theorem is claimed. The original A and B
  lists remain seven-node syntax, and the three generic `U(4)` nodes are unsupported
  by `CostModel.oneQubitCNOT`.
- The claimed six-`U(4)` synthesis and the heuristic dimension-counting lower
  bound are not established as theorems.
- No dense-generation theorem for a fixed finite gate set is claimed. Arbitrary
  one-qubit unitaries are primitives in the exact universality result.
- The proved `Theta((k + 1)^2 * 4^k)` statement describes the selected fixed,
  non-pruning synthesis schedule; it is not a circuit-complexity lower bound or
  an optimality result.
