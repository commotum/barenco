# 2-SEMANTICS

Status: in progress.

## Current Facts

- `Barenco.Basic` defines `Basis n := Fin n → Bool`, complex semantic matrices,
  certified `Matrix.unitaryGroup` gates, big-endian `basisIndex`, the source
  transpose bridge, and chronological raw-gate evaluation.
- `Barenco.ApiSmoke` verifies the exact pinned APIs for Kronecker unitarity,
  reindexing, permutation matrices, selected-wire splits, and the L² operator norm.
- The public semantics is standard column action. The source's row-action matrix
  `P` is represented as `Pᵀ`; chronological gates `g₁,g₂` evaluate as `g₂*g₁`.
- Mathlib has no quantum circuit syntax. Resource-countable syntax must be local.

## Updated Assumptions

- Direct basis-index matrices remain the public semantic target.
- A target split `Basis n ≃ Bool × ({i // i ≠ target} → Bool)` allows local and
  controlled gates to be built as reindexed block-diagonal matrices. This should
  make unitarity compositional while retaining transparent basis-entry theorems.
- Arbitrary basis/wire reindexing should be a certified unitary constructor, with
  orientation proved once and reused.
- Circuit primitives should carry both a certified unitary denotation and stable
  structural metadata; evaluator correctness and inverse remain independent of
  later cost weights.
- Dirty-wire correctness cannot be modeled merely by checking classical outputs;
  later constructions will use full matrix equality over this semantic core.

## Big Picture Objective

Implement a small reusable semantic and syntactic core for finite qubit registers,
arbitrary-wire one-qubit gates, positive multi-controls, and chronological circuits.

## Detailed Implementation Plan

- Refine basis/state definitions with computational-basis kets, column-action
  theorems, and explicit equivalence/reindex helpers.
- Prove reindexing, block diagonalization, and Kronecker constructions preserve
  matrix unitarity.
- Define one-qubit local gates on arbitrary targets and multiply controlled gates
  through target/complement block structure; prove entries, basis action, controls,
  untouched wires, and unitarity.
- Define X and CNOT with explicit distinct control/target evidence and prove their
  truth-table action on all computational basis states.
- Define syntactic primitives/circuits with chronological evaluator, append,
  identity, inverse/adjoint, evaluator unitarity, and stable kind/support metadata.
- Add boundary checks for zero/one qubit registers, empty controls, non-adjacent
  wires, and the paper's two-qubit order.
- Update conventions, traceability, corrections, and axiom audit with compiled Lean
  names and any revised representation decisions.

Expected files include `Barenco/Semantics.lean`, `Barenco/Controlled.lean`,
`Barenco/Circuit.lean`, root imports, this stage file, and documentation updates.

## Build Structure

- `Barenco.Basic` is the high-fanout core and owns only basis/state/matrix aliases,
  the source transpose bridge, and cheap chronology/cardinality facts. Further
  experimental semantics should not accumulate there.
- `Barenco.Semantics` is a generic proof leaf for basis kets and certified reindex,
  block-diagonal, and Kronecker constructors.
- `Barenco.Controlled` imports `Semantics` and owns target/complement splits plus
  local/controlled/X/CNOT constructors and their domain-specific proofs.
- `Barenco.Circuit` owns syntax/evaluation/adjoint and structural metadata without
  importing paper-specific theorem leaves.
- `Barenco.SemanticsExamples` is diagnostic/audit-only and contains boundary and
  low-dimensional checks, not public runtime definitions.
- `Barenco.lean` is the thin public re-export surface; internal leaves import their
  narrow dependencies, never the root module.
- Runtime/public API: `Basic`, `Semantics`, `Controlled`, `Circuit`. Proof-side:
  their theorem sections. Diagnostic: `ApiSmoke`, `AxiomAudit`, and
  `SemanticsExamples`. No fallback or temporary public declarations are planned.
- Focused builds: `lake build Barenco.Semantics`, `Barenco.Controlled`, and
  `Barenco.Circuit`. Adjacent consumers: `Barenco.SemanticsExamples` and root
  `Barenco`. Full builds are required here because the root/high-fanout core and
  public imports change and the stage completion criteria demand two full checks.

## Boundary Checks

- Runtime definitions stay in narrow foundational modules; exhaustive examples and
  negative probes stay in `SemanticsExamples`/audit modules.
- Public syntax metadata must either be correct by construction or accompanied by
  a checked well-formedness predicate before any resource theorem consumes it.

## No-Cheating Checks

- Unitarity is proved from exact matrix algebra; no finite test substitutes for the
  arbitrary-width theorem.
- Basis truth tables are sanity checks after general basis-action theorems.
- Control/target distinctness and duplicate-control exclusion are present in types.
- Circuit counts later inspect syntax metadata, never evaluator matrices.
- No `native_decide`/`bv_decide`, proof holes, or project axioms are introduced.
- Reindex and permutation orientation is asserted by theorems, not inferred from
  suggestive function names.

## Completion Requirements

- [ ] Raw/certified gate, state, basis-ket, and reindex APIs compile.
- [ ] Reindex, block-diagonal, and tensor unitary closure theorems compile.
- [ ] Arbitrary-target local gates and positive multi-controlled one-qubit gates
  have entry/basis-action and certified-unitarity theorems.
- [ ] X/CNOT basis action is proved generally and checked on the four two-bit inputs.
- [ ] Chronological circuit evaluation, append, identity, inverse/adjoint, and
  evaluator-unitarity theorems compile.
- [ ] Structural primitive metadata is retained independently of semantics.
- [ ] Boundary/non-adjacent examples compile without relying on basis enumeration.
- [ ] Focused builds, two full builds, hole searches, diff/whitespace checks, and
  headline axiom output are recorded.
- [ ] Traceability/conventions name the implemented definitions and Stage 3 receives
  explicit remaining obligations.

## Stage Results

- In progress.
