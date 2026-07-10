# 2-SEMANTICS

Status: completed 2026-07-09.

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
- The implemented target split `Basis n ≃ Bool × ({i // i ≠ target} → Bool)` builds
  local and controlled gates as reindexed block-diagonal matrices. Unitarity is
  compositional while basis entries remain transparent.
- Arbitrary basis reindexing is a certified unitary constructor with its inverse
  entry orientation proved once and reused.
- Circuit primitives carry both a certified unitary denotation and stable
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
- `Barenco.Circuit` imports the narrow certified `Controlled` foundation and owns
  syntax/evaluation/adjoint plus correctness-by-construction structural metadata.
- `Barenco.SemanticsExamples` is diagnostic/audit-only and contains boundary and
  low-dimensional checks, not public runtime definitions.
- `Barenco.lean` is the thin public re-export surface; internal leaves import their
  narrow dependencies, never the root module.
- Runtime/public API: `Basic`, `Semantics`, `Controlled`, `Circuit`. Proof-side:
  their theorem sections. Diagnostic: `ApiSmoke`, `AxiomAudit`, and
  `SemanticsExamples`. `Primitive.unclassified` is an explicit conservative
  fallback (`.other`, full-register support); there is no temporary public API.
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

- [x] Raw/certified gate, state, basis-ket, and reindex APIs compile.
- [x] Reindex, block-diagonal, and tensor unitary closure theorems compile.
- [x] Arbitrary-target local gates and positive multi-controlled one-qubit gates
  have entry/basis-action and certified-unitarity theorems.
- [x] X/CNOT basis action is proved generally and checked on the four two-bit inputs.
- [x] Chronological circuit evaluation, append, identity, inverse/adjoint, and
  evaluator-unitarity theorems compile.
- [x] Structural primitive metadata is retained independently of semantics.
- [x] Boundary/non-adjacent examples compile without relying on basis enumeration.
- [x] Focused builds, two full builds, hole searches, diff/whitespace checks, and
  headline axiom output are recorded.
- [x] Traceability/conventions name the implemented definitions and Stage 3 receives
  explicit remaining obligations.

## Stage Results

### Public runtime and semantic API

- `Barenco.Semantics` adds computational `basisKet`, basis-action matrix
  extensionality, certified `reindexUnitary`/multiplicative equivalence, the exact
  inverse-index orientation theorem, pointwise iff/certified block-diagonal
  unitarity, and certified Kronecker products.
- `Barenco.Controlled` implements target/complement splitting, target updates,
  raw/certified local gates, arbitrary predicate controls, positive `ControlSet`s,
  multi-controlled gates, Pauli-X, and proof-distinct CNOT. General entry,
  basis-column, active/inactive, untouched-wire, unitarity, empty-control, X-flip,
  and CNOT truth-table theorems compile for arbitrary register width.
- `Barenco.Circuit` implements chronological syntax/evaluation/append/identity and
  reverse-adjoint circuits with exact inverse/cancellation theorems. Raw
  `Primitive.mk` is module-private. Trusted smart constructors fix kind, exact
  support/cardinality, and certified denotation together for one-qubit, positive
  multi-controlled, and CNOT gates.
- `Primitive.unclassified` is intentionally conservative (`.other` and full
  support). Future costs must reject or explicitly price it; callers cannot forge a
  one-qubit/CNOT label. Toffoli and arbitrary-two-qubit smart constructors remain
  unavailable until certified semantics exists.
- `Barenco.lean` is a thin public re-export of `Basic`, `Semantics`, `Controlled`,
  and `Circuit`. Diagnostic modules are not re-exported.

### Diagnostics and boundaries

- `Barenco.SemanticsExamples` instantiates the general theorems for an actual empty
  positive-control set on one qubit, all four CNOT inputs, non-adjacent control 0 to
  target 2 with the middle wire preserved, the unique zero-qubit identity action,
  and the chronological noncommuting sequence X(0) then CNOT(0,1).
- All examples use trusted constructors and ordinary kernel reduction/theorem
  instantiation. They contain no `native_decide` or `bv_decide` and do not replace
  arbitrary-width proofs.
- `BUILD-PLAN.md` was adopted as an authoritative goal requirement during this
  stage. Module ownership, declaration classifications, focused/adjacent builds,
  high-fanout boundaries, and fallback handling are now recorded in every active
  Lean stage.

### Verification evidence

- Warning-as-error direct compilation succeeded for `Basic`, `Semantics`,
  `Controlled`, `Circuit`, `SemanticsExamples`, and `ApiSmoke`.
- Combined focused/adjacent build
  `lake build Barenco.Controlled Barenco.Circuit Barenco.SemanticsExamples Barenco`
  succeeded (2,364 jobs).
- `lake build Barenco.SemanticsExamples` succeeded (2,362 jobs).
- `lake build` succeeded twice from unchanged sources (2,363 jobs each).
- `lake env lean Barenco/AxiomAudit.lean` printed thirteen headline declarations;
  each depends only on standard `propext`, `Classical.choice`, and `Quot.sound`.
- Project Lean-source proof-hole/unsafe-decision/custom-axiom scans, trailing
  whitespace scan, and `git diff --check` produced no findings.

### Fold-forward obligations

- Stage 3 must define exact/global/basis-phase/basis-behavior/measurement relations,
  the L² operator distance bridge, syntax-derived costs, and named early/Section 8
  cost models. It must make `.other` rejection/pricing explicit.
- The paper-order `∧ₘ(U)` wrapper and its explicit `Fin (2^n)` lower-right-block
  matrix theorem remain; the stronger arbitrary-target/control-set semantics is
  already available underneath.
- General multi-wire local embeddings, signed/negative controls, Toffoli and
  arbitrary-two-qubit smart constructors, and CNOT/X involution lemmas remain
  relevant later work. None is claimed complete here.
