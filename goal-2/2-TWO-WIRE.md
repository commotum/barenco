# 2-TWO-WIRE

Status: in progress (2026-07-10).

## Current Facts

- Stage 1 froze `UnitaryGate 2` as the local type. For an ordered pair
  `(first,second)`, local bit `0` is the ambient first wire and local bit `1` is
  the ambient second wire, giving basis order `00,01,10,11`.
- A strict and trust-zero disposable prototype importing only `Barenco.Semantics`
  compiled the direct complement split, raw/certified `U⊗I` embedding, entry and
  spectator formulas, identity, multiplication, monoid-hom, inverse, and reversed-
  pair orientation. No project Lean source changed in Stage 1.
- The sequential `splitTarget` design also compiled, but it imports `Controlled`
  and exposes a nested complement. The selected core instead uses a direct
  complement subtype and remains below one-qubit/control semantics.
- `Barenco.Semantics` already supplies certified `reindexUnitary`,
  `kroneckerUnitary`, basis-ket action, and matrix extensionality. It lacks the
  narrow fixed-right-identity Kronecker hom laws, which this stage must prove.
- `Primitive.mk` remains private and no arbitrary-two-qubit syntax constructor is
  introduced in this stage. That trust-boundary edit belongs exclusively to Stage
  3 after semantic correctness is stable.
- Existing `localUnitary`, `positiveControlledUnitary`, and `cnotUnitary` are the
  targets of bridge theorems, not dependencies of the core layout/semantics files.

## Updated Assumptions

- Split layout and matrix semantics should remain separate leaves so optimizer and
  syntax consumers can import only what they need.
- `twoWireUnitary` should be packaged as a monoid hom from `UnitaryGate 2` to
  `UnitaryGate n`; identity and multiplication are primary proofs and inverse
  follows from `map_inv` rather than a fresh matrix calculation.
- The public raw entry theorem should be phrased through `AgreeOffTwoWire`, not
  equality of dependent complement functions. This is the stable bridge for
  spectator, reversed-pair, local, controlled, and CNOT results.
- Structural support `{first,second}` is deferred to Stage 3 syntax. The Stage 2
  semantics may be identity or scalar and does not claim both wires are minimally
  affected.
- A single public orientation theorem using an explicit local wire-swap reindex is
  sufficient; reversed complement subtypes should not be transported directly.

## Big Picture Objective

Implement and verify arbitrary-register semantics for every certified two-qubit
unitary acting on any ordered pair of distinct, possibly nonadjacent wires, with
explicit spectator and orientation behavior and no circuit-resource claim.

## Detailed Implementation Plan

- Add `Barenco/TwoWire/Layout.lean`:
  - `OrderedWirePair n`, extensionality, decidable pair equality, and `swap`;
  - direct `PairComplement`/`PairComplementBasis`;
  - `twoWireLocalBits`, inverse reconstruction, and
    `splitTwoWire : Basis n ≃ Basis 2 × PairComplementBasis pair`;
  - local-bit/spectator simp lemmas, `setTwoWire`, and agreement/equality lemmas;
  - explicit local `Basis 2` swap equivalence and its zero/one/involution laws.
- Add `Barenco/TwoWire/Semantics.lean`:
  - `TwoQubitMatrix`/`TwoQubitUnitary` public aliases;
  - raw and certified `twoWireRaw`/`twoWireUnitary` using reindexed `U⊗I`;
  - exact entry and basis-ket action formulas;
  - target-pair update, changed-spectator zero, and arbitrary spectator preservation;
  - identity, multiplication, monoid-hom, inverse/adjoint, proof-witness, and pair-
    reversal theorems.
- Add `Barenco/TwoWire/ControlledBridges.lean`:
  - first- and second-selected local-one-qubit bridge theorems;
  - canonical local CNOT and singleton-controlled-U bridge theorems;
  - only proof-side imports of `Barenco.Controlled` and any narrow Pauli API needed.
- Add root-excluded `Barenco/TwoWireExamples.lean` covering width two, reversed
  orientation, and padded nonadjacent wires with explicit basis action/spectators.
- Build leaves incrementally, repair only actual proof/API issues, then integrate
  the stable public modules into `Barenco.lean` and add maintained axiom checks.
- Update conventions/docs and this stage/master plan only after theorem names and
  scopes compile.

## Build Structure

- `Barenco/TwoWire/Layout.lean` — public runtime plus cheap proof API; imports only
  the lowest basis/equivalence layer required.
- `Barenco/TwoWire/Semantics.lean` — public runtime and general semantic proof API;
  imports `Layout` and `Barenco.Semantics`, never `Circuit` or `Cost`.
- `Barenco/TwoWire/ControlledBridges.lean` — public proof-side bridge leaf; imports
  core two-wire semantics and `Barenco.Controlled`.
- `Barenco/TwoWireExamples.lean` — diagnostic, root-excluded.
- `Barenco.lean` — stable public re-export only after focused verification.
- `Barenco/AxiomAudit.lean` — proof-side maintained checks for selected headline
  results after public integration.
- High-fanout files intentionally untouched in this stage: `Circuit.lean`,
  `Cost.lean`, all optimization modules, and all paper-specific construction files.
- Initial focused builds:
  `lake build Barenco.TwoWire.Layout`, then
  `lake build Barenco.TwoWire.Semantics`, then
  `lake build Barenco.TwoWire.ControlledBridges Barenco.TwoWireExamples`.
- Adjacent/public build:
  `lake build Barenco.TwoWire.ControlledBridges Barenco.TwoWireExamples`
  `Barenco.AxiomAudit Barenco`.
- Strict/trust-zero checks compile each public leaf directly, then the public root
  and axiom audit.

## Boundary Checks

- `OrderedWirePair` requires `first≠second`; there is no pair at widths zero or one.
  Equal-wire behavior is rejected by the input type, not assigned fallback
  semantics.
- Pair orientation is semantic. `(first,second,U)` and `(second,first,U)` are not
  identified; the latter equals the former only after the proved local swap
  reindexing of `U`.
- Exact full-register matrix equality is used throughout. No global or basis phase
  is discarded.
- Spectator preservation is arbitrary-register operator behavior, not only a
  width-two example or computational-basis truth table.
- No syntax, `PrimitiveKind`, support finset, gate count, or cost appears in the
  core semantic result. Stage 3 alone attaches resource-visible syntax.
- The core never imports lower bounds, universality, optimization, or paper-specific
  modules. Controlled/CNOT bridges do not flow back into the core.
- Identity and scalar local matrices remain legal; later structural support is an
  upper bound rather than a minimal-support assertion.
- No ancilla is allocated or assumed. Every unselected wire is a spectator.

## No-Cheating Checks

- No `Primitive.unclassified`, `.arbitraryTwoQubit` tag, `Circuit`, or cost model is
  used to construct or justify semantics.
- Unitarity comes from `kroneckerUnitary` and `reindexUnitary`, not an axiom or an
  arbitrary full-register matrix bundled with an unsupported proof.
- Spectator locality is proved from the entry/basis formulas, never inferred from
  metadata.
- The local wire order is tested at both indices and under explicit reversal.
- The public theorem is arbitrary-width and nonadjacent; width-two examples are
  diagnostics only.
- Repository scans reject proof holes, custom axioms, opaque declarations, and
  forbidden decision shortcuts.

## Completion Requirements

- [ ] Ordered pair, complement, split, reconstruction, agreement, update, and local
  swap APIs compile with documented `00,01,10,11` orientation.
- [ ] Raw/certified embeddings have exact entry, basis action, spectator-zero,
  identity, multiplication, inverse/adjoint, and reversal theorems.
- [ ] First-wire, second-wire, singleton-controlled-U, and CNOT bridges compile as
  exact arbitrary-register equalities.
- [ ] Width-two, reversed-order, and nonadjacent padded diagnostics compile and
  exercise target action plus spectator preservation.
- [ ] Stable public modules are integrated without importing diagnostics; headline
  results are present in `Barenco/AxiomAudit.lean` with accepted axiom sets.
- [ ] Focused/adjacent/root/audit builds, strict and trust-zero compilation,
  forbidden scans, and `git diff --check` pass with exact results recorded.
- [ ] Conventions/docs and `goal-2/0-plan.md` are folded forward with exact theorem
  names and Stage 2 marked complete.

## Stage Results

- Stage file created before any Stage 2 Lean source change.
