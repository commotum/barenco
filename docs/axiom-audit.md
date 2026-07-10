# Axiom Audit

The completed library permits no `sorry`, `admit`, or unexplained project-specific
axioms. This document records both syntactic hole searches and kernel-reported axioms
for headline exports.

## Policy

- A completed theorem is checked with `#print axioms` in a maintained audit module.
- Standard mathlib/Lean foundations such as `Classical.choice`, `propext`, and
  `Quot.sound` may appear, but their presence is recorded rather than hidden.
- Project declarations using `axiom`, unsafe proof shortcuts, `native_decide`, or
  `bv_decide` are not accepted in completed mathematical modules.
- Conditional mathematical assumptions belong as explicit theorem arguments or
  structures, not global axioms.
- A green build is necessary but does not replace this audit.

## Syntactic Audit Commands

Run from the repository root:

```text
rg -n '\b(sorry|admit|by\?|native_decide|bv_decide)\b' --glob '*.lean' .
rg -n '^\s*(axiom|opaque)\b' --glob '*.lean' Barenco Barenco.lean
git diff --check
```

Generated dependencies under `.lake/` are excluded from the project-source audit.

## Headline Audit Table

| Declaration | Module | `#print axioms` result | Explanation | Last verified |
|---|---|---|---|---|
| `Barenco.fromPaper_mul` | `Barenco.Basic` | `propext`, `Classical.choice`, `Quot.sound` | standard mathlib matrix foundations; no project axiom | 2026-07-09 |
| `Barenco.fromPaper_mem_unitaryGroup_iff` | `Barenco.Basic` | `propext`, `Classical.choice`, `Quot.sound` | standard mathlib unitary-group foundations; no project axiom | 2026-07-09 |
| `Barenco.evalGates_append` | `Barenco.Basic` | `propext`, `Classical.choice`, `Quot.sound` | standard mathlib matrix/list foundations; no project axiom | 2026-07-09 |
| `Barenco.fromPaper_paperProduct` | `Barenco.Basic` | `propext`, `Classical.choice`, `Quot.sound` | row/column convention bridge; no project axiom | 2026-07-09 |
| `Barenco.gate_mul_one` | `Barenco.Basic` | `propext`, `Classical.choice`, `Quot.sound` | standard mathlib matrix foundations; no project axiom | 2026-07-09 |
| `Barenco.reindex_mem_unitaryGroup_iff` | `Barenco.Semantics` | `propext`, `Classical.choice`, `Quot.sound` | certified basis transport; no project axiom | 2026-07-09 |
| `Barenco.blockDiagonal_mem_unitaryGroup_iff` | `Barenco.Semantics` | `propext`, `Classical.choice`, `Quot.sound` | certified block semantics; no project axiom | 2026-07-09 |
| `Barenco.localRaw_mem_unitaryGroup` | `Barenco.Controlled` | `propext`, `Classical.choice`, `Quot.sound` | arbitrary-target local unitarity; no project axiom | 2026-07-09 |
| `Barenco.positiveControlledRaw_truthTable` | `Barenco.Controlled` | `propext`, `Classical.choice`, `Quot.sound` | general multi-control basis action; no project axiom | 2026-07-09 |
| `Barenco.cnotRaw_mulVec_basisKet` | `Barenco.Controlled` | `propext`, `Classical.choice`, `Quot.sound` | full-register CNOT basis action; no project axiom | 2026-07-09 |
| `Barenco.Primitive.positiveControlled_support_card` | `Barenco.Circuit` | `propext`, `Classical.choice`, `Quot.sound` | structural support count; no project axiom | 2026-07-09 |
| `Barenco.Primitive.toffoli_support_card` | `Barenco.Circuit` | `propext`, `Classical.choice`, `Quot.sound` | three-distinct-wire Toffoli support count; no project axiom | 2026-07-09 |
| `Barenco.Primitive.toffoli_denotation_mulVec_basisKet` | `Barenco.Circuit` | `propext`, `Classical.choice`, `Quot.sound` | trusted Toffoli full-register basis action; no project axiom | 2026-07-09 |
| `Barenco.Circuit.eval_append` | `Barenco.Circuit` | `propext`, `Classical.choice`, `Quot.sound` | chronological evaluator composition; no project axiom | 2026-07-09 |
| `Barenco.Circuit.eval_adjoint` | `Barenco.Circuit` | `propext`, `Classical.choice`, `Quot.sound` | inverse evaluator; no project axiom | 2026-07-09 |
| `Barenco.GlobalPhaseEq.mul` | `Barenco.Equivalence.Phase` | `propext`, `Classical.choice`, `Quot.sound` | global-phase composition; no project axiom | 2026-07-09 |
| `Barenco.BasisPhaseEq.postcompose` | `Barenco.Equivalence.Phase` | `propext`, `Classical.choice`, `Quot.sound` | valid input-column-phase congruence boundary; no project axiom | 2026-07-09 |
| `Barenco.BasisPhaseEq.toBasisMeasurementEq` | `Barenco.Equivalence.Phase` | `propext`, `Classical.choice`, `Quot.sound` | basis-phase probability implication; no project axiom | 2026-07-09 |
| `Barenco.GlobalPhaseEq.toChannelEq` | `Barenco.Equivalence.Measurement` | `propext`, `Classical.choice`, `Quot.sound` | unit scalar cancellation in conjugation; no project axiom | 2026-07-09 |
| `Barenco.channelEq_iff_allMeasurementEq` | `Barenco.Equivalence.Measurement` | `propext`, `Classical.choice`, `Quot.sound` | arbitrary matrix-unit effects separate channel entries; no project axiom | 2026-07-09 |
| `Barenco.ChannelEq.toBasisMeasurementEq` | `Barenco.Equivalence.Measurement` | `propext`, `Classical.choice`, `Quot.sound` | channel equality implies squared-entry equality; no project axiom | 2026-07-09 |
| `Barenco.operatorDistance_unitary_mul_left` | `Barenco.Equivalence.OperatorNorm` | `propext`, `Classical.choice`, `Quot.sound` | L² operator distance under left unitary multiplication; no project axiom | 2026-07-09 |
| `Barenco.operatorDistance_unitary_mul_right` | `Barenco.Equivalence.OperatorNorm` | `propext`, `Classical.choice`, `Quot.sound` | L² operator distance under right unitary multiplication; no project axiom | 2026-07-09 |
| `Barenco.operatorDistance_mul_unitary_le` | `Barenco.Equivalence.OperatorNorm` | `propext`, `Classical.choice`, `Quot.sound` | additive two-factor unitary error bound; no project axiom | 2026-07-09 |
| `Barenco.operatorDistance_action_le` | `Barenco.Equivalence.OperatorNorm` | `propext`, `Classical.choice`, `Quot.sound` | induced-norm state-action bound; no project axiom | 2026-07-09 |
| `Barenco.operatorDistance_basisOutcomeProbability_le` | `Barenco.Equivalence.OperatorNorm` | `propext`, `Classical.choice`, `Quot.sound` | factor-two error bound for one computational-basis outcome; no project axiom | 2026-07-09 |
| `Barenco.operatorDistance_unitary_le_two` | `Barenco.Equivalence.OperatorNorm` | `propext`, `Classical.choice`, `Quot.sound` | nonempty-index unitary distance bound; no project axiom | 2026-07-09 |
| `Barenco.Circuit.cost_append` | `Barenco.Cost` | `propext`, `Classical.choice`, `Quot.sound` | partial syntax-cost append law; no project axiom | 2026-07-09 |
| `Barenco.Circuit.cost_adjoint` | `Barenco.Cost` | `propext`, `Classical.choice`, `Quot.sound` | partial syntax-cost adjoint invariance; no project axiom | 2026-07-09 |
| `Barenco.Circuit.touchedSupport_card_le_registerWidth` | `Barenco.Cost` | `propext`, `Classical.choice`, `Quot.sound` | named syntactic support fits ambient circuit width; no project axiom | 2026-07-09 |
| `Barenco.Primitive.namedModels_reject_unclassified_of_mem` | `Barenco.Cost` | `propext`, `Classical.choice`, `Quot.sound` | unsupported primitives cannot silently receive zero cost; no project axiom | 2026-07-09 |
| `Barenco.OneQubit.paperRy_mul` | `Barenco.OneQubit.Matrix` | `propext`, `Classical.choice`, `Quot.sound` | paper-row Y-rotation addition law; no project axiom | 2026-07-09 |
| `Barenco.OneQubit.paperX_mul_paperRy_mul_paperX` | `Barenco.OneQubit.Matrix` | `propext`, `Classical.choice`, `Quot.sound` | paper-row Pauli-X conjugation identity; no project axiom | 2026-07-09 |
| `Barenco.OneQubit.ry_mem_specialUnitaryGroup` | `Barenco.OneQubit.Certified` | `propext`, `Classical.choice`, `Quot.sound` | standard-column Y rotation is certified special unitary; no project axiom | 2026-07-09 |
| `Barenco.OneQubit.sigmaX_mul_ry_mul_sigmaX` | `Barenco.OneQubit.Certified` | `propext`, `Classical.choice`, `Quot.sound` | semantic Pauli-X conjugation identity; no project axiom | 2026-07-09 |
| `Barenco.OneQubit.paperA_mul_paperB_mul_paperC` | `Barenco.OneQubit.Decomposition` | `propext`, `Classical.choice`, `Quot.sound` | inactive-branch A/B/C identity; no project axiom | 2026-07-09 |
| `Barenco.OneQubit.paperA_mul_X_mul_paperB_mul_X_mul_paperC` | `Barenco.OneQubit.Decomposition` | `propext`, `Classical.choice`, `Quot.sound` | active-branch parameterized A/X/B/X/C identity; no project axiom | 2026-07-09 |
| `Barenco.OneQubit.specialUnitary_canonical` | `Barenco.OneQubit.Euler` | `propext`, `Classical.choice`, `Quot.sound` | canonical SU(2) entry form; no project axiom | 2026-07-09 |
| `Barenco.OneQubit.specialUnitary_eq_paperEuler_arg` | `Barenco.OneQubit.Euler` | `propext`, `Classical.choice`, `Quot.sound` | exact total-argument Euler formula, including zero entries; no project axiom | 2026-07-09 |
| `Barenco.OneQubit.specialUnitary_exists_rz_mul_ry_mul_rz` | `Barenco.OneQubit.Euler` | `propext`, `Classical.choice`, `Quot.sound` | standard-column SU(2) Euler existence; no project axiom | 2026-07-09 |
| `Barenco.OneQubit.removeGlobalPhase_det` | `Barenco.OneQubit.GlobalPhase` | `propext`, `Classical.choice`, `Quot.sound` | determinant-one certificate after principal phase removal; no project axiom | 2026-07-09 |
| `Barenco.OneQubit.phaseShift_mul_specialUnitaryPart` | `Barenco.OneQubit.GlobalPhase` | `propext`, `Classical.choice`, `Quot.sound` | exact reconstruction after determinant-phase split; no project axiom | 2026-07-09 |
| `Barenco.OneQubit.unitary_exists_phaseShift_mul_rz_mul_ry_mul_rz` | `Barenco.OneQubit.U2Euler` | `propext`, `Classical.choice`, `Quot.sound` | full standard-column U(2) Euler existence; no project axiom | 2026-07-09 |
| `Barenco.OneQubit.specialUnitary_exists_paperABC` | `Barenco.OneQubit.Lemma43` | `propext`, `Classical.choice`, `Quot.sound` | existential paper-row Lemma 4.3 matrix identities; no project axiom | 2026-07-09 |
| `Barenco.OneQubit.specialUnitary_exists_columnChronologicalABC` | `Barenco.OneQubit.Lemma43` | `propext`, `Classical.choice`, `Quot.sound` | standard-column chronological Lemma 4.3 matrix identities; no project axiom | 2026-07-09 |
| `Barenco.OneQubit.unitaryRoot_pow` | `Barenco.OneQubit.Roots` | `propext`, `Classical.choice`, `Quot.sound` | exact positive finite-dimensional unitary root; no project axiom | 2026-07-09 |
| `Barenco.OneQubit.unitaryRoot_pow_two_pow` | `Barenco.OneQubit.Roots` | `propext`, `Classical.choice`, `Quot.sound` | exact selected power-of-two root equation; no project axiom | 2026-07-09 |
| `Barenco.OneQubit.sigmaXUnitary_eq_pauliX` | `Barenco.OneQubit.CircuitBridge` | `propext`, `Classical.choice`, `Quot.sound` | Section 4 Pauli-X agrees with the certified circuit primitive; no project axiom | 2026-07-09 |
| `Barenco.OneQubit.paperY_mem_unitaryGroup` | `Barenco.OneQubit.Pauli` | `propext`, `Classical.choice`, `Quot.sound` | paper-row Pauli-Y is exactly certified unitary; no project axiom | 2026-07-09 |
| `Barenco.OneQubit.sigmaY_mem_unitaryGroup` | `Barenco.OneQubit.Pauli` | `propext`, `Classical.choice`, `Quot.sound` | standard-column Pauli-Y translation is exactly certified unitary; no project axiom | 2026-07-09 |
| `Barenco.ControlledCircuit.targetBlockRaw_mul` | `Barenco.ControlledCircuit.Block` | `propext`, `Classical.choice`, `Quot.sound` | pointwise multiplication of full-register target blocks; no project axiom | 2026-07-09 |
| `Barenco.ControlledCircuit.eval_controlledABCCircuit_eq_iff` | `Barenco.ControlledCircuit.Decomposition` | `propext`, `Classical.choice`, `Quot.sound` | exact inactive/active branch characterization of the five-gate circuit; no project axiom | 2026-07-09 |
| `Barenco.ControlledCircuit.controlledSU2Circuit_correct_iff` | `Barenco.ControlledCircuit.Decomposition` | `propext`, `Classical.choice`, `Quot.sound` | Lemma 5.1 controlled-circuit existence exactly iff the target determinant is one; no project axiom | 2026-07-09 |
| `Barenco.ControlledCircuit.controlledABCCircuit_oneQubitCNOTCost` | `Barenco.ControlledCircuit.Decomposition` | `propext`, `Classical.choice`, `Quot.sound` | syntax-derived five-operation one-qubit+CNOT cost; no project axiom | 2026-07-09 |
| `Barenco.ControlledCircuit.controlledScalarUnitary_eq_localControl` | `Barenco.ControlledCircuit.Phase` | `propext`, `Classical.choice`, `Quot.sound` | exact arbitrary-register Lemma 5.2 controlled-scalar/local-control identity; no project axiom | 2026-07-09 |
| `Barenco.ControlledCircuit.controlledU2Circuit_exists` | `Barenco.ControlledCircuit.Phase` | `propext`, `Classical.choice`, `Quot.sound` | exact six-primitive controlled-U existence from Corollary 5.3; no project axiom | 2026-07-09 |
| `Barenco.ControlledCircuit.controlledU2Circuit_oneQubitCNOTCost` | `Barenco.ControlledCircuit.Phase` | `propext`, `Classical.choice`, `Quot.sound` | syntax-derived six-operation one-qubit+CNOT cost; no project axiom | 2026-07-09 |
| `Barenco.ControlledCircuit.pauliConjugate_eq_sigmaX_mul_symmetricEuler` | `Barenco.ControlledCircuit.PauliConjugate` | `propext`, `Classical.choice`, `Quot.sound` | complete symmetric-Euler classification of special-unitary Pauli conjugates; no project axiom | 2026-07-09 |
| `Barenco.ControlledCircuit.twoCNOTFamily_iff` | `Barenco.ControlledCircuit.Special` | `propext`, `Classical.choice`, `Quot.sound` | both directions of the Lemma 5.4 two-CNOT family classification; no project axiom | 2026-07-09 |
| `Barenco.ControlledCircuit.oneCNOTFamily_iff` | `Barenco.ControlledCircuit.Special` | `propext`, `Classical.choice`, `Quot.sound` | both directions of the Lemma 5.5 one-CNOT family, including phase normalization; no project axiom | 2026-07-09 |
| `Barenco.ControlledCircuit.twoCNOTCircuit_oneQubitCNOTCost` | `Barenco.ControlledCircuit.SpecialTopology` | `propext`, `Classical.choice`, `Quot.sound` | syntax-derived two-one-qubit plus two-CNOT topology cost; no project axiom | 2026-07-09 |
| `Barenco.ControlledCircuit.oneCNOTCircuit_oneQubitCNOTCost` | `Barenco.ControlledCircuit.SpecialTopology` | `propext`, `Classical.choice`, `Quot.sound` | syntax-derived two-one-qubit plus one-CNOT topology cost; no project axiom | 2026-07-09 |
| `Barenco.ControlledCircuit.controlledVMacroU2Circuit_exists` | `Barenco.ControlledCircuit.Alternative` | `propext`, `Classical.choice`, `Quot.sound` | corrected Corollary 5.6 exact controlled-U macro-circuit existence; no project axiom | 2026-07-09 |
| `Barenco.ControlledCircuit.controlledVMacroU2Circuit_oneQubitCNOTCost` | `Barenco.ControlledCircuit.Alternative` | `propext`, `Classical.choice`, `Quot.sound` | partial cost model correctly rejects unexpanded controlled-V macros; no project axiom | 2026-07-09 |
| `Barenco.ControlledCircuit.eval_expandedVMacroU2Circuit_eq_macro` | `Barenco.ControlledCircuit.Expansion` | `propext`, `Classical.choice`, `Quot.sound` | exact evaluator preservation when both controlled-V macros are expanded; no project axiom | 2026-07-09 |
| `Barenco.ControlledCircuit.eval_expandedVMacroU2Circuit_eq_controlledU2Circuit` | `Barenco.ControlledCircuit.Expansion` | `propext`, `Classical.choice`, `Quot.sound` | exact evaluator equality after the three adjacent one-qubit merge groups; no project axiom | 2026-07-09 |
| `Barenco.ControlledCircuit.expanded_and_mergedVMacroU2Circuit_oneQubitCNOTCosts` | `Barenco.ControlledCircuit.Expansion` | `propext`, `Classical.choice`, `Quot.sound` | syntax-derived expanded and merged costs of ten and six; no project axiom | 2026-07-09 |
| `Barenco.ControlledCircuit.controlledZUnitary_swap` | `Barenco.ControlledCircuit.ControlledZ` | `propext`, `Classical.choice`, `Quot.sound` | exact control/target wire-swap symmetry of controlled-Z; no project axiom | 2026-07-09 |
| `Barenco.ThreeQubit.cnotRaw_commute_localRaw` | `Barenco.ThreeQubit.Lemma61` | `propext`, `Classical.choice`, `Quot.sound` | exact disjoint-wire CNOT/local-gate commutation used by the Section 6 cancellations; no project axiom | 2026-07-09 |
| `Barenco.ThreeQubit.eval_doubleControlledViaSquareCircuit_pow_two` | `Barenco.ThreeQubit.Lemma61` | `propext`, `Classical.choice`, `Quot.sound` | arbitrary-width Lemma 6.1 evaluator for a certified square witness; no project axiom | 2026-07-09 |
| `Barenco.ThreeQubit.eval_doubleControlledRootCircuit` | `Barenco.ThreeQubit.Lemma61` | `propext`, `Classical.choice`, `Quot.sound` | selected exact square-root form of Lemma 6.1; no project axiom | 2026-07-09 |
| `Barenco.ThreeQubit.eval_doubleControlledExpansion20Circuit_eq_16` | `Barenco.ThreeQubit.Expansion` | `propext`, `Classical.choice`, `Quot.sound` | full-register preservation under the two coordinated inverse-pair cancellations; no project axiom | 2026-07-09 |
| `Barenco.ThreeQubit.doubleControlledUnitary_has_sixteenPrimitiveCircuit` | `Barenco.ThreeQubit.Expansion` | `propext`, `Classical.choice`, `Quot.sound` | exact Corollary 6.2 existence and eight-one-qubit/eight-CNOT resource result; no project axiom | 2026-07-09 |
| `Barenco.ThreeQubit.wMatrix_eq_ry_pi` | `Barenco.ThreeQubit.RelativePhase` | `propext`, `Classical.choice`, `Quot.sound` | exact row-to-column translation of the paper's `W`; no project axiom | 2026-07-09 |
| `Barenco.ThreeQubit.paperW_eq_paperPhase_mul_paperY` | `Barenco.ThreeQubit.RelativePhase` | `propext`, `Classical.choice`, `Quot.sound` | exact source identity `W = Ph(pi/2) sigma_y` in row convention; no project axiom | 2026-07-09 |
| `Barenco.ThreeQubit.wUnitary_eq_phaseShift_mul_sigmaY` | `Barenco.ThreeQubit.RelativePhase` | `propext`, `Classical.choice`, `Quot.sound` | certified standard-column translation of the source's Pauli-Y factorization; no project axiom | 2026-07-09 |
| `Barenco.ThreeQubit.eval_relativePhaseToffoliACircuit` | `Barenco.ThreeQubit.RelativePhase` | `propext`, `Classical.choice`, `Quot.sound` | exact arbitrary-width evaluator of the A/CNOT diagram; no project axiom | 2026-07-09 |
| `Barenco.ThreeQubit.eval_relativePhaseToffoliBCircuit` | `Barenco.ThreeQubit.RelativePhase` | `propext`, `Classical.choice`, `Quot.sound` | exact arbitrary-width evaluator of the B/controlled-Z diagram; no project axiom | 2026-07-09 |
| `Barenco.ThreeQubit.eval_relativePhaseToffoliACircuit_eq_BCircuit` | `Barenco.ThreeQubit.RelativePhase` | `propext`, `Classical.choice`, `Quot.sound` | exact equality of the two Section 6.2 diagram evaluators; no project axiom | 2026-07-09 |
| `Barenco.ThreeQubit.relativeToffoliUnitary_sq` | `Barenco.ThreeQubit.RelativePhase` | `propext`, `Classical.choice`, `Quot.sound` | exact involution law underlying adjacent identical-pair cancellation; no project axiom | 2026-07-09 |
| `Barenco.ThreeQubit.relativePhaseToffoliACircuit_mulVec_basisKet` | `Barenco.ThreeQubit.RelativePhase` | `propext`, `Classical.choice`, `Quot.sound` | exact Toffoli basis action with the `101` input-column sign; no project axiom | 2026-07-09 |
| `Barenco.ThreeQubit.controlledWUnitary_mulVec_basisKet` | `Barenco.ThreeQubit.RelativePhase` | `propext`, `Classical.choice`, `Quot.sound` | exact controlled-`W` basis action with the distinct `111` sign; no project axiom | 2026-07-09 |
| `Barenco.ThreeQubit.relativePhaseToffoliACircuit_basisPhaseEq_toffoli` | `Barenco.ThreeQubit.RelativePhase` | `propext`, `Classical.choice`, `Quot.sound` | explicit basis-phase relation between the A diagram and Toffoli; no project axiom | 2026-07-09 |
| `Barenco.ThreeQubit.controlledWUnitary_basisPhaseEq_toffoli` | `Barenco.ThreeQubit.RelativePhase` | `propext`, `Classical.choice`, `Quot.sound` | explicit basis-phase relation between controlled-`W` and Toffoli; no project axiom | 2026-07-09 |
| `Barenco.ThreeQubit.relativePhaseToffoliACircuit_oneQubitCNOTCost` | `Barenco.ThreeQubit.RelativePhase` | `propext`, `Classical.choice`, `Quot.sound` | syntax-derived four-one-qubit/three-CNOT cost of seven; no project axiom | 2026-07-09 |
| `Barenco.ThreeQubit.relativePhaseToffoliBCircuit_oneQubitCNOTCost` | `Barenco.ThreeQubit.RelativePhase` | `propext`, `Classical.choice`, `Quot.sound` | partial cost correctly rejects the B circuit's controlled-Z macros; no project axiom | 2026-07-09 |
| `Barenco.ControlledCircuit.targetBlockRaw_mulVec_basisKet` | `Barenco.ControlledCircuit.Block` | `propext`, `Classical.choice`, `Quot.sound` | selected target-block basis-column action used by Gray circuits; no project axiom | 2026-07-09 |
| `Barenco.MultiControl.parityInclusionExclusionSum_formula` | `Barenco.MultiControl.Parity` | `propext`, `Classical.choice`, `Quot.sound` | exact signed subset-XOR identity; no project axiom | 2026-07-09 |
| `Barenco.MultiControl.grayCode_isChain` | `Barenco.MultiControl.GrayCode` | `propext`, `Classical.choice`, `Quot.sound` | reflected Gray adjacency proof; no project axiom | 2026-07-09 |
| `Barenco.MultiControl.nodup_grayCode` | `Barenco.MultiControl.GrayCode` | `propext`, `Quot.sound` | exact mask uniqueness without choice; no project axiom | 2026-07-09 |
| `Barenco.MultiControl.runXorEdges_grayCNOTEdges` | `Barenco.MultiControl.GrayAccumulator` | `propext`, `Classical.choice`, `Quot.sound` | complete generated CNOT restoration; no project axiom | 2026-07-09 |
| `Barenco.MultiControl.OrderedControlLayout.all_controls_iff` | `Barenco.MultiControl.Layout` | `propext`, `Classical.choice`, `Quot.sound` | ordered/unordered all-controls bridge; no project axiom | 2026-07-09 |
| `Barenco.MultiControl.grayRootProduct_selectedRoot_formula` | `Barenco.MultiControl.Lemma71` | `propext`, `Classical.choice`, `Quot.sound` | exact selected-root branch product; no project axiom | 2026-07-09 |
| `Barenco.MultiControl.eval_grayCNOTCircuit_mulVec_basisKet` | `Barenco.MultiControl.Lemma71` | `propext`, `Classical.choice`, `Quot.sound` | arbitrary-width generated CNOT restoration action; no project axiom | 2026-07-09 |
| `Barenco.MultiControl.eval_grayControlledViaRootCircuit` | `Barenco.MultiControl.Lemma71` | `propext`, `Classical.choice`, `Quot.sound` | exact arbitrary-width interleaved Lemma 7.1 evaluator; no project axiom | 2026-07-09 |
| `Barenco.MultiControl.eval_grayControlledCircuit` | `Barenco.MultiControl.Lemma71` | `propext`, `Classical.choice`, `Quot.sound` | selected exact root implements controlled U; no project axiom | 2026-07-09 |
| `Barenco.MultiControl.grayControlledViaRootCircuit_kindCounts` | `Barenco.MultiControl.Lemma71` | `propext`, `Classical.choice`, `Quot.sound` | syntax-derived root/CNOT macro counts; no project axiom | 2026-07-09 |
| `Barenco.MultiControl.eval_fourBitGrayCircuit` | `Barenco.MultiControl.Lemma71` | `propext`, `Classical.choice`, `Quot.sound` | exact displayed four-bit circuit evaluator; no project axiom | 2026-07-09 |
| exact universality headline | planned | pending | Stage 11 | — |
| resource headline | planned | pending | Stage 12 | — |

## Build Reproducibility Evidence

| Item | Expected | Evidence |
|---|---|---|
| Lean toolchain | `leanprover/lean4:v4.31.0` | `lean --version`: 4.31.0, commit `68218e8…`, 2026-07-09 |
| mathlib | commit `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` | exact input/resolved revision in `lakefile.toml` and `lake-manifest.json`, 2026-07-09 |
| focused build | `lake env lean Barenco/Basic.lean`; `lake env lean Barenco/ApiSmoke.lean` | both successful, 2026-07-09 |
| Stage 2 focused builds | `lake build Barenco.Semantics Barenco.Controlled Barenco.Circuit` | successful; warning-as-error direct compilation also successful, 2026-07-09 |
| Stage 2 adjacent build | `lake build Barenco.SemanticsExamples Barenco` | successful as part of combined 2,364-job build, 2026-07-09 |
| Stage 3 warning-as-error builds | direct `lake env lean -DwarningAsError=true` compilation of `Phase`, `Measurement`, `OperatorNorm`, `Cost`, the diagnostic example, the audit, and the root | all successful, 2026-07-09 |
| Stage 3 focused/adjacent build | `lake build Barenco.Equivalence.Phase Barenco.Equivalence.Measurement Barenco.Equivalence.OperatorNorm Barenco.Cost Barenco.EquivalenceExamples Barenco Barenco.AxiomAudit` | successful, 2,372 jobs, 2026-07-09 |
| Stage 4 warning-as-error audit | `lake env lean -DwarningAsError=true Barenco/AxiomAudit.lean` | successful; forty-six declarations printed, including all seventeen new Stage 4 checks; every result is exactly the standard trio shown above, 2026-07-09 |
| Stage 4 focused/adjacent build | `lake build Barenco.OneQubit.Matrix Barenco.OneQubit.Certified Barenco.OneQubit.Decomposition Barenco.OneQubit.Euler Barenco.OneQubit.GlobalPhase Barenco.OneQubit.U2Euler Barenco.OneQubit.Lemma43 Barenco.OneQubit.Roots Barenco.OneQubit.CircuitBridge Barenco.OneQubitExamples Barenco.AxiomAudit Barenco` | successful, 2,935 jobs, 2026-07-09 |
| Stage 4 full builds | two consecutive `lake build` runs after the public-root change | both successful, 2,933 jobs each, 2026-07-09 |
| Stage 5 warning-as-error audit | `lake env lean -DwarningAsError=true Barenco/AxiomAudit.lean` | successful; sixty-four declarations printed, including all eighteen new Stage 5 checks; every result is exactly `propext`, `Classical.choice`, and `Quot.sound`, 2026-07-09 |
| Stage 5 focused/adjacent build | `lake build Barenco.ControlledCircuit.Block Barenco.ControlledCircuit.Decomposition Barenco.ControlledCircuit.Phase Barenco.ControlledCircuit.SpecialTopology Barenco.ControlledCircuit.PauliConjugate Barenco.ControlledCircuit.Special Barenco.ControlledCircuit.Alternative Barenco.ControlledCircuit.Expansion Barenco.ControlledCircuit.ControlledZ Barenco.ControlledCircuitExamples Barenco.AxiomAudit Barenco` | successful, 2,944 jobs, 2026-07-09 |
| Stage 5 full builds | two consecutive `lake build` runs after the public-root change | both successful, 2,942 jobs each, 2026-07-09 |
| Stage 6 warning-as-error root/audit | `lake env lean -DwarningAsError=true Barenco.lean`; `lake env lean -DwarningAsError=true Barenco/AxiomAudit.lean` | both successful; the audit printed 84 declarations, including all 20 new Stage 6 checks, and every result is exactly `propext`, `Classical.choice`, and `Quot.sound`, 2026-07-09 |
| Stage 6 focused/diagnostic/root/audit build | `lake build Barenco.OneQubit.Pauli Barenco.ThreeQubit.Lemma61 Barenco.ThreeQubit.Expansion Barenco.ThreeQubit.RelativePhase Barenco.ThreeQubitExamples Barenco.AxiomAudit Barenco` | successful, 2,948 jobs, 2026-07-09 |
| Stage 6 full builds | two consecutive `lake build` runs after the final public-root integration | both successful, 2,946 jobs each, 2026-07-09 |
| Stage 7 Lemma 7.1 warning-as-error/root/audit | direct strict compilation of `Parity`, `GrayCode`, `GrayAccumulator`, `Layout`, `Lemma71`, `MultiControlExamples`, `Barenco.lean`, and `AxiomAudit.lean` | successful; the audit printed 96 declarations and every result is within `propext`, `Classical.choice`, and `Quot.sound`, 2026-07-09 |
| Stage 7 Lemma 7.1 focused/root/audit build | `lake build Barenco.MultiControl.Parity Barenco.MultiControl.GrayCode Barenco.MultiControl.GrayAccumulator Barenco.MultiControl.Layout Barenco.MultiControl.Lemma71 Barenco.MultiControlExamples Barenco.AxiomAudit Barenco` | successful after retrying one transient parallel output-file race, 3,482 jobs, 2026-07-09 |
| Stage 7 Lemma 7.1 full builds | two consecutive `lake build` runs after public-root integration | both successful, 3,480 jobs each, 2026-07-09 |
| Stage 2 full build | `lake build` | successful, 2,360 jobs, 2026-07-09 |
| Stage 2 second unchanged full build | `lake build` | successful, 2,360 jobs, 2026-07-09 |
