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
| `Barenco.operatorDistance_unitary_le_two` | `Barenco.Equivalence.OperatorNorm` | `propext`, `Classical.choice`, `Quot.sound` | nonempty-index unitary distance bound; no project axiom | 2026-07-09 |
| `Barenco.Circuit.cost_append` | `Barenco.Cost` | `propext`, `Classical.choice`, `Quot.sound` | partial syntax-cost append law; no project axiom | 2026-07-09 |
| `Barenco.Circuit.cost_adjoint` | `Barenco.Cost` | `propext`, `Classical.choice`, `Quot.sound` | partial syntax-cost adjoint invariance; no project axiom | 2026-07-09 |
| `Barenco.Primitive.namedModels_reject_unclassified_of_mem` | `Barenco.Cost` | `propext`, `Classical.choice`, `Quot.sound` | unsupported primitives cannot silently receive zero cost; no project axiom | 2026-07-09 |
| controlled-U decomposition headline | planned | pending | Stage 5 | — |
| multi-control construction headline | planned | pending | Stages 7–9 | — |
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
| Stage 3 warning-as-error builds | direct `lean -Ewarning` compilation of `Phase`, `Measurement`, `OperatorNorm`, and `Cost` | all successful, 2026-07-09 |
| Stage 3 focused/adjacent build | `lake build Barenco.Equivalence.Phase Barenco.Equivalence.Measurement Barenco.Equivalence.OperatorNorm Barenco.Cost Barenco Barenco.AxiomAudit` | successful, 2,371 jobs, 2026-07-09 |
| axiom audit | `lake env lean -Ewarning Barenco/AxiomAudit.lean` | twenty-seven declarations printed; every result is exactly the standard trio shown above, 2026-07-09 |
| Stage 2 full build | `lake build` | successful, 2,360 jobs, 2026-07-09 |
| Stage 2 second unchanged full build | `lake build` | successful, 2,360 jobs, 2026-07-09 |
