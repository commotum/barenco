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
| axiom audit | `lake env lean Barenco/AxiomAudit.lean` | thirteen declarations printed; results above, 2026-07-09 |
| full build | `lake build` | successful, 2,360 jobs, 2026-07-09 |
| second unchanged full build | `lake build` | successful, 2,360 jobs, 2026-07-09 |
