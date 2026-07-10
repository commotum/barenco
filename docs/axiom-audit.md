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
| `Barenco.gate_mul_one` | `Barenco.Basic` | pending first full Stage 1 audit | bootstrap theorem | pending |
| finite-register/circuit headline | planned | pending | Stage 2 | — |
| controlled-U decomposition headline | planned | pending | Stage 5 | — |
| multi-control construction headline | planned | pending | Stages 7–9 | — |
| exact universality headline | planned | pending | Stage 11 | — |
| resource headline | planned | pending | Stage 12 | — |

## Build Reproducibility Evidence

| Item | Expected | Evidence |
|---|---|---|
| Lean toolchain | `leanprover/lean4:v4.31.0` | pinned in `lean-toolchain`; verification pending |
| mathlib | commit `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` | pinned in `lakefile.toml`; manifest verification pending |
| focused build | `lake env lean Barenco/Basic.lean` | pending recording in Stage 1 results |
| full build | `lake build` | pending successful run after bootstrap fixes |
| second unchanged full build | `lake build` | pending |

