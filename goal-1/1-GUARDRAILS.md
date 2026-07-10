# 1-GUARDRAILS

Status: in progress.

## Current Facts

- The repository has a local PDF, structured Markdown transcription, and sixteen
  extracted diagram images for the paper.
- The pre-stage tools reported Lean 4.31.0 and Lake 5.0.0 from the user's unpinned
  default. The repo now pins `leanprover/lean4:v4.31.0` and mathlib commit
  `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`; `lake-manifest.json` records every
  resolved transitive dependency revision.
- The existing project is a minimal Python 3.13/uv package and does not constrain
  the Lean architecture.
- Git has one unrelated untracked `.DS_Store`; Stage 1 preserves it. Generated
  `.lake/` and `tmp/` trees are ignored through `.gitignore`.
- The paper says diagram time runs left-to-right, whereas ordinary matrix products
  apply the rightmost factor first.

## Updated Assumptions

- A matrix semantics indexed directly by bit assignments remains the leading
  option, because it exposes basis cases without committing the public API to a
  particular natural-number encoding.
- A syntax/semantics split is necessary from the first circuit module because later
  gate counts cannot be recovered from matrices.
- The exact compatible revision is resolved. Candidate unitary, Kronecker,
  reindexing, and L²-operator APIs still require compiling probes before the model
  is frozen.
- The Markdown transcription is a navigation aid; material signs, hypotheses,
  diagrams, and counts must also be checked against the supplied PDF.

## Big Picture Objective

Create a reproducible Lean baseline and enough source/API evidence to choose and
document the foundational model without making downstream paper claims depend on
untested conventions.

## Detailed Implementation Plan

- Inventory all numbered claims, Section 8 constructions, diagrams, and terminology
  changes in the PDF/transcription.
- Select and pin an exact Lean/mathlib pair; create `lean-toolchain`,
  `lakefile.toml`, root `Barenco.lean`, and a minimal `Barenco/Basic.lean` smoke
  module.
- Probe local mathlib definitions for matrices, unitarity, Kronecker products,
  finite linear operators, norms, permutations, and asymptotics.
- Create `docs/conventions.md`, `docs/traceability.md`, `docs/corrections.md`, and
  `docs/axiom-audit.md` with stable row formats and the full initial paper inventory.
- Define and run focused/full build, forbidden-hole, axiom, and diff checks.
- Track the resolved manifest and verify generated dependency/render files remain
  excluded from source and proof-hole audits.
- Record the selected Stage 2 representation and rejected alternatives with
  concrete API/build evidence.

Expected tracked changes: Lean project/source files, `lake-manifest.json`,
`.gitignore`, the four docs, this stage file, and updates to `goal-1/0-plan.md` after
verification.

## No-Cheating Checks

- The smoke build must import the pinned mathlib dependency, not a globally mutable
  checkout.
- No theorem is accepted merely because `native_decide` or finite enumeration
  succeeds for a few dimensions; examples are sanity checks only.
- Traceability inventory includes hard/unresolved claims, important unnumbered
  claims, all sixteen diagrams, and Section 8 heuristics, not only claims selected
  for early implementation.
- Conventions are backed by executable basis-order/composition probes before later
  circuit proofs use them.
- Search tracked Lean sources for forbidden holes and unexplained custom axioms.

## Completion Requirements

- [ ] Exact Lean and mathlib revisions are pinned and documented.
- [ ] The resolved manifest is tracked; generated `.lake/` and render scratch are
  ignored and absent from source audits.
- [ ] `lake build` succeeds twice from unchanged sources.
- [ ] The root module and smoke module compile without proof holes.
- [ ] Candidate mathlib APIs and the chosen foundational representation are
  recorded with compiling evidence.
- [ ] Conventions cover basis/wire order, execution/multiplication order, controls,
  phase relations, norm, ancilla contracts, and both cost models.
- [ ] Traceability inventories every numbered Section 4–7 result, important
  unnumbered definitions/constructions/external claims, all sixteen diagrams, and
  each distinct Section 8 construction, upper bound, and heuristic lower-bound claim.
- [ ] Correction and axiom-audit logs exist with explicit evidence/status formats.
- [ ] Focused/full builds, hole/axiom searches, and `git diff --check` are recorded.

## Stage Results

- In progress. Populate with exact commands, outputs, representation decision,
  source discrepancies, risks, and next-stage changes before marking complete.
