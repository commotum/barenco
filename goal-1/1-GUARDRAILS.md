# 1-GUARDRAILS

Status: completed 2026-07-09.

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
- Keep the resolved manifest as a versionable project artifact and verify generated dependency/render files remain
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

- [x] Exact Lean and mathlib revisions are pinned and documented.
- [x] The resolved manifest is present as a versionable project artifact; generated `.lake/` and render scratch are
  ignored and absent from source audits.
- [x] `lake build` succeeds twice from unchanged sources.
- [x] The root module and smoke module compile without proof holes.
- [x] Candidate mathlib APIs and the chosen foundational representation are
  recorded with compiling evidence.
- [x] Conventions cover basis/wire order, execution/multiplication order, controls,
  phase relations, norm, ancilla contracts, and both cost models.
- [x] Traceability inventories every numbered Section 4–7 result, important
  unnumbered definitions/constructions/external claims, all sixteen diagrams, and
  each distinct Section 8 construction, upper bound, and heuristic lower-bound claim.
- [x] Correction and axiom-audit logs exist with explicit evidence/status formats.
- [x] Focused/full builds, hole/axiom searches, and `git diff --check` are recorded.

## Stage Results

### Reproducible project

- Pinned Lean to `leanprover/lean4:v4.31.0` and mathlib to exact commit
  `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`. `lake-manifest.json` resolves all
  transitive revisions. `.lake/` and `tmp/` are ignored; the unrelated `.DS_Store`
  was preserved.
- The official mathlib v4.31.0 release and its matching toolchain were checked
  before project creation. The first build caught and repaired Lean 4.31's rule
  that `import` commands precede module documentation.

### Source and convention evidence

- Audited all 31 PDF pages and the Markdown index. Relevant manuscript pages were
  rendered and visually inspected for matrix signs, wire positions, labels, and
  gate order; render scratch was removed afterward.
- Confirmed the source's row-vector/right-action convention despite ket notation.
  `Barenco.fromPaper` is transpose, `fromPaper_mul` proves product reversal, and
  `fromPaper_mem_unitaryGroup_iff` proves unitarity preservation/reflection.
- Selected `Basis n := Fin n → Bool`, standard column-vector matrix semantics, wire
  zero at the top/leftmost bit, and chronological circuit lists. `basisIndex` checks
  `00,01,10,11 ↦ 0,1,2,3`; `evalGates_pair` and `evalGates_append` prove execution
  order rather than relying on comments.
- Rejected `Fin (2^n)` as the core basis because it obscures arbitrary wire updates;
  rejected `BitVec n` as the core because selected-wire/complement splits are less
  direct. Both remain planned bridge types for lexicographic matrices and Gray code.

### API probes and risks

- `Barenco/ApiSmoke.lean` compiles certified identity/Kronecker unitaries, matrix
  reindexing as an algebra equivalence, permutation-matrix action orientation,
  selected-wire splitting, and L² operator-norm submultiplicativity.
- Mathlib has no ready quantum-circuit/Gray-code framework. General unitary roots,
  normal-unitary spectral decomposition, Givens/two-level synthesis, and
  operator-error-to-measurement bounds remain substantive later stages.
- The correction log records fourteen initial issues, including Corollary 7.4's
  invalid `n=7` partition and arithmetic remainder, Lemma 7.8's missing branch/depth
  conditions, cost-model drift, unsupported six-U(4)-gate surjectivity, and
  conjectural dimension counting.

### Verification evidence

- `lake env lean Barenco/Basic.lean`: success.
- `lake env lean Barenco/ApiSmoke.lean`: success.
- `lake env lean Barenco/AxiomAudit.lean`: only `propext`, `Classical.choice`, and
  `Quot.sound` reported for the four audited exports; no project axiom.
- `lake build`: success twice from unchanged sources, 2,360 jobs each.
- Project Lean-source searches found no `sorry`, `admit`, `by?`, `native_decide`,
  `bv_decide`, project `axiom`, or `opaque` declaration.
- `git diff --check`, a trailing-whitespace scan, manifest revision check, and a
  script confirming all sixteen image filenames occur in traceability succeeded.

### Fold-forward decision

Stage 2 should retain the raw `Gate` matrix for algebra and introduce certified
unitary/local-gate structures plus syntactic circuits separately. Basis-action
matrices should define embeddings and controls directly; Kronecker/reindexing can
then be proved equivalent for contiguous cases instead of determining the API.
