# 9-AUDIT

Status: in progress (2026-07-11).

## Current Facts

- Stages 1--8 are complete.  The original three-part objective now has public
  certified two-wire semantics/syntax, a payload-preserving exact optimizer, and
  named tested outputs for relative-Toffoli cost three, the general Gray merger,
  and the corrected Corollary 7.4 merger.
- The strongest checked Corollary 7.4 output has balanced profile
  `(24n-102,24n-100,48n-202)` for every `n>=7`.  The paper's `48n-204` is not
  recovered and is not refuted.  The final trace theorem preserves the complete
  coherent mixed-orientation raw CNOT schedule, not an unstated orientation.
- The complete Corollary result is an explicit emitted list assembled from
  certified normalization subpasses and an avoiding-middle inverse deletion.  It
  has no advertised global fixed-point, canonicality, completeness, minimality,
  or lower-bound theorem.
- `Barenco.lean` exports the stable Goal 2 surface and excludes all diagnostic
  example modules.  `Barenco/AxiomAudit.lean` contains 480 maintained checks;
  `docs/axiom-audit.md` contains 480 matching declaration rows.  The source tree
  contains 145 Lean files below `Barenco/`.
- The final Stage 8 focused build passed with 3,496 jobs and its adjacent/public/
  audit builds passed with 3,617 jobs.  Twelve Stage 8/root/audit files passed
  strict and trust-zero compilation, and all Stage 8 forbidden/no-cheating scans
  and `git diff --check` passed.
- README, traceability, corrections, conventions, final report, and axiom-audit
  documentation are synchronized at the Stage 8 boundary.  The disposable
  256-orientation exploration is explicitly excluded from completion evidence.

## Updated Assumptions

- No additional mathematical or compiler implementation is expected unless the
  release audit exposes a concrete mismatch or regression.
- A cached/incremental green build is not the final clean-room build.  Stage 9
  must delete only generated Lake artifacts with `lake clean`, rebuild the public
  target from scratch, then explicitly rebuild root-excluded diagnostics and the
  axiom audit.
- Documentation claims must be rechecked against actual declarations and imports;
  matching prose from Stage 8 is not itself proof of release completion.
- The unresolved paper constant remains visible as future work, but resolving it
  is not silently made a Stage 9 requirement after the named construction has
  received the permitted “not recovered” outcome.

## Big Picture Objective

Deliver a release-grade audit of Goal 2: reconcile the complete public and
diagnostic surface, prove all original objective items have current authoritative
evidence, run clean and trust-boundary verification, and leave the final report,
stage ledgers, and persistent goal status in exact agreement.

## Detailed Implementation Plan

1. Reconcile every Goal 2 success metric and stage completion requirement against
   current Lean declarations, imports, diagnostics, documentation, and command
   evidence.  Treat missing or indirect evidence as incomplete.
2. Verify the public/diagnostic boundary and representative downstream workflows:
   ordered two-wire embedding/syntax, fusion/normalization, relative-Toffoli cost
   three, Gray boundaries, and Corollary 7.4 boundaries.
3. Run `lake clean` followed by the default full public build.  Then run a focused
   post-clean build of the representative diagnostics, public root, and axiom
   audit so root-excluded code is not mistaken for covered code.
4. Directly compile the public root, audit, and representative diagnostics with
   warning-as-error and trust level zero.  Record the exact targets and outcomes.
5. Run repository-wide proof-hole/custom-declaration scans, Goal 2 no-cheating
   scans, diagnostic root-exclusion checks, audit/table/file counts, documentation
   path/name/formula consistency checks, and `git diff --check`.
6. Repair only concrete discrepancies.  Any Lean change reopens the relevant
   focused, adjacent, strict, trust-zero, axiom, and clean-build evidence.
7. Record exact release results here and in `0-plan.md`; mark the persistent goal
   complete only after the final requirement matrix has no missing evidence.

## Build Structure

- No new Lean module is planned.  This stage owns release documentation and
  verification only; existing public/runtime/proof-side/diagnostic classifications
  remain those recorded in Stages 2--8.
- Clean public build:
  `lake clean`, then `lake build`.
- Post-clean public/diagnostic/audit build:
  `lake build Barenco.TwoWireCircuitExamples Barenco.FusionExamples
  Barenco.NormalizeExamples Barenco.ThreeQubit.RelativePhaseThreeGateExamples
  Barenco.MultiControl.GrayMergerExamples
  Barenco.MultiControl.Corollary74MergerExamples Barenco Barenco.AxiomAudit`.
- Direct strict and trust-zero targets are the same six representative diagnostic
  files plus `Barenco.lean` and `Barenco/AxiomAudit.lean`.
- A final cached `lake build` after stage/status/documentation edits confirms the
  recorded release tree still matches the compiled tree.

## Boundary Checks

- Public importability is checked independently from diagnostic compilation.
  Root-excluded examples may verify boundaries but never enter `Barenco.lean` or
  `Barenco/AxiomAudit.lean`.
- Exact equality, global phase, input-dependent basis phase, basis behavior,
  measurement equivalence, and classical reversible behavior retain their
  separately named relations.
- Ordered wire orientation, head-first chronology, scalar phase, arbitrary dirty-
  wire input, spectator restoration, and partial cost-model rejection remain
  visible in the public contracts.
- Syntax-derived resource theorems, constructive upper bounds, scoped lower
  bounds, fixed-construction asymptotics, and unresolved/minimality claims remain
  distinct in the final report.
- The Corollary `48n-202` theorem concerns the named emitted circuit.  It neither
  proves the paper's `48n-204` nor rules out another construction achieving it.
- Existing recursive resource theorems remain attached to the raw Corollary
  substitution; no optimized constant is transferred without new syntax.

## No-Cheating Checks

- Scan all project Lean sources for `sorry`, `admit`, `by?`, `native_decide`,
  `bv_decide`, `sorryAx`, `implemented_by`, actual custom `axiom`, and actual
  `opaque` declarations; classify comment-only matches explicitly.
- Scan Goal 2 runtime/public leaves for `Primitive.unclassified`, forged
  `Primitive.mk`/arbitrary-two-qubit metadata, whole-circuit exact-Toffoli choice,
  runtime `Classical.choose`/`Classical.choice`, matrix-equality decisions,
  hard-coded disputed formulas or low-width branches, and tracing commands.
- Confirm all arbitrary-two-qubit matches are trusted constructors, kind/cost
  theorems, or explicitly accepted model statements; the Corollary output must
  still have theoremized U(4) count zero.
- Confirm every audit result uses only documented standard foundations and that
  source/table counts agree exactly.
- Confirm the unmaintained 256-case exploration is absent from release evidence.

## Completion Requirements

- [ ] Every original Goal 2 success metric and all three test-case outcomes have
  direct current source/build/documentation evidence.
- [ ] Stable public imports and all representative root-excluded workflows compile;
  diagnostics remain absent from root and audit imports.
- [ ] README, traceability, correction log, conventions, final report, axiom audit,
  `0-plan.md`, and all completed stage files agree on formulas and statuses.
- [ ] A clean default build and post-clean public/diagnostic/audit build pass with
  exact commands and job counts recorded.
- [ ] Direct warning-as-error and trust-zero compilation passes for root, audit,
  and all six representative diagnostic files.
- [ ] The maintained axiom audit has matching source/table counts and no
  project-specific foundation.
- [ ] Repository-wide forbidden scans, scoped Goal 2 no-cheating scans,
  root-exclusion checks, documentation consistency checks, and `git diff --check`
  pass with classified expected matches only.
- [ ] The final report contains the completed Goal 2 additions, honest unresolved
  claims, exact/asymptotic resource status, build/axiom results, and future-use
  guidance.
- [ ] `goal-2/0-plan.md`, this stage, and the persistent goal status are marked
  complete only after the requirement-by-requirement audit passes.

## Stage Results

- Stage file created after the completed Stage 8 evidence was folded into
  `goal-2/0-plan.md` and before any Stage 9 clean-build or release-status edit.
- `lake clean` completed successfully, followed by a clean default `lake build`
  from an empty Lake tree.  All 3,623 dependency and public-project jobs passed;
  no cached project artifact was used as release evidence.
- The post-clean build of `TwoWireCircuitExamples`, `FusionExamples`,
  `NormalizeExamples`, `RelativePhaseThreeGateExamples`, `GrayMergerExamples`,
  `Corollary74MergerExamples`, `Barenco`, and `Barenco.AxiomAudit` also passed with
  3,623 jobs.  This separately covers the six representative root-excluded
  workflows that the default public build intentionally omits.
- All eight representative diagnostic/root/audit files passed direct
  `-DwarningAsError=true` compilation and direct
  `-t0 -DwarningAsError=true` compilation.  The audit printed all 480 maintained
  results in both modes; the only dependency sets were `{propext}`,
  `{propext, Quot.sound}`, and
  `{propext, Classical.choice, Quot.sound}`.  No project-specific axiom appears.
- Repository-wide proof-hole and trace scans are empty.  The custom-declaration
  scan has one classified prose-only hit (`Corollary74Fusion.lean:14`, “opaque
  expansion”) and no actual `axiom`/`opaque` declaration.  Scoped runtime scans
  found no whole-circuit exact-Toffoli choice, unclassified/forged primitive,
  runtime classical choice, matrix/unitary equality decision, hard-coded width
  branch, or diagnostic public import.  Three ordinary `decide` calls prove only
  free-group word nonidentity; arbitrary-two-qubit and `48n` hits occur only in
  kind/cost/count theorem statements, and the emitted Corollary U(4) count is zero.
- Audit source/table counts are exactly 480/480, the public tree has 145 Lean files
  below `Barenco/`, Lean is pinned to 4.31.0, and mathlib is pinned to
  `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.  An independent documentation
  audit found every local path and Stage 8 declaration, matched the source/table
  name sets exactly, confirmed every formula/status/trace qualification and the
  unchanged recursive substitution, and found no use of the disposable
  orientation search as evidence.  `git diff --check` passes.
- A final cached default `lake build` after the release-documentation update
  passed with 3,615 jobs, confirming that the recorded public source still matches
  the freshly rebuilt artifacts.
