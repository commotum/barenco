# 13-AUDIT

Status: complete (2026-07-10).

## Starting Evidence

- Stages 1--12 are complete and publicly integrated. The library currently has
  319 maintained `#print axioms` checks, no accepted proof holes or project
  axioms, and consecutive 3,585-job full builds.
- `docs/traceability.md`, `docs/corrections.md`, `docs/conventions.md`, and
  `docs/axiom-audit.md` already carry stage-by-stage evidence, but the final audit
  must reconcile them against the source and actual declarations rather than
  assuming cumulative documentation is complete.
- The repository still needs a user-facing library guide/final report. The empty
  `README.md` is the natural short entry point; a detailed report should remain a
  separate maintained document so build evidence, diagram coverage, exclusions,
  and future-use guidance are not compressed into marketing prose.

## Big Picture Objective

Close paper coverage honestly and deliver a reusable, reproducible library with
an explicit final report, diagram/resource inventory, and release-grade audit.

## Detailed Implementation Plan

1. Re-read the authoritative build plan and reconcile every traceability row,
   correction dependency, theorem status, and Section 8 classification with the
   compiled source tree.
2. Inventory all sixteen source diagrams from the paper assets/Markdown and map
   each to exact circuit syntax, evaluator proofs, wire/restoration results, cost
   theorems, or a precise partial/unresolved/excluded status.
3. Inventory every exact count, upper bound, lower bound, asymptotic statement,
   heuristic, and minimality claim; ensure no semantic equality is presented as a
   resource theorem and no fixed-schedule lower bound is presented as target
   hardness.
4. Write a concise `README.md` library guide and a detailed final report covering
   architecture, conventions, exported APIs, corrections, diagram coverage,
   resource coverage, unresolved claims, builds, axioms, and future-project use.
5. Audit public imports versus root-excluded diagnostics, theorem names,
   documentation links, pinned versions, source/artifact presence, forbidden
   tokens, custom axioms, whitespace, and repository state.
6. Repair only concrete discrepancies found by the audit. If Lean changes are
   needed, keep them narrow, update this stage file first, and rerun focused,
   strict, trust-zero, and two full builds.
7. Mark the stage and persistent goal complete only after every requested final
   report item has evidence and no required work remains.

## Boundary Checks

- “Covered” means a real Lean declaration or an explicit documented status, not a
  suggestive filename or prose analogy.
- Diagram semantics, ancillary-wire contracts, phase relation, and resource layer
  are classified separately when they differ.
- Exact generation, dense generation, primitive availability, synthesis cost, and
  optimality remain distinct.
- The six-`U(4)` architecture, dimension-count heuristic/lower conjecture, merged
  relative-phase cost three, unresolved Corollary 7.4 optimization, and any other
  documented obstruction remain unresolved unless new proof objects are actually
  supplied.
- A green incremental build is not a clean-room build; both are recorded with the
  exact command that was run.
- No `sorry`, `admit`, `by?`, custom `axiom`, `opaque`, `native_decide`, or
  `bv_decide` is permitted in completed project Lean sources.

## Completion Requirements

- [x] Every traceability and correction entry matches the current compiled API.
- [x] All sixteen diagrams have a final layer-by-layer classification.
- [x] Every exact/asymptotic/minimality resource claim has a final classification.
- [x] `README.md` provides usable imports, conventions, examples, and navigation.
- [x] A detailed final report contains every deliverable requested by the user.
- [x] Public/diagnostic module boundaries and documentation links are verified.
- [x] Pinned Lean/mathlib versions, focused/full builds, strict/trust-zero checks,
  forbidden scans, and the 319-entry axiom audit are recorded accurately.
- [x] `goal-1/0-plan.md`, this stage file, and the persistent goal status agree.

## Stage Results

- Reconciled the compiled API against the manuscript, traceability matrix, and
  correction log. The final log contains 35 material corrections or
  clarifications, each with its source, repair or obstruction, dependency impact,
  formal evidence, and status.
- Classified all sixteen source images by proof layer. Thirteen have explicit
  named circuit syntax and evaluator proofs; the controlled-Z image has exact
  arbitrary-register semantic equality but no separate countable circuit; the
  notation figure is realized by general controlled-operation infrastructure;
  and the six-`U(4)` architecture remains explicitly unresolved.
- Reconciled every resource claim without promoting semantic equality to a cost
  theorem. In particular, the fixed schedule has the proved finite sandwich
  `2 * B(k) ≤ exactSynthesisCost k U ≤ 112 * B(k)` and its own `Theta(B(k))`
  theorem, while historical efficiency, source-level gate mergers, target
  minimality, and the dimension heuristic remain excluded or unresolved.
- Added the user-facing `README.md` and `docs/final-report.md`, including the
  requested project structure, public APIs, conventions, diagram/resource
  inventories, corrections, omissions, audit results, and downstream guidance.
- Verified the public/diagnostic boundary and documentation navigation. The final
  tree has 109 Lean files below `Barenco/`; the manuscript has sixteen PNG
  references matching the sixteen extracted PNG assets; root-excluded example
  modules remain outside `Barenco.lean`.
- Ran `lake clean` and then a full build from an empty project build tree:
  3,593 jobs succeeded. A post-clean focused build of
  `Barenco.Universality.ResourceExamples`, `Barenco.AxiomAudit`, and `Barenco`
  succeeded with 3,587 jobs. Strict warning-as-error and trust-zero compilation
  passed for the public root, the axiom audit, and the resource diagnostic.
- Confirmed 319 maintained `#print axioms` checks. Exported headline theorems use
  only `propext`, `Classical.choice`, and `Quot.sound` (often a subset), with no
  project-specific axiom. Repository-wide scans found no `sorry`, `admit`, `by?`,
  `native_decide`, `bv_decide`, `sorryAx`, `implemented_by`, custom `axiom`, or
  `opaque` in project Lean sources; `git diff --check` passed.
