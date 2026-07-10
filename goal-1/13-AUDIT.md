# 13-AUDIT

Status: in progress.

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

- [ ] Every traceability and correction entry matches the current compiled API.
- [ ] All sixteen diagrams have a final layer-by-layer classification.
- [ ] Every exact/asymptotic/minimality resource claim has a final classification.
- [ ] `README.md` provides usable imports, conventions, examples, and navigation.
- [ ] A detailed final report contains every deliverable requested by the user.
- [ ] Public/diagnostic module boundaries and documentation links are verified.
- [ ] Pinned Lean/mathlib versions, focused/full builds, strict/trust-zero checks,
  forbidden scans, and the 319-entry axiom audit are recorded accurately.
- [ ] `goal-1/0-plan.md`, this stage file, and the persistent goal status agree.

## Stage Results

- Stage file created before final-audit implementation. Independent coverage,
  diagram, resource, and release audits are beginning from the compiled Stage 12
  state.
