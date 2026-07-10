# Goal 2 Execution Loop

Use this protocol for every implementation session. `goal-2/0-plan.md` is the
authoritative objective and stage map. `BUILD-PLAN.md` is the repository-wide Lean
build and module-structure protocol. A stage file records the actual evidence for
one stage; neither a chat summary nor a green build substitutes for it.

## Required Reading Order

Before changing Lean code:

1. Read `goal-2/0-plan.md` completely.
2. Read this file completely.
3. Read `BUILD-PLAN.md` completely.
4. Find the first incomplete stage in the Stage Index.
5. Read that stage file and the previous completed stage file, if they exist.
6. Inspect the current code, imports, tests, documentation, and Git state relevant
   to the selected stage.

If the current repository contradicts the plan, update the plan and stage facts
before implementation. Never preserve a stale assumption merely because it was
written earlier.

## Repeatable Stage Loop

1. **Sync current state with actual files and tests.** Inspect the relevant APIs,
   source passages, theorem signatures, imports, diagnostics, documentation, and
   working tree. Re-run the smallest baseline checks needed to distinguish a new
   failure from an existing one.
2. **Update `0-plan.md` with current facts before starting the next stage.** Record
   discoveries that change architecture, scope, source interpretation, boundary
   conditions, or dependent work.
3. **Select the first incomplete stage.** Do not skip a prerequisite because a
   later example looks easier. Split a stage only when checked evidence shows that
   its uncertainty or import fanout is too large.
4. **Create or refresh `goal-2/[INDEX]-[SHORTHAND].md` from the stage template.**
   Record current facts, assumptions, ownership, exact target declarations,
   boundary checks, commands, and completion requirements before Lean edits.
5. **Implement only that stage.** Keep changes narrow, classify declarations, and
   follow `BUILD-PLAN.md`. Do not mix speculative test-case optimization into a
   trusted semantic core.
6. **Add verification and no-cheating checks.** Every semantic construction needs
   evaluator or basis-action evidence; every resource result needs countable
   syntax; every optimizer rewrite needs exact soundness; every negative result
   needs a theorem in its stated scope.
7. **Run focused tests, full verification, and whitespace/diff checks appropriate
   to the repository.** Start with the touched leaf and adjacent consumers. Run
   root/full/clean builds when public or high-fanout imports require them. Include
   strict, trust-zero, axiom, forbidden-token, and `git diff --check` evidence.
8. **Record results in the stage file.** List exact declarations, files, commands,
   job counts where reported, outputs, axiom sets, failed routes, and mathematical
   lessons. “Build passed” without the command and coverage is insufficient.
9. **Fold results back into `0-plan.md`.** Mark the stage complete only when every
   completion requirement has evidence. Update current facts, assumptions,
   dependent stages, and the final classification of any paper claim affected.
10. **Continue toward the original objective.** Select the next incomplete stage.
    If stopping for the session, leave the goal resumable with current evidence,
    next experiments, unblock actions, and assumptions to challenge. Do not stop
    merely because one optimization path failed.

## Invariants

- Do not narrow the user's objective without saying so and recording the effect in
  `0-plan.md`.
- Do not mark a stage complete without requirement-by-requirement evidence.
- Do not use a test or green check as evidence unless it covers the requirement in
  question.
- Prefer small, low-complexity stages that reduce mathematical or architectural
  uncertainty.
- Convert blockers into work items: decompose them, test alternative formulations,
  prove a scoped obstruction, or identify the next missing witness.
- Preserve the distinction between implementation, verifier, diagnostic, and
  fallback paths.
- Preserve the distinction among an explicit optimized circuit, a general rewrite
  law, an executable normalizer, a normalizer fixed point, and a global lower bound.
- Treat verified, refuted, and not-recovered as distinct outcomes. A stalled
  normalizer is never a refutation.
- Keep exact equality, global phase, basis-dependent phase, basis behavior, and
  measurement equivalence distinct. The Goal 2 normalizer is exact unless a later
  stage explicitly introduces and proves another relation.
- Keep `oneQubitCNOT` and `arbitraryTwoQubit` costs distinct. A rewrite beneficial
  under one policy may make the other policy unsupported.
- Never infer locality from `Primitive.kind`, `Primitive.support`, or support
  cardinality without a semantic certificate.
- Never emit `Primitive.unclassified` as a fused one- or two-wire gate.
- Never price a semantic product without producing the corresponding output
  circuit syntax.
- Never replace transparent optimizer input with an opaque classical-choice
  witness whose boundary factors cannot be inspected.
- Never hard-code a disputed formula as a count function and use it as evidence
  for the circuit's actual length.
- Preserve ordered wire orientation. The unordered support finset does not identify
  the local `U(4)` basis convention.
- Preserve scalar phases under exact normalization.
- Keep diagnostics and exhaustive probes out of `Barenco.lean` unless a stage
  explicitly promotes a stable API.
- Preserve unrelated user changes and avoid destructive Git operations.

## Lean Verification Baseline

Every stage chooses exact module names in its stage file. The usual command classes
are:

```text
lake build Barenco.Narrow.Leaf
lake build Barenco.Adjacent.Consumer Barenco.AxiomAudit Barenco
lake env lean -DwarningAsError=true Barenco/Narrow/Leaf.lean
lake env lean -t0 -DwarningAsError=true Barenco/Narrow/Leaf.lean
lake env lean -DwarningAsError=true Barenco.lean
lake env lean -t0 -DwarningAsError=true Barenco/AxiomAudit.lean
lake build
git diff --check
```

Run a clean build at the final audit when public/high-fanout changes make cached
evidence inadequate:

```text
lake clean
lake build
```

Search project Lean sources for forbidden shortcuts after every Lean-changing
stage and repository-wide at final audit:

```text
rg -n --glob '*.lean' '\b(sorry|admit|by\?|native_decide|bv_decide|sorryAx|implemented_by)\b' Barenco Barenco.lean
rg -n --glob '*.lean' '^\s*(axiom|opaque)\b' Barenco Barenco.lean
```

An empty `rg` result is expected. Mentions inside planning/documentation guardrails
are not Lean declarations, but stage reports should distinguish such documentation
hits from source hits.

## Claim-Resolution Discipline

For each paper-facing test, record all of the following separately:

- source wording and variable convention;
- exact input circuit chronology;
- target relation: exact equality or a named weaker consequence inherited only
  after an exact optimizer bridge;
- legal wire distinctness and width assumptions;
- named cost model;
- literal output circuit;
- evaluator-preservation theorem;
- component, total, and accepted-cost theorems;
- whether the result verifies, refutes, or merely fails to recover the source
  claim;
- impact on dependent formulas and documentation.

If a source number is not achieved, retain the strongest verified output. Claim
“refuted” only after proving an impossibility theorem covering the same gate
grammar, equality relation, ancillary-wire policy, and cost model.

## Stage File Template

```markdown
# [INDEX]-[SHORTHAND]

Status: not started.

## Current Facts

- Facts from current code, tests, docs, source passages, and previous stage
  results.

## Updated Assumptions

- Assumptions that still look valid.
- Assumptions that changed.
- Assumptions that need tests before being trusted.

## Big Picture Objective

- Restate the stage objective, adjusted for current facts.

## Detailed Implementation Plan

- Concrete code/doc/test changes for this stage.
- Files expected to change.
- New definitions and theorem statements required.
- New tests or commands required.

## Build Structure

- New or touched Lean modules and declaration classifications.
- Why each module owns the declarations placed there.
- High-fanout modules intentionally avoided.
- Focused leaf build command.
- Adjacent consumer, root, audit, strict, and trust-zero builds required.

## Boundary Checks

- Runtime, public-API, proof-side, diagnostic, fallback, and temporary boundaries.
- Exact equality versus any phase-relaxed consequence used by the stage.
- Semantic locality certificate, ordered-pair orientation, and width/distinctness
  domains.
- Supported cost policy, partial-cost behavior, and unsupported-node barriers.
- Ancilla, spectator, control-count, and source-width domains when applicable.

## No-Cheating Checks

- Explicit checks proving the implementation does not route through forbidden
  fallback paths.
- Exact relation, locality evidence, syntax-to-cost linkage, and model boundaries.
- Tests distinguishing a constructive result, a scoped obstruction, and an
  inconclusive optimizer outcome.

## Completion Requirements

- Requirement-by-requirement checks.
- Required theorem signatures and boundary cases.
- Required build, audit, forbidden-scan, and diff commands.
- Documentation and fold-back updates required.

## Stage Results

- Fill in at the end of the stage.
- Include files and declarations added or changed.
- Include exact tests/builds/scans run and outcomes.
- Include axiom-audit results.
- Include what was learned and failed approaches.
- Include what should change in `0-plan.md` before the next stage.
```

## Session Handoff

When a session stops before goal completion, leave:

- the current stage status and last verified commit/worktree facts;
- exact commands most recently run;
- the smallest failing theorem or missing witness;
- relevant Lean error text or mathematical obstruction;
- assumptions already falsified;
- the next one to three concrete experiments;
- whether any paper claim remains verified, refuted, or not recovered;
- no unclassified temporary declaration presented as stable API.
