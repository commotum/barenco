# Goal 1 Execution Loop

Use this protocol for every working session on `goal-1`. The plan is authoritative,
but actual files, compiled results, and source evidence override stale prose.

## Repeatable Loop

1. Sync current state with actual files and tests.
2. Update `goal-1/0-plan.md` with current facts before starting the next stage.
3. Select the first incomplete stage.
4. Create or refresh `goal-1/[INDEX]-[SHORTHAND].md` from the stage template.
5. Implement only that stage.
6. Add verification and no-cheating checks.
7. Run focused tests, full verification, and whitespace/diff checks appropriate to
   the repo.
8. Record results in the stage file.
9. Fold results back into `goal-1/0-plan.md`.
10. Continue toward the original objective. If stopping for the session, leave the
    goal in a resumable state with current evidence, next experiments, unblock
    actions, and assumptions to challenge.

## Invariants

- Do not narrow the user's objective without saying so.
- Do not mark a stage complete without evidence.
- Do not use tests or green checks as evidence unless they cover the requirement.
- Prefer small, low-complexity stages that narrow uncertainty.
- Convert blockers into work items: decompose them, route around them, or turn them
  into proof and verification tasks.
- Preserve the distinction between implementation, verifier, diagnostic, and
  fallback paths.
- Read the paper claim and its dependencies before formalizing it; do not rely on
  the transcription's paraphrase alone when a symbol, sign, count, or diagram is
  material.
- Keep the project compiling after each small edit. Failed experiments belong in
  scratch files or stage evidence, not completed public modules.
- A semantic theorem cannot certify a structural cost; a basis-state check cannot
  certify a linear operator identity without an extensionality argument.
- Update traceability and corrections in the same stage as the corresponding
  mathematical decision.

## Verification Layers

For each construction, record which layers are actually complete:

1. Algebraic gate/matrix identity.
2. Circuit evaluator correctness on the full register.
3. Preservation of untouched wires and restoration of auxiliaries.
4. Exact resource count in a named syntax/cost model.
5. Asymptotic bound under explicit parameters and primitive assumptions.

Do not promote completion at one layer into a claim about a later layer.

## Standard Session Checks

- Focused module build or `lake env lean <file>` for changed modules.
- Full `lake build` after focused checks.
- Search completed Lean sources for `sorry`, `admit`, `by?`, and project-specific
  `axiom`/`opaque` declarations.
- Run the maintained headline `#print axioms` audit.
- Run `git diff --check` and inspect `git status --short` without modifying
  unrelated user changes.
- Compare changed traceability/correction rows with the theorem statements and the
  exact source locations they cite.

## Stage File Template

```markdown
# [INDEX]-[SHORTHAND]

## Current Facts

- Facts from current code, tests, docs, and previous stage results.

## Updated Assumptions

- Assumptions that still look valid.
- Assumptions that changed.
- Assumptions that need tests before being trusted.

## Big Picture Objective

- Restate the stage objective, adjusted for current facts.

## Detailed Implementation Plan

- Concrete code/doc/test changes for this stage.
- Files expected to change.
- New tests or commands required.

## No-Cheating Checks

- Explicit checks proving the implementation does not route through forbidden fallback paths.

## Completion Requirements

- Requirement-by-requirement checks.
- Required test commands.
- Documentation updates required.

## Stage Results

- Fill in at the end of the stage.
- Include tests run and outcomes.
- Include what was learned.
- Include what should change in `0-plan.md` before the next stage.
```

