# Continuation Prompt

```text
Work autonomously through goal-1/0-plan.md using the repeatable protocol in
goal-1/0-loop.md and the Lean module/build requirements in BUILD-PLAN.md.

The objective is to independently reconstruct “Elementary Gates for Quantum
Computation” as a reusable, pinned Lean 4/mathlib library: prove its central gate
identities, circuit decompositions, approximation and universality results, and
all justified resource claims; separate semantic, phase, norm, ancilla, and cost
notions; and maintain complete paper-to-Lean traceability plus a correction log.

Do not use sorry/admit/unexplained axioms, diagrams as proofs, semantic equality as
evidence for resource counts, or silent weakenings. Check the source, conventions,
boundary cases, roots, auxiliary-bit contracts, error metrics, and changed cost
models explicitly. If a paper claim is false or cannot be established, document
the exact obstruction, prove the strongest useful corrected result, and carry its
impact into dependent stages.

At each loop: inspect actual files/tests; update current facts; take the first
incomplete stage; create or refresh its stage file; implement only that stage in
small compiling increments; record module ownership, declaration classifications,
focused/adjacent builds, and boundary checks; add no-cheating verification; record
evidence; fold it into the plan; then continue. Completion means the original
objective is genuinely achieved. Until then, carry open issues forward as explicit
next work with evidence, experiments, assumptions to challenge, and unblock paths.
```
