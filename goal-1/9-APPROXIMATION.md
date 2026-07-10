# 9-APPROXIMATION

Status: in progress (source/API/architecture audit; no Stage 9 Lean module has
been added yet).

## Current Facts

- The source material is the approximation definition, probability observation,
  and Lemma 7.8 on manuscript pp. 22–24, Markdown lines 770–850. There is no
  circuit diagram. The proof recursively applies Lemma 7.5, stops after an
  integer depth, and replaces the remaining controlled root by identity.
- `operatorDistance A B = ‖A-B‖` already fixes mathlib's scoped L2 induced
  operator norm. Metric laws, exact left/right unitary invariance, state-action
  error, and a `2*distance` bound for one computational-basis outcome are proved
  in `Barenco.Equivalence.OperatorNorm`.
- `OneQubit.unitaryRoot k U` uses principal arguments on the finite spectrum and
  proves exact positive-power equations. `unitaryRoot (2^m) U` is therefore the
  right candidate for a coherent sequence, but the current public API proves only
  each power equation independently. Adjacent squaring and distance-to-identity
  remain obligations.
- Stage 7's exact `recursiveViaSquareCircuit` is the correct recursion dependency;
  the paper's reference to Lemma 7.3 is wrong (C-006). Its parameterized evaluator
  accepts any explicit square equation, so a coherent direct-root sequence can be
  used without redefining exact multi-control semantics.
- The principal eigenangle condition is essential. The paper writes eigenvalues
  as `exp(i*d_j)` but does not require `|d_j|≤pi`; without this choice its
  `pi/2^k` estimate is false. This is correction C-007.
- The statement quantifies every `epsilon>0` while writing
  `Theta(n*log(1/epsilon))`. For `epsilon≥1`, that expression is nonpositive or
  degenerate; the displayed ceiling can also exceed the number of recursive
  levels. A corrected theorem must expose integer depth, cap it by available
  controls, and use exact synthesis as fallback when the requested error is below
  what the truncated depth can certify. This is correction C-008.
- For source width `n≥7`, an approximate truncation can recurse only while the
  corrected Corollary 7.4 prefix-X expansion is legal. If `k` levels are executed
  and the residual controlled root is omitted, a natural safe domain is
  `k≤n-7`; exact synthesis of the residual width-seven base is the fallback.
- One primitive recursion level at current logical width `w≥8` consists of two
  selected controlled-root circuits and two prefix-MCX expansions, with exact
  profile `(64w-280,48w-196,112w-476)`. Summing `k` descending levels should give
  total `k*(112*n-476)-56*k*(k-1)`; this is an audit target until derived from
  literal syntax.
- The paper's “any event” probability claim is stronger than the existing
  per-coordinate theorem. It is mathematically recoverable for a normalized pure
  input and a computational-basis event by treating event restriction as an
  orthogonal projection/contraction; summing the coordinate theorem would give a
  spurious event-cardinality factor and is not acceptable.

## Source Claim Audit

| Claim | Source content | Audited status and routing |
|---|---|---|
| Approximation definition | Distance induced by Euclidean vector norm between unitaries. | Already corrected/proved as the L2 induced operator norm `operatorDistance`; retain exact metric scope and never substitute Frobenius norm. |
| Probability observation | Any measured event changes probability by at most `2*epsilon`. | Prove for normalized pure inputs and computational-basis events using a contraction/projection argument. Keep it distinct from arbitrary POVMs and from `AllMeasurementEq`. |
| Lemma 7.8 algebra | Coherent roots satisfy `V_(k+1)^2=V_k` and `‖V_k-I‖≤pi/2^k`. | Prove for the selected principal power-of-two roots, with the eigenphase branch explicit in the construction. |
| Lemma 7.8 circuit | Stop the Lemma 7.5 recursion after `k` levels and omit the remaining controlled root. | Define literal truncated syntax, prove exact evaluator factorization, controlled-block distance equality, and final error at most the residual root distance. |
| Lemma 7.8 resources | Claimed `Theta(n log(1/epsilon))` for all `epsilon>0`. | Replace by exact depth-indexed component/total counts and a construction-specific upper theorem. State the logarithmic regime and depth cap; use the already checked exact circuit as fallback. Do not claim an optimal lower bound. |

## Proposed Lean Architecture

- `Barenco/OneQubit/CoherentRoots.lean`: principal power-of-two root sequence,
  adjacent squaring, scalar/eigenphase bounds, and exact
  `operatorDistance(root m U, I)≤pi/2^m` for finite one-qubit unitaries. Keep CFC
  implementation details below a small public API.
- `Barenco/Equivalence/ControlledDistance.lean`: exact operator-distance equality
  between controlled blocks and their target matrices, including identity, plus
  any block-diagonal/reindex norm lemmas needed by the truncation proof.
- `Barenco/Equivalence/EventProbability.lean`: computational-basis event
  probability for normalized pure states and the cardinality-free
  `2*operatorDistance` bound via a proved contraction.
- `Barenco/MultiControl/Approximate.lean`: depth-indexed truncated Lemma 7.5 macro
  syntax, exact evaluator factorization against the omitted residual controlled
  root, and the semantic operator-error theorem.
- `Barenco/MultiControl/ApproximateExpansion.lean`: replace every retained macro
  by selected one-qubit/CNOT syntax under explicit depth/width inequalities and
  prove evaluator preservation plus exact component/total/cost sums.
- `Barenco/MultiControl/ApproximationResources.lean`: epsilon/depth selection,
  legal cap, exact-fallback statement, and construction-specific asymptotic upper
  language. Avoid a total natural-number logarithm that hides large-epsilon or
  insufficient-width cases.
- `Barenco/MultiControl/ApproximationExamples.lean`: root-excluded zero-depth,
  maximum-depth, large-epsilon, and width-seven fallback diagnostics.

The audit may split or rename leaves after checking mathlib's CFC, spectral norm,
projection, ceiling, and logarithm APIs. Any architecture change must be recorded
here before implementation.

## Detailed Implementation Plan

1. Complete independent source, CFC/root, controlled-block norm, event-probability,
   truncated-circuit, and exact-count audits.
2. Prove coherent principal roots and their operator-distance decay independently
   of circuit syntax.
3. Prove controlled-unitary versus identity distance is exactly the target
   distance on arbitrary ambient layouts.
4. Define the truncated macro recursion with explicit current root index, retained
   depth, residual control count, and full-register evaluator factorization.
5. Combine the preceding layers into an exact depth-indexed approximation theorem.
6. Expand retained macros into one-qubit/CNOT syntax and derive exact component,
   total, and accepted-cost formulas from the circuit representation.
7. Select a legal depth from epsilon in a clearly stated regime, cap it by the
   available recursion, and package exact fallback for smaller epsilon.
8. Prove the arbitrary computational-basis event probability consequence, add
   boundary diagnostics, then integrate root/docs/traceability/corrections/audit
   and run the full verification protocol.

## Boundary and No-Cheating Checks

- Coherence is an exact adjacent-square theorem for one named root sequence, not a
  collection of unrelated existential roots.
- The `pi/2^k` theorem identifies the principal eigenangle choice or an equivalent
  checked spectral construction.
- Approximation error uses the L2 induced operator norm already fixed by
  `operatorDistance`; no entrywise, Frobenius, or ambiguous norm enters.
- Truncation is a literal circuit obtained by omitting the residual controlled
  root. Error is not asserted from a resource recurrence or diagram prose.
- Every recursive depth is bounded by available controls and every primitive
  expansion by its `n≥7` dependency threshold.
- Large epsilon, zero depth, maximum truncated depth, and exact fallback are
  explicit cases; `log(1/epsilon)` is never treated as positive without proof.
- Event probability is cardinality-free because event restriction is proved
  contractive, not because per-outcome bounds are summed.
- Exact counts come only from circuit syntax. `Theta` is not exported without a
  matching lower bound in the same target, error, width, and cost model.
- No `Primitive.unclassified`, semantic dummy, hard-coded full matrix, `sorry`,
  `admit`, `by?`, custom `axiom`, `opaque`, `native_decide`, or `bv_decide` may
  occur in completed Stage 9 modules.

## Completion Requirements

- [ ] Principal power-of-two roots are coherent and have a proved
  `pi/2^k` operator-distance bound.
- [ ] Controlled-block distance is linked exactly to target distance.
- [ ] Truncated recursive syntax has an exact arbitrary-register evaluator and a
  proved epsilon-error theorem with explicit integer depth and cap.
- [ ] Primitive expansion has exact component/total/cost counts and a corrected
  construction-specific `n`/epsilon upper bound with exact fallback.
- [ ] Any-event probability error is proved for its precise pure-state and
  computational-basis-event hypotheses.
- [ ] Zero/maximum depth, large-epsilon, and smallest-width diagnostics compile.
- [ ] C-006–C-008, traceability, conventions, axiom audit, this file, and
  `0-plan.md` are synchronized; focused/adjacent, strict/trust-zero, forbidden,
  diff, two full-build, and axiom-audit evidence is recorded.

## Stage Results

- Stage file created before Stage 9 implementation. Initial audit separates the
  coherent-root, controlled-distance, truncated-syntax, resource, epsilon-domain,
  and event-probability obligations and fixes the safe raw count target above.
