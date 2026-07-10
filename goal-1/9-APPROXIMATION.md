# 9-APPROXIMATION

Status: in progress (mathematical, circuit, expansion, and resource layers are
implemented; examples, public integration, and final audits remain).

## Current Facts

- The source material is the approximation definition, probability observation,
  and Lemma 7.8 on manuscript pp. 22–24, Markdown lines 770–850. There is no
  circuit diagram. The proof recursively applies Lemma 7.5, stops after an
  integer depth, and replaces the remaining controlled root by identity.
- `operatorDistance A B = ‖A-B‖` fixes mathlib's scoped L2 induced operator norm.
  Metric laws, exact left/right unitary invariance, state-action error, and
  single-outcome bounds are proved in `Barenco.Equivalence.OperatorNorm`.
  `ControlledDistance` proves exact target-block norm preservation and exact
  positive-controlled-versus-target identity distance.
- `powerTwoRoot m U = unitaryRoot (2^m) U` is one coherent principal-spectrum
  sequence. `powerTwoRoot_zero`, `powerTwoRoot_succ_sq`, and
  `powerTwoRoot_operatorDistance_one_le` prove its exact base, adjacent squaring,
  and the stronger arbitrary-finite-dimensional bound
  `operatorDistance (powerTwoRoot m U) I ≤ pi/2^m`.
- Stage 7's exact `recursiveViaSquareCircuit` is the correct recursion dependency;
  the original PDF's reference to Lemma 7.3 is wrong (C-006), while the Markdown
  transcription already says Lemma 7.5. `truncatedRecursiveCircuitFrom` retains
  the first four Lemma 7.5 macros and recursively replaces the fifth, and its
  factorization theorem uses `powerTwoRoot_succ_sq`.
- The principal eigenangle condition is essential. The paper writes eigenvalues
  as `exp(i*d_j)` but does not require `|d_j|≤pi`; without this choice its
  `pi/2^k` estimate is false. This is correction C-007.
- The statement quantifies every `epsilon>0` while writing
  `Theta(n*log(1/epsilon))`. At `epsilon=1` the printed logarithm is zero although
  the displayed depth is `ceil(logb 2 pi)=2`, and the requested depth may exceed
  the controls. `principalRootBoundDepth` is the natural ceiling of
  `logb 2 (pi/epsilon)`. `epsilonSynthesisPrimitiveCircuit` uses literal
  truncation only when that depth fits and otherwise selects the exact recursive
  circuit; it never presents a capped truncation as meeting an uncertified error.
- For source width `n≥7`, the available exact recursion depth is `n-7`. The
  selected circuit meets every positive tolerance, is proved to use the empty
  circuit when `pi≤epsilon`, and falls back to exact synthesis when the requested
  depth is larger than `n-7`.
- `expandedTruncatedRecursiveCircuitFrom` is literal one-qubit/CNOT syntax and
  has exact retained-shell profile
  `(32k²+(64r+200)k, 24k²+(48r+164)k,
  56k²+(112r+364)k)` for residual exact depth `r` and retained depth `k`.
  The cost model accepts exactly the displayed total. Exact completion recovers
  the established full-recursion count at combined depth `r+k`.
- `EventProbability` proves a cardinality-free constant-one probability bound for
  every finite computational-basis event on unitary images of a common
  norm-at-most-one pure input. The paper's `2*epsilon` statement is retained as a
  weaker corollary. Neither theorem is generalized to arbitrary POVMs.
- The controlled-distance proof does not expand Euclidean sums manually.
  `Matrix.blockDiagonalRingHom`, `Matrix.blockDiagonal_conjTranspose`, and
  `Matrix.blockDiagonal_injective` package as an injective complex star-algebra
  hom, hence are isometric by `NonUnitalStarAlgHom.norm_map`. The simultaneous
  row/column `Matrix.reindexAlgEquiv` likewise packages as a star-algebra
  equivalence and preserves the L2 operator norm. Their composition gives
  `‖targetBlockRaw target F‖=‖F‖`, from which exact controlled-target distance is
  a finite Pi-norm calculation once one active complementary assignment is named.
- The ordinary `Matrix` L2 norm and `CStarMatrix` functional-calculus wrappers are
  bridged by a file-local C-star instance and the existing identity star-algebra
  equivalence; no global norm instance or project axiom is added.
- A general controlled predicate needs an explicit active-block witness for exact
  distance equality; positive controls discharge it with the all-true
  complementary assignment.
- For residual exact depth `r` and retained depth `k`, use a layout with
  `(r+6)+k` controls, hence logical source width `r+k+7`. The Nat-safe exact
  retained-shell profile is
  `(32*k^2+(64*r+200)*k, 24*k^2+(48*r+164)*k,
  56*k^2+(112*r+364)*k)`. Adding the established residual exact circuit recovers
  the full depth-`r+k` count componentwise. The selected source-width total is at
  most `440+112*n*min(principalRootBoundDepth epsilon,n-7)`, and
  `epsilonSynthesisTotalCountAtWidth_lt_logarithmic` proves the explicit
  construction-specific logarithmic upper bound under `0<epsilon≤1`.

## Source Claim Audit

| Claim | Source content | Audited status and routing |
|---|---|---|
| Approximation definition | Distance induced by Euclidean vector norm between unitaries. | Corrected and proved as the L2 induced operator norm `operatorDistance`, including exact controlled-target distance; no Frobenius norm is substituted. |
| Probability observation | Any measured event changes probability by at most `2*epsilon`. | Corrected and proved for norm-at-most-one pure inputs and finite computational-basis events. A stronger constant-one theorem and the source-facing constant-two corollary are exported; arbitrary POVMs remain outside scope. |
| Lemma 7.8 algebra | Coherent roots satisfy `V_(k+1)^2=V_k` and `‖V_k-I‖≤pi/2^k`. | Corrected and proved for the selected principal power-of-two sequence in arbitrary finite dimension. |
| Lemma 7.8 circuit | Stop the Lemma 7.5 recursion after `k` levels and omit the remaining controlled root. | Corrected and proved with literal macro and one-qubit/CNOT syntax, exact residual factorization, exact controlled-distance reduction, and `pi/2^k` error. |
| Lemma 7.8 resources | Claimed `Theta(n log(1/epsilon))` for all `epsilon>0`. | Corrected and proved as exact depth-indexed syntax counts plus a piecewise selector with exact fallback. A capacity-aware uniform upper and an explicit `0<epsilon≤1` logarithmic upper are exported; no optimal `Theta` claim is made. |

## Implemented Lean Architecture

- `Barenco/OneQubit/CoherentRoots.lean`: principal power-of-two root sequence,
  adjacent squaring, scalar/eigenphase bounds, and exact
  `operatorDistance(root m U, I)≤pi/2^m` for arbitrary finite-dimensional
  unitaries, with CFC implementation details below a small public API.
- `Barenco/Equivalence/ControlledDistance.lean`: exact operator-distance equality
  between controlled blocks and their target matrices, including the
  block-diagonal/reindex norm lemmas used by truncation.
- `Barenco/Equivalence/EventProbability.lean`: computational-basis event
  probability for pure states, the cardinality-free constant-one bound, and the
  paper-facing constant-two corollary.
- `Barenco/MultiControl/Approximate.lean`: depth-indexed truncated Lemma 7.5 macro
  syntax, exact evaluator factorization against the omitted residual controlled
  root, and the semantic operator-error theorem.
- `Barenco/MultiControl/ApproximateExpansion.lean`: every retained macro is
  replaced by selected one-qubit/CNOT syntax under explicit depth/width
  inequalities, with evaluator preservation and exact component/total/cost sums.
- `Barenco/MultiControl/ApproximationResources.lean`: epsilon/depth selection,
  legal cap, exact-fallback statement, and construction-specific asymptotic upper
  language, including explicit large-epsilon and insufficient-width branches.
- `Barenco/MultiControl/ApproximationExamples.lean`: planned root-excluded
  zero-depth, maximum-depth, large-epsilon, and width-seven fallback diagnostics.

## Detailed Implementation Plan

1. Source, CFC/root, controlled-block norm, event-probability, truncated-circuit,
   and exact-count audits are complete.
2. Coherent principal roots and their operator-distance decay are proved
   independently of circuit syntax.
3. Controlled-unitary versus identity distance is proved exactly on arbitrary
   ambient layouts.
4. The truncated macro recursion carries explicit current-root, retained-depth,
   and residual-control indices and has an exact full-register factorization.
5. Literal one-qubit/CNOT expansion preserves the macro evaluator and has exact
   syntax-derived component, total, completion, and accepted-cost formulas.
6. The natural-ceiling epsilon selector, capacity test, exact fallback, selected
   count linkage, uniform bound, and small-error logarithmic upper are proved.
7. Constant-one and paper-facing constant-two finite computational-basis-event
   consequences are proved for the selected circuit.
8. Boundary diagnostics, public integration, documentation/audit synchronization,
   and the final verification protocol remain.

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
  proved epsilon-error theorem with explicit integer depth and capacity branch.
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
- `CoherentRoots` proves one named principal power-of-two root sequence, exact
  adjacent squaring, and `pi/2^m` L² operator-distance decay in arbitrary finite
  dimension.
- `ControlledDistance` proves exact target-block norm preservation and reduces
  positive-controlled identity distance exactly to the one-qubit target.
- `EventProbability` proves a cardinality-free constant-one bound for finite
  computational-basis events and the source-facing constant-two corollary under
  explicit pure-input hypotheses.
- `Approximate` defines literal retained-shell truncation and proves exact
  arbitrary-register residual factorization, exact residual-root error, and the
  `pi/2^k` bound. Appending the residual controlled macro is exactly correct.
- `ApproximateExpansion` replaces every retained macro by literal one-qubit/CNOT
  syntax, preserves the evaluator and residual error, derives exact retained and
  completed counts/costs, and provides an exact primitive completion.
- `ApproximationResources` proves the natural-ceiling depth characterization,
  large-epsilon zero-depth case, exact-fallback selector for insufficient width,
  every-positive-epsilon operator bound, selected finite-event bounds, exact
  syntax/count/cost linkage, the uniform
  `440+112*n*min(principalRootBoundDepth epsilon,n-7)` upper bound, and the
  explicit `0<epsilon≤1` logarithmic-regime upper theorem.
- Boundary examples, public-root/audit integration, final scans, and full builds
  remain before this stage can be marked complete.
