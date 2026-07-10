# Correction and Clarification Log

Every entry records a material difference between the manuscript and the formalized
statement. “Open” means the repair is identified but not yet machine checked.

## Entry Format

- **Source:** exact manuscript location.
- **Issue:** what is false, ambiguous, missing, or convention-dependent.
- **Repair:** strongest currently justified replacement.
- **Dependent impact:** claims that must use the repair.
- **Formal evidence:** Lean names/build evidence once available.
- **Status:** open, corrected and proved, partial, excluded, or unresolved.

## C-001 — Undefined subscript in the controlled-gate definition

- **Source:** manuscript p. 6, definition of `∧ₘ(U)`; Markdown lines 96–104.
- **Issue:** the second output ket in the active branch is printed with
  `x₁,…,xₙ,1`, although only `x₁,…,xₘ,y` were introduced. This is an indexing typo.
- **Repair:** use `x₁,…,xₘ,1`. The Markdown transcription already makes this silent
  correction.
- **Dependent impact:** foundational basis-action definition only.
- **Formal evidence:** `Barenco.positiveControlledRaw_truthTable` gives the corrected
  arbitrary-width basis action; `positiveControlledRaw_mem_unitaryGroup` proves the
  resulting matrix is unitary for unitary `U`.
- **Status:** corrected and proved at the reusable semantic level; the later
  paper-order wrapper will only add notation/lexicographic presentation.

## C-002 — Row action hidden behind ket notation

- **Source:** manuscript pp. 6–10, especially the coefficients `u[y,0]`, `u[y,1]`,
  the statement that diagrams execute left-to-right, and products such as
  `A·X·B·X·C` in Lemma 5.1.
- **Issue:** the paper consistently acts on basis rows from the right, despite ket
  notation normally suggesting column vectors. Directly copying its matrices into
  standard Lean `mulVec` semantics would transpose actions and reverse identities.
- **Repair:** the public library uses standard column semantics and translates a
  source matrix `P` as `Pᵀ`. Chronological circuit evaluation left-multiplies gates,
  so transposition converts the paper's chronological products exactly.
- **Dependent impact:** every paper matrix and diagram, especially Sections 4–7.
- **Formal evidence:** `Barenco.fromPaper_apply`, `Barenco.fromPaper_mul`,
  `Barenco.fromPaper_mem_unitaryGroup_iff`, `Barenco.evalGates_pair`,
  `Barenco.evalGates_append`, and `Barenco.fromPaper_paperProduct` compile in
  `Barenco.Basic`. Section 4 now keeps the source matrices (`paperRy`, `paperRz`,
  `paperPhase`, `paperX`) separate from the standard-column matrices (`ry`, `rz`,
  `phaseShift`, `sigmaX`). `columnEuler_eq`,
  `columnC_mul_X_mul_columnB_mul_X_mul_columnA`, and
  `specialUnitary_exists_columnChronologicalABC` machine-check the transposed and
  reversed products used by Lemma 4.3. `sigmaXUnitary_eq_pauliX` connects the
  Section 4 matrix to the existing circuit primitive. Section 5's
  `eval_controlledABCCircuit_raw_blocks`, `eval_twoCNOTCircuit_raw_blocks`, and
  `eval_oneCNOTCircuit_raw_blocks` prove the reversed active/inactive products as
  full-register chronological circuit evaluators.
- **Status:** corrected and proved for the convention bridge, Section 4 identities,
  Lemma 4.3's matrix algebra, and all four Section 5 diagrams. Every later paper
  diagram must still use the bridge explicitly; no circuit theorem is inferred
  merely from a subsystem matrix equality.

## C-003 — Corollary 7.4 partition violates Lemma 7.2 at n = 7

- **Source:** manuscript p. 20; Markdown lines 688–700.
- **Issue:** the proof chooses `m₁=⌈n/2⌉` and `m₂=n−m₁−1`. For `n=7`, this gives
  `m₂=2`, but Lemma 7.2 requires each `m≥3`; its formula would misleadingly assign
  zero primitive Toffolis to a nontrivial gate.
- **Repair:** choose `m₁=⌊n/2⌋` and `m₂=n−m₁−1`. For every `n≥7`, both are at least
  three and the same total `8(n−5)` follows.
- **Dependent impact:** Corollary 7.4, Lemmas 7.5/7.9/7.11, Corollaries 7.6/7.10/7.12,
  and Section 8 costs.
- **Formal evidence:** `InwardLadderLayout.slotCount_le_ambientWidth`,
  `inwardLadderCircuit`, `eval_inwardLadderCircuit`, and the exact
  `inwardLadderCircuit_toffoliCount` now establish the Lemma 7.2 ingredient on
  arbitrary layouts. `FourBlockLayout.eval_fourBlockCircuit` proves Lemma 7.3's
  exact dirty-wire composition, and `eval_fourBlockSubstitutionCircuit` provides
  the checked expansion boundary. `balancedLeftTail`, `balancedRightTail`,
  `balancedLayout`, and `balancedCorollary74Circuit` now implement the repaired
  floor partition and concrete ladder substitution, with exact operator equality,
  `n−2` controls, and `8(n−5)` Toffoli macros for every `n≥7`.
- **Status:** corrected and proved, including the contextual and literal primitive
  layers recorded separately under C-004.

## C-004 — Corollary 7.4 remainder has an arithmetic error

- **Source:** manuscript p. 20; Markdown lines 704–712.
- **Issue:** the proof has `8(n−5)=8n−40` Toffolis, says four must be exact, then
  calls the remainder `8n−36`. The correct remainder is `8n−44`.
- **Repair:** use four exact and `8n−44` relative-phase Toffoli occurrences. The
  literal named expansion uses four sixteen-node exact circuits and `8n−44`
  seven-node relative circuits, hence `32n−144` one-qubit gates,
  `24n−100` CNOTs, and `56n−244` total primitives.  The final printed
  `48n−204` does not follow from the erroneous intermediate sentence and must
  be reconstructed by an explicit evaluator-preserving normalization before it
  can be exported.
- **Dependent impact:** exact early-basic count in Corollary 7.4 and leading counts
  derived from it.
- **Formal evidence:** `corollary74Circuit_toffoliCount` and
  `balancedCorollary74Circuit_gateCount` establish `8(n−5)=8n−40` from explicit
  syntax; `balancedLayout_targetWire_not_mem_aImplementation_touchedSupport`
  establishes the phase-ready target exclusion.
  `eval_balancedRelativeCorollary74Circuit`,
  `balancedRelativeCorollary74Circuit_toffoliCount`, and
  `balancedRelativeCorollary74RelativeOccurrenceCount` now prove exact contextual
  semantics with four exact and `8n−44` relative occurrences.
  `eval_balancedExpandedRelativeCorollary74Circuit` and the accompanying syntax
  theorems prove the literal expansion's exact semantics, `32n−144` one-qubit
  count, `24n−100` CNOT count, and `56n−244` accepted total cost. No claim that
  `48n−204` is correct is made.
- **Additional structural requirement:** a generic minimally capacitated Lemma 7.3
  substitution may borrow the final target inside an A ladder, causing additional
  Toffolis to touch it. The repaired balanced partition satisfies a stronger
  capacity inequality that keeps A's borrowed prefix entirely on right-group data
  controls. The later “four exact target occurrences” statement is therefore
  valid, if at all, only for that phase-ready balanced syntax and needs its own
  touched-target theorem.
- **Optimization obstruction:** independent symbolic audits recover the raw
  `56n−244` count but do not recover the printed optimized constant. The obvious
  palindrome-boundary fusions leave central base-Toffoli pairs separated by
  gates using the same target as a control. Disjoint-support commutation therefore
  cannot justify their cancellation. Different coordinated exact-gate
  orientations produce different provisional constants, so none is accepted
  without named normalized syntax and an exact evaluator theorem.
- **Status:** corrected and proved through a literal primitive upper bound;
  optimized source count unresolved.

## C-005 — Quadratic “Theta” is not an optimal-synthesis theorem

- **Source:** Corollary 7.6, manuscript pp. 21–22; lines 724–746.
- **Issue:** the recurrence proves that the displayed recursive construction uses a
  quadratic number of operations. The only general lower bound later proved is
  linear (Lemma 7.7). Thus the paper does not prove that the *minimum* exact cost is
  `Θ(n²)`.
- **Repair:** export an exact/`O(n²)` upper bound for the named construction. Reserve
  `Θ(n²)` for that algorithm's own executed count if both finite bounds are shown;
  state optimal synthesis only between the separately proved linear lower and
  quadratic upper bounds.
- **Dependent impact:** Corollary 7.6, Section 8 per-two-level and total estimates.
- **Formal evidence:** `recursivePrimitiveCircuit` is an explicit one-qubit/CNOT
  syntax whose evaluator is proved exactly. Its structural theorems give
  `32d²+200d+252` one-qubit gates, `24d²+164d+188` CNOTs, and accepted cost
  `56d²+364d+440`, where `d=n−7`. `Resources.lean` proves exact successor
  recurrences, the Nat-safe width form `56n²+636−420n`, and
  `recursivePrimitiveTotalCount_isBigOWith_width` with constant 56. No optimal
  lower bound or two-sided synthesis theorem is exported. The leading constant
  differs from the paper because C-004's advertised optimized Corollary 7.4
  circuit remains unproved; every present coefficient comes from literal checked
  syntax.
- **Status:** corrected and proved as an exact construction count and quadratic
  upper bound; optimal-synthesis `Θ(n²)` intentionally not claimed.

## C-006 — Lemma 7.8 cites the wrong recursive lemma

- **Source:** Lemma 7.8 proof, original PDF p. 23. The original PDF refers to
  Lemma 7.3; the Markdown transcription at line 782 already carries the repaired
  reference to Lemma 7.5.
- **Issue:** Lemma 7.3 is the four-block dirty-wire construction and is not the
  successive-square-root recursion used in Lemma 7.8. The relevant recursive
  identity is Lemma 7.5.
- **Repair:** replace the cross-reference with Lemma 7.5.
- **Dependent impact:** traceability and proof narrative only.
- **Formal evidence:** `truncatedRecursiveCircuitFrom` recursively replaces the
  fifth macro of `recursiveViaSquareCircuit` by the next retained shell.
  `positiveControlledUnitary_eq_residual_mul_eval_truncatedFrom` invokes
  `eval_recursiveViaSquareCircuit_of_sq_eq` with the coherent equation
  `powerTwoRoot_succ_sq`; no Lemma 7.3/FourBlock theorem is a dependency.
- **Status:** corrected and proved. The log preserves the original-PDF discrepancy
  rather than hiding it behind the already normalized Markdown wording.

## C-007 — Lemma 7.8 omits the eigenphase branch needed by its norm bound

- **Source:** manuscript p. 23; Markdown lines 787–830.
- **Issue:** writing unitary eigenvalues as `exp(i dⱼ)` does not determine `dⱼ`.
  The estimate `‖Dₖ-I‖≤π/2^k` needs representatives with `|dⱼ|≤π` (or an equivalent
  principal-argument choice).
- **Repair:** choose eigenangles in a principal interval. The exact root layer may
  construct each positive root independently, but Lemma 7.8 additionally needs a
  coherent power-of-two sequence, its adjacent squaring equations, and the
  operator-distance bound to the identity.
- **Dependent impact:** Lemma 7.8 error and depth bounds; general root API.
- **Formal evidence:** for every finite complex unitary matrix and `0 < k`,
  `unitaryRoot` chooses the principal-argument spectral root and
  `unitaryRoot_pow` proves its exact `k`th power is the input. The named sequence
  `powerTwoRoot` satisfies `powerTwoRoot_zero` and the exact adjacent equation
  `powerTwoRoot_succ_sq`. `unitaryRootScalar_pow_two_distance_one_le` proves the
  scalar principal-angle estimate, and the stronger finite-dimensional theorem
  `powerTwoRoot_operatorDistance_one_le` proves
  `operatorDistance (powerTwoRoot m U) I ≤ pi / 2^m`. The finite-spectrum
  continuous-functional-calculus implementation does not assume that the chosen
  root varies continuously with `U`. As a concrete obstruction to the source's
  missing branch choice, writing the eigenvalue `1` as `exp(i*2*pi)` would select
  `-I` at the first root level, whose distance `2` from `I` is greater than
  `pi/2`.
- **Status:** corrected and proved at the exact algebraic and L² operator-norm
  layers, in the stronger arbitrary-finite-dimensional form. Epsilon selection
  and construction resources are separated into C-008.

## C-008 — Lemma 7.8 does not handle all epsilon regimes

- **Source:** Lemma 7.8 statement/proof, manuscript pp. 23–24; lines 774–850.
- **Issue:** the statement allows every `ε>0`, while an unqualified
  `log(1/ε)` becomes nonpositive for large `ε`. The proposed integer depth
  `ceil(log₂(π/ε))` can also exceed the number of available recursive levels. At
  `ε=1`, for example, the printed `log(1/ε)` is zero although the displayed depth
  is `ceil(log₂ pi)=2`; for `1<ε<pi` the former is negative while a positive
  retained depth may still be selected.
- **Repair:** make the natural depth selector and capacity branch explicit.
  `principalRootBoundDepth ε = ⌈log₂(pi/ε)⌉₊` is the natural ceiling, hence clamps
  the negative-log regime to zero. If the requested depth fits the available
  controls, use the literal truncated primitive circuit; otherwise use the
  already verified exact recursive circuit, never a capped approximation that
  fails its requested tolerance. State logarithmic resource language only in an
  explicit positive small-error regime and as an upper bound for the named
  construction, not as an optimal-synthesis `Theta` theorem.
- **Dependent impact:** Lemma 7.8 and any universality-efficiency claim using it.
- **Formal evidence:** `principalRootBoundDepth_le_iff` characterizes the least
  certified natural depth, `principalRootBoundDepth_spec` proves its error bound,
  `principalRootBoundDepth_eq_zero_iff` handles `pi ≤ ε`, and
  `capacity_lt_principalRootBoundDepth_iff` identifies the exact-fallback branch.
  `epsilonSynthesisPrimitiveCircuit` selects literal one-qubit/CNOT truncation
  only when the depth fits and otherwise selects `recursivePrimitiveCircuit`;
  `operatorDistance_epsilonSynthesisPrimitiveCircuit_le` proves the requested
  error for every `ε>0`. For residual exact depth `r` and retained depth `k`, the
  syntax-linked exact counts are
  `32k²+(64r+200)k` one-qubit gates,
  `24k²+(48r+164)k` CNOTs, and
  `56k²+(112r+364)k` total/cost. At logical source width `n≥7`,
  `epsilonSynthesisTotalCountAtWidth_le` proves the uniform bound
  `440 + 112*n*min(principalRootBoundDepth ε, n-7)`, including exact fallback,
  while `epsilonSynthesisTotalCountAtWidth_lt_logarithmic` gives the explicit
  logarithmic-regime upper bound under `0<ε≤1`.
- **Status:** corrected and proved as an exact depth-indexed, piecewise
  construction with syntax-derived resources and exact fallback. The source's
  unrestricted or optimal-synthesis `Theta(n log(1/ε))` wording is intentionally
  not exported.

## C-009 — Phase congruence is not one equivalence relation

- **Source:** Section 6.2, manuscript pp. 15–16; lines 552–584.
- **Issue:** “congruent modulo phase shifts” is not defined and is discussed both as
  basis-dependent signs, classical reversible equivalence, and something that may
  cancel in a larger circuit. These are different semantic relations.
- **Repair:** compute an exact diagonal-phase witness for each circuit, state
  basis-dependent phase equivalence, derive reversible-basis behavior, and prove
  exact cancellation only in the concrete context where it occurs.
- **Dependent impact:** Section 6.2 circuits and Corollary 7.4's reduced gate count.
- **Formal evidence:** `GlobalPhaseEq` is one constant `Circle` scalar;
  `BasisPhaseEq` is an input-column phase function; `SameBasisBehavior` and
  `BasisMeasurementEq` are separate relations. Both Section 6.2 diagrams now
  compile with exact signed basis actions and exact equality to each other;
  `relativePhaseToffoliACircuit_basisPhaseEq_toffoli` and its B-circuit analogue
  record the `101` column sign. `relativeHalfPhaseExponent` and
  `relativeInwardPhaseExponent` compute its recursive propagation, while
  `eval_relativeCorollary74Circuit` proves exact cancellation only in the corrected
  ordered `Arel;Bhybrid;adjoint(Arel);Bhybrid` context.
- **Status:** corrected and proved for the Section 6 diagrams and their Corollary
  7.4 contextual use.

## C-010 — Auxiliary-wire contracts are underspecified

- **Source:** Lemmas 7.2–7.3 and 7.11, manuscript pp. 18–20 and 25.
- **Issue:** the constructions mix borrowed arbitrary wires and a fixed-zero wire,
  while prose says only that bits “incur no net change.” This does not by itself
  express correctness on superpositions or restoration of entanglement. For
  Lemma 7.11 the exact firing condition on a basis input is
  `aux xor conjunction(dataControls)`: the auxiliary is restored for either
  classical value, but the intended controlled-U behavior holds only when it
  begins at zero. A superposed auxiliary can become entangled with the data.
- **Repair:** prove full-register equality for dirty borrowed wires. State Lemma 7.11
  as equality on the clean-zero input subspace, quantified over arbitrary data
  states, and prove output factorization/restoration.
- **Dependent impact:** Corollaries 7.4, 7.10, 7.12 and downstream reuse of ancillas.
- **Formal evidence:** `inwardLadderUpdate_eq_update`,
  `inwardLadderUpdate_apply_borrowedWire`, and `eval_inwardLadderCircuit` prove
  Lemma 7.2 as exact full-register equality with arbitrary dirty borrowed inputs;
  `fourBlockUpdate_eq_update`, `fourBlockUpdate_apply_dirtyWire`, and
  `eval_fourBlockCircuit` do the same for Lemma 7.3's single borrowed wire.
  Stage 7's `expandedRecursivePrefixXCircuit` is the checked primitive dependency
  for Lemma 7.11: each compute/uncompute MCX uses the U target as a dirty wire and
  restores it. `fixedWireSubspace`, `cleanZeroSubspace`,
  `cleanZeroLinearEquiv`, and `fixedWireSubspace_factorization` provide the exact
  support/factorization model. `eval_cleanAncillaCircuit_mulVec_basisKet` and
  `cleanAncillaTargetProduct_eq_of_aux_true` expose both auxiliary branches;
  `eval_cleanAncillaCircuit_mulVec_of_mem_cleanZero`,
  `eval_cleanAncillaCircuit_mulVec_mem_cleanZero`, and
  `eval_cleanAncillaCircuit_factorization` prove arbitrary-state correctness,
  closure, and no residual entanglement. The expanded counterparts transport all
  three properties to counted one-qubit/CNOT syntax. Semantic syntax is valid
  from logical width two; the selected linear expansion requires width at least
  seven.
- **Status:** corrected and proved for all dirty contracts in Lemmas 7.2–7.3 and
  the clean-zero contract in Lemma 7.11.

## C-011 — “Basic operation” changes and drifts

- **Source:** Section 3 p. 8, Corollary 5.6 p. 14, Section 8 p. 26.
- **Issue:** Sections 3–7 define one-qubit gates and CNOT as basic; Corollary 5.6
  calls controlled special-family gates basic in its wording; Section 8 explicitly
  changes basic to arbitrary two-qubit U(4). A single numeric cost is ambiguous.
- **Repair:** use distinct named cost models, count controlled intermediate gates
  structurally unless declared primitive, and attach every bound to one model.
- **Dependent impact:** all resource theorems.
- **Formal evidence:** `CostModel.oneQubitCNOT` and
  `CostModel.arbitraryTwoQubit` are distinct partial models;
  `Circuit.cost` returns `none` for an unsupported occurrence, and
  `Primitive.namedModels_reject_unclassified_of_mem` proves that neither model
  silently prices `.unclassified`. Append and adjoint cost laws are compiled.
  For Corollary 5.6, `controlledVMacroU2Circuit_gateCount` and
  `controlledVMacroU2Circuit_kindCounts` prove the structural six-node macro
  count—four one-qubit plus two controlled-`V` occurrences—while
  `controlledVMacroU2Circuit_oneQubitCNOTCost` proves that the Sections 3–7 model
  rejects the unexpanded controlled-`V` occurrences with cost `none`.
  `expandedVMacroU2Circuit_gateCount`,
  `expandedVMacroU2Circuit_kindCounts`, and
  `expandedVMacroU2Circuit_oneQubitCNOTCost` prove that literal expansion of both
  macros has ten nodes—eight one-qubit plus two CNOT occurrences—and cost
  `some 10`. Under `D * F = I`,
  `eval_expandedVMacroU2Circuit_eq_controlledU2Circuit` proves the three local
  merge groups give evaluator equality with the distinct six-node
  `controlledU2Circuit`; `controlledU2Circuit_gateCount`,
  `controlledU2Circuit_kindCounts`, and `controlledU2Circuit_oneQubitCNOTCost`
  prove its four-plus-two syntax and cost `some 6`. The combined cost statement is
  `expanded_and_mergedVMacroU2Circuit_oneQubitCNOTCosts`. Under the additional
  equation `V = F * X * D`, `eval_expandedVMacroU2Circuit_eq_macro` also connects
  the ten-node expansion to the six-node macro evaluator.
- **Status:** corrected and proved at the cost-model foundation and for all
  Section 5 constructions. Every later numerical paper bound still requires a
  concrete supported circuit and its own theorem.

## C-012 — Six arbitrary two-qubit gates for every U(8) is unsupported

- **Source:** Section 8, manuscript pp. 26–27; lines 903–933.
- **Issue:** the paper says “the answer is six” and displays parameter-space
  dimensions reaching 64. Dimension equality is necessary evidence but does not
  prove that the circuit parameterization is surjective onto all of U(8). No
  constructive or topological proof is supplied.
- **Repair:** do not export universal six-gate sufficiency unless an independent
  proof is found. The architecture and parameter count may be documented; a proved
  generic/local result would be stated with its actual hypotheses.
- **Dependent impact:** none of the paper's general universality construction, which
  uses a separate two-level method; affects only Section 8 minimal/sufficiency claims.
- **Formal evidence:** none.
- **Status:** unresolved.

## C-013 — Dimension-count lower bound is explicitly conjectural

- **Source:** manuscript p. 27; lines 931–937.
- **Issue:** the formula `(4^n−3n−1)/9` is introduced as “a conjecture, just based on
  dimension counting.” It lacks a formal parameter map, image/fiber argument, and
  coverage theorem.
- **Repair:** retain it as historical motivation, not an unconditional Lean theorem.
  A future rigorous lower bound must name the circuit architecture, smooth spaces,
  quotient redundancies, and exact generic/worst-case conclusion.
- **Dependent impact:** comparison with the general synthesis upper bound.
- **Formal evidence:** none.
- **Status:** excluded from theorem scope pending a new proof.

## C-014 — General-unitary `Theta` claim is an outlined upper construction

- **Source:** Section 8, manuscript pp. 27–28; lines 939–983.
- **Issue:** the source sketches, but does not prove, the two-level decomposition,
  product order, negative-control conjugation, or Gray-path semantics. Its
  `Θ(n³4^n)` wording is used as a uniform implementation estimate without a matching
  lower bound for optimal synthesis, and individual unitaries can be much cheaper.
- **Repair:** supply a concrete elimination and circuit construction, then export a
  syntax-based constructed upper bound. The source Gray route supports at most a
  uniform cubic-per-factor upper argument from the stated path bound. The formal
  library uses a stronger affine endpoint normalization, targeting a quadratic
  per-factor upper bound: local X gates send the first endpoint to zero,
  common-pivot CNOTs send the second to a singleton, and one adjacent controlled
  block is conjugated by that literal transport. A `Theta` result may describe a
  deliberately fixed schedule that retains identity gates, but not optimal cost
  without a matching theorem.
- **Dependent impact:** central exact-universality and resource headline results.
- **Formal evidence:** `decomposeFinUnitary` and `decomposeFiniteUnitary` return
  explicit conventional-order factors and a diagonal residual with exact equation
  `U = finiteFactorProduct factors * residual`; `eval_diagonalCircuit` synthesizes
  that residual without discarding any phase; `eval_twoLevelCircuit` implements
  each ordered factor through exact affine conjugation; `orderedCircuitProduct`
  supplies the explicit bridge from mathematical factor order to chronological
  syntax; `ZeroWidth.lean` and `WidthOne.lean` prove the sharp boundary cases.
  Exact factor and diagonal costs are syntax-derived, and
  `eval_exactSynthesisCircuit` plus
  `exactSynthesisCircuit_oneQubitCNOTCost` assemble them in the proved product
  order. `decomposeQubitUnitary_factors_length` and
  `allComplementPatterns_length` count the fixed schedules;
  `exactSynthesisCost_bounds` proves the finite quadratic-times-exponential
  sandwich; and `exactSynthesisCost_isBigOWith_fixedSchedule` and
  `exactSynthesisCost_isTheta_fixedSchedule` state the upper and deliberately
  padded two-sided algorithmic results.
- **Status:** corrected and proved for exact synthesis and the selected fixed
  construction. No optimal general-synthesis `Theta` theorem is claimed.

## C-015 — Algebraic all-measurement equality is not yet a physical measurement model

- **Source:** Section 6.2, manuscript pp. 15–16, and the approximation/probability
  discussion on pp. 22–23.
- **Issue:** phrases such as “same measurements” can hide materially different
  quantifiers. Equality only for computational-basis inputs/outcomes is weaker than
  equality for arbitrary input states and effects. Conversely, calling an arbitrary
  complex matrix a state or effect does not prove positivity, normalization, reality,
  or probability bounds.
- **Repair:** `BasisMeasurementEq` compares squared entry moduli only.
  `ChannelEq` quantifies conjugation over every square complex input matrix, while
  `AllMeasurementEq` quantifies `trace (effect * state)` over every input/effect
  matrix. Matrix-unit effects prove those latter two algebraic relations equivalent.
  Physical density matrices and positive effects will be separate restricted types.
- **Dependent impact:** phase-relaxed constructions, the paper's `2ε` observation,
  and any later claim about observable outcome probabilities.
- **Formal evidence:** `GlobalPhaseEq.toChannelEq`,
  `channelEq_iff_allMeasurementEq`, `ChannelEq.bornWeight_eq`, and
  `ChannelEq.toBasisMeasurementEq` compile in
  `Barenco.Equivalence.Measurement`. For pure states represented in
  `EuclideanSpace`, `operatorDistance_basisOutcomeProbability_le` proves the
  `2ε` bound for one named computational-basis outcome under the explicit
  norm-at-most-one hypothesis. `eventProbability` and `eventProjection` define a
  finite computational-basis event and its projective restriction;
  `operatorDistance_eventProbability_le` proves the stronger cardinality-free
  constant-one bound for unitary images of a common norm-at-most-one pure input,
  and `operatorDistance_eventProbability_le_two_mul` records the paper-facing
  constant-two corollary. `epsilonSynthesisPrimitiveCircuit_eventProbability_le`
  and its `_two_mul` form apply those results to the corrected Lemma 7.8 circuit.
- **Status:** corrected and proved as an algebraic separation and for arbitrary
  finite computational-basis events on pure inputs. No arbitrary-POVM theorem or
  claim that unrestricted matrices are physical density/effect objects is made.

## C-016 — Lemma 4.1 suppresses degenerate phase choices and determinant normalization

- **Source:** Lemma 4.1 proof, manuscript p. 8; Markdown lines 210–221.
- **Issue:** orthonormality is said to imply the displayed four-angle form
  “immediately,” but the proof does not construct angles when a phase-carrying
  entry is zero. It also leaves the U(2) determinant square-root choice implicit.
  In the special-unitary paragraph, `det (Ph(δ)) = exp(2 i δ)`, so determinant
  one allows scalar phase `-1` as well as `1`; the manuscript mentions this but
  does not show the claimed absorption into a Z rotation.
- **Repair:** first prove the canonical SU(2) entry form
  `[[a,b],[-conj b,conj a]]`, then choose
  `theta = 2 arccos ‖a‖` and use mathlib's total `Complex.arg` for `a` and `b`.
  The polar identity remains valid at zero, giving the endpoint cases
  `theta = pi` and `theta = 0` without division by an entry. For U(2), choose half
  the principal argument of the determinant, prove that the corresponding scalar
  phase has determinant exactly `det U`, remove it, and reconstruct `U` exactly.
  Keep the possible special-unitary scalar `-1` explicit and absorb it by a
  `2*pi` shift of a Z angle when that presentation is needed.
- **Dependent impact:** the exact SU(2)/U(2) Euler theorem, Lemma 4.3, and the
  controlled-gate constructions beginning in Section 5.
- **Formal evidence:** `specialUnitary_canonical`,
  `specialUnitary_eq_paperEuler_arg`, `specialUnitary_eulerTheta_mem_Icc`,
  `specialUnitary_exists_rz_mul_ry_mul_rz`, `determinantPhaseAngle_mem_Ioc`,
  `removeGlobalPhase_det`, `phaseShift_mul_specialUnitaryPart`,
  `paperPhase_pi_mul_paperRz`, and
  `unitary_exists_phaseShift_mul_rz_mul_ry_mul_rz` compile in the Section 4
  one-qubit modules.
- **Status:** corrected and proved, including both zero-entry endpoints, exact
  determinant normalization, the row/column order distinction, and the middle
  angle bound `theta ∈ [0, pi]`.

## C-017 — Lemmas 5.4–5.5 omit essential classification and converse details

- **Source:** Lemma 5.4 proof, manuscript pp. 12–13; Lemma 5.5 proof, p. 13;
  Markdown lines 423–486.
- **Issue:** Lemma 5.4 says that specializing Lemma 4.1 classifies a traceless
  determinant-`-1` unitary, but it does not construct the two real parameters when
  the phase-carrying off-diagonal entry is zero. Lemma 5.5's one-sentence proof
  starts with a Lemma 5.4 realization, appends an XOR, and cancels the adjacent XOR
  pair. This proves sufficiency for the displayed family as written, but never
  starts from an arbitrary one-CNOT realization and therefore does not prove
  necessity. It also permits arbitrary unitary `A,B`, whereas the Lemma 5.4
  witnesses used by that argument are special unitary; the missing converse needs
  an explicit phase-normalization step.
- **Repair:** derive `B=A⁻¹` from the actual inactive branch `B*A=I`. Classify
  `A† X A` as a Hermitian traceless unitary with first row `(r,z)` satisfying
  `r²+‖z‖²=1`; choose `theta=2*arcsin r` and `alpha=-arg z`. The total complex polar
  identity handles `z=0`. For arbitrary U(2) `A`, remove its determinant phase and
  prove that the opposite scalar phases cancel exactly around X before applying
  the SU(2) classification.
- **Dependent impact:** Lemmas 5.4–5.5, Corollary 5.6, and every later use of the
  special controlled-`V` family.
- **Formal evidence:** `pauliConjugate_eq_sigmaX_mul_symmetricEuler`,
  `sigmaX_mul_star_mul_sigmaX_mul_eq_symmetricEuler`,
  `eval_twoCNOTCircuit_eq_iff`, `eval_oneCNOTCircuit_eq_iff`,
  `twoCNOTFamily_iff`, `oneCNOTSpecialFamily_iff`,
  `unitaryPauliConjugate_eq_specialUnitaryPart`, and `oneCNOTFamily_iff` compile.
  The evaluator iff theorems independently extract inactive and active branches
  from full-register equality; the family iff theorems then prove both necessity
  and sufficiency.
- **Status:** corrected and proved in both directions, including zero-coordinate
  cases and the paper's arbitrary-unitary quantification.

## C-018 — “Rx(theta) is not of this form” has discrete scalar exceptions

- **Source:** discussion after Lemma 5.4, manuscript p. 13; Markdown line 469.
- **Issue:** the unconditional sentence is false when `sin(theta/2)=0`, equivalently
  when `theta=2*pi*k` for some integer `k`. Then the displayed matrix is
  `Rx(theta)=(-1)^k I`, so it is either `I` or `-I`; both scalars belong to the
  equal-outer-angle `Rz Ry Rz` family. The intended contrast is true only for
  non-scalar x-axis rotations.
- **Repair:** state that `Rx(theta)` is outside the Lemma 5.4 family when
  `sin(theta/2) ≠ 0`. Retain the scalar cases explicitly:
  `symmetricEuler 0 0 = I` and `symmetricEuler pi 0 = -I` in the library's
  standard-column convention.
- **Dependent impact:** illustrative examples only; no numbered construction or
  resource theorem depends on the sentence.
- **Formal evidence:** the root-excluded diagnostic theorem
  `ControlledCircuitExamples.symmetricEuler_zero_angle` proves
  `symmetricEuler alpha 0 = rz (2*alpha)`, which yields the two scalar cases at
  `alpha=0` and `alpha=pi`; `twoCNOTFamily_iff` is the complete circuit-family iff.
  The generic non-membership claim is documented here rather than needed by the
  paper's construction chain.
- **Status:** corrected as an expository discrete scalar exception; the general Rx
  non-membership theorem is intentionally not needed by the paper's main chain.

## C-019 — Lemma 6.1 suppresses root existence and one inverse-order case

- **Source:** Lemma 6.1, manuscript pp. 14–15; Markdown lines 526–544; image
  `lemma-6-1-controlled-controlled-u.png`.
- **Issue:** the proof says only to choose a unitary `V` with `V²=U`, without
  proving that every unitary `U` has such a unitary square root. Its inactive-case
  prose mentions `V*V†=I`, but input controls `10` instead produce
  `V†*V=I`. The arithmetic explanation also silently uses that `V†=V⁻¹`
  commutes with `V`. Finally, the diagram requires three pairwise distinct wires,
  which the prose does not state as a boundary condition.
- **Repair:** use the proved finite-spectrum `unitarySquareRoot U` and its exact
  equation, retain a stronger parameterized theorem for every certified witness
  `V²=U`, and prove all four control cases after explicitly conjugating the middle
  controlled gate through CNOT. Quantify arbitrary ambient width and three
  pairwise distinct named wires.
- **Dependent impact:** Corollary 6.2 and every recursive root/Gray-code
  construction in Sections 7 and 9 must use the certified root theorem and the
  exact full-register circuit result, not the source's unproved choice.
- **Formal evidence:** `doubleControlledViaSquareCircuit`,
  `eval_doubleControlledViaSquareCircuit_pow_two`,
  `eval_doubleControlledViaSquareCircuit_of_sq_eq`,
  `doubleControlledRootCircuit`, `eval_doubleControlledRootCircuit`, and
  `doubleControlledViaSquareCircuit_exists` compile. The proof uses both
  directions of the unitary identities and proves equality of arbitrary-width
  matrices, which includes restoration of the second control and all spectators.
- **Status:** corrected and proved exactly.

## C-020 — Corollary 6.2's “adjacent” cancellations require commutation and shared witnesses

- **Source:** paragraph before Corollary 6.2, manuscript p. 15; Markdown lines
  545–550.
- **Issue:** independently expanding the three controlled gates gives twenty
  primitives, not sixteen. The claimed inverse pairs are not literally adjacent
  in the serialized circuit: `C` and `C†` are separated by the control-to-control
  CNOT, while `A†` and `A` are separated by two control-wire phase gates and that
  CNOT. They cancel only after proving disjoint-wire commutation. Moreover, the
  controlled-`V†` implementation must be the exact adjoint of the same chosen
  controlled-`V` factorization; independent existential Section 5 witnesses do
  not justify the cancellations.
- **Repair:** construct the coordinated twenty-node circuit
  `S(second); K; S(second)†; K; S(first)`, prove its exact evaluator, commute the
  two target-local inverse pairs across the intervening control-only gates, and
  name the resulting sixteen-node syntax. Choose the Section 5 factors once and
  reuse them on both controls.
- **Dependent impact:** the printed upper bound is valid, but only for the
  coordinated construction. Later resource recurrences may use sixteen only by
  citing this explicit syntax/cost theorem.
- **Formal evidence:** `cnotRaw_commute_localRaw`,
  `localRaw_commute_of_ne`, `doubleControlledExpansion20Circuit`,
  `eval_doubleControlledExpansion20Circuit_eq_16`,
  `doubleControlledExpansion16Circuit`,
  `eval_doubleControlledExpansion16Circuit_of_products`, and
  `doubleControlledUnitary_has_sixteenPrimitiveCircuit` compile. The final
  circuit has exactly eight `.oneQubit` and eight `.cnot` nodes and cost
  `some 16` under `CostModel.oneQubitCNOT`.
- **Status:** clarified and proved as an exact constructed upper bound.

## C-021 — The PDF attributes the controlled-W minus sign to the wrong gate

- **Source:** Section 6.2 opening paragraph, manuscript pp. 15–16; Markdown lines
  552–566.
- **Issue:** after introducing `∧₂(W)` and exact Toffoli `∧₂(X)`, the original PDF
  says “the latter maps `|111⟩` to `-|110⟩`.” Grammatically, “latter” names
  Toffoli, which is false; the minus sign belongs to the former, controlled-`W`.
  The Markdown transcription silently changes “latter” to “former.” A separate
  possible confusion is that the two following seven-node diagrams do not equal
  controlled-`W`: their basis-dependent minus sign is on input `|101⟩`, whereas
  controlled-`W` has it on `|111⟩`.
- **Repair:** define and certify the paper-row and semantic-column Pauli-Y matrices,
  prove the displayed identity `paperW = paperPhase (pi/2) * paperY`, translate it
  exactly to `wMatrix = phaseShift (pi/2) * sigmaY` (accounting for transpose
  reversal and the antisymmetric Pauli-Y sign), and also identify the result with
  `Wᵀ=Ry(pi)`. Prove its exact controlled basis action and keep it distinct
  from the exact common evaluator of the A/CNOT and B/controlled-Z diagrams.
  Relate each operator to exact Toffoli through its own explicit input-column
  phase witness; do not use global-phase equality.
- **Dependent impact:** relative-phase cancellation in Corollary 7.4 must use the
  actual `|101⟩` witness of the displayed circuits, not the `|111⟩` witness of
  controlled-`W`. Claims about paired occurrences require an ordered basis-path
  calculation when intervening gates are present.
- **Formal evidence:** `paperY_mem_unitaryGroup`, `sigmaY_mem_unitaryGroup`,
  `paperW_eq_paperPhase_mul_paperY`, `wMatrix_eq_sigmaY_mul_phaseShift`,
  `wMatrix_eq_phaseShift_mul_sigmaY`, `wUnitary_eq_phaseShift_mul_sigmaY`,
  `wMatrix_eq_ry_pi`, `coe_wUnitary`,
  `controlledWUnitary_mulVec_basisKet`,
  `relativePhaseToffoliACircuit_mulVec_basisKet`,
  `relativePhaseToffoliBCircuit_mulVec_basisKet`, and
  `eval_relativePhaseToffoliACircuit_eq_BCircuit` compile. The derived
  `BasisPhaseEq`, `SameBasisBehavior`, and `BasisMeasurementEq` theorems retain
  the distinct phase predicates.
- **Status:** corrected and proved with exact arbitrary-width signed actions; the
  Markdown wording is correct, while the original PDF is not.

## C-022 — Corollary 7.10 drops one control in its printed statement

- **Source:** Lemma 7.9 and Corollary 7.10, manuscript p. 24; Markdown lines
  854–875; image `lemma-7-9-linear-su2-control.png`.
- **Issue:** Lemma 7.9 states and diagrams a fully controlled
  `∧_{n−1}(W)` gate, and its construction is meant to combine with the linear
  one-fewer-control Toffoli dependency from Corollary 7.4. Corollary 7.10 instead
  prints `∧_{n−2}(W)`. The following example then describes a transformation
  congruent to the n-bit Toffoli `∧_{n−1}(X)`, which again requires the fully
  controlled interpretation. These surrounding dependencies do not support the
  weaker printed subscript as the intended conclusion.
- **Repair:** treat `∧_{n−2}(W)` as a likely subscript typo, but do not silently
  replace it in a theorem. In Stage 8, reconstruct the Lemma 7.9 circuit and prove
  the intended stronger linear upper bound for `∧_{n−1}(W)` on an n-bit register,
  with all width hypotheses and the Sections 3–7 cost model explicit.
- **Dependent impact:** Corollary 7.10, its phase-relaxed n-bit Toffoli example,
  and later synthesis/resource estimates that use a linear special-unitary
  multi-control construction.
- **Formal evidence:** source audit fixes the exact chronology as
  `C(c,A,t);MCX(P,t);C(c,B,t);MCX(P,t);C(c,C,t)` and its four target products as
  `I`, `X²`, `CBA`, and `CXBXA`. Determinant one is necessary for this topology.
  `eval_linearABCCircuit_of_products` checks those four products,
  `eval_linearSU2Circuit` selects one certified ABC factorization, and
  `eval_expandedLinearSU2Circuit` links the five macros to literal one-qubit/CNOT
  syntax. The logical-width theorems and `linearSU2*CountAtWidth` resource links
  prove exactly `64n−279` one-qubit plus `48n−194` CNOT operations, total
  `112n−473`, for `n≥7`. `fullyControlledWPhase_input` and
  `fullyControlledW_basisPhaseEq_pauliX` compute the special-W example's exact
  input-column sign and its justified phase-relaxed consequences.
- **Status:** corrected and proved; the source's printed subscript remains visible
  here rather than being silently normalized away.

## C-023 — Lemma 7.5 omits its recursive width and base cases

- **Source:** Lemma 7.5 and Corollary 7.6, manuscript pp. 21–22; Markdown lines
  716–746; image `lemma-7-5-quadratic-general-control.png`.
- **Issue:** Lemma 7.5 quantifies `n` without a lower bound, although its displayed
  recursive step must select a last control, separate the remaining control
  prefix, and invoke gates indexed by `n−2`. That syntax is not meaningful at
  every natural-number boundary, and the one-line proof supplies neither a legal
  recursive domain nor terminating base circuits. The following cost recurrence
  likewise omits the small-width cases and the separate threshold needed before
  Corollary 7.4 can price its multi-controlled-X subcircuits.
- **Repair:** index the semantic recursive step by a width carrying the required
  last-control/prefix decomposition (equivalently, prove the exact minimum width),
  and state explicit local/controlled base cases before recursion. Treat an empty
  residual prefix only through a proved boundary theorem. State the resource
  recurrence separately from its finite base range and from Corollary 7.4's
  applicability threshold.
- **Dependent impact:** Corollaries 7.6 and 7.8, every recursive fully controlled
  circuit constructor, and downstream Section 8 estimates that charge the
  quadratic exact construction.
- **Formal evidence:** `recursiveViaSquareCircuit` is indexed by an
  `OrderedControlLayout (prefix+1) ambientWidth` and stores the exact five-node
  chronology. `eval_recursiveViaSquareCircuit_pow_two` and its square-equation
  variant prove exact full-register semantics; `recursiveRootCircuit` supplies
  the certified square root. The proof genuinely includes `prefix=0`, while
  `zeroControlCircuit` and `eval_zeroControlCircuit` expose the distinct local
  base. `recursiveSubstitutionCircuit` proves evaluator and additive resource
  preservation for five supplied implementations. `sixControlExpandedGrayCircuit`
  supplies the separately proved recursive resource base with exact
  `(252,188,440)` one-qubit/CNOT/total counts. `recursivePrimitiveCircuit` then
  recurses only from that legal six-control base, has an exact evaluator at every
  depth, and proves all component/count/cost recurrences. `Resources.lean`
  separates depth and source-width indexing and states every lower threshold.
- **Status:** corrected and proved, including semantic boundaries, terminating
  primitive recursion, explicit base, and exact resource linkage.

## C-024 — Lemma 7.1 has a useful one-control extension but no zero-control Gray case

- **Source:** Lemma 7.1 and the preceding four-bit Gray construction, manuscript
  pp. 17–18; Markdown lines 585–629.
- **Issue:** the source states the construction only in its multi-control range.
  The same schedule is valid with one positive control: it reduces to one
  controlled-`U` node and no Gray CNOT. Extending the formula to zero controls,
  however, would be false for this generator: the nonempty-mask Gray code is
  empty and its circuit denotes identity, whereas the desired empty-control gate
  is the local `U` operation.
- **Repair:** index the reusable theorem by `tail + 1` controls. Prove the
  `tail = 0` syntax exactly equals one controlled-root primitive, and keep the
  zero-control local-gate case separate rather than hiding it behind truncated
  natural subtraction.
- **Dependent impact:** boundary cases of exact multi-control synthesis and any
  later recurrence that uses Lemma 7.1 as a base construction. The paper's stated
  range remains correct; the formal theorem is a justified strengthening.
- **Formal evidence:** `grayControlledViaRootCircuit_zero_eq_singleton`,
  `eval_grayControlledViaRootCircuit`, `grayControlledViaRootCircuit_kindCounts`,
  `grayControlledCircuit`, and `eval_grayControlledCircuit` compile. At
  `tail = 0` the counts specialize to one controlled-root macro and zero CNOTs.
- **Status:** boundary clarified and stronger positive-control theorem proved.

## C-025 — Relative-phase cancellation needs an adjoint A implementation

- **Source:** Corollary 7.4, manuscript p. 20; Markdown lines 688–712.
- **Issue:** the source says a later “similar gate” cancels the phase of an
  earlier relative-phase Toffoli implementation but does not specify the required
  reversed circuit. With the Section 6 diagram's actual `101` input phase,
  replacing both A blocks by the same chronological all-relative ladder is false:
  already at the `n=7` boundary it leaves a minus sign whenever all A controls are
  one. `BasisPhaseEq` is not a precomposition congruence and cannot justify the
  replacement.
- **Repair:** use an all-relative A ladder in the first A position and its circuit
  adjoint in the second. The balanced A support excludes the final target, so the
  intervening B block leaves A's phase-bearing subsystem unchanged and the inverse
  phases cancel. For B, retain the two outer/final-target Toffolis exactly and use
  identical all-relative smaller halves; each half is a palindrome of involutions,
  so its paired phase cancels. This yields exactly four exact Toffolis.
- **Dependent impact:** contextual correctness and every early-basic count in
  Corollary 7.4, plus Lemma 7.5/Corollary 7.6 costs that depend on it.
- **Formal evidence:** the exact balanced target-exclusion theorem already compiles;
  `relativeHalfPhaseExponent`, `eval_relativeHalfLadderCircuit_sq`,
  `eval_relativeInwardLadderCircuit_mulVec_basisKet`,
  `eval_hybridInwardLadderCircuit`,
  `eval_adjoint_relativeCorollary74AImplementation_mulVec_basisKet`, and
  `eval_relativeCorollary74Circuit` now machine-check the signed-half, hybrid-B,
  adjoint-A, and full contextual arguments. The balanced wrapper proves four exact
  and `8n−44` relative occurrences.
- **Status:** corrected and proved.

## C-026 — Corollaries 7.10 and 7.12 do not prove optimal linear synthesis

- **Source:** Corollaries 7.10 and 7.12, manuscript pp. 24–25; Markdown lines
  862–889.
- **Issue:** both corollaries use `Θ(n)` after exhibiting a linear-size circuit
  without stating the optimization quantifiers. Lemma 7.7 supplies a linear lower
  invariant for exact, no-ancilla, nonscalar fully controlled targets, but it does
  not cover Corollary 7.12's clean-ancilla model. Read as a statement about minimum
  cost uniformly over every target gate, the claim is immediately false for the
  identity, which needs no operations. Corollary 7.12 additionally changes the
  available resource by assuming one clean reusable bit.
- **Repair:** give exact component and total counts for each named syntax, then
  state an `O(n)` upper bound if asymptotic packaging is useful. A future
  two-sided exact no-ancilla theorem may specialize Lemma 7.7 to the nonscalar
  `W` family after explicitly bridging the counted construction into the same
  restricted syntax and quantifiers. The clean-ancilla claim still needs a new
  lower-bound invariant. Do not call either present result optimal synthesis.
- **Dependent impact:** the intended corrected Corollary 7.10, the clean-ancilla
  Corollary 7.12, and any later comparison between no-ancilla and clean-ancilla
  resource models.
- **Formal evidence:** `expandedLinearSU2Circuit` and
  `expandedCleanAncillaCircuit` are the counted primitive syntax. Their component,
  total, accepted-cost, and logical-width theorems prove exact totals
  `112n−473` and `112n−482` for `n≥7`; the corresponding
  `linearSU2*CountAtWidth` and `cleanAncilla*CountAtWidth` theorems link the
  numeric functions back to those circuits. `linearSU2TotalCount_isBigOWith_width`
  and `cleanAncillaTotalCount_isBigOWith_width` prove construction-specific
  `IsBigOWith 112` bounds, with ordinary `O(n)` corollaries. The separate
  `fullyControlled_cnotCount_lowerBound` proves the exact no-ancilla nonscalar
  lower invariant described in C-027; no theorem currently packages it with this
  generic `Circuit` upper syntax into an optimal-cost function.
- **Status:** corrected and proved as exact counts and linear upper bounds for the
  named constructions; optimal `Θ(n)` is intentionally not exported.

## C-027 — Lemma 7.7 understates its CNOT invariant and omits the tensor proof

- **Source:** Lemma 7.7, manuscript p. 22; Markdown lines 750–768.
- **Issue:** the statement asks for at least `n−1` *basic operations*, but the
  proof assumes arbitrarily many one-bit gates and derives a contradiction from
  having fewer than `n−1` XOR gates. Once valid, that argument proves the stronger
  lower bound on CNOT occurrences themselves. Two semantic claims are also only
  asserted: that a disconnected, possibly noncontiguous wire partition makes the
  whole circuit an `A tensor B`, and that a fully controlled nonscalar target
  cannot have such a factorization. The notation does not specify the basis
  reordering or tensor-factor order, and a support count alone proves neither
  matrix claim.
- **Repair:** quantify over the proof-carrying `BasicCircuit` syntax containing
  exactly arbitrary one-qubit gates and distinct-wire CNOTs. Form its undirected
  CNOT interaction graph, retain repeated CNOTs as occurrences while collapsing
  duplicate graph edges, and use the finite connected-graph edge bound. For an
  arbitrary cut, split basis functions into selected and complementary wires with
  `wireSplit`, reindex both matrix axes with `partitionReindex`, and define
  `TensorFactorsAcross` using the resulting left-first Kronecker convention.
  Prove factorization for each same-side primitive and preserve it through the
  chronological evaluator. Finally, orient the disconnected cut as the component
  containing the target and prove by explicit basis assignments that separating
  any listed positive control forces the target matrix to be scalar.
- **Dependent impact:** the source's `n−1` basic-operation claim follows as a
  weaker corollary of an `n−1` CNOT-occurrence theorem. The result is restricted
  to exact equality on one register, with no ancilla, measurement, approximation,
  or phase-relaxed target relation. It excludes scalar-phase targets exactly;
  at one wire the lower bound is the trivial zero, and no target exists at width
  zero. This linear theorem does not turn the Section 5/6 named-topology upper
  counts into global minima and does not supply the missing quadratic or Section 8
  conjectural lower bounds.
- **Formal evidence:** `BasicPrimitive`, `BasicCircuit`, `BasicCircuit.erase`,
  `BasicCircuit.eval_erase`, and the exact count/cost bridges fix the allowed
  syntax. `interactionGraph_edgeFinset_card_le_cnotCount` and
  `cnotCount_lowerBound_of_interactionGraph_connected` prove the duplicate-safe
  graph layer. `wireSplit`, `partitionReindex`, `TensorFactorsAcross`, and
  `eval_tensorFactorsAcross_targetComponent` prove the suppressed tensor step.
  `isScalarQubitMatrix_coe_iff_exists_phaseShiftUnitary` and
  `not_tensorFactorsAcross_fullyControlled_of_not_scalar` prove the scalar
  boundary and obstruction. `fullyControlled_cnotCount_lowerBound` is the
  strengthened headline theorem; `fullyControlled_gateCount_lowerBound` and
  `fullyControlled_oneQubitCNOTCost_lowerBound` recover the paper-facing total and
  named-cost forms.
- **Status:** corrected and proved. Public integration, boundary examples, all 18
  new maintained axiom checks, strict/trust-zero compilation, the focused build,
  and two full builds passed with Stage 10.

## C-028 — Exact one-qubit/CNOT universality has a zero-wire obstruction

- **Source:** abstract and Section 8, especially manuscript pp. 1 and 27–28;
  Markdown lines 39 and 939–983.
- **Issue:** the broad statement that arbitrary one-qubit gates and CNOT generate
  every finite-qubit unitary is false if “finite” includes width zero and equality
  is exact. `Basis 0` has one computational-basis state, so its certified unitary
  group contains every `U(1)` scalar phase. But the restricted syntax has no legal
  one-qubit target and no pair of distinct wires for CNOT; it can only be empty and
  therefore evaluates to identity.
- **Repair:** state exact universality for positive register width. Prove separately
  that every restricted zero-wire circuit evaluates to identity and exhibit or
  characterize the nonidentity zero-wire phases it cannot reach. Width one remains
  the direct arbitrary-one-qubit primitive case. Do not erase this obstruction by
  silently switching to global-phase equality.
- **Dependent impact:** the headline exact-universality theorem, its boundary
  examples, and any API advertised for “all `n`.” It does not affect ordinary
  positive-width quantum registers or a separately stated global-phase-relaxed
  zero-width theorem.
- **Formal evidence:** `basicCircuit_zero_eq_nil`, `basicCircuit_zero_eval`,
  `zeroWidthNegUnitary_ne_one`, and `no_basicCircuit_zero_realizes_neg` in
  `Barenco/Universality/ZeroWidth.lean`; `eval_widthOneCircuit` and
  `widthOneCircuit_oneQubitCNOTCost` prove the direct width-one boundary in
  `Barenco/Universality/WidthOne.lean`; `exact_oneQubitCNOT_universality` proves
  exact accepted synthesis at every successor width.
- **Status:** corrected and proved with sharp zero-, one-, and positive-width
  statements.

## C-029 — The final Gray edge may reverse the two-level block orientation

- **Source:** Section 8 Gray-path construction, manuscript pp. 27–28; Markdown
  lines 959–976.
- **Issue:** a local one-qubit matrix is ordered by target values
  `(false,true)`, while the requested two-level block is ordered by its two named
  path endpoints. The paper does not relate these orders. In its own example the
  final edge is `00110111 -> 00100111`, so the target bit runs `(true,false)`.
  Applying the unmodified local matrix on that edge represents `X U X` relative
  to the ordered endpoints, not `U`.
- **Repair:** carry the ordered endpoint equivalence explicitly. If the final edge
  has target order `(false,true)`, use `U`; if it has `(true,false)`, use the
  certified conjugate `X U X`. Prove the resulting move/apply/unmove conjugation
  on every basis state and then extend to exact matrix equality.
- **Dependent impact:** every non-adjacent two-level circuit, the exact
  universality theorem, and its resource counts. Control-polarity X conjugations
  are a separate issue and do not repair this target-order reversal.
- **Formal evidence:** `endpointOrientedUnitary_apply`,
  `local_endpointOriented_mulVec_first`,
  `local_endpointOriented_mulVec_second`, and
  `eval_adjacentTwoLevelCircuit` in
  `Barenco/Universality/AdjacentTwoLevel.lean` prove the ordered block on the
  complete register for both endpoint orientations.
  `eval_twoLevelCircuit` transports that adjacent result to every distinct ordered
  pair by a literal affine circuit and its adjoint.
- **Status:** corrected and proved for adjacent and arbitrary distinct pairs.

## C-030 — A path-length upper bound does not prove per-factor cubic Theta

- **Source:** Section 8, manuscript p. 28; Markdown lines 971–983.
- **Issue:** the paper reuses `m` both for bit-string width in the decomposition
  formula and for the number of vertices in a Gray path. For the latter it proves
  only `m <= n+1`, then concludes that every two-level factor costs
  `Theta(n^3)`. This supplies a uniform cubic upper bound after a quadratic
  multi-control expansion, not a matching lower bound. Adjacent endpoints have
  path length two and need one fully controlled gate, so the named cost is only
  quadratic in that case.
- **Repair:** use register width `n`, Hamming distance `d`, and path length `d+1`
  as distinct parameters. The exact macro count for distinct endpoints is
  `2*d-1`, giving a per-factor bound `O((2*d-1)*n^2)` and worst-case
  `O(n^3)`. Consequently the immediate general synthesis claim is a uniform
  `O(n^3*4^n)` upper bound. A two-sided theorem may later describe a fixed
  non-pruning schedule after its aggregate counts are proved; it is not an
  optimal-synthesis theorem.
- **Dependent impact:** U8 path counts, the general resource headline, and any
  comparison with the conjectural dimension lower bound. Exact universality does
  not depend on the asymptotic correction.
- **Formal evidence:** `length_basisPath`, `length_basisPath_sub_one`,
  `length_basisPath_le`, `basisPath_edge_hammingDist`, and `basisPath_isChain` in
  `Barenco/Universality/BasisPath.lean`. The main library construction is
  strengthened by affine endpoint
  transport: `affinePairCircuit_cnotCount` proves exactly `d-1` clearing CNOTs,
  `affinePairCircuit_oneQubitCount` proves the exact translation-X count, and
  `twoLevelCircuit_oneQubitCNOTCost` accounts for those transports around one
  fully controlled adjacent block. `twoLevelCircuitCost_le_sq_succ` supplies the
  uniform quadratic factor envelope, and `exactSynthesisCost_le_benchmark` plus
  `exactSynthesisCost_isBigOWith_fixedSchedule` aggregate the affine backend.
- **Status:** source path correction and exact affine structural formulas proved;
  the library backend's stronger aggregate upper bound is proved. The source's
  unrepresented complete Gray-walk macro count remains partial rather than being
  transferred to the affine circuit.

## C-031 — Main synthesis replaces the Gray walk by affine endpoint normalization

- **Source:** Section 8 two-level implementation, manuscript pp. 27–28; Markdown
  lines 959–976.
- **Issue:** the source moves between two basis strings one Gray edge at a time,
  applies a multiply controlled block at the final edge, and reverses the walk.
  This is a valid architecture only after endpoint orientation, negative controls,
  chronology, and reverse restoration are supplied. It is not forced by the
  mathematics, and attaching its `2m-3` macro count to a different implementation
  would be invalid.
- **Repair:** the main library uses an exact affine normalization. Local X gates on
  the true wires of the first endpoint send it to the all-zero assignment and send
  the second endpoint to their Boolean difference. Choose one differing pivot and
  use that pivot as the control of a CNOT to every other differing wire; the pair
  is then all-zero and the singleton supported at the pivot. Apply one exactly
  oriented adjacent mixed-polarity block and execute the adjoint affine circuit.
  The source's duplicate-free shortest Hamming path remains formalized separately
  for traceability.
- **Dependent impact:** arbitrary two-level circuits, their exact X/CNOT counts,
  the final universality circuit, and Stage 12 resource aggregation. The library's
  main circuit has one fully controlled block per algebraic factor instead of a
  repeated controlled block at every path edge, so the paper's path-macro formula
  is not its resource formula.
- **Formal evidence:** `affinePairCircuit`,
  `eval_affinePairCircuit_mulVec_basisKet`,
  `eval_affinePairCircuit_first`, `eval_affinePairCircuit_second`,
  `affinePairCircuit_oneQubitCount`, `affinePairCircuit_cnotCount`,
  `affinePairCircuit_oneQubitCNOTCost`,
  `unitary_conjugate_twoLevelUnitary`, `eval_twoLevelCircuit`,
  `affinePairGateCount_le`, `twoLevelCircuitCost_le_sq_succ`, and the aggregate
  `exactSynthesisCost_bounds` theorem.
- **Status:** implementation difference documented and exact circuit semantics
  and aggregate resource comparison proved.

## C-032 — Section 8's at-most-two-qubit model includes one-control macros

- **Source:** Section 8, manuscript p. 26; Markdown lines 891–900.
- **Issue:** the first formal cost model for Section 8 accepted `.oneQubit`,
  `.cnot`, and `.arbitraryTwoQubit`, but rejected every
  `.controlledOneQubit controls` node. That was too coarse: a zero-control macro
  acts on one wire and a one-control macro on exactly two. The omission prevented
  the already certified five-node Lemma 6.1 and thirteen-node Lemma 7.1 circuits
  from receiving their stated Section 8 upper counts. It also made a recursive
  rejection theorem accidentally true only because valid two-wire nodes were
  being rejected.
- **Repair:** price `.controlledOneQubit controls` at one exactly when
  `controls <= 1`, and continue to reject it when `2 <= controls`. Re-audit every
  earlier theorem that mentioned the model. The recursive five-node circuit has
  cost five at prefix arities zero and one and is rejected only from prefix arity
  two onward.
- **Dependent impact:** the Section 8 five- and thirteen-operation upper bounds,
  both unmerged relative-phase circuits, the later explicit three-gate
  implementation, the recursive macro boundary, and the comparison between the
  two named models. It does not create an arbitrary two-qubit embedding or, by
  itself, justify gate merging.
- **Formal evidence:** `CostModel.arbitraryTwoQubit_controlled`,
  `CostModel.arbitraryTwoQubit_controlled_eq_some_one_iff`,
  `Primitive.arbitraryTwoQubit_cost_positiveControlled`,
  `recursiveViaSquareCircuit_arbitraryTwoQubitCost`,
  `doubleControlledRootCircuit_arbitraryTwoQubitCost`, and
  `fourBitGrayCircuit_arbitraryTwoQubitCost`. The distinct syntax-and-semantics
  proof for the relative-phase merger is recorded separately in C-036.
- **Status:** corrected and proved with explicit zero-, one-, and at-least-two
  control boundaries. The two source circuits retain exact Section 8 cost seven;
  C-036 proves the separate named three-node implementation rather than repricing
  either source list.

## C-033 — A fixed-schedule Theta lower bound is not target hardness

- **Source:** Section 8, manuscript pp. 27–28; Markdown lines 939–983.
- **Issue:** the source presents `Theta(n^3 * 4^n)` as the cost of its general
  synthesis outline, but does not distinguish a lower bound caused by a fixed
  non-pruning schedule from a lower bound on all circuits for the target unitary.
  Those are radically different claims. In particular, the library eliminator
  emits its complete factor schedule even for the identity.
- **Repair:** count the selected syntax exactly before taking asymptotics. In
  width `k+1`, elimination emits `Nat.choose (2^(k+1)) 2` factor circuits and the
  diagonal stage emits `2^k` blocks, for `2*4^k` scheduled blocks in total. The
  affine backend gives a quadratic envelope per block and the machine-checked
  finite sandwich
  `2*(k+1)^2*4^k <= exactSynthesisCost <= 112*(k+1)^2*4^k`.
  Export `Theta((k+1)^2*4^k)` only under a name that says `fixedSchedule`.
- **Dependent impact:** the aggregate universality resource headline and every
  comparison with conjectural dimension lower bounds. The upper inequality is a
  valid construction bound for every target. The lower inequality describes
  padding in this particular implementation; it says nothing about an optimal
  circuit, and is especially non-informative for easy targets such as identity.
- **Formal evidence:** `decomposeQubitUnitary_factors_length`,
  `allComplementPatterns_length`, `choose_two_pow_succ_add_pow`,
  `two_mul_exactSynthesisBenchmark_le_cost`, `exactSynthesisCost_bounds`,
  `exactSynthesisCost_isBigOWith_fixedSchedule`, and
  `exactSynthesisCost_isTheta_fixedSchedule`.
- **Status:** corrected and proved for the named non-pruning affine construction;
  no general exact-synthesis lower bound or optimality theorem is claimed.

## C-034 — “Most efficient known” is not a timeless mathematical theorem

- **Source:** Section 7, manuscript p. 18; Markdown line 652.
- **Issue:** after discussing the Gray construction, the paper says it was the
  most efficient known method for three through eight bits. This is a historical
  comparative statement, not a theorem proved in the paper. It does not specify
  an exhaustive circuit class, whether gates may be merged, the precise primitive
  cost model, or a reproducible search/benchmark protocol. It is also inherently
  time-dependent.
- **Repair:** classify the statement explicitly as unverified historical context.
  Export only construction-specific exact counts and proved bounds for named
  syntax. Do not reinterpret “known” as an optimality or minimality theorem.
- **Dependent impact:** the status of Lemma 7.1's resource row and any comparison
  between the raw Gray expansion, later recursive constructions, or modern
  synthesis methods. No semantic circuit theorem depends on the claim.
- **Formal evidence:** the library's exact `expandedGrayControlledCircuit` count
  theorems price one specific schedule. No declaration asserts comparative
  efficiency or optimality.
- **Status:** intentionally excluded as a formal theorem and now explicitly traced.

## C-035 — Lemma 7.1's post-merger one-qubit count lacks a merger construction

- **Source:** Section 7, manuscript p. 18; Markdown lines 654–665.
- **Issue:** after the omitted Gray-code proof, the paper reports a post-merger
  count of `2 * 2^(n-1)` one-bit gates and `3 * 2^(n-1) - 4` XOR gates. The
  inter-block one-qubit merger schedule is not displayed or proved. A semantic
  equality cannot by itself justify deleting or combining syntax nodes.
- **Repair:** retain the checked raw profile, then reconstruct the missing merger
  with coherent factor provenance. Select the phase/A/B/C package once for `V`,
  use its literal reverse/inverse block for `V⁻¹`, prove that consecutive nonempty
  Gray masks have opposite cardinality parity, and expose each outgoing target
  endpoint across the control-only Gray CNOT. Executable free-group normalization
  deletes the resulting inverse endpoint pair at every one of the `2^m-2`
  internal boundaries. A literal regrouping theorem connects these local rewrites
  to the established raw schedule, and exact evaluator plus ordered-CNOT-trace
  theorems connect the emitted syntax to the established Lemma 7.1 macro on an
  arbitrary ambient register.
- **Dependent impact:** Lemma 7.1 resource status, the historical small-width
  comparison, and any downstream formula that uses the source's merged primitive
  count. The exact Gray semantics and CNOT count are unaffected.
- **Formal evidence:** `coherentGrayControlledViaRootCircuit`,
  `normalizeAtWire_grayBoundary`,
  `coherentGrayRegroupedViaRootCircuit_eq_raw`,
  `mergedGrayControlledViaRootSymbolicCircuit_eq_normalForm`,
  `eval_mergedGrayControlledCircuit`,
  `cnotTrace_mergedGrayControlledViaRootSymbolicCircuit_eq_raw`, and the
  `mergedGrayControlledViaRoot*Count`/cost theorems.
- **Status:** corrected and proved. For `m=n-1>0` controls, the named exact emitted
  syntax has `2 * 2^m` one-qubit nodes, `3 * 2^m - 4` CNOTs, and total/cost
  `5 * 2^m - 4`, exactly the source's post-merger arithmetic. This is a
  constructive upper count, not a minimum.

## C-036 — Section 8's cost-three statement omits the merged syntax and phase scope

- **Source:** Section 6.2, manuscript p. 16; Section 8, manuscript p. 26;
  Markdown lines 567–583 and 891–901.
- **Issue:** the source says that three arbitrary two-bit operations produce
  Toffoli “modulo phases” after permitting mergers in the Section 6.2 construction,
  but it gives neither the three merged payloads nor an evaluator-preservation
  argument. Exact semantics and cost seven for the original list cannot establish a
  cost-three theorem for different syntax. The phrase “modulo phases” is also not
  one global scalar here: the displayed A/B circuits have an input-column sign on
  `101`. The following numerical discussion explicitly does not prove that three is
  minimal.
- **Repair:** retain the A chronology in transparent syntax and apply the general
  exact Section 8 normalizer. It emits three certified ordered-pair `U(4)` nodes:
  `A; CNOT(second,target)`, `A; CNOT(first,target)`, and
  `A†; CNOT(second,target); A†`. Define that list independently as
  `relativePhaseToffoliThreeGateFusionCircuit`, lower it only through the trusted
  arbitrary-two-qubit constructor, and prove exact full-register equality to both
  the seven-node A evaluator and `relativeToffoliUnitary`. Under pairwise-distinct
  named wires, transfer the exact `101` signed basis action and its
  `BasisPhaseEq`, `SameBasisBehavior`, and `BasisMeasurementEq` consequences.
  Use the all-zero and `101` columns to prove separately that the circuit is
  neither exact Toffoli nor related to Toffoli by one global phase.
  Derive the profile `(oneQ,CNOT,U4,total)=(0,0,3,3)` and both partial costs from
  the named fusion and lowered syntax.
- **Dependent impact:** the Section 8 cost-three statement is recovered as a
  constructive upper count. The original A and B lists remain seven-node syntax;
  the B diagram has no separate normalizer-output theorem, and the generic `U(4)`
  output is unsupported by the Sections 3–7 one-qubit/CNOT model. This result does
  not change Corollary 7.4's early-model expansion, settle Lemma 7.1's distinct Gray
  merger problem, prove optimizer completeness, or establish a three-gate lower
  bound.
- **Formal evidence:**
  `section8Normalize_relativePhaseToffoliAFusionCircuit`,
  `eval_relativePhaseToffoliThreeGateFusionCircuit_eq_A`,
  `eval_relativePhaseToffoliThreeGateCircuit_eq_A`,
  `eval_relativePhaseToffoliThreeGateCircuit`,
  `relativePhaseToffoliThreeGateCircuit_mulVec_basisKet`,
  `relativePhaseToffoliThreeGateCircuit_basisPhaseEq_toffoli`,
  `relativePhaseToffoliThreeGateCircuit_sameBasisBehavior`,
  `relativePhaseToffoliThreeGateCircuit_basisMeasurementEq`,
  `relativePhaseToffoliThreeGateCircuit_ne_toffoli`,
  `relativePhaseToffoliThreeGateCircuit_not_globalPhaseEq_toffoli`, and the
  fusion and lowered component/count/cost theorems compile.
- **Status:** clarified and proved as an explicit syntax-derived constructive upper
  count. Exact-Toffoli and global-phase equality are formally refuted; no channel,
  all-measurement, arbitrary-input measurement, or minimality theorem is claimed.

## C-037 — Gray inverse mergers require one coherent factor choice

- **Source:** Section 7, manuscript pp. 17–18; Markdown lines 616–665.
- **Issue:** applying the Section 5 existence theorem independently to every
  signed root produces correct controlled-`V` and controlled-`V⁻¹` blocks, but it
  does not make their selected A/B/C factors definitionally or theoremically
  inverse. Therefore the paper's boundary cancellation cannot be justified from
  independently chosen decompositions, even though their complete matrices have
  the desired semantics.
- **Repair:** `grayFactorValuation V` makes exactly one selected factor package
  visible to the optimizer. Odd Gray masks use the boundary-oriented positive
  block `A; phase; CNOT; B; CNOT; C`; nonempty even masks use its literal formal
  adjoint `C⁻¹; CNOT; B⁻¹; CNOT; phase⁻¹; A⁻¹`. The symbolic atom grammar records
  inverse provenance, while the valuation theorem proves the positive and
  negative blocks implement the required signed roots. No equality decision on
  unitary matrices is used.
- **Dependent impact:** this coherent family replaces the independently selected
  raw fusion family only for the post-merger proof. The older raw builder and all
  of its semantics/count theorems remain valid; they simply do not certify the
  missing inverse relationship. The repair enables C-035 without changing the
  controlled-unitary target or discarding scalar phase.
- **Formal evidence:** `GrayFactorAtom`, `grayFactorValuation`,
  `grayPositiveRootSymbolicCircuit`, `grayNegativeRootSymbolicCircuit`,
  `eval_erase_coherentGrayRootSymbolicCircuit`, and
  `eval_erase_coherentGrayControlledViaRootCircuit_eq_macro`.
- **Status:** corrected and proved for every positive control count and arbitrary
  ordered ambient layout.
