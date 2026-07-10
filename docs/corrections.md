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
- **Formal evidence:** planned integer-bound and reconstructed-circuit theorems.
- **Status:** open.

## C-004 — Corollary 7.4 remainder has an arithmetic error

- **Source:** manuscript p. 20; Markdown lines 704–712.
- **Issue:** the proof has `8(n−5)=8n−40` Toffolis, says four must be exact, then
  calls the remainder `8n−36`. The correct remainder is `8n−44`.
- **Repair:** use four exact and `8n−44` relative-phase Toffoli occurrences. The
  final printed `48n−204` may still result after expansions and one-qubit mergers,
  but it does not follow from the erroneous intermediate sentence and must be
  reconstructed syntactically.
- **Dependent impact:** exact early-basic count in Corollary 7.4 and leading counts
  derived from it.
- **Formal evidence:** planned syntax count; no claim yet that `48n−204` is correct.
- **Status:** open.

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
- **Formal evidence:** planned recurrence and lower-bound modules.
- **Status:** open.

## C-006 — Lemma 7.8 cites the wrong recursive lemma

- **Source:** Lemma 7.8 proof, manuscript p. 23; Markdown line 782.
- **Issue:** it says the matrices are used in recursive applications of Lemma 7.3.
  The relevant square-root recursion is Lemma 7.5.
- **Repair:** replace the cross-reference with Lemma 7.5.
- **Dependent impact:** traceability and proof narrative only.
- **Formal evidence:** corrected dependency planned in approximation module.
- **Status:** open.

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
  `Barenco.OneQubit.unitaryRoot` chooses the principal-argument spectral root and
  `unitaryRoot_pow` proves its exact `k`th power is the input.
  `unitarySquareRoot_pow_two` and `unitaryRoot_pow_two_pow` supply exact square and
  power-of-two root equations. The finite-spectrum continuous-functional-calculus
  implementation does not assume a globally continuous principal-root function.
- **Status:** partial. Exact positive root existence, including all power-of-two
  roots, is proved. No exported theorem yet relates the selected roots at adjacent
  depths, proves `‖Dₖ-I‖≤π/2^k`, synthesizes the roots as circuits, or derives the
  approximation/resource bounds of Lemma 7.8.

## C-008 — Lemma 7.8 does not handle all epsilon regimes

- **Source:** Lemma 7.8 statement/proof, manuscript pp. 23–24; lines 774–850.
- **Issue:** the statement allows every `ε>0`, while an unqualified
  `log(1/ε)` becomes nonpositive for large `ε`. The proposed integer depth
  `ceil(log₂(π/ε))` can also exceed the number of available recursive levels.
- **Repair:** state an explicit integer-depth theorem. For the asymptotic corollary,
  restrict the logarithmic regime (for example `0<ε<1`), cap approximate recursion
  by the available controls, and use exact synthesis as fallback. A safe uniform
  upper shape is `O(n · min(n, ceil(log₂(π/ε))))` plus fixed overhead, with boundary
  cases stated separately.
- **Dependent impact:** Lemma 7.8 and any universality-efficiency claim using it.
- **Formal evidence:** `Barenco.operatorDistance` now fixes the L² induced operator
  norm and its metric, multiplication, unitary-invariance, state-action, and
  single-basis-outcome factor-two probability laws. The recursion-depth/epsilon
  repair itself remains planned.
- **Status:** open; exact best finite formula not yet selected.

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
  `BasisMeasurementEq` are separate relations. The compiled implications include
  global-to-basis phase, basis phase to basis probabilities, and global phase to
  channel equality. No Section 6.2 circuit witness has been supplied.
- **Status:** partial: the semantic ambiguity is resolved, while both relative-phase
  Toffoli diagrams and their claimed later cancellation remain open.

## C-010 — Auxiliary-wire contracts are underspecified

- **Source:** Lemmas 7.2–7.3 and 7.11, manuscript pp. 18–20 and 25.
- **Issue:** the constructions mix borrowed arbitrary wires and a fixed-zero wire,
  while prose says only that bits “incur no net change.” This does not by itself
  express correctness on superpositions or restoration of entanglement.
- **Repair:** prove full-register equality for dirty borrowed wires. State Lemma 7.11
  as equality on the clean-zero input subspace, quantified over arbitrary data
  states, and prove output factorization/restoration.
- **Dependent impact:** Corollaries 7.4, 7.10, 7.12 and downstream reuse of ancillas.
- **Formal evidence:** planned ancilla contract theorems.
- **Status:** open.

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
  syntax-based worst-case/uniform `O(n³4^n)` upper bound. A `Θ` result may describe a
  deliberately fixed schedule that retains identity gates, but not optimal cost
  without a matching theorem.
- **Dependent impact:** central exact-universality and resource headline results.
- **Formal evidence:** planned universality/resource stages.
- **Status:** open.

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
  norm-at-most-one hypothesis.
- **Status:** corrected and proved as an algebraic separation, with the single-basis
  probability consequence proved. Physical density/effect structures and general
  event/POVM error bounds remain open.

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
