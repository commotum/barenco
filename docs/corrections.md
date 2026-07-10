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
  `Barenco.Basic`.
- **Status:** corrected and proved at the convention/translation layer; every
  downstream paper diagram must still use the bridge explicitly.

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
- **Repair:** choose eigenangles in a principal interval and construct a coherent
  root sequence from those choices. Prove unitarity, squaring, and the norm bound.
- **Dependent impact:** Lemma 7.8 error and depth bounds; general root API.
- **Formal evidence:** planned root/approximation theorems.
- **Status:** open.

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
- **Status:** corrected and proved at the cost-model foundation. Every numerical
  paper bound still requires a concrete supported circuit and its own theorem.

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
