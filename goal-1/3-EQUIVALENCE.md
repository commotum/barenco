# 3-EQUIVALENCE

Status: complete.

## Current Facts

- Stage 2 exposes raw `Gate n` matrices, certified `UnitaryGate n`, basis kets and
  matrix extensionality, arbitrary-target local/positive-controlled gates, trusted
  circuit primitives, and chronological certified evaluation/adjoints.
- `Primitive.mk` is private. Standard one-qubit/positive-control/CNOT metadata is
  correct by construction; arbitrary fallback gates are `.other` with full support.
- Exact, global-phase, input-basis-phase, classical basis-behavior,
  computational-basis measurement, channel, and arbitrary-effect algebraic
  relations now compile with only the implications that are mathematically valid.
- The selected approximation norm is mathlib's scoped L² induced operator norm;
  compiled laws include unitary invariance, product-error accumulation, state
  action, and a factor-two error bound for one computational-basis outcome.
- Syntax-derived counts, ambient width, touched support, and two named partial cost
  models now compile. Unsupported primitives propagate `none` and cannot silently
  count as free in either paper model.
- `BUILD-PLAN.md` governs module ownership, focused/adjacent builds, and boundary
  evidence for this stage.

## Updated Assumptions

- Basis-dependent phase is best represented as an independent unit-circle factor
  for each input column, matching “the output state for this basis input differs by
  a phase.” Left/post-composition preserves it; arbitrary right/pre-composition need
  not.
- Classical reversible behavior can be represented coarsely by which basis input
  maps to which basis output up to a unit phase. This relation is operationally
  meaningful for basis-monomial gates and intentionally ignores nonclassical detail.
- Full all-input/all-measurement equivalence should be modeled as equality of
  conjugation channels `ρ ↦ UρU†`; equal output density matrices imply equal Born
  weights for every effect. This is distinct from basis-only probabilities.
- `Circle` is the correct phase witness type; it packages unit norm rather than
  requiring repeated scalar hypotheses.
- Cost evaluation should be partial (`Option ℕ`) so unsupported/unclassified kinds
  cannot silently receive zero cost.

## Big Picture Objective

Implement and relate the exact, phase-relaxed, basis-behavior, observational,
operator-distance, and structural-cost notions needed to state every later paper
claim at its actual strength.

## Detailed Implementation Plan

- Define exact matrix/circuit equivalence.
- Define global-phase equality over `Circle`; prove equivalence, multiplication,
  adjoint, and exact-to-global rules.
- Define input-basis-dependent phase equality; prove equivalence, global-to-basis,
  basis action, post-composition, and computational-basis probability preservation.
- Define basis transition/classical behavior and prove the phase implications that
  are valid without declaring nonclassical gates classically equivalent by fiat.
- Define computational-basis measurement equality explicitly in terms of
  `Complex.normSq` of matrix entries.
- Define unitary conjugation channels and all-measurement/channel equality; prove
  equivalence, composition, global-phase implication, and equality of Born weights
  for arbitrary density/effect matrices.
- Add a small explicit one-qubit counterexample showing basis-dependent phase does
  not imply channel/all-measurement equality.
- Define L² operator distance and prove metric-style facts, multiplication/error
  bounds, and the state-vector action bound using the exact scoped matrix norm.
- Define exact syntax counts, touched support, partial named cost models for
  Sections 3–7 and Section 8, append/adjoint/count laws, and explicit rejection of
  `.other`/unsupported primitive kinds.
- Update the public root, conventions, traceability, corrections, axiom audit, and
  this stage evidence.

## Build Structure

- `Barenco/Equivalence/Phase.lean`: low-dependency public definitions and proofs for
  exact/global/basis phase plus basis-only observations.
- `Barenco/Equivalence/Measurement.lean`: public conjugation-channel and arbitrary
  effect/Born-weight layer, importing only `Phase` plus needed matrix trace algebra.
- `Barenco/Equivalence/OperatorNorm.lean`: public scoped L² norm/distance facts in a
  separate analysis leaf so algebraic consumers do not inherit the norm instance.
- `Barenco/Cost.lean`: public syntax-only counts and named partial cost models;
  imports `Circuit` but no phase/norm theorem leaf.
- `Barenco/EquivalenceExamples.lean`: diagnostic counterexamples and small relation
  checks; never imported by the root public API.
- `Barenco.lean`: thin re-export of the four public leaves; because this high-fanout
  file changes, adjacent root and two full builds are required.
- Runtime/public: relation/distance/cost definitions. Proof-side/public: laws and
  implications. Diagnostic: counterexamples. Fallback: only existing
  `Primitive.unclassified`, which cost models reject. No temporary public API.
- Focused builds target each new leaf. Adjacent builds target the diagnostic module,
  root `Barenco`, and `AxiomAudit`.

## Boundary Checks

- Channel equality is not defined as basis-probability equality; the former
  quantifies arbitrary input matrices and hence arbitrary downstream effects.
- Basis behavior is labeled as a coarse classical relation and not used as equality
  of quantum action.
- Scoped matrix norm instances remain isolated in the operator-norm leaf.
- Cost modules inspect `Primitive.kind`/syntax only and never reverse-engineer
  evaluator matrices.
- Partial cost evaluation must return `none` for `.other` and unsupported kinds.

## No-Cheating Checks

- Do not prove phase claims by checking only dimensions 1–3; general matrix/column
  proofs precede examples.
- Do not treat equality of modulus-squared entries as all-measurement equivalence.
- Do not assert basis-phase congruence under arbitrary pre-composition; include a
  checked counterexample or exact required hypothesis.
- Do not give unknown primitives zero cost or count semantic equality as a circuit.
- No `sorry`, `admit`, custom axioms, `native_decide`, or `bv_decide`.

## Completion Requirements

- [x] Exact/global/basis-phase definitions and equivalence/implication/congruence
  theorems compile.
- [x] Basis behavior and computational-basis measurement relations compile with
  justified phase implications.
- [x] Channel/all-measurement equality, channel composition, global-phase
  implication, and arbitrary-effect Born-weight consequence compile.
- [x] A kernel-checked counterexample separates basis-dependent phase from channel
  equality.
- [x] L² operator distance and state-action/submultiplicative error bounds compile
  without leaking a global norm instance into algebra modules.
- [x] Syntax length/support/kind counts and both named partial cost models compile;
  `.other` and unsupported kinds are proved rejected.
- [x] Append and adjoint preservation/additivity facts compile for counts/costs.
- [x] Focused, adjacent, warning-as-error, two full builds, scans, and headline
  axiom output are recorded.
- [x] Documentation maps every new relation/cost definition and carries remaining
  approximation/resource obligations forward explicitly.

## Stage Results

- `Barenco/Equivalence/Phase.lean` defines `ExactCircuitEq`, `GlobalPhaseEq`,
  input-column `BasisPhaseEq`, `BasisTransition`, `SameBasisBehavior`, and
  `BasisMeasurementEq`. It proves equivalence laws and the exact valid implication
  chain; only common postcomposition is exported for basis-dependent phases.
- `Barenco/Equivalence/Measurement.lean` defines raw conjugation channels,
  `ChannelEq`, `BornWeight`, and algebraically strengthened `AllMeasurementEq`.
  Matrix-unit effects prove `channelEq_iff_allMeasurementEq`; global phase cancels,
  and channel equality implies computational-basis probability equality.
- `Barenco/EquivalenceExamples.lean` is diagnostic-only. Its explicit `diag(1,-1)`
  example is basis-phase equivalent to identity but not channel/all-measurement
  equivalent, preventing an invalid implication from entering the public API.
- `Barenco/Equivalence/OperatorNorm.lean` isolates the scoped L² operator norm and
  defines `operatorDistance`. Its public proofs include metric laws, unitary
  invariance, two-factor error accumulation, state/coordinate bounds, and
  `operatorDistance_basisOutcomeProbability_le`, which proves the exact factor-two
  bound for one basis outcome when `‖ψ‖ ≤ 1`. Arbitrary events and POVMs remain
  explicit later obligations.
- `Barenco/Cost.lean` defines `Circuit.registerWidth`, `gateCount`, `kindCount`,
  `touchedSupport`, partial `Circuit.cost`, and `CostModel.oneQubitCNOT` versus
  `CostModel.arbitraryTwoQubit`. Counts/costs satisfy append and adjoint laws;
  support cardinality is bounded by width; named models reject any circuit
  containing `.unclassified` or another unsupported kind.
- Width is a structural type-index resource. Clean/dirty ancilla initialization,
  ownership, entanglement, and restoration are intentionally deferred to Stage 8,
  where they can be stated as semantic contracts for actual constructions rather
  than guessed from a numeric width annotation. This is the recorded refinement of
  the broader Stage 3 wording in `0-plan.md`.
- Runtime/public declarations are the relation, distance, cost, width/count, and
  channel definitions. Their laws are proof-side/public. The separation example is
  diagnostic. `Primitive.unclassified` remains the sole fallback and both named
  paper models prove that they reject it. No temporary declarations entered the API.
- Focused/adjacent verification:
  `lake build Barenco.Equivalence.Phase Barenco.Equivalence.Measurement
  Barenco.Equivalence.OperatorNorm Barenco.Cost Barenco.EquivalenceExamples
  Barenco.AxiomAudit Barenco` succeeded with 2,372 jobs.
- Direct `lake env lean -DwarningAsError=true` compilation succeeded for all four
  public leaves, the diagnostic example, `AxiomAudit`, and the public root.
  Two unchanged `lake build` runs then succeeded with 2,370 jobs each.
- The completed Lean-source scan found no `sorry`, `admit`, `by?`, `native_decide`,
  `bv_decide`, project `axiom`, or `opaque` declaration; the Lean trailing-space
  scan and `git diff --check` were clean.
- `Barenco/AxiomAudit.lean` prints 29 headline declarations. Every declaration
  reports exactly `[propext, Classical.choice, Quot.sound]`, with no project-specific
  axiom. The exact table and build evidence are in `docs/axiom-audit.md`.
