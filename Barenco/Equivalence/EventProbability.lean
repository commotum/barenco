import Barenco.Equivalence.OperatorNorm

/-!
# Computational-basis event probabilities

This module turns the coordinatewise probability estimate from
`Barenco.Equivalence.OperatorNorm` into a cardinality-free estimate for an
arbitrary finite event in the computational basis.

An `event : Finset ι` denotes the projective measurement effect obtained by
summing the standard-basis projectors indexed by `event`.  This is narrower
than an arbitrary projector or POVM effect: no result in this file should be
read as a general POVM theorem.  Conversely, the event may contain any number
of basis outcomes; the bound below has no factor depending on `event.card`.

For a possibly unnormalized amplitude vector, `eventProbability` is a Born
weight.  It is a probability when the vector has norm one, and a subprobability
for a vector of norm at most one.  The main result assumes the latter, slightly
stronger, hypothesis.

Two explicit maps expose the geometry used in the proof:

* `eventProjection` keeps the event coordinates and zeros the others.  Its norm
  is contractive, and its squared norm is exactly the event probability.
* `eventReflection` is `+1` on the event and `-1` off the event.  It is a linear
  isometric equivalence.  Its expectation yields a sharp, cardinality-free
  probability estimate.

The sharp exported bound has constant one.  A separate constant-two corollary
records exactly the weaker estimate claimed in Barenco et al.
-/

namespace Barenco

open Matrix
open scoped Matrix.Norms.L2Operator

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/--
The Born weight of a finite computational-basis event in an amplitude vector.

No normalization is built into the definition.  Thus this is a probability
only when `ψ` is normalized (and a subprobability when `‖ψ‖ ≤ 1`).
-/
def eventProbability (event : Finset ι) (ψ : ι → ℂ) : ℝ :=
  ∑ i ∈ event, Complex.normSq (ψ i)

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem eventProbability_empty (ψ : ι → ℂ) :
    eventProbability ∅ ψ = 0 := by
  simp [eventProbability]

omit [Fintype ι] [DecidableEq ι] in
/-- Computational-basis event weights are nonnegative. -/
theorem eventProbability_nonneg (event : Finset ι) (ψ : ι → ℂ) :
    0 ≤ eventProbability event ψ := by
  exact Finset.sum_nonneg fun _ _ ↦ Complex.normSq_nonneg _

/-- The coordinate projection onto a computational-basis event. -/
noncomputable def eventProjection (event : Finset ι) :
    EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι where
  toFun ψ := WithLp.toLp 2 (fun i ↦ if i ∈ event then ψ i else 0)
  map_add' x y := by
    ext i
    by_cases hi : i ∈ event <;> simp [hi]
  map_smul' c x := by
    ext i
    by_cases hi : i ∈ event <;> simp [hi]

omit [Fintype ι] in
@[simp]
theorem eventProjection_apply (event : Finset ι)
    (ψ : EuclideanSpace ℂ ι) (i : ι) :
    eventProjection event ψ i = if i ∈ event then ψ i else 0 :=
  rfl

/-- Restricting an L2 vector to a computational-basis event is contractive. -/
theorem eventProjection_norm_le (event : Finset ι)
    (ψ : EuclideanSpace ℂ ι) :
    ‖eventProjection event ψ‖ ≤ ‖ψ‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _),
    EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  apply Finset.sum_le_sum
  intro i _
  by_cases hmem : i ∈ event <;> simp [hmem]

/-- Event probability is the squared norm of the explicit event projection. -/
theorem eventProbability_eq_eventProjection_norm_sq
    (event : Finset ι) (ψ : EuclideanSpace ℂ ι) :
    eventProbability event ψ = ‖eventProjection event ψ‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, eventProbability]
  simp only [Complex.normSq_eq_norm_sq, eventProjection_apply]
  have hterm (i : ι) :
      ‖if i ∈ event then ψ i else 0‖ ^ 2 =
        if i ∈ event then ‖ψ i‖ ^ 2 else 0 := by
    by_cases hi : i ∈ event <;> simp [hi]
  simp_rw [hterm]
  rw [← Finset.sum_filter]
  simp

omit [Fintype ι] in
/-- The event projection is idempotent. -/
@[simp]
theorem eventProjection_eventProjection (event : Finset ι)
    (ψ : EuclideanSpace ℂ ι) :
    eventProjection event (eventProjection event ψ) = eventProjection event ψ := by
  ext i
  by_cases hi : i ∈ event <;> simp [hi]

/--
Reflection across the event-coordinate subspace: `+1` on the event and `-1`
on its complement.
-/
noncomputable def eventReflection (event : Finset ι) :
    EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι where
  toLinearEquiv :=
    { toFun := fun ψ ↦
        WithLp.toLp 2 (fun i ↦ if i ∈ event then ψ i else -ψ i)
      invFun := fun ψ ↦
        WithLp.toLp 2 (fun i ↦ if i ∈ event then ψ i else -ψ i)
      left_inv := by
        intro x
        ext i
        by_cases hi : i ∈ event <;> simp [hi]
      right_inv := by
        intro x
        ext i
        by_cases hi : i ∈ event <;> simp [hi]
      map_add' := by
        intro x y
        ext i
        by_cases hi : i ∈ event
        · simp [hi]
        · simp [hi]
          abel
      map_smul' := by
        intro c x
        ext i
        by_cases hi : i ∈ event <;> simp [hi] }
  norm_map' := by
    intro x
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
      EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hmem : i ∈ event <;> simp [hmem]

@[simp]
theorem eventReflection_apply (event : Finset ι)
    (ψ : EuclideanSpace ℂ ι) (i : ι) :
    eventReflection event ψ i = if i ∈ event then ψ i else -ψ i :=
  rfl

/-- The event reflection is involutive. -/
@[simp]
theorem eventReflection_eventReflection (event : Finset ι)
    (ψ : EuclideanSpace ℂ ι) :
    eventReflection event (eventReflection event ψ) = ψ := by
  exact (eventReflection event).left_inv ψ

/-- Event probability written as a single sum over the full finite index type. -/
private theorem eventProbability_eq_ite_sum (event : Finset ι)
    (ψ : EuclideanSpace ℂ ι) :
    eventProbability event ψ =
      ∑ i : ι, if i ∈ event then Complex.normSq (ψ i) else 0 := by
  rw [eventProbability, ← Finset.sum_filter]
  simp

/--
The reflection expectation is twice the event probability minus the total
squared norm.  This is the finite-coordinate form of `R = 2P - I`.
-/
theorem eventReflection_inner_self_re (event : Finset ι)
    (ψ : EuclideanSpace ℂ ι) :
    (inner ℂ ψ (eventReflection event ψ)).re =
      2 * eventProbability event ψ - ‖ψ‖ ^ 2 := by
  rw [PiLp.inner_apply, Complex.re_sum, eventProbability_eq_ite_sum,
    EuclideanSpace.norm_sq_eq, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hnorm : ‖ψ i‖ ^ 2 = (ψ i).re ^ 2 + (ψ i).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hnormSq :
      Complex.normSq (ψ i) = (ψ i).re ^ 2 + (ψ i).im ^ 2 := by
    rw [Complex.normSq_apply]
    ring
  by_cases hmem : i ∈ event
  · simp [eventReflection_apply, hmem, pow_two, Complex.mul_re, hnormSq]
    nlinarith [hnorm]
  · simp [eventReflection_apply, hmem, pow_two, Complex.mul_re, hnorm]

/--
A sharp event estimate for two equal-norm pure amplitude vectors.

The equal-norm hypothesis is exactly what lets the non-event contribution
cancel in the reflection expectation.  Unitary images of a common input satisfy
it automatically.
-/
theorem abs_eventProbability_sub_eventProbability_le_of_norm_eq
    (event : Finset ι) (x y : EuclideanSpace ℂ ι) (hxyNorm : ‖x‖ = ‖y‖) :
    abs (eventProbability event x - eventProbability event y) ≤
      ‖x‖ * ‖x - y‖ := by
  let R := eventReflection event
  have hinner :
      inner ℂ x (R x) - inner ℂ y (R y) =
        inner ℂ (x - y) (R x) + inner ℂ y (R (x - y)) := by
    simp only [map_sub, inner_sub_left, inner_sub_right]
    ring
  have hrel :
      2 * (eventProbability event x - eventProbability event y) =
        (inner ℂ x (R x) - inner ℂ y (R y)).re := by
    dsimp only [R]
    rw [Complex.sub_re, eventReflection_inner_self_re,
      eventReflection_inner_self_re, hxyNorm]
    ring
  have hinnerBound :
      abs ((inner ℂ x (R x) - inner ℂ y (R y)).re) ≤
        2 * ‖x‖ * ‖x - y‖ := by
    calc
      abs ((inner ℂ x (R x) - inner ℂ y (R y)).re) ≤
          ‖inner ℂ x (R x) - inner ℂ y (R y)‖ :=
        Complex.abs_re_le_norm _
      _ = ‖inner ℂ (x - y) (R x) + inner ℂ y (R (x - y))‖ := by
        rw [hinner]
      _ ≤ ‖inner ℂ (x - y) (R x)‖ + ‖inner ℂ y (R (x - y))‖ :=
        norm_add_le _ _
      _ ≤ ‖x - y‖ * ‖R x‖ + ‖y‖ * ‖R (x - y)‖ :=
        add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
      _ = 2 * ‖x‖ * ‖x - y‖ := by
        rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map,
          ← hxyNorm]
        ring
  calc
    abs (eventProbability event x - eventProbability event y) =
        (1 / 2 : ℝ) *
          abs (2 * (eventProbability event x - eventProbability event y)) := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    _ = (1 / 2 : ℝ) *
        abs ((inner ℂ x (R x) - inner ℂ y (R y)).re) := by
      rw [hrel]
    _ ≤ (1 / 2 : ℝ) * (2 * ‖x‖ * ‖x - y‖) := by
      gcongr
    _ = ‖x‖ * ‖x - y‖ := by ring

/-! ### Unitary actions and operator-distance bounds -/

private noncomputable def unitaryAction (U : Matrix.unitaryGroup ι ℂ)
    (ψ : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  (EuclideanSpace.equiv ι ℂ).symm ((U : Matrix ι ι ℂ) *ᵥ ψ)

private theorem unitaryAction_mul (U V : Matrix.unitaryGroup ι ℂ)
    (ψ : EuclideanSpace ℂ ι) :
    unitaryAction (U * V) ψ = unitaryAction U (unitaryAction V ψ) := by
  ext i
  change ((((U : Matrix ι ι ℂ) * (V : Matrix ι ι ℂ)) *ᵥ ψ) i) =
    (((U : Matrix ι ι ℂ) *ᵥ ((V : Matrix ι ι ℂ) *ᵥ ψ)) i)
  rw [Matrix.mulVec_mulVec]

@[simp]
private theorem unitaryAction_one (ψ : EuclideanSpace ℂ ι) :
    unitaryAction (1 : Matrix.unitaryGroup ι ℂ) ψ = ψ := by
  ext i
  simp [unitaryAction]

private theorem unitaryAction_norm_le (U : Matrix.unitaryGroup ι ℂ)
    (ψ : EuclideanSpace ℂ ι) :
    ‖unitaryAction U ψ‖ ≤ ‖ψ‖ := by
  cases isEmpty_or_nonempty ι with
  | inl hempty =>
      letI := hempty
      have hψzero : ψ = 0 := Subsingleton.elim _ _
      subst ψ
      simp [unitaryAction]
  | inr hnonempty =>
      letI := hnonempty
      calc
        ‖unitaryAction U ψ‖ ≤ ‖(U : Matrix ι ι ℂ)‖ * ‖ψ‖ :=
          Matrix.l2_opNorm_mulVec (U : Matrix ι ι ℂ) ψ
        _ = ‖ψ‖ := by rw [CStarRing.norm_coe_unitary, one_mul]

private theorem unitaryAction_norm_eq (U : Matrix.unitaryGroup ι ℂ)
    (ψ : EuclideanSpace ℂ ι) :
    ‖unitaryAction U ψ‖ = ‖ψ‖ := by
  apply le_antisymm
  · exact unitaryAction_norm_le U ψ
  · have h := unitaryAction_norm_le U⁻¹ (unitaryAction U ψ)
    rw [← unitaryAction_mul, inv_mul_cancel, unitaryAction_one] at h
    exact h

/--
Sharp cardinality-free computational-basis event bound for unitary actions.

For any pure input of norm at most one, the change in the Born probability of
any finite computational-basis event is at most the L2 induced operator distance
between the two unitaries.  This theorem also covers an empty finite index type;
no `Nonempty ι` hypothesis is required.
-/
theorem operatorDistance_eventProbability_le
    (U V : Matrix.unitaryGroup ι ℂ) (ψ : EuclideanSpace ℂ ι)
    (hψ : ‖ψ‖ ≤ 1) (event : Finset ι) :
    abs
        (eventProbability event ((U : Matrix ι ι ℂ) *ᵥ ψ) -
          eventProbability event ((V : Matrix ι ι ℂ) *ᵥ ψ)) ≤
      operatorDistance (U : Matrix ι ι ℂ) (V : Matrix ι ι ℂ) := by
  let x := unitaryAction U ψ
  let y := unitaryAction V ψ
  change abs (eventProbability event x - eventProbability event y) ≤
    operatorDistance (U : Matrix ι ι ℂ) (V : Matrix ι ι ℂ)
  have hxNorm : ‖x‖ = ‖ψ‖ := unitaryAction_norm_eq U ψ
  have hyNorm : ‖y‖ = ‖ψ‖ := unitaryAction_norm_eq V ψ
  have hxyNorm : ‖x‖ = ‖y‖ := hxNorm.trans hyNorm.symm
  have hdiff :
      ‖x - y‖ ≤ operatorDistance (U : Matrix ι ι ℂ) (V : Matrix ι ι ℂ) := by
    calc
      ‖x - y‖ =
          ‖(EuclideanSpace.equiv ι ℂ).symm
            (((U : Matrix ι ι ℂ) - (V : Matrix ι ι ℂ)) *ᵥ ψ)‖ := by
        congr 1
        ext i
        simp [x, y, unitaryAction, Matrix.sub_mulVec]
      _ ≤ operatorDistance (U : Matrix ι ι ℂ) (V : Matrix ι ι ℂ) * ‖ψ‖ :=
        operatorDistance_action_le (U : Matrix ι ι ℂ) (V : Matrix ι ι ℂ) ψ
      _ ≤ operatorDistance (U : Matrix ι ι ℂ) (V : Matrix ι ι ℂ) * 1 :=
        mul_le_mul_of_nonneg_left hψ (operatorDistance_nonneg _ _)
      _ = operatorDistance (U : Matrix ι ι ℂ) (V : Matrix ι ι ℂ) := mul_one _
  calc
    abs (eventProbability event x - eventProbability event y) ≤
        ‖x‖ * ‖x - y‖ :=
      abs_eventProbability_sub_eventProbability_le_of_norm_eq event x y hxyNorm
    _ ≤ 1 * operatorDistance (U : Matrix ι ι ℂ) (V : Matrix ι ι ℂ) := by
      exact mul_le_mul (hxNorm.le.trans hψ) hdiff (norm_nonneg _) (by norm_num)
    _ = operatorDistance (U : Matrix ι ι ℂ) (V : Matrix ι ι ℂ) := one_mul _

/--
The constant-two computational-basis event estimate stated by Barenco et al.

The factor two is valid but non-sharp; `operatorDistance_eventProbability_le`
proves the stronger constant-one bound under the same hypotheses.  This remains
a theorem about standard-basis events, not arbitrary POVMs.
-/
theorem operatorDistance_eventProbability_le_two_mul
    (U V : Matrix.unitaryGroup ι ℂ) (ψ : EuclideanSpace ℂ ι)
    (hψ : ‖ψ‖ ≤ 1) (event : Finset ι) :
    abs
        (eventProbability event ((U : Matrix ι ι ℂ) *ᵥ ψ) -
          eventProbability event ((V : Matrix ι ι ℂ) *ᵥ ψ)) ≤
      2 * operatorDistance (U : Matrix ι ι ℂ) (V : Matrix ι ι ℂ) := by
  calc
    abs
          (eventProbability event ((U : Matrix ι ι ℂ) *ᵥ ψ) -
            eventProbability event ((V : Matrix ι ι ℂ) *ᵥ ψ)) ≤
        operatorDistance (U : Matrix ι ι ℂ) (V : Matrix ι ι ℂ) :=
      operatorDistance_eventProbability_le U V ψ hψ event
    _ ≤ 2 * operatorDistance (U : Matrix ι ι ℂ) (V : Matrix ι ι ℂ) := by
      nlinarith [operatorDistance_nonneg (U : Matrix ι ι ℂ) (V : Matrix ι ι ℂ)]

end Barenco
