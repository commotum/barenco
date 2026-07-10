import Barenco.Circuit
import Mathlib.Analysis.Complex.Circle

/-!
# Exact, phase-relaxed, and computational-basis equivalence

This module separates five relations that later circuit constructions need:

* `ExactCircuitEq` is equality of certified circuit denotations.
* `GlobalPhaseEq U V` means `V = ζ • U` for one `ζ : Circle`.
* `BasisPhaseEq U V` permits an independent unit phase for every input column.
* `SameBasisBehavior` remembers only exact basis-to-basis transitions up to phase.
* `BasisMeasurementEq` compares squared moduli of computational-basis amplitudes.

Matrices act on column vectors from the left.  Thus multiplying both sides of a
`BasisPhaseEq` by the same matrix on the left is post-composition and preserves
the relation.  Multiplication on the right mixes input columns and is deliberately
not exposed as a congruence theorem.
-/

namespace Barenco

open Matrix

/-! ## Exact circuit equivalence -/

/-- Two circuits are exactly equivalent when their certified denotations agree. -/
def ExactCircuitEq {n : ℕ} (first second : Circuit n) : Prop :=
  Circuit.eval first = Circuit.eval second

namespace ExactCircuitEq

protected theorem refl {n : ℕ} (circuit : Circuit n) :
    ExactCircuitEq circuit circuit :=
  rfl

protected theorem symm {n : ℕ} {first second : Circuit n}
    (h : ExactCircuitEq first second) : ExactCircuitEq second first :=
  Eq.symm h

protected theorem trans {n : ℕ} {first second third : Circuit n}
    (h₁ : ExactCircuitEq first second) (h₂ : ExactCircuitEq second third) :
    ExactCircuitEq first third :=
  Eq.trans h₁ h₂

theorem equivalence (n : ℕ) : Equivalence (@ExactCircuitEq n) :=
  ⟨ExactCircuitEq.refl, ExactCircuitEq.symm, ExactCircuitEq.trans⟩

/-- Exact equivalence is a congruence for chronological circuit append. -/
theorem append {n : ℕ} {first first' second second' : Circuit n}
    (hFirst : ExactCircuitEq first first') (hSecond : ExactCircuitEq second second') :
    ExactCircuitEq (Circuit.append first second) (Circuit.append first' second') := by
  unfold ExactCircuitEq at *
  rw [Circuit.eval_append, Circuit.eval_append, hFirst, hSecond]

/-- Taking the adjoint circuit preserves exact equivalence. -/
theorem adjoint {n : ℕ} {first second : Circuit n} (h : ExactCircuitEq first second) :
    ExactCircuitEq (Circuit.adjoint first) (Circuit.adjoint second) := by
  unfold ExactCircuitEq at *
  rw [Circuit.eval_adjoint, Circuit.eval_adjoint, h]

end ExactCircuitEq

/-! ## One global phase -/

/-- `V` differs from `U` by one unit complex scalar. -/
def GlobalPhaseEq {ι : Type*} (U V : Matrix ι ι ℂ) : Prop :=
  ∃ phase : Circle, V = (phase : ℂ) • U

namespace GlobalPhaseEq

protected theorem refl {ι : Type*} (U : Matrix ι ι ℂ) : GlobalPhaseEq U U := by
  refine ⟨1, ?_⟩
  simp

protected theorem symm {ι : Type*} {U V : Matrix ι ι ℂ}
    (h : GlobalPhaseEq U V) : GlobalPhaseEq V U := by
  rcases h with ⟨phase, rfl⟩
  refine ⟨phase⁻¹, ?_⟩
  ext row col
  simp

protected theorem trans {ι : Type*} {U V W : Matrix ι ι ℂ}
    (hUV : GlobalPhaseEq U V) (hVW : GlobalPhaseEq V W) : GlobalPhaseEq U W := by
  rcases hUV with ⟨phaseUV, rfl⟩
  rcases hVW with ⟨phaseVW, rfl⟩
  refine ⟨phaseVW * phaseUV, ?_⟩
  simp [smul_smul]

theorem equivalence (ι : Type*) : Equivalence (@GlobalPhaseEq ι) :=
  ⟨GlobalPhaseEq.refl, GlobalPhaseEq.symm, GlobalPhaseEq.trans⟩

/-- Exact matrix equality implies global-phase equality, with phase one. -/
theorem of_eq {ι : Type*} {U V : Matrix ι ι ℂ} (h : U = V) : GlobalPhaseEq U V := by
  subst V
  exact GlobalPhaseEq.refl U

/-- Global phases multiply when matrix products are composed. -/
theorem mul {ι : Type*} [Fintype ι]
    {U V X Y : Matrix ι ι ℂ} (hUV : GlobalPhaseEq U V) (hXY : GlobalPhaseEq X Y) :
    GlobalPhaseEq (U * X) (V * Y) := by
  rcases hUV with ⟨phaseUV, rfl⟩
  rcases hXY with ⟨phaseXY, rfl⟩
  refine ⟨phaseUV * phaseXY, ?_⟩
  simp [smul_smul, mul_comm]

/-- Post-composition by the same matrix preserves a global phase. -/
theorem mul_left {ι : Type*} [Fintype ι] {U V : Matrix ι ι ℂ}
    (W : Matrix ι ι ℂ) (h : GlobalPhaseEq U V) :
    GlobalPhaseEq (W * U) (W * V) :=
  GlobalPhaseEq.mul (GlobalPhaseEq.refl W) h

/-- Pre-composition by the same matrix also preserves a single global phase. -/
theorem mul_right {ι : Type*} [Fintype ι] {U V : Matrix ι ι ℂ}
    (W : Matrix ι ι ℂ) (h : GlobalPhaseEq U V) :
    GlobalPhaseEq (U * W) (V * W) :=
  GlobalPhaseEq.mul h (GlobalPhaseEq.refl W)

/-- Taking conjugate transpose inverts the witnessing global phase. -/
theorem conjTranspose {ι : Type*} {U V : Matrix ι ι ℂ} (h : GlobalPhaseEq U V) :
    GlobalPhaseEq Uᴴ Vᴴ := by
  rcases h with ⟨phase, rfl⟩
  refine ⟨phase⁻¹, ?_⟩
  have hstar : star (phase : ℂ) = ((phase⁻¹ : Circle) : ℂ) :=
    (Circle.coe_inv_eq_conj phase).symm
  rw [Matrix.conjTranspose_smul, hstar]

/-- Quantum-gate terminology alias for `GlobalPhaseEq.conjTranspose`. -/
theorem adjoint {ι : Type*} {U V : Matrix ι ι ℂ} (h : GlobalPhaseEq U V) :
    GlobalPhaseEq Uᴴ Vᴴ :=
  GlobalPhaseEq.conjTranspose h

end GlobalPhaseEq

/-- Exact circuit equivalence implies global-phase equality of the raw matrices. -/
theorem ExactCircuitEq.toGlobalPhaseEq {n : ℕ} {first second : Circuit n}
    (h : ExactCircuitEq first second) :
    GlobalPhaseEq (Circuit.eval first : Gate n) (Circuit.eval second : Gate n) := by
  apply GlobalPhaseEq.of_eq
  exact congrArg (fun U : UnitaryGate n ↦ (U : Gate n)) h

/-! ## Independent phases on computational-basis input columns -/

/-- `V` differs from `U` by an independently chosen unit phase on each input column. -/
def BasisPhaseEq {ι : Type*} (U V : Matrix ι ι ℂ) : Prop :=
  ∃ phase : ι → Circle, ∀ row input, V row input = (phase input : ℂ) * U row input

namespace BasisPhaseEq

protected theorem refl {ι : Type*} (U : Matrix ι ι ℂ) : BasisPhaseEq U U := by
  refine ⟨fun _ ↦ 1, ?_⟩
  simp

protected theorem symm {ι : Type*} {U V : Matrix ι ι ℂ}
    (h : BasisPhaseEq U V) : BasisPhaseEq V U := by
  rcases h with ⟨phase, hphase⟩
  refine ⟨fun input ↦ (phase input)⁻¹, ?_⟩
  intro row input
  rw [hphase]
  simp

protected theorem trans {ι : Type*} {U V W : Matrix ι ι ℂ}
    (hUV : BasisPhaseEq U V) (hVW : BasisPhaseEq V W) : BasisPhaseEq U W := by
  rcases hUV with ⟨phaseUV, hUV⟩
  rcases hVW with ⟨phaseVW, hVW⟩
  refine ⟨fun input ↦ phaseVW input * phaseUV input, ?_⟩
  intro row input
  rw [hVW, hUV]
  simp [mul_assoc]

theorem equivalence (ι : Type*) : Equivalence (@BasisPhaseEq ι) :=
  ⟨BasisPhaseEq.refl, BasisPhaseEq.symm, BasisPhaseEq.trans⟩

/-- Exact matrix equality implies equality up to input-column phases. -/
theorem of_eq {ι : Type*} {U V : Matrix ι ι ℂ} (h : U = V) : BasisPhaseEq U V := by
  subst V
  exact BasisPhaseEq.refl U

/-- A single global phase is the constant special case of input-column phases. -/
theorem of_globalPhaseEq {ι : Type*} {U V : Matrix ι ι ℂ}
    (h : GlobalPhaseEq U V) : BasisPhaseEq U V := by
  rcases h with ⟨phase, hphase⟩
  refine ⟨fun _ ↦ phase, ?_⟩
  intro row input
  rw [hphase]
  rfl

/-- Entrywise input-column phases are equivalent to phased action on every basis ket. -/
theorem iff_mulVec_basisKet {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U V : Matrix ι ι ℂ) :
    BasisPhaseEq U V ↔
      ∃ phase : ι → Circle, ∀ input,
        V *ᵥ basisKet input = (phase input : ℂ) • (U *ᵥ basisKet input) := by
  constructor
  · rintro ⟨phase, hphase⟩
    refine ⟨phase, fun input ↦ ?_⟩
    ext row
    simp [hphase]
  · rintro ⟨phase, hphase⟩
    refine ⟨phase, ?_⟩
    intro row input
    simpa using congrFun (hphase input) row

/--
Post-composition preserves input-column phases.  With column-vector semantics,
post-composition is multiplication by the common matrix on the left.
-/
theorem postcompose {ι : Type*} [Fintype ι] {U V : Matrix ι ι ℂ}
    (h : BasisPhaseEq U V) (W : Matrix ι ι ℂ) :
    BasisPhaseEq (W * U) (W * V) := by
  rcases h with ⟨phase, hphase⟩
  refine ⟨phase, ?_⟩
  intro row input
  simp only [Matrix.mul_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [hphase]
  ring

end BasisPhaseEq

theorem GlobalPhaseEq.toBasisPhaseEq {ι : Type*} {U V : Matrix ι ι ℂ}
    (h : GlobalPhaseEq U V) : BasisPhaseEq U V :=
  BasisPhaseEq.of_globalPhaseEq h

theorem ExactCircuitEq.toBasisPhaseEq {n : ℕ} {first second : Circuit n}
    (h : ExactCircuitEq first second) :
    BasisPhaseEq (Circuit.eval first : Gate n) (Circuit.eval second : Gate n) :=
  h.toGlobalPhaseEq.toBasisPhaseEq

/-! ## Coarse classical behavior on basis states -/

/-- `U` sends `|input⟩` exactly to `|output⟩`, up to one unit phase. -/
def BasisTransition {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (input output : ι) : Prop :=
  ∃ phase : Circle, U *ᵥ basisKet input = (phase : ℂ) • basisKet output

/--
Two matrices have the same coarse classical basis behavior when they realize the
same basis-to-basis transitions.  For non-monomial matrices this intentionally
forgets all columns that are not a phased basis ket.
-/
def SameBasisBehavior {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U V : Matrix ι ι ℂ) : Prop :=
  ∀ input output, BasisTransition U input output ↔ BasisTransition V input output

namespace SameBasisBehavior

protected theorem refl {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) : SameBasisBehavior U U :=
  fun _ _ ↦ Iff.rfl

protected theorem symm {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U V : Matrix ι ι ℂ} (h : SameBasisBehavior U V) : SameBasisBehavior V U :=
  fun input output ↦ (h input output).symm

protected theorem trans {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U V W : Matrix ι ι ℂ} (hUV : SameBasisBehavior U V)
    (hVW : SameBasisBehavior V W) : SameBasisBehavior U W :=
  fun input output ↦ (hUV input output).trans (hVW input output)

theorem equivalence (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Equivalence (@SameBasisBehavior ι _ _) :=
  ⟨SameBasisBehavior.refl, SameBasisBehavior.symm, SameBasisBehavior.trans⟩

end SameBasisBehavior

/-- Input-column phases preserve every exact basis-to-basis transition. -/
theorem BasisTransition.of_basisPhaseEq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U V : Matrix ι ι ℂ} {input output : ι} (hPhase : BasisPhaseEq U V)
    (hTransition : BasisTransition U input output) : BasisTransition V input output := by
  rcases (BasisPhaseEq.iff_mulVec_basisKet U V).1 hPhase with ⟨inputPhase, hAction⟩
  rcases hTransition with ⟨outputPhase, hOutput⟩
  refine ⟨inputPhase input * outputPhase, ?_⟩
  rw [hAction input, hOutput, smul_smul]
  simp

/-- Input-column phase equality implies the same coarse classical basis behavior. -/
theorem BasisPhaseEq.toSameBasisBehavior {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U V : Matrix ι ι ℂ} (h : BasisPhaseEq U V) : SameBasisBehavior U V := by
  intro input output
  constructor
  · exact BasisTransition.of_basisPhaseEq h
  · exact BasisTransition.of_basisPhaseEq (BasisPhaseEq.symm h)

/-! ## Computational-basis measurement probabilities -/

/-- Equality of all computational-basis transition probabilities. -/
def BasisMeasurementEq {ι : Type*} (U V : Matrix ι ι ℂ) : Prop :=
  ∀ output input, Complex.normSq (U output input) = Complex.normSq (V output input)

namespace BasisMeasurementEq

protected theorem refl {ι : Type*} (U : Matrix ι ι ℂ) : BasisMeasurementEq U U :=
  fun _ _ ↦ rfl

protected theorem symm {ι : Type*} {U V : Matrix ι ι ℂ}
    (h : BasisMeasurementEq U V) : BasisMeasurementEq V U :=
  fun output input ↦ (h output input).symm

protected theorem trans {ι : Type*} {U V W : Matrix ι ι ℂ}
    (hUV : BasisMeasurementEq U V) (hVW : BasisMeasurementEq V W) :
    BasisMeasurementEq U W :=
  fun output input ↦ (hUV output input).trans (hVW output input)

theorem equivalence (ι : Type*) : Equivalence (@BasisMeasurementEq ι) :=
  ⟨BasisMeasurementEq.refl, BasisMeasurementEq.symm, BasisMeasurementEq.trans⟩

end BasisMeasurementEq

/-- Input-column phases preserve computational-basis measurement probabilities. -/
theorem BasisPhaseEq.toBasisMeasurementEq {ι : Type*} {U V : Matrix ι ι ℂ}
    (h : BasisPhaseEq U V) : BasisMeasurementEq U V := by
  rcases h with ⟨phase, hphase⟩
  intro output input
  rw [hphase, Complex.normSq_mul, Circle.normSq_coe, one_mul]

theorem GlobalPhaseEq.toBasisMeasurementEq {ι : Type*} {U V : Matrix ι ι ℂ}
    (h : GlobalPhaseEq U V) : BasisMeasurementEq U V :=
  h.toBasisPhaseEq.toBasisMeasurementEq

theorem ExactCircuitEq.toBasisMeasurementEq {n : ℕ} {first second : Circuit n}
    (h : ExactCircuitEq first second) :
    BasisMeasurementEq (Circuit.eval first : Gate n) (Circuit.eval second : Gate n) :=
  h.toBasisPhaseEq.toBasisMeasurementEq

end Barenco
