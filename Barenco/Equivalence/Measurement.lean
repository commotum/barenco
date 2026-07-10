import Barenco.Equivalence.Phase
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Conjugation channels and measurement equivalence

This file formalizes the strongest observational equivalence used by the
library.  The algebraic channel is defined on arbitrary square matrices; when
its first argument is unitary it is the usual unitary conjugation channel.
Inputs and effects are deliberately not restricted to positive or normalized
matrices, so the resulting equality theorem is an exact linear-algebraic one.
-/

namespace Barenco

open Matrix

variable {ι : Type*} [Fintype ι]

/-- Conjugation by `U`, acting on an arbitrary square matrix `input`. -/
def conjugationChannel (U input : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  U * input * Uᴴ

/-- Equality of conjugation channels on every matrix input. -/
def ChannelEq (U V : Matrix ι ι ℂ) : Prop :=
  ∀ input : Matrix ι ι ℂ, conjugationChannel U input = conjugationChannel V input

/-- The trace pairing of an arbitrary effect with an arbitrary matrix state. -/
def BornWeight (effect state : Matrix ι ι ℂ) : ℂ :=
  Matrix.trace (effect * state)

/-- Equality of every arbitrary-effect Born weight on every matrix input. -/
def AllMeasurementEq (U V : Matrix ι ι ℂ) : Prop :=
  ∀ (input effect : Matrix ι ι ℂ),
    BornWeight effect (conjugationChannel U input) =
      BornWeight effect (conjugationChannel V input)

theorem channelEq_refl (U : Matrix ι ι ℂ) : ChannelEq U U :=
  fun _ => rfl

theorem channelEq_symm {U V : Matrix ι ι ℂ} (h : ChannelEq U V) : ChannelEq V U :=
  fun input => (h input).symm

theorem channelEq_trans {U V W : Matrix ι ι ℂ}
    (hUV : ChannelEq U V) (hVW : ChannelEq V W) : ChannelEq U W :=
  fun input => (hUV input).trans (hVW input)

theorem channelEq_equivalence :
    Equivalence (@ChannelEq ι _) :=
  ⟨channelEq_refl, @channelEq_symm ι _, @channelEq_trans ι _⟩

theorem allMeasurementEq_refl (U : Matrix ι ι ℂ) : AllMeasurementEq U U :=
  fun _ _ => rfl

theorem allMeasurementEq_symm {U V : Matrix ι ι ℂ} (h : AllMeasurementEq U V) :
    AllMeasurementEq V U :=
  fun input effect => (h input effect).symm

theorem allMeasurementEq_trans {U V W : Matrix ι ι ℂ}
    (hUV : AllMeasurementEq U V) (hVW : AllMeasurementEq V W) :
    AllMeasurementEq U W :=
  fun input effect => (hUV input effect).trans (hVW input effect)

theorem allMeasurementEq_equivalence :
    Equivalence (@AllMeasurementEq ι _) :=
  ⟨allMeasurementEq_refl, @allMeasurementEq_symm ι _, @allMeasurementEq_trans ι _⟩

/-- Exact matrix equality implies channel equality. -/
theorem channelEq_of_eq {U V : Matrix ι ι ℂ} (h : U = V) : ChannelEq U V := by
  subst V
  exact channelEq_refl U

/-- Exact matrix equality implies equality of all measurement weights. -/
theorem allMeasurementEq_of_eq {U V : Matrix ι ι ℂ} (h : U = V) :
    AllMeasurementEq U V := by
  subst V
  exact allMeasurementEq_refl U

/-- Conjugation by a product composes the corresponding conjugation channels. -/
theorem conjugationChannel_mul (U V input : Matrix ι ι ℂ) :
    conjugationChannel (U * V) input =
      conjugationChannel U (conjugationChannel V input) := by
  simp only [conjugationChannel, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-- Multiplying a matrix by a unit-modulus scalar does not change its channel. -/
theorem conjugationChannel_circle_smul (phase : Circle) (U input : Matrix ι ι ℂ) :
    conjugationChannel ((phase : ℂ) • U) input = conjugationChannel U input := by
  simp [conjugationChannel, Matrix.conjTranspose_smul, ← Circle.coe_inv_eq_conj,
    Matrix.mul_assoc]

/-- Channel equality is preserved by multiplication on both sides. -/
theorem ChannelEq.mul {U U' V V' : Matrix ι ι ℂ}
    (hU : ChannelEq U U') (hV : ChannelEq V V') :
    ChannelEq (U * V) (U' * V') := by
  intro input
  calc
    conjugationChannel (U * V) input =
        conjugationChannel U (conjugationChannel V input) :=
      conjugationChannel_mul U V input
    _ = conjugationChannel U' (conjugationChannel V input) :=
      hU (conjugationChannel V input)
    _ = conjugationChannel U' (conjugationChannel V' input) :=
      congrArg (conjugationChannel U') (hV input)
    _ = conjugationChannel (U' * V') input :=
      (conjugationChannel_mul U' V' input).symm

/-- Channel equality gives equal Born weights for every input and every effect. -/
theorem ChannelEq.bornWeight_eq {U V : Matrix ι ι ℂ} (h : ChannelEq U V)
    (input effect : Matrix ι ι ℂ) :
    BornWeight effect (conjugationChannel U input) =
      BornWeight effect (conjugationChannel V input) :=
  congrArg (BornWeight effect) (h input)

/-- Channel equality implies equality of all arbitrary-effect measurements. -/
theorem ChannelEq.allMeasurementEq {U V : Matrix ι ι ℂ} (h : ChannelEq U V) :
    AllMeasurementEq U V :=
  fun input effect => h.bornWeight_eq input effect

/-- A single global phase cancels between the two sides of conjugation. -/
theorem GlobalPhaseEq.toChannelEq {U V : Matrix ι ι ℂ} (h : GlobalPhaseEq U V) :
    ChannelEq U V := by
  rcases h with ⟨phase, rfl⟩
  intro input
  exact (conjugationChannel_circle_smul phase U input).symm

/-- Global-phase equality implies equality of every arbitrary-effect Born weight. -/
theorem GlobalPhaseEq.toAllMeasurementEq {U V : Matrix ι ι ℂ}
    (h : GlobalPhaseEq U V) : AllMeasurementEq U V :=
  h.toChannelEq.allMeasurementEq

section Identity

variable [DecidableEq ι]

@[simp]
theorem conjugationChannel_one (input : Matrix ι ι ℂ) :
    conjugationChannel (1 : Matrix ι ι ℂ) input = input := by
  simp [conjugationChannel]

/-- A matrix unit with its sole nonzero entry at `(row, col)`. -/
def matrixUnit (row col : ι) : Matrix ι ι ℂ :=
  Matrix.single row col 1

omit [Fintype ι] in
@[simp]
theorem matrixUnit_apply (row col i j : ι) :
    matrixUnit row col i j = if i = row ∧ j = col then 1 else 0 :=
  by simp [matrixUnit, Matrix.single_apply, eq_comm]

/-- Pairing with the transposed matrix unit extracts one matrix entry. -/
@[simp]
theorem bornWeight_matrixUnit (state : Matrix ι ι ℂ) (row col : ι) :
    BornWeight (matrixUnit col row) state = state row col := by
  simp [BornWeight, matrixUnit, Matrix.trace_single_mul]

/-- Arbitrary-effect equality separates channels because matrix units separate entries. -/
theorem AllMeasurementEq.toChannelEq {U V : Matrix ι ι ℂ} (h : AllMeasurementEq U V) :
    ChannelEq U V := by
  intro input
  ext row col
  simpa using h input (matrixUnit col row)

/-- Channel equality and all-arbitrary-effect equality are the same relation. -/
theorem channelEq_iff_allMeasurementEq (U V : Matrix ι ι ℂ) :
    ChannelEq U V ↔ AllMeasurementEq U V :=
  ⟨ChannelEq.allMeasurementEq, AllMeasurementEq.toChannelEq⟩

/-- The rank-one projector onto a computational-basis index. -/
def basisProjector (input : ι) : Matrix ι ι ℂ := fun row col =>
  if row = input ∧ col = input then 1 else 0

omit [Fintype ι] in
@[simp]
theorem basisProjector_apply (input row col : ι) :
    basisProjector input row col = if row = input ∧ col = input then 1 else 0 :=
  rfl

/-- A basis projector reads one squared transition amplitude from a channel. -/
theorem conjugationChannel_basisProjector_apply_self
    (U : Matrix ι ι ℂ) (input output : ι) :
    conjugationChannel U (basisProjector input) output output =
      Complex.normSq (U output input) := by
  have hinner (x : ι) :
      (∑ y, U output y * basisProjector input y x) =
        if x = input then U output input else 0 := by
    by_cases hx : x = input
    · subst x
      simp [basisProjector]
    · simp [basisProjector, hx]
  simp only [conjugationChannel, Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp_rw [hinner]
  simp [Complex.mul_conj]

/-- Equality on all matrix inputs implies equality of computational-basis probabilities. -/
theorem ChannelEq.toBasisMeasurementEq {U V : Matrix ι ι ℂ} (h : ChannelEq U V) :
    BasisMeasurementEq U V := by
  intro output input
  have hdiagonal := congrArg (fun M : Matrix ι ι ℂ => M output output)
    (h (basisProjector input))
  rw [conjugationChannel_basisProjector_apply_self,
    conjugationChannel_basisProjector_apply_self] at hdiagonal
  exact Complex.ofReal_injective hdiagonal

end Identity

end Barenco
