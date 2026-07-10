import Barenco.Semantics
import Mathlib.Logic.Equiv.Prod

/-!
# Local and positively controlled one-qubit gates

This module embeds a one-qubit matrix at an arbitrary target wire.  The
implementation splits a basis assignment at the target, builds a block-diagonal
matrix indexed by assignments of all other wires, and reindexes the result back
to the register basis.  Controlled gates choose either the supplied one-qubit
matrix or the identity independently in every complementary block.
-/

namespace Barenco

open Matrix

/-- The wire indices other than `target`. -/
abbrev TargetComplement {n : ℕ} (target : Fin n) := {i : Fin n // i ≠ target}

/-- Computational-basis assignments on all wires other than `target`. -/
abbrev ComplementBasis {n : ℕ} (target : Fin n) := TargetComplement target → Bool

/-- Split a register assignment into its target bit and all complementary bits. -/
def splitTarget {n : ℕ} (target : Fin n) :
    Basis n ≃ Bool × ComplementBasis target :=
  Equiv.piSplitAt target (fun _ => Bool)

@[simp]
theorem splitTarget_fst {n : ℕ} (target : Fin n) (x : Basis n) :
    (splitTarget target x).1 = x target := rfl

@[simp]
theorem splitTarget_snd_apply {n : ℕ} (target : Fin n) (x : Basis n)
    (i : TargetComplement target) :
    (splitTarget target x).2 i = x i := rfl

/--
Embed a raw one-qubit matrix at `target`, acting as the identity on every other
wire.
-/
def localRaw {n : ℕ} (target : Fin n) (U : QubitMatrix) : Gate n :=
  Matrix.reindexAlgEquiv ℂ ℂ (splitTarget target).symm
    (Matrix.blockDiagonal fun _ : ComplementBasis target => U)

/--
Embed `U` at `target` in precisely those complementary basis blocks satisfying
`enabled`; inactive blocks contain the one-qubit identity.
-/
def controlledRaw {n : ℕ} (target : Fin n)
    (enabled : ComplementBasis target → Bool) (U : QubitMatrix) : Gate n :=
  Matrix.reindexAlgEquiv ℂ ℂ (splitTarget target).symm
    (Matrix.blockDiagonal fun rest => if enabled rest then U else 1)

theorem localRaw_apply {n : ℕ} (target : Fin n) (U : QubitMatrix)
    (row col : Basis n) :
    localRaw target U row col =
      if (splitTarget target row).2 = (splitTarget target col).2 then
        U (row target) (col target)
      else 0 := by
  rfl

theorem controlledRaw_apply {n : ℕ} (target : Fin n)
    (enabled : ComplementBasis target → Bool) (U : QubitMatrix)
    (row col : Basis n) :
    controlledRaw target enabled U row col =
      if (splitTarget target row).2 = (splitTarget target col).2 then
        (if enabled (splitTarget target row).2 then U else 1)
          (row target) (col target)
      else 0 := by
  rfl

/-- Two assignments agree on every wire other than `target`. -/
def AgreeOff {n : ℕ} (target : Fin n) (x y : Basis n) : Prop :=
  ∀ i, i ≠ target → x i = y i

theorem splitTarget_snd_eq_iff {n : ℕ} (target : Fin n) (x y : Basis n) :
    (splitTarget target x).2 = (splitTarget target y).2 ↔ AgreeOff target x y := by
  constructor
  · intro h i hi
    exact congrFun h ⟨i, hi⟩
  · intro h
    funext i
    exact h i i.property

theorem localRaw_apply_eq_if_agreeOff {n : ℕ} (target : Fin n) (U : QubitMatrix)
    (row col : Basis n) :
    localRaw target U row col =
      if AgreeOff target row col then U (row target) (col target) else 0 := by
  rw [localRaw_apply]
  simp only [splitTarget_snd_eq_iff]

theorem controlledRaw_apply_eq_if_agreeOff {n : ℕ} (target : Fin n)
    (enabled : ComplementBasis target → Bool) (U : QubitMatrix)
    (row col : Basis n) :
    controlledRaw target enabled U row col =
      if AgreeOff target row col then
        (if enabled (splitTarget target row).2 then U else 1)
          (row target) (col target)
      else 0 := by
  rw [controlledRaw_apply]
  simp only [splitTarget_snd_eq_iff]

/-- Certified arbitrary-target embedding of a one-qubit unitary. -/
def localUnitary {n : ℕ} (target : Fin n) (U : QubitUnitary) : UnitaryGate n :=
  reindexUnitary (splitTarget target).symm
    (blockDiagonalUnitary fun _ : ComplementBasis target => U)

@[simp]
theorem coe_localUnitary {n : ℕ} (target : Fin n) (U : QubitUnitary) :
    (localUnitary target U : Gate n) = localRaw target U := rfl

/-- Certified arbitrary-target controlled one-qubit unitary. -/
def controlledUnitary {n : ℕ} (target : Fin n)
    (enabled : ComplementBasis target → Bool) (U : QubitUnitary) : UnitaryGate n :=
  reindexUnitary (splitTarget target).symm
    (blockDiagonalUnitary fun rest => if enabled rest then U else 1)

@[simp]
theorem coe_controlledUnitary {n : ℕ} (target : Fin n)
    (enabled : ComplementBasis target → Bool) (U : QubitUnitary) :
    (controlledUnitary target enabled U : Gate n) = controlledRaw target enabled U := rfl

end Barenco
