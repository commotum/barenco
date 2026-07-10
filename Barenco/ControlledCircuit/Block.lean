import Barenco.Circuit

/-!
# Target-block algebra for controlled one-qubit circuits

Every target-local or target-controlled matrix in `Barenco.Controlled` is a
reindexed block-diagonal matrix over `splitTarget`. This leaf exposes that common
representation and its exact algebra so later circuit evaluator proofs can work
blockwise while still concluding equality of full-register matrices.

All declarations here are public proof-side API. `targetBlockRaw` is an auxiliary
semantic representation, not circuit syntax; this module defines no circuit
builder and makes no resource claim.
-/

namespace Barenco.ControlledCircuit

/--
Assemble a full-register matrix from one target-qubit matrix for each assignment
of the complementary wires.
-/
def targetBlockRaw {n : ℕ} (target : Fin n)
    (blocks : ComplementBasis target → QubitMatrix) : Gate n :=
  Matrix.reindexAlgEquiv ℂ ℂ (splitTarget target).symm
    (Matrix.blockDiagonal blocks)

/-- Exact entry formula for the target-block representation. -/
theorem targetBlockRaw_apply {n : ℕ} (target : Fin n)
    (blocks : ComplementBasis target → QubitMatrix) (row col : Basis n) :
    targetBlockRaw target blocks row col =
      if (splitTarget target row).2 = (splitTarget target col).2 then
        blocks (splitTarget target row).2 (row target) (col target)
      else 0 := by
  rfl

/-- Full-register multiplication is pointwise multiplication of target blocks. -/
theorem targetBlockRaw_mul {n : ℕ} (target : Fin n)
    (F G : ComplementBasis target → QubitMatrix) :
    targetBlockRaw target F * targetBlockRaw target G =
      targetBlockRaw target (fun rest => F rest * G rest) := by
  change Matrix.reindexAlgEquiv ℂ ℂ (splitTarget target).symm (Matrix.blockDiagonal F) *
      Matrix.reindexAlgEquiv ℂ ℂ (splitTarget target).symm (Matrix.blockDiagonal G) =
    Matrix.reindexAlgEquiv ℂ ℂ (splitTarget target).symm
      (Matrix.blockDiagonal fun rest => F rest * G rest)
  rw [← map_mul, ← Matrix.blockDiagonal_mul]

/-- Pointwise identity blocks assemble to the full-register identity. -/
@[simp]
theorem targetBlockRaw_one {n : ℕ} (target : Fin n) :
    targetBlockRaw target (fun _ => (1 : QubitMatrix)) = (1 : Gate n) := by
  change Matrix.reindexAlgEquiv ℂ ℂ (splitTarget target).symm
      (Matrix.blockDiagonal (1 : ComplementBasis target → QubitMatrix)) = 1
  rw [Matrix.blockDiagonal_one, map_one]

/-- Distinct block families give distinct full-register target-block matrices. -/
theorem targetBlockRaw_injective {n : ℕ} (target : Fin n) :
    Function.Injective (targetBlockRaw target) := by
  intro F G h
  apply Matrix.blockDiagonal_injective
  apply (Matrix.reindexAlgEquiv ℂ ℂ (splitTarget target).symm).injective
  exact h

/-- Equality of full target-block matrices is exactly equality of every block. -/
@[simp]
theorem targetBlockRaw_inj {n : ℕ} (target : Fin n)
    {F G : ComplementBasis target → QubitMatrix} :
    targetBlockRaw target F = targetBlockRaw target G ↔ F = G :=
  (targetBlockRaw_injective target).eq_iff

/-! ## Bridges to the established controlled-gate semantics -/

/-- A target-local matrix has the same block in every complementary assignment. -/
theorem localRaw_eq_targetBlockRaw {n : ℕ} (target : Fin n) (U : QubitMatrix) :
    localRaw target U = targetBlockRaw target (fun _ => U) := by
  rfl

/-- A controlled matrix selects `U` or identity independently in every target block. -/
theorem controlledRaw_eq_targetBlockRaw {n : ℕ} (target : Fin n)
    (enabled : ComplementBasis target → Bool) (U : QubitMatrix) :
    controlledRaw target enabled U =
      targetBlockRaw target (fun rest => if enabled rest then U else 1) := by
  rfl

/--
A singleton positive control selects the active target block exactly when that
control bit is true.
-/
theorem positiveControlledRaw_singleton_eq_targetBlockRaw {n : ℕ}
    (control target : Fin n) (h : control ≠ target) (U : QubitMatrix) :
    positiveControlledRaw target ({⟨control, h⟩} : ControlSet target) U =
      targetBlockRaw target
        (fun rest => if rest ⟨control, h⟩ then U else 1) := by
  rw [positiveControlledRaw, controlledRaw_eq_targetBlockRaw]
  congr 1
  funext rest
  simp [positiveControlsEnabled]

/-- CNOT is the singleton-control target block choosing Pauli-X or identity. -/
theorem cnotRaw_eq_targetBlockRaw {n : ℕ} (control target : Fin n)
    (h : control ≠ target) :
    cnotRaw control target h =
      targetBlockRaw target
        (fun rest => if rest ⟨control, h⟩ then (pauliX : QubitMatrix) else 1) := by
  rw [cnotRaw, positiveControlledRaw_singleton_eq_targetBlockRaw]

end Barenco.ControlledCircuit
