import Barenco.Cost

/-!
# Exact width-one synthesis

The one-qubit boundary does not require finite-dimensional elimination.  The
computational basis `Basis 1` is canonically equivalent to `Bool` by evaluation
at wire zero.  Reindexing along this equivalence turns any certified width-one
unitary directly into the arbitrary one-qubit primitive accepted by the
Sections 3--7 cost model.
-/

namespace Barenco.Universality

noncomputable section

/-! ## The canonical width-one basis equivalence -/

/-- Evaluation at the unique wire identifies `Basis 1` with `Bool`. -/
def basisOneEquivBool : Basis 1 ≃ Bool where
  toFun basis := basis 0
  invFun bit := fun _ => bit
  left_inv basis := by
    funext wire
    rw [Subsingleton.elim wire 0]
  right_inv _bit := rfl

@[simp]
theorem basisOneEquivBool_apply (basis : Basis 1) :
    basisOneEquivBool basis = basis 0 := rfl

@[simp]
theorem basisOneEquivBool_symm_apply (bit : Bool) (wire : Fin 1) :
    basisOneEquivBool.symm bit wire = bit := rfl

/-! ## Direct primitive synthesis -/

/-- Reindex a width-one semantic unitary into the library's Bool-indexed qubit type. -/
def widthOneQubitUnitary (U : UnitaryGate 1) : QubitUnitary :=
  reindexUnitary basisOneEquivBool U

@[simp]
theorem widthOneQubitUnitary_apply (U : UnitaryGate 1) (row col : Bool) :
    widthOneQubitUnitary U row col =
      U (basisOneEquivBool.symm row) (basisOneEquivBool.symm col) := rfl

/-- Embedding the reindexed qubit gate back at the unique wire recovers `U`. -/
@[simp]
theorem localUnitary_widthOneQubitUnitary (U : UnitaryGate 1) :
    localUnitary (0 : Fin 1) (widthOneQubitUnitary U) = U := by
  apply Subtype.ext
  ext row col
  rw [coe_localUnitary, localRaw_apply]
  have hrest : (splitTarget (0 : Fin 1) row).2 =
      (splitTarget (0 : Fin 1) col).2 := by
    funext wire
    exact (wire.property (Subsingleton.elim wire.1 0)).elim
  rw [if_pos hrest]
  change U (basisOneEquivBool.symm (row 0))
      (basisOneEquivBool.symm (col 0)) = U row col
  simpa only [basisOneEquivBool_apply] using
    congrArg₂ (fun first second => U first second)
      (basisOneEquivBool.symm_apply_apply row)
      (basisOneEquivBool.symm_apply_apply col)

/-- The direct exact circuit is one arbitrary one-qubit primitive on wire zero. -/
def widthOneCircuit (U : UnitaryGate 1) : Circuit 1 :=
  [Primitive.oneQubit 0 (widthOneQubitUnitary U)]

/-- Exact evaluator of the direct width-one circuit. -/
@[simp]
theorem eval_widthOneCircuit (U : UnitaryGate 1) :
    Circuit.eval (widthOneCircuit U) = U := by
  simp [widthOneCircuit]

/-- The direct width-one circuit has exactly one primitive occurrence. -/
@[simp]
theorem widthOneCircuit_gateCount (U : UnitaryGate 1) :
    Circuit.gateCount (widthOneCircuit U) = 1 := rfl

/-- The direct width-one circuit is accepted at exact cost one. -/
@[simp]
theorem widthOneCircuit_oneQubitCNOTCost (U : UnitaryGate 1) :
    Circuit.cost CostModel.oneQubitCNOT (widthOneCircuit U) = some 1 := by
  simp [widthOneCircuit, Circuit.cost, Circuit.addCost]

end

end Barenco.Universality
