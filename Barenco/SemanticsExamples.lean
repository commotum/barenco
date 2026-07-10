import Barenco.Circuit

/-!
# Low-dimensional semantic sanity checks

These examples instantiate the general basis-action theorems from `Controlled`
at the smallest register sizes where indexing and execution-order errors are
visible.  Every finite computation is checked by ordinary kernel reduction; this
file uses no native or bit-vector decision procedures.
-/

namespace Barenco
namespace SemanticsExamples

open Matrix

/-! ## Empty-control local gate -/

private def oneBit (b : Bool) : Basis 1 :=
  fun _ ↦ b

/-- On one wire, the empty-control local X gate maps `|b⟩` to `|¬b⟩`. -/
theorem emptyControl_localX (b : Bool) :
    (positiveControlledUnitary (0 : Fin 1) (∅ : ControlSet (0 : Fin 1)) pauliX : Gate 1) *ᵥ
        basisKet (oneBit b) =
      basisKet (oneBit (!b)) := by
  rw [positiveControlledUnitary_empty]
  change (xUnitary (0 : Fin 1) : Gate 1) *ᵥ basisKet (oneBit b) =
    basisKet (oneBit (!b))
  rw [coe_xUnitary, xRaw_mulVec_basisKet]
  apply congrArg basisKet
  funext i
  fin_cases i
  simp [oneBit]

/-! ## All four two-qubit CNOT basis cases -/

private def cnot01 : UnitaryGate 2 :=
  cnotUnitary (0 : Fin 2) (1 : Fin 2) (by decide)

/-- General two-qubit CNOT action, with wire `0` controlling wire `1`. -/
theorem cnot01_action (controlBit targetBit : Bool) :
    (cnot01 : Gate 2) *ᵥ basisKet (twoBit controlBit targetBit) =
      basisKet (twoBit controlBit (if controlBit then !targetBit else targetBit)) := by
  unfold cnot01
  rw [coe_cnotUnitary, cnotRaw_mulVec_basisKet]
  apply congrArg basisKet
  funext i
  fin_cases i <;> cases controlBit <;> simp [twoBit]

theorem cnot01_false_false :
    (cnot01 : Gate 2) *ᵥ basisKet (twoBit false false) =
      basisKet (twoBit false false) := by
  simpa using cnot01_action false false

theorem cnot01_false_true :
    (cnot01 : Gate 2) *ᵥ basisKet (twoBit false true) =
      basisKet (twoBit false true) := by
  simpa using cnot01_action false true

theorem cnot01_true_false :
    (cnot01 : Gate 2) *ᵥ basisKet (twoBit true false) =
      basisKet (twoBit true true) := by
  simpa using cnot01_action true false

theorem cnot01_true_true :
    (cnot01 : Gate 2) *ᵥ basisKet (twoBit true true) =
      basisKet (twoBit true false) := by
  simpa using cnot01_action true true

/-! ## A non-adjacent three-qubit control and target -/

private def threeBit (high middle low : Bool) : Basis 3 :=
  fun i ↦ if i = 0 then high else if i = 1 then middle else low

private def cnot02 : UnitaryGate 3 :=
  cnotUnitary (0 : Fin 3) (2 : Fin 3) (by decide)

/--
Wire `0` controls non-adjacent wire `2`; the arbitrary middle bit is visibly
preserved in the resulting ket.
-/
theorem nonAdjacent_cnot02_action_preserves_middle (high middle low : Bool) :
    (cnot02 : Gate 3) *ᵥ basisKet (threeBit high middle low) =
      basisKet (threeBit high middle (if high then !low else low)) := by
  unfold cnot02
  rw [coe_cnotUnitary, cnotRaw_mulVec_basisKet]
  apply congrArg basisKet
  funext i
  fin_cases i <;> cases high <;> simp [threeBit]

/-! ## The zero-qubit circuit boundary -/

private def emptyBasis : Basis 0 :=
  fun i ↦ Fin.elim0 i

/-- The empty circuit is the certified identity even at register width zero. -/
theorem zeroQubit_identityCircuit :
    Circuit.eval (Circuit.identity 0) = (1 : UnitaryGate 0) := by
  exact Circuit.eval_identity 0

/-- The zero-qubit identity circuit fixes the unique computational-basis ket. -/
theorem zeroQubit_identityCircuit_action :
    (Circuit.eval (Circuit.identity 0) : Gate 0) *ᵥ basisKet emptyBasis =
      basisKet emptyBasis := by
  rw [Circuit.eval_identity]
  exact Matrix.one_mulVec _

/-! ## Chronological action of two circuit primitives -/

private def firstFlipControl : Primitive 2 :=
  Primitive.oneQubit (0 : Fin 2) pauliX

private def thenCnot01 : Primitive 2 :=
  Primitive.cnot (0 : Fin 2) (1 : Fin 2) (by decide)

/--
The first primitive changes `|00⟩` to `|10⟩`; the second then sees the enabled
control and changes it to `|11⟩`.  Reversing execution would instead end at
`|10⟩`, so this checks the chronological convention nontrivially.  The syntax
uses the trusted one-qubit and CNOT smart constructors, not raw metadata tags.
-/
theorem chronological_twoPrimitives :
    (Circuit.eval [firstFlipControl, thenCnot01] : Gate 2) *ᵥ
        basisKet (twoBit false false) = basisKet (twoBit true true) := by
  rw [Circuit.eval_pair_mulVec]
  simp only [firstFlipControl, thenCnot01, Primitive.oneQubit_denotation,
    Primitive.cnot_denotation]
  rw [coe_localUnitary]
  change (cnot01 : Gate 2) *ᵥ
    (xRaw (0 : Fin 2) *ᵥ basisKet (twoBit false false)) = basisKet (twoBit true true)
  rw [xRaw_mulVec_basisKet]
  unfold cnot01
  rw [coe_cnotUnitary, cnotRaw_mulVec_basisKet]
  apply congrArg basisKet
  funext i
  fin_cases i <;> simp [twoBit]

end SemanticsExamples
end Barenco
