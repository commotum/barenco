import Barenco.Circuit
import Barenco.Controlled
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Low-dimensional semantic sanity checks

These examples exercise the certified semantic constructors at the smallest
register sizes where indexing mistakes are visible.  All finite computations are
proved by ordinary kernel reduction and theorem instantiation; this file does not
use native or bit-vector decision procedures.
-/

namespace Barenco
namespace SemanticsExamples

open Matrix

/-! ## A certified bit flip used only by the examples -/

private def bitFlipPerm : Equiv.Perm Bool :=
  Equiv.swap false true

private def bitFlipMatrix : QubitMatrix :=
  bitFlipPerm.permMatrix ℂ

private theorem bitFlipMatrix_mem_unitaryGroup :
    bitFlipMatrix ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  simp only [bitFlipMatrix, Matrix.conjTranspose_permMatrix]
  rw [← Matrix.permMatrix_mul]
  simp

private def bitFlipUnitary : QubitUnitary :=
  ⟨bitFlipMatrix, bitFlipMatrix_mem_unitaryGroup⟩

@[simp]
private theorem bitFlipUnitary_apply (row col : Bool) :
    bitFlipUnitary row col = if row = !col then 1 else 0 := by
  cases row <;> cases col <;> rfl

/-! ## General basis-action lemmas instantiated below -/

/-- Change just `target` to `value`. -/
private def setTarget {n : ℕ} (target : Fin n) (value : Bool) (x : Basis n) : Basis n :=
  Function.update x target value

/-- Flip just the target bit. -/
private def flipTarget {n : ℕ} (target : Fin n) (x : Basis n) : Basis n :=
  setTarget target (!x target) x

private theorem eq_setTarget_iff {n : ℕ} (target : Fin n) (value : Bool)
    (row x : Basis n) :
    row = setTarget target value x ↔
      AgreeOff target row x ∧ row target = value := by
  constructor
  · intro h
    subst row
    constructor
    · intro i hi
      simp [setTarget, Function.update_of_ne hi]
    · simp [setTarget]
  · rintro ⟨hoff, htarget⟩
    funext i
    by_cases hi : i = target
    · subst i
      simpa [setTarget] using htarget
    · simpa [setTarget, Function.update_of_ne hi] using hoff i hi

private theorem eq_setTarget_iff_of_agreeOff {n : ℕ} (target : Fin n) (value : Bool)
    (row x : Basis n) (hoff : AgreeOff target row x) :
    row = setTarget target value x ↔ row target = value := by
  constructor
  · exact fun h ↦ ((eq_setTarget_iff target value row x).1 h).2
  · exact fun h ↦ (eq_setTarget_iff target value row x).2 ⟨hoff, h⟩

private theorem ne_setTarget_of_not_agreeOff {n : ℕ} (target : Fin n) (value : Bool)
    (row x : Basis n) (hoff : ¬AgreeOff target row x) :
    row ≠ setTarget target value x := by
  intro h
  exact hoff ((eq_setTarget_iff target value row x).1 h).1

/-- An uncontrolled local bit flip has the expected basis-state action. -/
private theorem localBitFlip_mulVec_basisKet {n : ℕ} (target : Fin n) (x : Basis n) :
    (localUnitary target bitFlipUnitary : Gate n) *ᵥ basisKet x =
      basisKet (flipTarget target x) := by
  ext row
  simp only [mulVec_basisKet_apply, coe_localUnitary,
    localRaw_apply_eq_if_agreeOff, bitFlipUnitary_apply, basisKet_apply, flipTarget]
  by_cases hoff : AgreeOff target row x
  · rw [if_pos hoff, eq_setTarget_iff_of_agreeOff target (!x target) row x hoff]
  · rw [if_neg hoff, if_neg (ne_setTarget_of_not_agreeOff target (!x target) row x hoff)]

/-- Read the control bit from the complementary assignment used by `controlledUnitary`. -/
private def controlEnabled {n : ℕ} (control target : Fin n) (h : control ≠ target) :
    ComplementBasis target → Bool :=
  fun rest ↦ rest ⟨control, h⟩

/-- A controlled bit flip built from the generic controlled-unitary constructor. -/
private def controlledBitFlip {n : ℕ} (control target : Fin n) (h : control ≠ target) :
    UnitaryGate n :=
  controlledUnitary target (controlEnabled control target h) bitFlipUnitary

/-- The classical basis assignment produced by a controlled bit flip. -/
private def controlledBitFlipOutput {n : ℕ} (control target : Fin n) (x : Basis n) :
    Basis n :=
  setTarget target (if x control then !x target else x target) x

/-- A controlled bit flip has the expected action on every computational-basis ket. -/
private theorem controlledBitFlip_mulVec_basisKet {n : ℕ}
    (control target : Fin n) (h : control ≠ target) (x : Basis n) :
    (controlledBitFlip control target h : Gate n) *ᵥ basisKet x =
      basisKet (controlledBitFlipOutput control target x) := by
  ext row
  simp only [mulVec_basisKet_apply, controlledBitFlip, coe_controlledUnitary,
    controlledRaw_apply_eq_if_agreeOff, basisKet_apply, controlledBitFlipOutput]
  by_cases hoff : AgreeOff target row x
  · have hcontrol : row control = x control := hoff control h
    have henabled :
        controlEnabled control target h (splitTarget target row).2 = x control := by
      simp [controlEnabled, hcontrol]
    rw [if_pos hoff, henabled]
    cases hx : x control
    · simp only [hx, Bool.false_eq_true, if_false, Matrix.one_apply]
      rw [eq_setTarget_iff_of_agreeOff target (x target) row x hoff]
    · simp only [hx, if_true, bitFlipUnitary_apply]
      rw [eq_setTarget_iff_of_agreeOff target (!x target) row x hoff]
  · rw [if_neg hoff,
      if_neg (ne_setTarget_of_not_agreeOff target
        (if x control then !x target else x target) row x hoff)]

/-! ## Empty-control local gate -/

private def oneBit (b : Bool) : Basis 1 :=
  fun _ ↦ b

/-- On one wire, the empty-control local gate maps `|b⟩` to `|¬b⟩`. -/
theorem emptyControl_localBitFlip (b : Bool) :
    (localUnitary (0 : Fin 1) bitFlipUnitary : Gate 1) *ᵥ basisKet (oneBit b) =
      basisKet (oneBit (!b)) := by
  rw [localBitFlip_mulVec_basisKet]
  apply congrArg basisKet
  funext i
  fin_cases i
  rfl

/-! ## All four two-qubit CNOT basis cases -/

private def cnot01 : UnitaryGate 2 :=
  controlledBitFlip (0 : Fin 2) (1 : Fin 2) (by decide)

/-- General two-qubit CNOT action, with wire `0` controlling wire `1`. -/
theorem cnot01_action (controlBit targetBit : Bool) :
    (cnot01 : Gate 2) *ᵥ basisKet (twoBit controlBit targetBit) =
      basisKet (twoBit controlBit (if controlBit then !targetBit else targetBit)) := by
  unfold cnot01
  rw [controlledBitFlip_mulVec_basisKet]
  apply congrArg basisKet
  funext i
  fin_cases i <;>
    simp [controlledBitFlipOutput, setTarget, twoBit, Function.update_apply]

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
  controlledBitFlip (0 : Fin 3) (2 : Fin 3) (by decide)

/--
Wire `0` controls non-adjacent wire `2`; the arbitrary middle bit is visibly
preserved in the result.
-/
theorem nonAdjacent_cnot02_action_preserves_middle (high middle low : Bool) :
    (cnot02 : Gate 3) *ᵥ basisKet (threeBit high middle low) =
      basisKet (threeBit high middle (if high then !low else low)) := by
  unfold cnot02
  rw [controlledBitFlip_mulVec_basisKet]
  apply congrArg basisKet
  funext i
  fin_cases i <;>
    simp [controlledBitFlipOutput, setTarget, threeBit, Function.update_apply]

/-! ## The zero-qubit circuit boundary -/

private def emptyBasis : Basis 0 :=
  fun i ↦ Fin.elim0 i

theorem zeroQubit_identityCircuit :
    Circuit.eval (Circuit.identity 0) = (1 : UnitaryGate 0) := by
  exact Circuit.eval_identity 0

theorem zeroQubit_identityCircuit_action :
    (Circuit.eval (Circuit.identity 0) : Gate 0) *ᵥ basisKet emptyBasis =
      basisKet emptyBasis := by
  rw [Circuit.eval_identity]
  exact Matrix.one_mulVec _

/-! ## Chronological action of two circuit primitives -/

private def firstFlipControl : Primitive 2 :=
  Primitive.unclassified "example-X-on-wire-0" (localUnitary (0 : Fin 2) bitFlipUnitary)

private def thenCnot01 : Primitive 2 :=
  Primitive.unclassified "example-CNOT-0-1" cnot01

/--
The first primitive changes `|00⟩` to `|10⟩`; the second then sees the enabled
control and changes it to `|11⟩`.  Reversing execution would instead end at
`|10⟩`, so this checks the chronological convention nontrivially.
-/
theorem chronological_twoPrimitives :
    (Circuit.eval [firstFlipControl, thenCnot01] : Gate 2) *ᵥ
        basisKet (twoBit false false) = basisKet (twoBit true true) := by
  rw [Circuit.eval_pair_mulVec]
  simp only [firstFlipControl, thenCnot01, Primitive.unclassified_denotation]
  rw [localBitFlip_mulVec_basisKet]
  unfold cnot01
  rw [controlledBitFlip_mulVec_basisKet]
  apply congrArg basisKet
  funext i
  fin_cases i <;>
    simp [controlledBitFlipOutput, flipTarget, setTarget, twoBit, Function.update_apply]

end SemanticsExamples
end Barenco
