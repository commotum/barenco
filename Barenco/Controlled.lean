import Barenco.Semantics
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Bool
import Mathlib.LinearAlgebra.Matrix.Permutation

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

/-- Replace the target bit while retaining every complementary bit. -/
def setTarget {n : ℕ} (target : Fin n) (x : Basis n) (bit : Bool) : Basis n :=
  (splitTarget target).symm (bit, (splitTarget target x).2)

@[simp]
theorem splitTarget_setTarget {n : ℕ} (target : Fin n) (x : Basis n) (bit : Bool) :
    splitTarget target (setTarget target x bit) =
      (bit, (splitTarget target x).2) := by
  simp [setTarget]

@[simp]
theorem setTarget_apply_target {n : ℕ} (target : Fin n) (x : Basis n) (bit : Bool) :
    setTarget target x bit target = bit := by
  change (splitTarget target (setTarget target x bit)).1 = bit
  exact congrArg Prod.fst (splitTarget_setTarget target x bit)

@[simp]
theorem setTarget_apply_of_ne {n : ℕ} (target : Fin n) (x : Basis n) (bit : Bool)
    (i : Fin n) (hi : i ≠ target) :
    setTarget target x bit i = x i := by
  change (splitTarget target (setTarget target x bit)).2 ⟨i, hi⟩ =
    (splitTarget target x).2 ⟨i, hi⟩
  exact congrArg (fun p => p.2 ⟨i, hi⟩) (splitTarget_setTarget target x bit)

@[simp]
theorem setTarget_self {n : ℕ} (target : Fin n) (x : Basis n) :
    setTarget target x (x target) = x := by
  apply (splitTarget target).injective
  ext <;> simp

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
abbrev AgreeOff {n : ℕ} (target : Fin n) (x y : Basis n) : Prop :=
  ∀ i, i ≠ target → x i = y i

theorem splitTarget_snd_eq_iff {n : ℕ} (target : Fin n) (x y : Basis n) :
    (splitTarget target x).2 = (splitTarget target y).2 ↔ AgreeOff target x y := by
  constructor
  · intro h i hi
    exact congrFun h ⟨i, hi⟩
  · intro h
    funext i
    exact h i i.property

theorem eq_iff_target_eq_of_agreeOff {n : ℕ} {target : Fin n} {x y : Basis n}
    (h : AgreeOff target x y) :
    x = y ↔ x target = y target := by
  constructor
  · exact fun hxy => congrFun hxy target
  · intro htarget
    funext i
    by_cases hi : i = target
    · simpa [hi] using htarget
    · exact h i hi

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

@[simp]
theorem coe_ite_qubitUnitary (p : Prop) [Decidable p] (U V : QubitUnitary) :
    (((if p then U else V : QubitUnitary) : QubitMatrix)) =
      if p then (U : QubitMatrix) else (V : QubitMatrix) := by
  by_cases h : p <;> simp [h]

/-- Certified arbitrary-target controlled one-qubit unitary. -/
def controlledUnitary {n : ℕ} (target : Fin n)
    (enabled : ComplementBasis target → Bool) (U : QubitUnitary) : UnitaryGate n :=
  reindexUnitary (splitTarget target).symm
    (blockDiagonalUnitary fun rest => if enabled rest then U else 1)

@[simp]
theorem coe_controlledUnitary {n : ℕ} (target : Fin n)
    (enabled : ComplementBasis target → Bool) (U : QubitUnitary) :
    (controlledUnitary target enabled U : Gate n) = controlledRaw target enabled U := by
  ext row col
  simp [controlledUnitary, controlledRaw, Matrix.blockDiagonal_apply]

theorem localRaw_mem_unitaryGroup {n : ℕ} (target : Fin n) (U : QubitUnitary) :
    localRaw target U ∈ Matrix.unitaryGroup (Basis n) ℂ := by
  simpa using (localUnitary target U).property

theorem controlledRaw_mem_unitaryGroup {n : ℕ} (target : Fin n)
    (enabled : ComplementBasis target → Bool) (U : QubitUnitary) :
    controlledRaw target enabled U ∈ Matrix.unitaryGroup (Basis n) ℂ := by
  simpa using (controlledUnitary target enabled U).property

/-- Basis-column action of an arbitrary-target one-qubit matrix. -/
theorem localRaw_mulVec_basisKet {n : ℕ} (target : Fin n) (U : QubitMatrix)
    (x : Basis n) :
    localRaw target U *ᵥ basisKet x = fun row =>
      if AgreeOff target row x then U (row target) (x target) else 0 := by
  funext row
  rw [mulVec_basisKet_apply, localRaw_apply_eq_if_agreeOff]

/-- The target-changing entry in the column for `x` is the corresponding entry of `U`. -/
@[simp]
theorem localRaw_mulVec_basisKet_setTarget {n : ℕ} (target : Fin n) (U : QubitMatrix)
    (x : Basis n) (bit : Bool) :
    (localRaw target U *ᵥ basisKet x) (setTarget target x bit) =
      U bit (x target) := by
  rw [localRaw_mulVec_basisKet]
  have hagree : AgreeOff target (setTarget target x bit) x := by
    intro i hi
    exact setTarget_apply_of_ne target x bit i hi
  change (if AgreeOff target (setTarget target x bit) x then
      U (setTarget target x bit target) (x target) else 0) = U bit (x target)
  rw [if_pos hagree]
  simp

/-- Local gates have zero basis-column amplitude on assignments changing a non-target wire. -/
theorem localRaw_mulVec_basisKet_eq_zero_of_changed {n : ℕ} (target : Fin n)
    (U : QubitMatrix) {x row : Basis n} (i : Fin n) (hi : i ≠ target)
    (hchanged : row i ≠ x i) :
    (localRaw target U *ᵥ basisKet x) row = 0 := by
  rw [localRaw_mulVec_basisKet]
  have hagree : ¬AgreeOff target row x := by
    intro h
    exact hchanged (h i hi)
  change (if AgreeOff target row x then U (row target) (x target) else 0) = 0
  rw [if_neg hagree]

/-- Basis-column action of a controlled one-qubit matrix, before splitting active cases. -/
theorem controlledRaw_mulVec_basisKet {n : ℕ} (target : Fin n)
    (enabled : ComplementBasis target → Bool) (U : QubitMatrix) (x : Basis n) :
    controlledRaw target enabled U *ᵥ basisKet x = fun row =>
      if AgreeOff target row x then
        (if enabled (splitTarget target x).2 then U else 1)
          (row target) (x target)
      else 0 := by
  funext row
  rw [mulVec_basisKet_apply, controlledRaw_apply_eq_if_agreeOff]
  by_cases hagree : AgreeOff target row x
  · have hrest : (splitTarget target row).2 = (splitTarget target x).2 :=
      (splitTarget_snd_eq_iff target row x).2 hagree
    simp [hrest]
  · simp [hagree]

/-- An active controlled block has exactly the local-gate basis-column action. -/
theorem controlledRaw_mulVec_basisKet_of_enabled {n : ℕ} (target : Fin n)
    (enabled : ComplementBasis target → Bool) (U : QubitMatrix) (x : Basis n)
    (h : enabled (splitTarget target x).2 = true) :
    controlledRaw target enabled U *ᵥ basisKet x =
      localRaw target U *ᵥ basisKet x := by
  rw [controlledRaw_mulVec_basisKet, localRaw_mulVec_basisKet]
  simp [h]

/-- An inactive controlled block fixes its computational-basis ket. -/
theorem controlledRaw_mulVec_basisKet_of_disabled {n : ℕ} (target : Fin n)
    (enabled : ComplementBasis target → Bool) (U : QubitMatrix) (x : Basis n)
    (h : enabled (splitTarget target x).2 = false) :
    controlledRaw target enabled U *ᵥ basisKet x = basisKet x := by
  rw [controlledRaw_mulVec_basisKet]
  funext row
  by_cases hagree : AgreeOff target row x
  · have heq : row = x ↔ row target = x target :=
      eq_iff_target_eq_of_agreeOff hagree
    rw [if_pos hagree, basisKet_apply]
    simp [h, Matrix.one_apply, heq]
  · have hne : row ≠ x := fun hrow => hagree (hrow ▸ fun _ _ => rfl)
    rw [if_neg hagree, basisKet_apply, if_neg hne]

/-- Controlled gates have zero basis-column amplitude after changing a non-target wire. -/
theorem controlledRaw_mulVec_basisKet_eq_zero_of_changed {n : ℕ} (target : Fin n)
    (enabled : ComplementBasis target → Bool) (U : QubitMatrix)
    {x row : Basis n} (i : Fin n) (hi : i ≠ target) (hchanged : row i ≠ x i) :
    (controlledRaw target enabled U *ᵥ basisKet x) row = 0 := by
  rw [controlledRaw_mulVec_basisKet]
  have hagree : ¬AgreeOff target row x := by
    intro h
    exact hchanged (h i hi)
  change (if AgreeOff target row x then _ else 0) = 0
  rw [if_neg hagree]

/--
General controlled-gate truth table: active control assignments receive `U`, and
inactive assignments are fixed.
-/
theorem controlledRaw_truthTable {n : ℕ} (target : Fin n)
    (enabled : ComplementBasis target → Bool) (U : QubitMatrix) (x : Basis n) :
    controlledRaw target enabled U *ᵥ basisKet x =
      if enabled (splitTarget target x).2 then
        localRaw target U *ᵥ basisKet x
      else basisKet x := by
  cases h : enabled (splitTarget target x).2
  · simpa [h] using controlledRaw_mulVec_basisKet_of_disabled target enabled U x h
  · simpa [h] using controlledRaw_mulVec_basisKet_of_enabled target enabled U x h

/-- A finite set of positive controls, all definitionally distinct from `target`. -/
abbrev ControlSet {n : ℕ} (target : Fin n) := Finset (TargetComplement target)

/-- The positive-control predicate: every listed control bit is `true`. -/
def positiveControlsEnabled {n : ℕ} {target : Fin n} (controls : ControlSet target)
    (rest : ComplementBasis target) : Bool :=
  decide (∀ i ∈ controls, rest i = true)

@[simp]
theorem positiveControlsEnabled_eq_true_iff {n : ℕ} {target : Fin n}
    (controls : ControlSet target) (rest : ComplementBasis target) :
    positiveControlsEnabled controls rest = true ↔
      ∀ i ∈ controls, rest i = true := by
  simp [positiveControlsEnabled]

@[simp]
theorem positiveControlsEnabled_splitTarget_eq_true_iff {n : ℕ} {target : Fin n}
    (controls : ControlSet target) (x : Basis n) :
    positiveControlsEnabled controls (splitTarget target x).2 = true ↔
      ∀ i ∈ controls, x i = true := by
  simp [positiveControlsEnabled]

/-- Raw positive multi-controlled one-qubit gate. -/
def positiveControlledRaw {n : ℕ} (target : Fin n) (controls : ControlSet target)
    (U : QubitMatrix) : Gate n :=
  controlledRaw target (positiveControlsEnabled controls) U

/-- Certified positive multi-controlled one-qubit gate. -/
def positiveControlledUnitary {n : ℕ} (target : Fin n) (controls : ControlSet target)
    (U : QubitUnitary) : UnitaryGate n :=
  controlledUnitary target (positiveControlsEnabled controls) U

/-- With no controls, positive control reduces definitionally to the local gate. -/
@[simp]
theorem positiveControlledRaw_empty {n : ℕ} (target : Fin n) (U : QubitMatrix) :
    positiveControlledRaw target (∅ : ControlSet target) U = localRaw target U := by
  ext row col
  simp [positiveControlledRaw, controlledRaw_apply, localRaw_apply,
    positiveControlsEnabled]

/-- The certified empty-control gate is exactly the certified local gate. -/
@[simp]
theorem positiveControlledUnitary_empty {n : ℕ} (target : Fin n) (U : QubitUnitary) :
    positiveControlledUnitary target (∅ : ControlSet target) U = localUnitary target U := by
  apply Subtype.ext
  unfold positiveControlledUnitary
  rw [coe_controlledUnitary, coe_localUnitary]
  exact positiveControlledRaw_empty target U

@[simp]
theorem coe_positiveControlledUnitary {n : ℕ} (target : Fin n)
    (controls : ControlSet target) (U : QubitUnitary) :
    (positiveControlledUnitary target controls U : Gate n) =
      positiveControlledRaw target controls U := by
  simp [positiveControlledUnitary, positiveControlledRaw]

theorem positiveControlledRaw_mem_unitaryGroup {n : ℕ} (target : Fin n)
    (controls : ControlSet target) (U : QubitUnitary) :
    positiveControlledRaw target controls U ∈ Matrix.unitaryGroup (Basis n) ℂ := by
  simpa using (positiveControlledUnitary target controls U).property

/-- Truth table for an arbitrary positive multi-controlled one-qubit matrix. -/
theorem positiveControlledRaw_truthTable {n : ℕ} (target : Fin n)
    (controls : ControlSet target) (U : QubitMatrix) (x : Basis n) :
    positiveControlledRaw target controls U *ᵥ basisKet x =
      if ∀ i ∈ controls, x i = true then
        localRaw target U *ᵥ basisKet x
      else basisKet x := by
  by_cases h : ∀ i ∈ controls, x i = true
  · have henabled : positiveControlsEnabled controls (splitTarget target x).2 = true :=
      (positiveControlsEnabled_splitTarget_eq_true_iff controls x).2 h
    rw [if_pos h]
    exact controlledRaw_mulVec_basisKet_of_enabled target
      (positiveControlsEnabled controls) U x henabled
  · have henabled : positiveControlsEnabled controls (splitTarget target x).2 = false := by
      cases hvalue : positiveControlsEnabled controls (splitTarget target x).2
      · rfl
      · exact (h (positiveControlsEnabled_splitTarget_eq_true_iff controls x |>.1 hvalue)).elim
    rw [if_neg h]
    exact controlledRaw_mulVec_basisKet_of_disabled target
      (positiveControlsEnabled controls) U x henabled

/-- Positive controlled gates cannot change a non-target wire on a basis column. -/
theorem positiveControlledRaw_mulVec_basisKet_eq_zero_of_changed {n : ℕ}
    (target : Fin n) (controls : ControlSet target) (U : QubitMatrix)
    {x row : Basis n} (i : Fin n) (hi : i ≠ target) (hchanged : row i ≠ x i) :
    (positiveControlledRaw target controls U *ᵥ basisKet x) row = 0 := by
  exact controlledRaw_mulVec_basisKet_eq_zero_of_changed target
    (positiveControlsEnabled controls) U i hi hchanged

/-- The one-qubit Pauli-X permutation matrix, with its unitarity certificate. -/
def pauliX : QubitUnitary :=
  ⟨Equiv.boolNot.permMatrix ℂ, by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    rw [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
    simp⟩

@[simp]
theorem coe_pauliX : (pauliX : QubitMatrix) = Equiv.boolNot.permMatrix ℂ := rfl

/-- Pauli-X sends `|bit⟩` to `|!bit⟩`. -/
@[simp]
theorem pauliX_mulVec_basisKet (bit : Bool) :
    (pauliX : QubitMatrix) *ᵥ basisKet bit = basisKet (!bit) := by
  rw [coe_pauliX, Matrix.permMatrix_mulVec]
  funext row
  cases bit <;> cases row <;> rfl

@[simp]
theorem pauliX_apply (row col : Bool) :
    pauliX row col = if row = !col then 1 else 0 := by
  calc
    pauliX row col = ((pauliX : QubitMatrix) *ᵥ basisKet col) row := by simp
    _ = basisKet (!col) row := by rw [pauliX_mulVec_basisKet]
    _ = if row = !col then 1 else 0 := basisKet_apply _ _

/-- Raw Pauli-X embedded at an arbitrary target. -/
def xRaw {n : ℕ} (target : Fin n) : Gate n :=
  localRaw target pauliX

/-- Certified Pauli-X embedded at an arbitrary target. -/
def xUnitary {n : ℕ} (target : Fin n) : UnitaryGate n :=
  localUnitary target pauliX

@[simp]
theorem coe_xUnitary {n : ℕ} (target : Fin n) :
    (xUnitary target : Gate n) = xRaw target := rfl

theorem xRaw_mem_unitaryGroup {n : ℕ} (target : Fin n) :
    xRaw target ∈ Matrix.unitaryGroup (Basis n) ℂ :=
  (xUnitary target).property

theorem eq_setTarget_iff {n : ℕ} (target : Fin n) (x row : Basis n) (bit : Bool) :
    row = setTarget target x bit ↔
      AgreeOff target row x ∧ row target = bit := by
  constructor
  · rintro rfl
    constructor
    · intro i hi
      exact setTarget_apply_of_ne target x bit i hi
    · simp
  · rintro ⟨hagree, htarget⟩
    funext i
    by_cases hi : i = target
    · subst i
      simpa using htarget
    · rw [setTarget_apply_of_ne target x bit i hi]
      exact hagree i hi

/-- Arbitrary-target Pauli-X flips exactly the target bit. -/
@[simp]
theorem xRaw_mulVec_basisKet {n : ℕ} (target : Fin n) (x : Basis n) :
    xRaw target *ᵥ basisKet x = basisKet (setTarget target x (!x target)) := by
  rw [xRaw, localRaw_mulVec_basisKet]
  funext row
  rw [basisKet_apply]
  simp only [pauliX_apply]
  by_cases hagree : AgreeOff target row x
  · rw [if_pos hagree]
    by_cases htarget : row target = !x target
    · rw [if_pos htarget, if_pos ((eq_setTarget_iff target x row _).2 ⟨hagree, htarget⟩)]
    · rw [if_neg htarget, if_neg]
      exact fun hrow => htarget ((eq_setTarget_iff target x row _).1 hrow).2
  · rw [if_neg hagree, if_neg]
    exact fun hrow => hagree ((eq_setTarget_iff target x row _).1 hrow).1

/--
Raw CNOT with a positive `control` and distinct `target`.  The proof argument
prevents accidentally identifying the two wires.
-/
def cnotRaw {n : ℕ} (control target : Fin n) (h : control ≠ target) : Gate n :=
  positiveControlledRaw target ({⟨control, h⟩} : ControlSet target) pauliX

/-- Certified CNOT with distinct control and target wires. -/
def cnotUnitary {n : ℕ} (control target : Fin n) (h : control ≠ target) :
    UnitaryGate n :=
  positiveControlledUnitary target ({⟨control, h⟩} : ControlSet target) pauliX

@[simp]
theorem coe_cnotUnitary {n : ℕ} (control target : Fin n) (h : control ≠ target) :
    (cnotUnitary control target h : Gate n) = cnotRaw control target h := by
  simp [cnotUnitary, cnotRaw]

theorem cnotRaw_mem_unitaryGroup {n : ℕ} (control target : Fin n)
    (h : control ≠ target) :
    cnotRaw control target h ∈ Matrix.unitaryGroup (Basis n) ℂ := by
  simpa using (cnotUnitary control target h).property

/-- CNOT's full computational-basis truth table. -/
@[simp]
theorem cnotRaw_mulVec_basisKet {n : ℕ} (control target : Fin n)
    (h : control ≠ target) (x : Basis n) :
    cnotRaw control target h *ᵥ basisKet x =
      basisKet (if x control then setTarget target x (!x target) else x) := by
  rw [cnotRaw, positiveControlledRaw_truthTable]
  cases hcontrol : x control
  · simp [hcontrol]
  · simpa [hcontrol, xRaw] using xRaw_mulVec_basisKet target x

end Barenco
