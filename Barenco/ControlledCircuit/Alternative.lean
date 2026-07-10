import Barenco.ControlledCircuit.Special

/-!
# Controlled-V alternative library (corrected Corollary 5.6)

Corollary 5.6 replaces each CNOT in the general controlled-U construction by a
fixed controlled gate `C(V)` from the Lemma 5.5 family. In standard-column
orientation, choose unitary factors `D,F` with

* `D * F = I`, and
* `V = F * X * D`.

Substituting `F; C(V); D` for each CNOT and merging adjacent target-local gates
gives a six-node circuit: four one-qubit gates and two controlled-`V` macros.

This is not a six-basic-gate result under the Sections 3–7 cost model, whose only
two-qubit primitive is CNOT. The syntax below deliberately retains each macro as
`.controlledOneQubit 1`; `CostModel.oneQubitCNOT` therefore returns `none` until
the macros are expanded. A separate expansion leaf proves the CNOT cost and the
three advertised merge groups.
-/

namespace Barenco.ControlledCircuit

open Barenco.OneQubit

noncomputable section

/--
The target-only five-node core of Corollary 5.6. Chronologically its local gates
are `F*P`, `F*Q*D`, and `R*D`, separated by two identical controlled-`V` macros.
-/
def controlledVMacroCoreCircuit {n : ℕ} (control target : Fin n)
    (h : control ≠ target) (P Q R D F V : QubitUnitary) : Circuit n :=
  [Primitive.oneQubit target (F * P),
    Primitive.positiveControlled target ({⟨control, h⟩} : ControlSet target) V,
    Primitive.oneQubit target (F * Q * D),
    Primitive.positiveControlled target ({⟨control, h⟩} : ControlSet target) V,
    Primitive.oneQubit target (R * D)]

/-- Direct full-register matrix product of the target-only macro core. -/
theorem eval_controlledVMacroCoreCircuit_raw {n : ℕ}
    (control target : Fin n) (h : control ≠ target)
    (P Q R D F V : QubitUnitary) :
    (Circuit.eval (controlledVMacroCoreCircuit control target h P Q R D F V) : Gate n) =
      localRaw target (R * D) *
        positiveControlledRaw target ({⟨control, h⟩} : ControlSet target) V *
        localRaw target (F * Q * D) *
        positiveControlledRaw target ({⟨control, h⟩} : ControlSet target) V *
        localRaw target (F * P) := by
  simp [controlledVMacroCoreCircuit, Circuit.eval]

/-- Exact inactive and active blocks of the controlled-`V` macro core. -/
theorem eval_controlledVMacroCoreCircuit_raw_blocks {n : ℕ}
    (control target : Fin n) (h : control ≠ target)
    (P Q R D F V : QubitUnitary) :
    (Circuit.eval (controlledVMacroCoreCircuit control target h P Q R D F V) : Gate n) =
      targetBlockRaw target (fun rest =>
        if rest ⟨control, h⟩ then
          ((R * D : QubitUnitary) : QubitMatrix) * (V : QubitMatrix) *
            ((F * Q * D : QubitUnitary) : QubitMatrix) * (V : QubitMatrix) *
            ((F * P : QubitUnitary) : QubitMatrix)
        else
          ((R * D : QubitUnitary) : QubitMatrix) *
            ((F * Q * D : QubitUnitary) : QubitMatrix) *
            ((F * P : QubitUnitary) : QubitMatrix)) := by
  rw [eval_controlledVMacroCoreCircuit_raw]
  simp_rw [localRaw_eq_targetBlockRaw,
    positiveControlledRaw_singleton_eq_targetBlockRaw]
  rw [targetBlockRaw_mul, targetBlockRaw_mul, targetBlockRaw_mul,
    targetBlockRaw_mul]
  congr 1
  funext rest
  cases hr : rest ⟨control, h⟩ <;> simp

/-- Complete two-branch characterization of the target-only macro core. -/
theorem eval_controlledVMacroCoreCircuit_eq_iff {n : ℕ}
    (control target : Fin n) (h : control ≠ target)
    (P Q R D F V W : QubitUnitary) :
    Circuit.eval (controlledVMacroCoreCircuit control target h P Q R D F V) =
        positiveControlledUnitary target ({⟨control, h⟩} : ControlSet target) W ↔
      ((R * D : QubitUnitary) : QubitMatrix) *
          ((F * Q * D : QubitUnitary) : QubitMatrix) *
          ((F * P : QubitUnitary) : QubitMatrix) = 1 ∧
        ((R * D : QubitUnitary) : QubitMatrix) * (V : QubitMatrix) *
          ((F * Q * D : QubitUnitary) : QubitMatrix) * (V : QubitMatrix) *
          ((F * P : QubitUnitary) : QubitMatrix) = (W : QubitMatrix) := by
  constructor
  · intro heval
    have hraw := congrArg Subtype.val heval
    rw [eval_controlledVMacroCoreCircuit_raw_blocks, coe_positiveControlledUnitary,
      positiveControlledRaw_singleton_eq_targetBlockRaw] at hraw
    have hblocks := targetBlockRaw_injective target hraw
    exact ⟨by simpa using congrFun hblocks (fun _ => false),
      by simpa using congrFun hblocks (fun _ => true)⟩
  · rintro ⟨hinactive, hactive⟩
    simp only [Submonoid.coe_mul] at hinactive hactive
    apply Subtype.ext
    rw [eval_controlledVMacroCoreCircuit_raw_blocks, coe_positiveControlledUnitary,
      positiveControlledRaw_singleton_eq_targetBlockRaw]
    congr 1
    funext rest
    cases hcontrol : rest ⟨control, h⟩ <;> simp [hinactive, hactive]

/--
Replacing each macro by `F*X*D` reduces the two branch products to the original
A/B/C branch products.
-/
theorem eval_controlledVMacroCoreCircuit_of_products {n : ℕ}
    (control target : Fin n) (h : control ≠ target)
    (P Q R D F V W : QubitUnitary)
    (hDF : (D : QubitMatrix) * (F : QubitMatrix) = 1)
    (hV : (V : QubitMatrix) = (F : QubitMatrix) * sigmaX * (D : QubitMatrix))
    (hinactive : (R : QubitMatrix) * (Q : QubitMatrix) * (P : QubitMatrix) = 1)
    (hactive : (R : QubitMatrix) * sigmaX * (Q : QubitMatrix) * sigmaX *
      (P : QubitMatrix) = (W : QubitMatrix)) :
    Circuit.eval (controlledVMacroCoreCircuit control target h P Q R D F V) =
      positiveControlledUnitary target ({⟨control, h⟩} : ControlSet target) W := by
  apply (eval_controlledVMacroCoreCircuit_eq_iff control target h P Q R D F V W).mpr
  constructor
  · simp only [Submonoid.coe_mul]
    calc
      ((R : QubitMatrix) * D) * ((F : QubitMatrix) * Q * D) * ((F : QubitMatrix) * P) =
          (R : QubitMatrix) * (D * F) * Q * (D * F) * P := by noncomm_ring
      _ = (R : QubitMatrix) * Q * P := by rw [hDF]; simp
      _ = 1 := hinactive
  · simp only [Submonoid.coe_mul]
    rw [hV]
    calc
      ((R : QubitMatrix) * D) * (F * sigmaX * D) * (F * Q * D) *
          (F * sigmaX * D) * (F * P) =
        (R : QubitMatrix) * (D * F) * sigmaX * (D * F) * Q *
          (D * F) * sigmaX * (D * F) * P := by noncomm_ring
      _ = (R : QubitMatrix) * sigmaX * Q * sigmaX * P := by rw [hDF]; simp
      _ = (W : QubitMatrix) := hactive

/-- The full six-node macro circuit, including the control-wire phase gate first. -/
def controlledVMacroU2Circuit {n : ℕ} (control target : Fin n)
    (h : control ≠ target) (delta : ℝ)
    (P Q R D F V : QubitUnitary) : Circuit n :=
  Circuit.append (controlledPhaseCircuit control delta)
    (controlledVMacroCoreCircuit control target h P Q R D F V)

/-- Parameterized exact correctness of the full controlled-`V` macro circuit. -/
theorem eval_controlledVMacroU2Circuit_of_products {n : ℕ}
    (control target : Fin n) (h : control ≠ target) (delta : ℝ)
    (P Q R D F V W U : QubitUnitary)
    (hDF : (D : QubitMatrix) * (F : QubitMatrix) = 1)
    (hV : (V : QubitMatrix) = (F : QubitMatrix) * sigmaX * (D : QubitMatrix))
    (hinactive : (R : QubitMatrix) * (Q : QubitMatrix) * (P : QubitMatrix) = 1)
    (hactive : (R : QubitMatrix) * sigmaX * (Q : QubitMatrix) * sigmaX *
      (P : QubitMatrix) = (W : QubitMatrix))
    (hU : (U : QubitMatrix) = phaseShift delta * (W : QubitMatrix)) :
    Circuit.eval (controlledVMacroU2Circuit control target h delta P Q R D F V) =
      positiveControlledUnitary target ({⟨control, h⟩} : ControlSet target) U := by
  have hcore := eval_controlledVMacroCoreCircuit_of_products control target h
    P Q R D F V W hDF hV hinactive hactive
  have hWU : W * phaseShiftUnitary delta = U := by
    apply Subtype.ext
    change (W : QubitMatrix) * phaseShift delta = (U : QubitMatrix)
    rw [← phaseShift_mul_comm]
    exact hU.symm
  rw [controlledVMacroU2Circuit, Circuit.eval_append, hcore,
    eval_controlledPhaseCircuit control target h delta,
    singleControlledUnitary_mul control target h W (phaseShiftUnitary delta), hWU]

/--
Corrected Corollary 5.6: for every fixed pair of real parameters, every
controlled one-qubit unitary has an exact six-node circuit using two copies of
the associated controlled-`V` macro.
-/
theorem controlledVMacroU2Circuit_exists {n : ℕ}
    (control target : Fin n) (h : control ≠ target)
    (alpha theta : ℝ) (U : QubitUnitary) :
    ∃ P Q R : QubitSpecialUnitary,
      let D := columnASpecialUnitary alpha theta
      let F := columnBSpecialUnitary alpha theta alpha
      let V := pauliConjugateUnitary D
      Circuit.eval (controlledVMacroU2Circuit control target h
        (determinantPhaseAngle U)
        (specialUnitaryAsUnitary P) (specialUnitaryAsUnitary Q)
        (specialUnitaryAsUnitary R) (specialUnitaryAsUnitary D)
        (specialUnitaryAsUnitary F) V) =
        positiveControlledUnitary target ({⟨control, h⟩} : ControlSet target) U := by
  obtain ⟨P, Q, R, hinactive, hactive⟩ :=
    specialUnitary_exists_columnChronologicalABC (specialUnitaryPart U)
  refine ⟨P, Q, R, ?_⟩
  dsimp only
  let D := columnASpecialUnitary alpha theta
  let F := columnBSpecialUnitary alpha theta alpha
  have hFraw : (F : QubitMatrix) = star (D : QubitMatrix) := by
    simp only [D, F, coe_columnASpecialUnitary, coe_columnBSpecialUnitary]
    exact (star_columnA_eq_columnB alpha theta).symm
  have hDF :
      (specialUnitaryAsUnitary D : QubitMatrix) *
        (specialUnitaryAsUnitary F : QubitMatrix) = 1 := by
    rw [coe_specialUnitaryAsUnitary, coe_specialUnitaryAsUnitary, hFraw]
    have hgroup : specialUnitaryAsUnitary D * (specialUnitaryAsUnitary D)⁻¹ = 1 :=
      mul_inv_cancel _
    exact congrArg Subtype.val hgroup
  have hV : (pauliConjugateUnitary D : QubitMatrix) =
      (specialUnitaryAsUnitary F : QubitMatrix) * sigmaX *
        (specialUnitaryAsUnitary D : QubitMatrix) := by
    rw [coe_pauliConjugateUnitary, coe_specialUnitaryAsUnitary,
      coe_specialUnitaryAsUnitary, pauliConjugate, hFraw]
  apply eval_controlledVMacroU2Circuit_of_products control target h
    (determinantPhaseAngle U)
    (specialUnitaryAsUnitary P) (specialUnitaryAsUnitary Q)
    (specialUnitaryAsUnitary R) (specialUnitaryAsUnitary D)
    (specialUnitaryAsUnitary F) (pauliConjugateUnitary D)
    (specialUnitaryAsUnitary (specialUnitaryPart U)) U
  · exact hDF
  · exact hV
  · exact hinactive
  · exact hactive
  · exact (phaseShift_mul_specialUnitaryPart U).symm

/-! ## Structural macro resources -/

@[simp]
theorem controlledVMacroU2Circuit_gateCount {n : ℕ}
    (control target : Fin n) (h : control ≠ target)
    (delta : ℝ) (P Q R D F V : QubitUnitary) :
    Circuit.gateCount
      (controlledVMacroU2Circuit control target h delta P Q R D F V) = 6 := by
  rfl

@[simp]
theorem controlledVMacroU2Circuit_kindCounts {n : ℕ}
    (control target : Fin n) (h : control ≠ target)
    (delta : ℝ) (P Q R D F V : QubitUnitary) :
    Circuit.kindCount .oneQubit
        (controlledVMacroU2Circuit control target h delta P Q R D F V) = 4 ∧
      Circuit.kindCount (.controlledOneQubit 1)
        (controlledVMacroU2Circuit control target h delta P Q R D F V) = 2 := by
  simp [controlledVMacroU2Circuit, controlledPhaseCircuit,
    controlledVMacroCoreCircuit, Circuit.append, Circuit.kindCount]

/-- The Sections 3–7 cost model rejects the two unexpanded controlled-`V` macros. -/
@[simp]
theorem controlledVMacroU2Circuit_oneQubitCNOTCost {n : ℕ}
    (control target : Fin n) (h : control ≠ target)
    (delta : ℝ) (P Q R D F V : QubitUnitary) :
    Circuit.cost CostModel.oneQubitCNOT
      (controlledVMacroU2Circuit control target h delta P Q R D F V) = none := by
  rfl

end

end Barenco.ControlledCircuit
