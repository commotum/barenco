import Barenco.LowerBounds.Lemma77

/-!
# Diagnostic examples for the Lemma 7.7 lower bound

This root-excluded leaf checks the exact small-width boundaries of Barenco
Lemma 7.7.  Every implementation witness is a literal `BasicCircuit`, and every
resource statement is computed from `BasicCircuit.cnotCount`,
`BasicCircuit.oneQubitCount`, or `BasicCircuit.gateCount`.  Matrix equality alone
is never used as a resource certificate.

The examples show that the general `n - 1` CNOT lower bound is zero at width one,
is attained by the canonical CNOT at width two, and gives two CNOTs at width
three.  The final empty-circuit witness records why the nonscalar hypothesis is
essential: a fully controlled identity target is still the identity operation.
-/

namespace Barenco.LowerBounds.LowerBoundExamples

noncomputable section

/-! ## Target matrices used by the diagnostics -/

/-- Pauli-X is nonscalar, as witnessed by its nonzero off-diagonal entries. -/
theorem pauliX_not_scalar :
    ¬IsScalarQubitMatrix (pauliX : QubitMatrix) := by
  rw [isScalarQubitMatrix_iff_entries]
  simp [pauliX_apply]

/-- The certified one-qubit identity lies on the scalar boundary. -/
theorem identity_is_scalar :
    IsScalarQubitMatrix ((1 : QubitUnitary) : QubitMatrix) := by
  refine ⟨1, ?_⟩
  simp

/-! ## Width one: the zero-CNOT boundary -/

/-- Lemma 7.7 specializes to the vacuous but exact lower bound zero at width one. -/
theorem widthOne_fullyControlledX_cnotLowerBound (circuit : BasicCircuit 1)
    (heval : circuit.eval =
      positiveControlledUnitary (0 : Fin 1)
        (Finset.univ : ControlSet (0 : Fin 1)) pauliX) :
    0 ≤ circuit.cnotCount := by
  exact circuit.fullyControlled_cnotCount_lowerBound (0 : Fin 1) pauliX
    pauliX_not_scalar heval

/-- Literal one-qubit Pauli-X circuit attaining the width-one CNOT bound. -/
def canonicalWidthOneX : BasicCircuit 1 :=
  [.oneQubit (0 : Fin 1) pauliX]

private theorem widthOne_fullControlSet_empty :
    (Finset.univ : ControlSet (0 : Fin 1)) = ∅ := by
  decide

/-- The literal width-one witness has the intended fully controlled semantics. -/
theorem canonicalWidthOneX_eval :
    canonicalWidthOneX.eval =
      positiveControlledUnitary (0 : Fin 1)
        (Finset.univ : ControlSet (0 : Fin 1)) pauliX := by
  simp only [canonicalWidthOneX, BasicCircuit.eval_cons, BasicCircuit.eval_nil,
    BasicPrimitive.denotation_oneQubit, one_mul]
  rw [widthOne_fullControlSet_empty, positiveControlledUnitary_empty]

/-- The width-one witness has zero CNOTs and one basic gate, by syntax. -/
theorem canonicalWidthOneX_counts :
    canonicalWidthOneX.cnotCount = 0 ∧
      canonicalWidthOneX.oneQubitCount = 1 ∧
      canonicalWidthOneX.gateCount = 1 := by
  exact ⟨rfl, rfl, rfl⟩

/-! ## Width two: controlled-X needs and attains one CNOT -/

private theorem zero_ne_one_fin2 : (0 : Fin 2) ≠ 1 := by decide

/-- Every exact two-wire controlled-X `BasicCircuit` contains a CNOT. -/
theorem widthTwo_controlledX_cnotLowerBound (circuit : BasicCircuit 2)
    (heval : circuit.eval =
      positiveControlledUnitary (1 : Fin 2)
        (Finset.univ : ControlSet (1 : Fin 2)) pauliX) :
    1 ≤ circuit.cnotCount := by
  simpa using circuit.fullyControlled_cnotCount_lowerBound (1 : Fin 2) pauliX
    pauliX_not_scalar heval

/-- The canonical control-zero, target-one CNOT as restricted basic syntax. -/
def canonicalWidthTwoCNOT : BasicCircuit 2 :=
  [.cnot (0 : Fin 2) (1 : Fin 2) zero_ne_one_fin2]

private theorem widthTwo_singletonControl_eq_univ :
    ({⟨(0 : Fin 2), zero_ne_one_fin2⟩} : ControlSet (1 : Fin 2)) =
      Finset.univ := by
  decide

/-- The canonical one-CNOT witness is exactly fully controlled Pauli-X. -/
theorem canonicalWidthTwoCNOT_eval :
    canonicalWidthTwoCNOT.eval =
      positiveControlledUnitary (1 : Fin 2)
        (Finset.univ : ControlSet (1 : Fin 2)) pauliX := by
  simp only [canonicalWidthTwoCNOT, BasicCircuit.eval_cons,
    BasicCircuit.eval_nil, BasicPrimitive.denotation_cnot, one_mul]
  rw [cnotUnitary, widthTwo_singletonControl_eq_univ]

/-- The attaining witness has exactly one CNOT and one total basic gate. -/
theorem canonicalWidthTwoCNOT_counts :
    canonicalWidthTwoCNOT.cnotCount = 1 ∧
      canonicalWidthTwoCNOT.oneQubitCount = 0 ∧
      canonicalWidthTwoCNOT.gateCount = 1 := by
  exact ⟨rfl, rfl, rfl⟩

/-- One CNOT is attained by a literal exact two-wire controlled-X circuit. -/
theorem widthTwo_controlledX_oneCNOT_attained :
    ∃ circuit : BasicCircuit 2,
      circuit.eval =
          positiveControlledUnitary (1 : Fin 2)
            (Finset.univ : ControlSet (1 : Fin 2)) pauliX ∧
        circuit.cnotCount = 1 ∧ circuit.gateCount = 1 := by
  exact ⟨canonicalWidthTwoCNOT, canonicalWidthTwoCNOT_eval,
    canonicalWidthTwoCNOT_counts.1, canonicalWidthTwoCNOT_counts.2.2⟩

/-! ## Width three: doubly controlled X needs two CNOTs -/

/-- Every exact three-wire fully controlled Pauli-X circuit has at least two CNOTs. -/
theorem widthThree_fullyControlledX_cnotLowerBound (circuit : BasicCircuit 3)
    (heval : circuit.eval =
      positiveControlledUnitary (2 : Fin 3)
        (Finset.univ : ControlSet (2 : Fin 3)) pauliX) :
    2 ≤ circuit.cnotCount := by
  simpa using circuit.fullyControlled_cnotCount_lowerBound (2 : Fin 3) pauliX
    pauliX_not_scalar heval

/-! ## Scalar boundary: an empty exact implementation -/

/-- A fully controlled identity target is exactly the full-register identity. -/
theorem widthTwo_fullyControlledIdentity_eq_one :
    positiveControlledUnitary (1 : Fin 2)
        (Finset.univ : ControlSet (1 : Fin 2)) (1 : QubitUnitary) = 1 := by
  apply Subtype.ext
  rw [coe_positiveControlledUnitary]
  ext row col
  rw [positiveControlledRaw, controlledRaw_apply_eq_if_agreeOff]
  change
    (if AgreeOff (1 : Fin 2) row col then
        (if positiveControlsEnabled (Finset.univ : ControlSet (1 : Fin 2))
            (splitTarget (1 : Fin 2) row).2 then
          (1 : QubitMatrix)
        else 1) (row 1) (col 1)
      else 0) = (1 : Gate 2) row col
  by_cases hagree : AgreeOff (1 : Fin 2) row col
  · rw [if_pos hagree]
    simp only [ite_self]
    rw [Matrix.one_apply, Matrix.one_apply]
    by_cases htarget : row (1 : Fin 2) = col 1
    · have hrow : row = col := (eq_iff_target_eq_of_agreeOff hagree).2 htarget
      simp [hrow]
    · have hrow : row ≠ col := by
        intro h
        exact htarget (congrFun h 1)
      simp [htarget, hrow]
  · rw [if_neg hagree, Matrix.one_apply, if_neg]
    intro hrow
    subst col
    exact hagree fun _ _ => rfl

/--
The empty restricted circuit exactly realizes the fully controlled identity with
zero CNOTs and zero total gates.  Thus dropping the nonscalar hypothesis would
make the width-two `1 ≤ cnotCount` conclusion false.
-/
theorem widthTwo_empty_fullyControlledIdentity :
    BasicCircuit.eval ([] : BasicCircuit 2) =
        positiveControlledUnitary (1 : Fin 2)
          (Finset.univ : ControlSet (1 : Fin 2)) (1 : QubitUnitary) ∧
      BasicCircuit.cnotCount ([] : BasicCircuit 2) = 0 ∧
      BasicCircuit.gateCount ([] : BasicCircuit 2) = 0 := by
  constructor
  · rw [widthTwo_fullyControlledIdentity_eq_one]
    rfl
  · exact ⟨rfl, rfl⟩

end


end Barenco.LowerBounds.LowerBoundExamples
