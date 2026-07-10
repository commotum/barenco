import Barenco.ControlledCircuit.Decomposition
import Barenco.OneQubit.SelectedABC

/-!
# Selected exact five-node controlled special-unitary circuits

This leaf packages the five-node Lemma 5.1 implementation of a singly
controlled special-unitary target.  It is deliberately distinct from the
six-node selected arbitrary-U(2) circuit: determinant one removes the separate
controlled scalar-phase node.
-/

namespace Barenco.ControlledCircuit

open Barenco.OneQubit

noncomputable section

/-- Complete semantic and resource contract for a selected controlled-SU(2) circuit. -/
def SelectedControlledSU2Spec {n : ℕ} (control target : Fin n)
    (h : control ≠ target) (W : QubitSpecialUnitary) (circuit : Circuit n) : Prop :=
  Circuit.eval circuit =
      positiveControlledUnitary target
        ({⟨control, h⟩} : ControlSet target) (specialUnitaryAsUnitary W) ∧
    Circuit.gateCount circuit = 5 ∧
    Circuit.kindCount .oneQubit circuit = 3 ∧
    Circuit.kindCount .cnot circuit = 2 ∧
    Circuit.cost CostModel.oneQubitCNOT circuit = some 5

/--
One fixed five-node exact implementation of a singly controlled special unitary.
-/
def selectedControlledSU2Circuit {n : ℕ} (control target : Fin n)
    (h : control ≠ target) (W : QubitSpecialUnitary) : Circuit n :=
  let factors := selectedColumnABCFactors W
  controlledABCCircuit control target h
    (specialUnitaryAsUnitary factors.A)
    (specialUnitaryAsUnitary factors.B)
    (specialUnitaryAsUnitary factors.C)

/-- The selected five-node circuit has the exact controlled-`W` evaluator. -/
@[simp]
theorem eval_selectedControlledSU2Circuit {n : ℕ}
    (control target : Fin n) (h : control ≠ target)
    (W : QubitSpecialUnitary) :
    Circuit.eval (selectedControlledSU2Circuit control target h W) =
      positiveControlledUnitary target
        ({⟨control, h⟩} : ControlSet target) (specialUnitaryAsUnitary W) := by
  let factors := selectedColumnABCFactors W
  apply (eval_controlledABCCircuit_eq_iff control target h
    (specialUnitaryAsUnitary factors.A)
    (specialUnitaryAsUnitary factors.B)
    (specialUnitaryAsUnitary factors.C)
    (specialUnitaryAsUnitary W)).mpr
  exact ⟨factors.inactive, by
    simpa only [coe_specialUnitaryAsUnitary] using factors.active⟩

@[simp]
theorem selectedControlledSU2Circuit_gateCount {n : ℕ}
    (control target : Fin n) (h : control ≠ target)
    (W : QubitSpecialUnitary) :
    Circuit.gateCount (selectedControlledSU2Circuit control target h W) = 5 := by
  simp [selectedControlledSU2Circuit]

@[simp]
theorem selectedControlledSU2Circuit_oneQubitCount {n : ℕ}
    (control target : Fin n) (h : control ≠ target)
    (W : QubitSpecialUnitary) :
    Circuit.kindCount .oneQubit
        (selectedControlledSU2Circuit control target h W) = 3 := by
  simp [selectedControlledSU2Circuit]

@[simp]
theorem selectedControlledSU2Circuit_cnotCount {n : ℕ}
    (control target : Fin n) (h : control ≠ target)
    (W : QubitSpecialUnitary) :
    Circuit.kindCount .cnot
        (selectedControlledSU2Circuit control target h W) = 2 := by
  simp [selectedControlledSU2Circuit]

@[simp]
theorem selectedControlledSU2Circuit_oneQubitCNOTCost {n : ℕ}
    (control target : Fin n) (h : control ≠ target)
    (W : QubitSpecialUnitary) :
    Circuit.cost CostModel.oneQubitCNOT
        (selectedControlledSU2Circuit control target h W) = some 5 := by
  simp [selectedControlledSU2Circuit]

/-- The selected circuit satisfies its complete semantic and resource contract. -/
theorem selectedControlledSU2Circuit_spec {n : ℕ}
    (control target : Fin n) (h : control ≠ target)
    (W : QubitSpecialUnitary) :
    SelectedControlledSU2Spec control target h W
      (selectedControlledSU2Circuit control target h W) := by
  exact ⟨eval_selectedControlledSU2Circuit control target h W,
    selectedControlledSU2Circuit_gateCount control target h W,
    selectedControlledSU2Circuit_oneQubitCount control target h W,
    selectedControlledSU2Circuit_cnotCount control target h W,
    selectedControlledSU2Circuit_oneQubitCNOTCost control target h W⟩

end


end Barenco.ControlledCircuit
