import Barenco.ControlledCircuit.Phase

/-!
# Selected exact six-node controlled one-qubit circuits

Corollary 5.3 supplies special-unitary factors existentially.  This leaf packages
one such factorization as an actual noncomputable circuit so later schedule and
recursive constructions can reuse the same exact evaluator and syntax-derived
resource contract.
-/

namespace Barenco.ControlledCircuit

open Barenco.OneQubit

noncomputable section

/-- Complete semantic and resource contract for a selected Corollary 5.3 circuit. -/
def SelectedControlledU2Spec {n : ℕ} (control target : Fin n)
    (h : control ≠ target) (U : QubitUnitary) (circuit : Circuit n) : Prop :=
  Circuit.eval circuit =
      positiveControlledUnitary target
        ({⟨control, h⟩} : ControlSet target) U ∧
    Circuit.gateCount circuit = 6 ∧
    Circuit.kindCount .oneQubit circuit = 4 ∧
    Circuit.kindCount .cnot circuit = 2 ∧
    Circuit.cost CostModel.oneQubitCNOT circuit = some 6

private theorem exists_selectedControlledU2Circuit {n : ℕ}
    (control target : Fin n) (h : control ≠ target) (U : QubitUnitary) :
    ∃ circuit : Circuit n, SelectedControlledU2Spec control target h U circuit := by
  obtain ⟨A, B, C, heval⟩ := controlledU2Circuit_exists control target h U
  let circuit := controlledU2Circuit control target h
    (determinantPhaseAngle U) (specialUnitaryAsUnitary A)
      (specialUnitaryAsUnitary B) (specialUnitaryAsUnitary C)
  refine ⟨circuit, heval, ?_, ?_, ?_, ?_⟩
  · exact controlledU2Circuit_gateCount _ _ _ _ _ _ _
  · exact (controlledU2Circuit_kindCounts _ _ _ _ _ _ _).1
  · exact (controlledU2Circuit_kindCounts _ _ _ _ _ _ _).2
  · exact controlledU2Circuit_oneQubitCNOTCost _ _ _ _ _ _ _

/-- One fixed exact six-node implementation of a singly controlled `U`. -/
def selectedControlledU2Circuit {n : ℕ} (control target : Fin n)
    (h : control ≠ target) (U : QubitUnitary) : Circuit n :=
  Classical.choose (exists_selectedControlledU2Circuit control target h U)

/-- The selected circuit satisfies its complete semantic and resource contract. -/
theorem selectedControlledU2Circuit_spec {n : ℕ}
    (control target : Fin n) (h : control ≠ target) (U : QubitUnitary) :
    SelectedControlledU2Spec control target h U
      (selectedControlledU2Circuit control target h U) :=
  Classical.choose_spec (exists_selectedControlledU2Circuit control target h U)

@[simp]
theorem eval_selectedControlledU2Circuit {n : ℕ}
    (control target : Fin n) (h : control ≠ target) (U : QubitUnitary) :
    Circuit.eval (selectedControlledU2Circuit control target h U) =
      positiveControlledUnitary target
        ({⟨control, h⟩} : ControlSet target) U :=
  (selectedControlledU2Circuit_spec control target h U).1

@[simp]
theorem selectedControlledU2Circuit_gateCount {n : ℕ}
    (control target : Fin n) (h : control ≠ target) (U : QubitUnitary) :
    Circuit.gateCount (selectedControlledU2Circuit control target h U) = 6 :=
  (selectedControlledU2Circuit_spec control target h U).2.1

@[simp]
theorem selectedControlledU2Circuit_oneQubitCount {n : ℕ}
    (control target : Fin n) (h : control ≠ target) (U : QubitUnitary) :
    Circuit.kindCount .oneQubit
        (selectedControlledU2Circuit control target h U) = 4 :=
  (selectedControlledU2Circuit_spec control target h U).2.2.1

@[simp]
theorem selectedControlledU2Circuit_cnotCount {n : ℕ}
    (control target : Fin n) (h : control ≠ target) (U : QubitUnitary) :
    Circuit.kindCount .cnot
        (selectedControlledU2Circuit control target h U) = 2 :=
  (selectedControlledU2Circuit_spec control target h U).2.2.2.1

@[simp]
theorem selectedControlledU2Circuit_oneQubitCNOTCost {n : ℕ}
    (control target : Fin n) (h : control ≠ target) (U : QubitUnitary) :
    Circuit.cost CostModel.oneQubitCNOT
        (selectedControlledU2Circuit control target h U) = some 6 :=
  (selectedControlledU2Circuit_spec control target h U).2.2.2.2

end


end Barenco.ControlledCircuit
