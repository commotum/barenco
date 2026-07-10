import Barenco.ControlledCircuit.Phase
import Barenco.OneQubit.SelectedABC
import Barenco.Optimization.FusionResources

/-!
# Transparent selected controlled-U fusion circuit

This module chooses one checked column-chronological `A/B/C` factorization of
the determinant-one part of an arbitrary one-qubit unitary and retains every
factor in optimizer-visible syntax.  Its six chronological nodes are

`phase(control); A(target); CNOT; B(target); CNOT; C(target)`.

Unlike the existing whole-circuit selector, this constructor retains a literal
`FusionCircuit`, lowers exactly to the parameterized
`controlledU2Circuit`, and derives its resource profile from the visible syntax.
-/

namespace Barenco.ControlledCircuit

open Barenco.OneQubit
open Barenco.Optimization

noncomputable section

/--
One transparent six-node implementation of a singleton-controlled arbitrary
one-qubit unitary.  The selected factors retain their local payloads for later
fusion and normalization.
-/
def canonicalSelectedControlledU2FusionCircuit {n : ℕ}
    (control target : Fin n) (h : control ≠ target)
    (U : QubitUnitary) : FusionCircuit n :=
  let factors := selectedColumnABCFactors (specialUnitaryPart U)
  [.oneQubit control (controlPhaseUnitary (determinantPhaseAngle U)),
    .oneQubit target (specialUnitaryAsUnitary factors.A),
    .cnot control target h,
    .oneQubit target (specialUnitaryAsUnitary factors.B),
    .cnot control target h,
    .oneQubit target (specialUnitaryAsUnitary factors.C)]

/--
Trusted lowering exposes exactly the existing parameterized six-node circuit,
with no whole-circuit selection or metadata reconstruction.
-/
@[simp]
theorem lower_canonicalSelectedControlledU2FusionCircuit {n : ℕ}
    (control target : Fin n) (h : control ≠ target)
    (U : QubitUnitary) :
    (canonicalSelectedControlledU2FusionCircuit control target h U).lower =
      let factors := selectedColumnABCFactors (specialUnitaryPart U)
      controlledU2Circuit control target h
        (determinantPhaseAngle U)
        (specialUnitaryAsUnitary factors.A)
        (specialUnitaryAsUnitary factors.B)
        (specialUnitaryAsUnitary factors.C) := by
  rfl

/-- Exact full-register evaluator of the transparent selected circuit. -/
@[simp]
theorem eval_canonicalSelectedControlledU2FusionCircuit {n : ℕ}
    (control target : Fin n) (h : control ≠ target)
    (U : QubitUnitary) :
    (canonicalSelectedControlledU2FusionCircuit control target h U).eval =
      positiveControlledUnitary target
        ({⟨control, h⟩} : ControlSet target) U := by
  let factors := selectedColumnABCFactors (specialUnitaryPart U)
  rw [← FusionCircuit.eval_lower,
    lower_canonicalSelectedControlledU2FusionCircuit]
  apply eval_controlledU2Circuit_of_products control target h
    (determinantPhaseAngle U)
    (specialUnitaryAsUnitary factors.A)
    (specialUnitaryAsUnitary factors.B)
    (specialUnitaryAsUnitary factors.C)
    (specialUnitaryAsUnitary (specialUnitaryPart U)) U
  · exact factors.inactive
  · simpa only [coe_specialUnitaryAsUnitary] using factors.active
  · exact (phaseShift_mul_specialUnitaryPart U).symm

/-! ## Literal optimizer-visible resources -/

/-- The transparent schedule contains six visible nodes. -/
@[simp]
theorem canonicalSelectedControlledU2FusionCircuit_gateCount {n : ℕ}
    (control target : Fin n) (h : control ≠ target)
    (U : QubitUnitary) :
    FusionCircuit.gateCount
      (canonicalSelectedControlledU2FusionCircuit control target h U) = 6 := by
  rfl

/-- Four nodes carry explicit one-qubit payloads. -/
@[simp]
theorem canonicalSelectedControlledU2FusionCircuit_oneQubitCount {n : ℕ}
    (control target : Fin n) (h : control ≠ target)
    (U : QubitUnitary) :
    FusionCircuit.oneQubitCount
      (canonicalSelectedControlledU2FusionCircuit control target h U) = 4 := by
  simp [canonicalSelectedControlledU2FusionCircuit,
    FusionCircuit.oneQubitCount, FusionCircuit.kindCount,
    FusionPrimitive.kind]

/-- Two literal CNOT nodes separate the selected target factors. -/
@[simp]
theorem canonicalSelectedControlledU2FusionCircuit_cnotCount {n : ℕ}
    (control target : Fin n) (h : control ≠ target)
    (U : QubitUnitary) :
    FusionCircuit.cnotCount
      (canonicalSelectedControlledU2FusionCircuit control target h U) = 2 := by
  simp [canonicalSelectedControlledU2FusionCircuit,
    FusionCircuit.cnotCount, FusionCircuit.kindCount,
    FusionPrimitive.kind]

/-- The schedule contains no generic `U(4)` fusion node before normalization. -/
@[simp]
theorem canonicalSelectedControlledU2FusionCircuit_twoQubitCount {n : ℕ}
    (control target : Fin n) (h : control ≠ target)
    (U : QubitUnitary) :
    FusionCircuit.twoQubitCount
      (canonicalSelectedControlledU2FusionCircuit control target h U) = 0 := by
  simp [canonicalSelectedControlledU2FusionCircuit,
    FusionCircuit.twoQubitCount, FusionCircuit.kindCount,
    FusionPrimitive.kind]

/-- The exact literal profile is four one-qubit nodes, two CNOTs, six total. -/
theorem canonicalSelectedControlledU2FusionCircuit_profile {n : ℕ}
    (control target : Fin n) (h : control ≠ target)
    (U : QubitUnitary) :
    FusionCircuit.oneQubitCount
        (canonicalSelectedControlledU2FusionCircuit control target h U) = 4 ∧
      FusionCircuit.cnotCount
        (canonicalSelectedControlledU2FusionCircuit control target h U) = 2 ∧
      FusionCircuit.gateCount
        (canonicalSelectedControlledU2FusionCircuit control target h U) = 6 := by
  simp

/-- The Sections 3--7 model accepts the literal schedule at exact cost six. -/
@[simp]
theorem canonicalSelectedControlledU2FusionCircuit_oneQubitCNOTCost {n : ℕ}
    (control target : Fin n) (h : control ≠ target)
    (U : QubitUnitary) :
    FusionCircuit.cost CostModel.oneQubitCNOT
      (canonicalSelectedControlledU2FusionCircuit control target h U) = some 6 := by
  rw [FusionCircuit.oneQubitCNOT_cost_eq]
  simp

/-- Section 8 also charges the six pre-normalization visible nodes. -/
@[simp]
theorem canonicalSelectedControlledU2FusionCircuit_arbitraryTwoQubitCost {n : ℕ}
    (control target : Fin n) (h : control ≠ target)
    (U : QubitUnitary) :
    FusionCircuit.cost CostModel.arbitraryTwoQubit
      (canonicalSelectedControlledU2FusionCircuit control target h U) = some 6 := by
  rw [FusionCircuit.arbitraryTwoQubit_cost_eq_gateCount]
  simp

/-- The lowered trusted syntax retains the same exact early-model cost. -/
@[simp]
theorem lower_canonicalSelectedControlledU2FusionCircuit_oneQubitCNOTCost
    {n : ℕ} (control target : Fin n) (h : control ≠ target)
    (U : QubitUnitary) :
    Circuit.cost CostModel.oneQubitCNOT
      (canonicalSelectedControlledU2FusionCircuit control target h U).lower =
        some 6 := by
  rw [FusionCircuit.cost_lower]
  exact canonicalSelectedControlledU2FusionCircuit_oneQubitCNOTCost
    control target h U

end


end Barenco.ControlledCircuit
