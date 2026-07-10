import Barenco.OneQubit.SelectedABC
import Barenco.Optimization.FusionResources
import Barenco.ThreeQubit.Expansion

/-!
# Transparent fusion syntax for the sixteen-node double-control expansion

This module retains every local factor in Barenco Corollary 6.2 as optimizer-
visible one-qubit/CNOT syntax.  One square root and one checked A/B/C factor
package are selected for the target unitary, then reused throughout the complete
chronology.  In contrast to the older whole-circuit choice wrapper, downstream
normalizers can inspect every boundary payload.

The circuit list is chronological.  Its exact full-register evaluator is the
double-controlled target unitary; no scalar or basis-dependent phase is erased.
-/

namespace Barenco.ThreeQubit

open Barenco.OneQubit
open Barenco.ControlledCircuit
open Barenco.Optimization

noncomputable section

/--
One coherent, transparent sixteen-node Corollary 6.2 expansion of a
double-controlled one-qubit unitary.

The ordered roles `first` and `second` affect the literal factor schedule and
CNOT directions, even though the semantic two-control set is unordered.
-/
def selectedDoubleControlledExpansion16FusionCircuit {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (U : QubitUnitary) : FusionCircuit n :=
  let V := unitarySquareRoot U
  let factors := selectedColumnABCFactors (specialUnitaryPart V)
  let P2 : FusionPrimitive n :=
    .oneQubit second (controlPhaseUnitary (determinantPhaseAngle V))
  let Af : FusionPrimitive n :=
    .oneQubit target (specialUnitaryAsUnitary factors.A)
  let Bf : FusionPrimitive n :=
    .oneQubit target (specialUnitaryAsUnitary factors.B)
  let Cf : FusionPrimitive n :=
    .oneQubit target (specialUnitaryAsUnitary factors.C)
  let X2t : FusionPrimitive n := .cnot second target hsecondTarget
  let X12 : FusionPrimitive n := .cnot first second hfirstSecond
  let P1 : FusionPrimitive n :=
    .oneQubit first (controlPhaseUnitary (determinantPhaseAngle V))
  let X1t : FusionPrimitive n := .cnot first target hfirstTarget
  [P2, Af, X2t, Bf, X2t, X12,
    X2t.adjoint, Bf.adjoint, X2t.adjoint, P2.adjoint,
    X12, P1, X1t, Bf, X1t, Cf]

/--
Trusted lowering is exactly the established oriented sixteen-node chronology.
-/
@[simp]
theorem lower_selectedDoubleControlledExpansion16FusionCircuit {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (U : QubitUnitary) :
    (selectedDoubleControlledExpansion16FusionCircuit first second target
      hfirstSecond hfirstTarget hsecondTarget U).lower =
      let V := unitarySquareRoot U
      let factors := selectedColumnABCFactors (specialUnitaryPart V)
      doubleControlledExpansion16Circuit first second target hfirstSecond
        hfirstTarget hsecondTarget (determinantPhaseAngle V)
        (specialUnitaryAsUnitary factors.A)
        (specialUnitaryAsUnitary factors.B)
        (specialUnitaryAsUnitary factors.C) := by
  simp only [selectedDoubleControlledExpansion16FusionCircuit,
    doubleControlledExpansion16Circuit, FusionCircuit.lower,
    List.map_cons, List.map_nil]
  simp only [FusionPrimitive.lower_adjoint]
  rfl

/-- Exact arbitrary-register semantics of the transparent selected expansion. -/
@[simp]
theorem eval_selectedDoubleControlledExpansion16FusionCircuit {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (U : QubitUnitary) :
    (selectedDoubleControlledExpansion16FusionCircuit first second target
      hfirstSecond hfirstTarget hsecondTarget U).eval =
      positiveControlledUnitary target
        (twoControlSet first second target hfirstTarget hsecondTarget) U := by
  let V := unitarySquareRoot U
  let factors := selectedColumnABCFactors (specialUnitaryPart V)
  rw [← FusionCircuit.eval_lower,
    lower_selectedDoubleControlledExpansion16FusionCircuit]
  apply eval_doubleControlledExpansion16Circuit_of_products first second target
    hfirstSecond hfirstTarget hsecondTarget (determinantPhaseAngle V)
    (specialUnitaryAsUnitary factors.A)
    (specialUnitaryAsUnitary factors.B)
    (specialUnitaryAsUnitary factors.C)
    (specialUnitaryAsUnitary (specialUnitaryPart V)) V U
  · exact factors.inactive
  · simpa only [coe_specialUnitaryAsUnitary] using factors.active
  · exact (phaseShift_mul_specialUnitaryPart V).symm
  · exact unitarySquareRoot_pow_two U

/-! ## Literal syntax resources -/

@[simp]
theorem selectedDoubleControlledExpansion16FusionCircuit_oneQubitCount {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (U : QubitUnitary) :
    FusionCircuit.oneQubitCount
        (selectedDoubleControlledExpansion16FusionCircuit first second target
          hfirstSecond hfirstTarget hsecondTarget U) = 8 := by
  simp [selectedDoubleControlledExpansion16FusionCircuit,
    FusionCircuit.oneQubitCount, FusionCircuit.kindCount,
    FusionPrimitive.kind, FusionPrimitive.adjoint]

@[simp]
theorem selectedDoubleControlledExpansion16FusionCircuit_cnotCount {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (U : QubitUnitary) :
    FusionCircuit.cnotCount
        (selectedDoubleControlledExpansion16FusionCircuit first second target
          hfirstSecond hfirstTarget hsecondTarget U) = 8 := by
  simp [selectedDoubleControlledExpansion16FusionCircuit,
    FusionCircuit.cnotCount, FusionCircuit.kindCount,
    FusionPrimitive.kind, FusionPrimitive.adjoint]

@[simp]
theorem selectedDoubleControlledExpansion16FusionCircuit_twoQubitCount {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (U : QubitUnitary) :
    FusionCircuit.twoQubitCount
        (selectedDoubleControlledExpansion16FusionCircuit first second target
          hfirstSecond hfirstTarget hsecondTarget U) = 0 := by
  simp [selectedDoubleControlledExpansion16FusionCircuit,
    FusionCircuit.twoQubitCount, FusionCircuit.kindCount,
    FusionPrimitive.kind, FusionPrimitive.adjoint]

@[simp]
theorem selectedDoubleControlledExpansion16FusionCircuit_gateCount {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (U : QubitUnitary) :
    FusionCircuit.gateCount
        (selectedDoubleControlledExpansion16FusionCircuit first second target
          hfirstSecond hfirstTarget hsecondTarget U) = 16 := by
  simp [selectedDoubleControlledExpansion16FusionCircuit,
    FusionCircuit.gateCount]

@[simp]
theorem selectedDoubleControlledExpansion16FusionCircuit_oneQubitCNOTCost {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (U : QubitUnitary) :
    FusionCircuit.cost CostModel.oneQubitCNOT
        (selectedDoubleControlledExpansion16FusionCircuit first second target
          hfirstSecond hfirstTarget hsecondTarget U) = some 16 := by
  rw [FusionCircuit.oneQubitCNOT_cost_eq]
  simp

@[simp]
theorem selectedDoubleControlledExpansion16FusionCircuit_arbitraryTwoQubitCost
    {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (U : QubitUnitary) :
    FusionCircuit.cost CostModel.arbitraryTwoQubit
        (selectedDoubleControlledExpansion16FusionCircuit first second target
          hfirstSecond hfirstTarget hsecondTarget U) = some 16 := by
  rw [FusionCircuit.arbitraryTwoQubit_cost_eq_gateCount]
  simp

end

end Barenco.ThreeQubit
