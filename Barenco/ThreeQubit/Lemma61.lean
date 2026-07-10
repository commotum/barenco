import Barenco.ControlledCircuit.Phase
import Barenco.OneQubit.Roots
import Barenco.Cost

/-!
# Barenco Lemma 6.1: a doubly controlled one-qubit gate

This file reconstructs the five-node macro circuit from Barenco et al., Lemma
6.1 on three named, pairwise distinct wires in an arbitrary ambient register.
The circuit list is chronological:

`C₂(V); CNOT(1,2); C₂(V⁻¹); CNOT(1,2); C₁(V)`.

Here `Cᵢ` controls the final target from control wire `i`; the two CNOTs act
from the first control onto the second.  They restore the second wire exactly.
The selected-root wrapper uses the finite-unitary square root from Stage 4.

The controlled nodes in this file are deliberate macros.  Their five-node
structural count is not a one-qubit+CNOT cost; Corollary 6.2 requires a separate
explicit expansion.
-/

namespace Barenco.ThreeQubit

open Barenco.OneQubit

noncomputable section

/-- The unordered pair of positive controls used by a doubly controlled gate. -/
def twoControlSet {n : ℕ} (first second target : Fin n)
    (hfirst : first ≠ target) (hsecond : second ≠ target) : ControlSet target :=
  {⟨first, hfirst⟩, ⟨second, hsecond⟩}

/--
The chronological five-node macro circuit displayed in Lemma 6.1.

The inverse is the certified unitary-group inverse of the same `V`; it is not an
independently chosen witness.
-/
def doubleControlledViaSquareCircuit {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (V : QubitUnitary) : Circuit n :=
  [Primitive.positiveControlled target
      ({⟨second, hsecondTarget⟩} : ControlSet target) V,
    Primitive.cnot first second hfirstSecond,
    Primitive.positiveControlled target
      ({⟨second, hsecondTarget⟩} : ControlSet target) V⁻¹,
    Primitive.cnot first second hfirstSecond,
    Primitive.positiveControlled target
      ({⟨first, hfirstTarget⟩} : ControlSet target) V]

/-- Lemma 6.1 specialized to the selected exact square root of `U`. -/
def doubleControlledRootCircuit {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (U : QubitUnitary) : Circuit n :=
  doubleControlledViaSquareCircuit first second target hfirstSecond
    hfirstTarget hsecondTarget (unitarySquareRoot U)

/-! ## Macro-level structural resources -/

@[simp]
theorem doubleControlledViaSquareCircuit_gateCount {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (V : QubitUnitary) :
    Circuit.gateCount
      (doubleControlledViaSquareCircuit first second target hfirstSecond
        hfirstTarget hsecondTarget V) = 5 := by
  rfl

@[simp]
theorem doubleControlledViaSquareCircuit_cnotCount {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (V : QubitUnitary) :
    Circuit.kindCount .cnot
      (doubleControlledViaSquareCircuit first second target hfirstSecond
        hfirstTarget hsecondTarget V) = 2 := by
  simp [doubleControlledViaSquareCircuit, Circuit.kindCount]

@[simp]
theorem doubleControlledViaSquareCircuit_controlledCount {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (V : QubitUnitary) :
    Circuit.kindCount (.controlledOneQubit 1)
      (doubleControlledViaSquareCircuit first second target hfirstSecond
        hfirstTarget hsecondTarget V) = 3 := by
  simp [doubleControlledViaSquareCircuit, Circuit.kindCount]

@[simp]
theorem doubleControlledViaSquareCircuit_oneQubitCount {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (V : QubitUnitary) :
    Circuit.kindCount .oneQubit
      (doubleControlledViaSquareCircuit first second target hfirstSecond
        hfirstTarget hsecondTarget V) = 0 := by
  simp [doubleControlledViaSquareCircuit, Circuit.kindCount]

/-- The Section 3–7 basic-gate model rejects the unexpanded controlled macros. -/
@[simp]
theorem doubleControlledViaSquareCircuit_oneQubitCNOTCost {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (V : QubitUnitary) :
    Circuit.cost CostModel.oneQubitCNOT
      (doubleControlledViaSquareCircuit first second target hfirstSecond
        hfirstTarget hsecondTarget V) = none := by
  simp [doubleControlledViaSquareCircuit, Circuit.cost, Circuit.addCost]

end

end Barenco.ThreeQubit
