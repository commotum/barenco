import Barenco.ThreeQubit.Lemma61

/-!
# Barenco Corollary 6.2: sixteen one-qubit/CNOT primitives

This file expands the three controlled-one-qubit macros in Lemma 6.1 using one
shared Corollary 5.3 decomposition.  The direct expansion has twenty primitives:
twelve one-qubit gates and eight CNOTs.  The middle implementation is the exact
adjoint of the first, so two inverse pairs can be commuted across operations on
disjoint wires and cancelled.  The resulting named syntax has exactly sixteen
primitives: eight one-qubit gates and eight CNOTs.

The source calls the cancelled gates adjacent. In chronological list syntax they
are not literally adjacent; their separation by control-only operations is why
the disjoint-wire commutation theorems from `Lemma61` are required.
-/

namespace Barenco.ThreeQubit

open Barenco.OneQubit
open Barenco.ControlledCircuit

noncomputable section

/--
The unmerged twenty-node expansion
`S(second); K; S(second)†; K; S(first)`.

Here `S(control)` is the six-node Corollary 5.3 circuit and `K` is CNOT from the
first control to the second. The same parameters are deliberately reused at both
controls, and the middle circuit is their exact syntactic adjoint.
-/
def doubleControlledExpansion20Circuit {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (delta : ℝ) (A B C : QubitUnitary) : Circuit n :=
  Circuit.append
    (controlledU2Circuit second target hsecondTarget delta A B C)
    (Circuit.append [Primitive.cnot first second hfirstSecond]
      (Circuit.append
        (Circuit.adjoint
          (controlledU2Circuit second target hsecondTarget delta A B C))
        (Circuit.append [Primitive.cnot first second hfirstSecond]
          (controlledU2Circuit first target hfirstTarget delta A B C))))

/--
The explicit sixteen-node circuit after the paper's two inverse-pair
cancellations.
-/
def doubleControlledExpansion16Circuit {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (delta : ℝ) (A B C : QubitUnitary) : Circuit n :=
  [Primitive.oneQubit second (controlPhaseUnitary delta),
    Primitive.oneQubit target A,
    Primitive.cnot second target hsecondTarget,
    Primitive.oneQubit target B,
    Primitive.cnot second target hsecondTarget,
    Primitive.cnot first second hfirstSecond,
    (Primitive.cnot second target hsecondTarget).adjoint,
    (Primitive.oneQubit target B).adjoint,
    (Primitive.cnot second target hsecondTarget).adjoint,
    (Primitive.oneQubit second (controlPhaseUnitary delta)).adjoint,
    Primitive.cnot first second hfirstSecond,
    Primitive.oneQubit first (controlPhaseUnitary delta),
    Primitive.cnot first target hfirstTarget,
    Primitive.oneQubit target B,
    Primitive.cnot first target hfirstTarget,
    Primitive.oneQubit target C]

/-! ## Structural resources -/

@[simp]
theorem doubleControlledExpansion20Circuit_gateCount {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (delta : ℝ) (A B C : QubitUnitary) :
  Circuit.gateCount
      (doubleControlledExpansion20Circuit first second target hfirstSecond
        hfirstTarget hsecondTarget delta A B C) = 20 := by
  rfl

@[simp]
theorem doubleControlledExpansion20Circuit_kindCounts {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (delta : ℝ) (A B C : QubitUnitary) :
    Circuit.kindCount .oneQubit
        (doubleControlledExpansion20Circuit first second target hfirstSecond
          hfirstTarget hsecondTarget delta A B C) = 12 ∧
      Circuit.kindCount .cnot
        (doubleControlledExpansion20Circuit first second target hfirstSecond
          hfirstTarget hsecondTarget delta A B C) = 8 := by
  constructor <;> rfl

@[simp]
theorem doubleControlledExpansion20Circuit_oneQubitCNOTCost {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (delta : ℝ) (A B C : QubitUnitary) :
    Circuit.cost CostModel.oneQubitCNOT
      (doubleControlledExpansion20Circuit first second target hfirstSecond
        hfirstTarget hsecondTarget delta A B C) = some 20 := by
  simp [doubleControlledExpansion20Circuit, Circuit.cost_append,
    Circuit.cost, Circuit.addCost]

@[simp]
theorem doubleControlledExpansion16Circuit_gateCount {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (delta : ℝ) (A B C : QubitUnitary) :
    Circuit.gateCount
      (doubleControlledExpansion16Circuit first second target hfirstSecond
        hfirstTarget hsecondTarget delta A B C) = 16 := by
  rfl

@[simp]
theorem doubleControlledExpansion16Circuit_kindCounts {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (delta : ℝ) (A B C : QubitUnitary) :
    Circuit.kindCount .oneQubit
        (doubleControlledExpansion16Circuit first second target hfirstSecond
          hfirstTarget hsecondTarget delta A B C) = 8 ∧
      Circuit.kindCount .cnot
        (doubleControlledExpansion16Circuit first second target hfirstSecond
          hfirstTarget hsecondTarget delta A B C) = 8 := by
  simp [doubleControlledExpansion16Circuit, Circuit.kindCount]

@[simp]
theorem doubleControlledExpansion16Circuit_oneQubitCNOTCost {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (delta : ℝ) (A B C : QubitUnitary) :
    Circuit.cost CostModel.oneQubitCNOT
      (doubleControlledExpansion16Circuit first second target hfirstSecond
        hfirstTarget hsecondTarget delta A B C) = some 16 := by
  simp [doubleControlledExpansion16Circuit, Circuit.cost, Circuit.addCost]

end

end Barenco.ThreeQubit
