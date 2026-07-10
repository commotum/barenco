import Barenco.MultiControl.Lemma71

/-!
# Section 8 basic-operation costs for verified macro circuits

Section 8 changes the paper's basic-operation convention: every operation on
at most two qubits costs one.  Under `CostModel.arbitraryTwoQubit`, a
`.controlledOneQubit controls` node is therefore basic exactly when
`controls ≤ 1`.

This file prices two circuits whose literal syntax and full-register semantics
were proved earlier: the five-node circuit of Lemma 6.1 and the displayed
thirteen-node instance of Lemma 7.1.  The results below are syntax-derived;
they do not infer costs from semantic matrix equalities.

The paper's separate three-operation relative-phase construction is not priced
here.  Establishing that claim requires a literal three-node circuit whose
merged operations are certified to act on at most two wires.
-/

namespace Barenco.ThreeQubit

noncomputable section

/-- The five literal nodes of Lemma 6.1 are all Section 8 basic operations. -/
@[simp]
theorem doubleControlledViaSquareCircuit_arbitraryTwoQubitCost {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (V : QubitUnitary) :
    Circuit.cost CostModel.arbitraryTwoQubit
        (doubleControlledViaSquareCircuit first second target hfirstSecond
          hfirstTarget hsecondTarget V) = some 5 := by
  simp [doubleControlledViaSquareCircuit, Circuit.cost, Circuit.addCost]

/-- The selected-square-root form of Lemma 6.1 has the same exact cost five. -/
@[simp]
theorem doubleControlledRootCircuit_arbitraryTwoQubitCost {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (U : QubitUnitary) :
    Circuit.cost CostModel.arbitraryTwoQubit
        (doubleControlledRootCircuit first second target hfirstSecond
          hfirstTarget hsecondTarget U) = some 5 := by
  simp [doubleControlledRootCircuit]

end

end Barenco.ThreeQubit

namespace Barenco.MultiControl

noncomputable section

/--
The displayed Lemma 7.1 circuit has seven singly controlled target gates and
six CNOTs, hence exact Section 8 cost thirteen.
-/
@[simp]
theorem fourBitGrayCircuit_arbitraryTwoQubitCost {ambientWidth : ℕ}
    (layout : OrderedControlLayout 3 ambientWidth) (V : QubitUnitary) :
    Circuit.cost CostModel.arbitraryTwoQubit
        (fourBitGrayCircuit layout V) = some 13 := by
  simp [fourBitGrayCircuit, Circuit.cost, Circuit.addCost]

end

end Barenco.MultiControl
