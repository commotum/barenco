import Barenco.MultiControl.LastTargetSwap
import Barenco.MultiControl.LinearSpecialUnitary
import Barenco.ControlledCircuit.SelectedSpecial

/-!
# Primitive expansion of the linear fully controlled SU(2) construction

This leaf expands every macro in Barenco Lemma 7.9.  Each of the three
final-control SU(2) gates uses its selected five-node Lemma 5.1 circuit, while
each prefix-controlled target X uses the literal corrected Corollary 7.4
expansion from `LastTargetSwap`.

The construction is valid in an arbitrary ambient register.  Its resource
formulas depend on the logical width `p + 2` (the `p + 1` controls and target),
never on the number of ambient spectator wires.
-/

namespace Barenco.MultiControl

open Barenco.OneQubit
open Barenco.ControlledCircuit

noncomputable section

namespace OrderedControlLayout

/-! ## Five-way primitive substitution -/

/--
Expand the five chronological Lemma 7.9 macros for explicitly supplied
special-unitary factors `A`, `B`, and `C`.
-/
def expandedLinearABCCircuit {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) (A B C : QubitSpecialUnitary) : Circuit ambientWidth :=
  Circuit.append
    (selectedControlledSU2Circuit layout.lastControlWire layout.targetWire
      layout.lastControlWire_ne_targetWire A)
    (Circuit.append
      (layout.expandedPrefixTargetXCircuit hwidth)
      (Circuit.append
        (selectedControlledSU2Circuit layout.lastControlWire layout.targetWire
          layout.lastControlWire_ne_targetWire B)
        (Circuit.append
          (layout.expandedPrefixTargetXCircuit hwidth)
          (selectedControlledSU2Circuit layout.lastControlWire layout.targetWire
            layout.lastControlWire_ne_targetWire C))))

/-- Every supplied primitive component preserves its corresponding macro evaluator. -/
@[simp]
theorem eval_expandedLinearABCCircuit {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) (A B C : QubitSpecialUnitary) :
    Circuit.eval (layout.expandedLinearABCCircuit hwidth A B C) =
      Circuit.eval (layout.linearABCCircuit
        (specialUnitaryAsUnitary A) (specialUnitaryAsUnitary B)
        (specialUnitaryAsUnitary C)) := by
  simp [expandedLinearABCCircuit, linearABCCircuit, Circuit.eval_append,
    lastControlledTarget]

/-! ## Selected Lemma 7.9 wrapper -/

/-- Fully primitive Lemma 7.9 circuit using one selected outer ABC factorization. -/
def expandedLinearSU2Circuit {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) (W : QubitSpecialUnitary) : Circuit ambientWidth :=
  let factors := selectedColumnABCFactors W
  layout.expandedLinearABCCircuit hwidth factors.A factors.B factors.C

/-- Primitive expansion preserves the exact selected five-macro evaluator. -/
@[simp]
theorem eval_expandedLinearSU2Circuit_eq_linear {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) (W : QubitSpecialUnitary) :
    Circuit.eval (layout.expandedLinearSU2Circuit hwidth W) =
      Circuit.eval (layout.linearSU2Circuit W) := by
  simp [expandedLinearSU2Circuit, linearSU2Circuit]

/-- Exact fully controlled special-unitary semantics on the complete ambient register. -/
@[simp]
theorem eval_expandedLinearSU2Circuit {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) (W : QubitSpecialUnitary) :
    Circuit.eval (layout.expandedLinearSU2Circuit hwidth W) =
      positiveControlledUnitary layout.targetWire layout.controlSet
        (specialUnitaryAsUnitary W) := by
  rw [eval_expandedLinearSU2Circuit_eq_linear, eval_linearSU2Circuit]

/-! ## Exact primitive resources -/

@[simp]
theorem expandedLinearABCCircuit_oneQubitCount {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) (A B C : QubitSpecialUnitary) :
    Circuit.kindCount .oneQubit
        (layout.expandedLinearABCCircuit hwidth A B C) = 64 * p - 151 := by
  simp [expandedLinearABCCircuit, Circuit.kindCount_append]
  omega

@[simp]
theorem expandedLinearABCCircuit_cnotCount {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) (A B C : QubitSpecialUnitary) :
    Circuit.kindCount .cnot
        (layout.expandedLinearABCCircuit hwidth A B C) = 48 * p - 98 := by
  simp [expandedLinearABCCircuit, Circuit.kindCount_append]
  omega

@[simp]
theorem expandedLinearABCCircuit_gateCount {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) (A B C : QubitSpecialUnitary) :
    Circuit.gateCount (layout.expandedLinearABCCircuit hwidth A B C) =
      112 * p - 249 := by
  simp [expandedLinearABCCircuit, Circuit.gateCount_append]
  omega

@[simp]
theorem expandedLinearABCCircuit_oneQubitCNOTCost {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) (A B C : QubitSpecialUnitary) :
    Circuit.cost CostModel.oneQubitCNOT
        (layout.expandedLinearABCCircuit hwidth A B C) =
      some (112 * p - 249) := by
  simp [expandedLinearABCCircuit, Circuit.cost_append, Circuit.addCost]
  have hmcx : 56 * p - 132 + 132 = 56 * p := by
    exact Nat.sub_add_cancel (by omega)
  have htotal : 112 * p - 249 + 249 = 112 * p := by
    exact Nat.sub_add_cancel (by omega)
  omega

@[simp]
theorem expandedLinearSU2Circuit_oneQubitCount {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) (W : QubitSpecialUnitary) :
    Circuit.kindCount .oneQubit
        (layout.expandedLinearSU2Circuit hwidth W) = 64 * p - 151 := by
  simp [expandedLinearSU2Circuit]

@[simp]
theorem expandedLinearSU2Circuit_cnotCount {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) (W : QubitSpecialUnitary) :
    Circuit.kindCount .cnot (layout.expandedLinearSU2Circuit hwidth W) =
      48 * p - 98 := by
  simp [expandedLinearSU2Circuit]

@[simp]
theorem expandedLinearSU2Circuit_gateCount {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) (W : QubitSpecialUnitary) :
    Circuit.gateCount (layout.expandedLinearSU2Circuit hwidth W) =
      112 * p - 249 := by
  simp [expandedLinearSU2Circuit]

@[simp]
theorem expandedLinearSU2Circuit_oneQubitCNOTCost {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) (W : QubitSpecialUnitary) :
    Circuit.cost CostModel.oneQubitCNOT
        (layout.expandedLinearSU2Circuit hwidth W) =
      some (112 * p - 249) := by
  simp [expandedLinearSU2Circuit]

/-! ## Logical-width forms -/

/-- One-qubit count expressed in the logical width `p + 2`. -/
theorem expandedLinearSU2Circuit_oneQubitCount_logicalWidth
    {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) (W : QubitSpecialUnitary) :
    Circuit.kindCount .oneQubit
        (layout.expandedLinearSU2Circuit hwidth W) =
      64 * (p + 2) - 279 := by
  rw [expandedLinearSU2Circuit_oneQubitCount]
  omega

/-- CNOT count expressed in the logical width `p + 2`. -/
theorem expandedLinearSU2Circuit_cnotCount_logicalWidth
    {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) (W : QubitSpecialUnitary) :
    Circuit.kindCount .cnot (layout.expandedLinearSU2Circuit hwidth W) =
      48 * (p + 2) - 194 := by
  rw [expandedLinearSU2Circuit_cnotCount]
  omega

/-- Total primitive count expressed in the logical width `p + 2`. -/
theorem expandedLinearSU2Circuit_gateCount_logicalWidth
    {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) (W : QubitSpecialUnitary) :
    Circuit.gateCount (layout.expandedLinearSU2Circuit hwidth W) =
      112 * (p + 2) - 473 := by
  rw [expandedLinearSU2Circuit_gateCount]
  omega

/-- Accepted early-basic cost expressed in the logical width `p + 2`. -/
theorem expandedLinearSU2Circuit_oneQubitCNOTCost_logicalWidth
    {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) (W : QubitSpecialUnitary) :
    Circuit.cost CostModel.oneQubitCNOT
        (layout.expandedLinearSU2Circuit hwidth W) =
      some (112 * (p + 2) - 473) := by
  rw [expandedLinearSU2Circuit_oneQubitCNOTCost]
  exact congrArg some (by omega)

/-! ## Smallest expanded width -/

/-- The width-seven primitive construction has exact profile `(169, 142, 311)`. -/
theorem expandedLinearSU2Circuit_seven_resources {ambientWidth : ℕ}
    (layout : OrderedControlLayout 6 ambientWidth) (W : QubitSpecialUnitary) :
    Circuit.kindCount .oneQubit
        (layout.expandedLinearSU2Circuit (p := 5) (by omega) W) = 169 ∧
      Circuit.kindCount .cnot
          (layout.expandedLinearSU2Circuit (p := 5) (by omega) W) = 142 ∧
      Circuit.gateCount
          (layout.expandedLinearSU2Circuit (p := 5) (by omega) W) = 311 ∧
      Circuit.cost CostModel.oneQubitCNOT
          (layout.expandedLinearSU2Circuit (p := 5) (by omega) W) = some 311 := by
  norm_num

end OrderedControlLayout

end

end Barenco.MultiControl
