import Barenco.MultiControl.RecursiveExpansion
import Mathlib.Data.Fin.Embedding

/-!
# Literal synthesis of a fully controlled one-qubit gate

This module packages the Sections 5--7 constructions behind one dispatcher for
a positive-width register.  For `controlCount + 1` wires, `fullControlLayout`
uses every wire other than the selected target, in the canonical order supplied
by `Fin.succAbove`.

The returned syntax contains only literal one-qubit and CNOT primitives:

* zero controls use `zeroControlCircuit`;
* one through five controls use `expandedGrayControlledCircuit`;
* six or more controls use `recursivePrimitiveCircuit`.

The accepted-cost theorem is syntax-derived.  It is not inferred from the
semantic equality.
-/

namespace Barenco.Universality

noncomputable section

open Barenco.MultiControl
open Barenco.MultiControl.OrderedControlLayout

/-! ## Canonical all-other-wires layout -/

/--
The canonical layout whose controls are all wires other than `target`.

`target.succAbove` lists the wires in increasing order while skipping the
target, so the layout contains exactly `controlCount` controls in ambient width
`controlCount + 1`.
-/
def fullControlLayout {controlCount : ℕ}
    (target : Fin (controlCount + 1)) :
    OrderedControlLayout controlCount (controlCount + 1) where
  controlWire := target.succAboveEmb
  targetWire := target
  control_ne_target := target.succAbove_ne

@[simp]
theorem fullControlLayout_targetWire {controlCount : ℕ}
    (target : Fin (controlCount + 1)) :
    (fullControlLayout target).targetWire = target := rfl

@[simp]
theorem fullControlLayout_controlWire {controlCount : ℕ}
    (target : Fin (controlCount + 1)) (control : Fin controlCount) :
    (fullControlLayout target).controlWire control = target.succAbove control := rfl

theorem fullControlLayout_controlComplementEmbedding {controlCount : ℕ}
    (target : Fin (controlCount + 1)) :
    (fullControlLayout target).controlComplementEmbedding =
      (finSuccAboveEquiv target).toEmbedding := by
  ext control
  rfl

/-- The canonical layout's unordered control set is the full target complement. -/
@[simp]
theorem fullControlLayout_controlSet {controlCount : ℕ}
    (target : Fin (controlCount + 1)) :
    (fullControlLayout target).controlSet = Finset.univ := by
  rw [OrderedControlLayout.controlSet,
    fullControlLayout_controlComplementEmbedding]
  exact Finset.map_univ_equiv (finSuccAboveEquiv target)

/-! ## Width-sensitive primitive dispatcher -/

/--
A literal one-qubit/CNOT implementation of the gate controlled by every wire
other than `target`.

The final pattern is `depth + 6`, matching the indexing convention of
`recursivePrimitiveCircuit`.
-/
def fullControlCircuit :
    (controlCount : ℕ) → Fin (controlCount + 1) → QubitUnitary →
      Circuit (controlCount + 1)
  | 0, target, U => zeroControlCircuit target U
  | 1, target, U =>
      expandedGrayControlledCircuit (tail := 0) (fullControlLayout target) U
  | 2, target, U =>
      expandedGrayControlledCircuit (tail := 1) (fullControlLayout target) U
  | 3, target, U =>
      expandedGrayControlledCircuit (tail := 2) (fullControlLayout target) U
  | 4, target, U =>
      expandedGrayControlledCircuit (tail := 3) (fullControlLayout target) U
  | 5, target, U =>
      expandedGrayControlledCircuit (tail := 4) (fullControlLayout target) U
  | depth + 6, target, U =>
      recursivePrimitiveCircuit depth (fullControlLayout target) U

/-- Exact semantics before forgetting the ordered-layout presentation. -/
theorem eval_fullControlCircuit_layout :
    ∀ (controlCount : ℕ) (target : Fin (controlCount + 1))
      (U : QubitUnitary),
      Circuit.eval (fullControlCircuit controlCount target U) =
        positiveControlledUnitary target
          (fullControlLayout target).controlSet U
  | 0, target, U => by
      simp [fullControlCircuit, fullControlLayout,
        OrderedControlLayout.controlSet,
        OrderedControlLayout.controlComplementEmbedding]
  | 1, target, U => by
      simp [fullControlCircuit]
  | 2, target, U => by
      simp [fullControlCircuit]
  | 3, target, U => by
      simp [fullControlCircuit]
  | 4, target, U => by
      simp [fullControlCircuit]
  | 5, target, U => by
      simp [fullControlCircuit]
  | depth + 6, target, U => by
      simp [fullControlCircuit]

/--
The dispatcher exactly implements the positive controlled gate whose controls
are all wires other than the target.
-/
@[simp]
theorem eval_fullControlCircuit (controlCount : ℕ)
    (target : Fin (controlCount + 1)) (U : QubitUnitary) :
    Circuit.eval (fullControlCircuit controlCount target U) =
      positiveControlledUnitary target Finset.univ U := by
  rw [eval_fullControlCircuit_layout, fullControlLayout_controlSet]
  rfl

/-! ## Accepted literal-syntax cost -/

/-- Exact one-qubit/CNOT cost of the selected implementation family. -/
def fullControlCircuitCost : ℕ → ℕ
  | 0 => 1
  | 1 => 6
  | 2 => 20
  | 3 => 48
  | 4 => 104
  | 5 => 216
  | depth + 6 => 56 * depth ^ 2 + 364 * depth + 440

/--
The full-control dispatcher is accepted by the one-qubit+CNOT cost model.
Consequently no controlled, Toffoli, arbitrary-two-qubit, or unclassified macro
remains in its final syntax.
-/
@[simp]
theorem fullControlCircuit_oneQubitCNOTCost :
    ∀ (controlCount : ℕ) (target : Fin (controlCount + 1))
      (U : QubitUnitary),
      Circuit.cost CostModel.oneQubitCNOT
          (fullControlCircuit controlCount target U) =
        some (fullControlCircuitCost controlCount)
  | 0, target, U => by
      simp [fullControlCircuit, fullControlCircuitCost]
  | 1, target, U => by
      simp [fullControlCircuit, fullControlCircuitCost]
  | 2, target, U => by
      simp [fullControlCircuit, fullControlCircuitCost]
  | 3, target, U => by
      simp [fullControlCircuit, fullControlCircuitCost]
  | 4, target, U => by
      simp [fullControlCircuit, fullControlCircuitCost]
  | 5, target, U => by
      simp [fullControlCircuit, fullControlCircuitCost]
  | depth + 6, target, U => by
      simp [fullControlCircuit, fullControlCircuitCost]

/-- Existential accepted-cost form for clients that do not need the closed count. -/
theorem exists_fullControlCircuit_oneQubitCNOTCost (controlCount : ℕ)
    (target : Fin (controlCount + 1)) (U : QubitUnitary) :
    ∃ cost, Circuit.cost CostModel.oneQubitCNOT
      (fullControlCircuit controlCount target U) = some cost :=
  ⟨fullControlCircuitCost controlCount,
    fullControlCircuit_oneQubitCNOTCost controlCount target U⟩

end

end Barenco.Universality
