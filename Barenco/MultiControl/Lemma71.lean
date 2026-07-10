import Barenco.MultiControl.GrayAccumulator
import Barenco.MultiControl.Layout

/-!
# Gray-code circuit semantics for Lemma 7.1

This file begins the semantic bridge from the pure Boolean Gray accumulator to
certified arbitrary-width quantum circuits.  The first layer identifies the
ambient basis update of an embedded logical CNOT and proves that restricting it
back to the ordered controls is exactly `xorWireUpdate`.

The full interleaved controlled-root circuit and its evaluator are added only
after the generated Gray edge schedule has a general validity/restoration proof.
-/

namespace Barenco.MultiControl

open scoped Matrix

/-- Ambient computational-basis update of one logical-control CNOT. -/
def embeddedCNOTUpdate {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (control target : Fin controlCount) (input : Basis ambientWidth) :
    Basis ambientWidth :=
  if input (layout.controlWire control) then
    setTarget (layout.controlWire target) input (!input (layout.controlWire target))
  else input

/-- The certified embedded CNOT has exactly the stated ambient basis action. -/
theorem cnotPrimitive_mulVec_basisKet {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (control target : Fin controlCount) (h : control ≠ target)
    (input : Basis ambientWidth) :
    ((layout.cnotPrimitive control target h).denotation : Gate ambientWidth) *ᵥ
        basisKet input =
      basisKet (embeddedCNOTUpdate layout control target input) := by
  rw [OrderedControlLayout.cnotPrimitive, Primitive.cnot_denotation_val]
  simpa [embeddedCNOTUpdate] using
    cnotRaw_mulVec_basisKet (layout.controlWire control)
      (layout.controlWire target) (layout.controlWire_ne h) input

/-- Restricting an embedded logical CNOT is exactly the pure Boolean XOR update. -/
theorem restrictControls_embeddedCNOTUpdate {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (control target : Fin controlCount)
    (input : Basis ambientWidth) :
    layout.restrictControls (embeddedCNOTUpdate layout control target input) =
      xorWireUpdate control target (layout.restrictControls input) := by
  funext wire
  by_cases hwire : wire = target
  · subst wire
    cases hcontrol : input (layout.controlWire control) <;>
      cases htarget : input (layout.controlWire target) <;>
      simp [embeddedCNOTUpdate, OrderedControlLayout.restrictControls,
        xorWireUpdate, hcontrol, htarget] <;>
      decide
  · have hambient : layout.controlWire wire ≠ layout.controlWire target :=
      layout.controlWire_ne hwire
    cases hcontrol : input (layout.controlWire control) <;>
      simp [embeddedCNOTUpdate, OrderedControlLayout.restrictControls,
        xorWireUpdate, hcontrol, hwire, hambient]

/-- An embedded logical CNOT preserves every ambient wire other than its target. -/
theorem embeddedCNOTUpdate_apply_of_ne {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (control target : Fin controlCount) (input : Basis ambientWidth)
    (wire : Fin ambientWidth) (hwire : wire ≠ layout.controlWire target) :
    embeddedCNOTUpdate layout control target input wire = input wire := by
  cases hcontrol : input (layout.controlWire control) <;>
    simp [embeddedCNOTUpdate, hcontrol, hwire]

/-- In particular, an embedded control-to-control CNOT preserves the quantum target. -/
@[simp]
theorem embeddedCNOTUpdate_apply_targetWire {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (control target : Fin controlCount) (input : Basis ambientWidth) :
    embeddedCNOTUpdate layout control target input layout.targetWire =
      input layout.targetWire := by
  apply embeddedCNOTUpdate_apply_of_ne
  exact Ne.symm (layout.control_ne_target target)

/-- Execute a list of logical-control CNOT edges inside the ambient register. -/
def runEmbeddedCNOTUpdates {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (edges : List (Fin controlCount × Fin controlCount))
    (input : Basis ambientWidth) : Basis ambientWidth :=
  edges.foldl
    (fun current edge => embeddedCNOTUpdate layout edge.1 edge.2 current) input

@[simp]
theorem runEmbeddedCNOTUpdates_nil {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (input : Basis ambientWidth) :
    runEmbeddedCNOTUpdates layout [] input = input := rfl

/-- Restriction commutes exactly with executing any ordered logical CNOT edge list. -/
theorem restrictControls_runEmbeddedCNOTUpdates {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (edges : List (Fin controlCount × Fin controlCount))
    (input : Basis ambientWidth) :
    layout.restrictControls (runEmbeddedCNOTUpdates layout edges input) =
      runXorEdges edges (layout.restrictControls input) := by
  induction edges generalizing input with
  | nil => rfl
  | cons edge edges ih =>
      change layout.restrictControls
          (runEmbeddedCNOTUpdates layout edges
            (embeddedCNOTUpdate layout edge.1 edge.2 input)) =
        runXorEdges edges
          (xorWireUpdate edge.1 edge.2 (layout.restrictControls input))
      rw [ih, restrictControls_embeddedCNOTUpdate]

/-- Every control-to-control edge schedule preserves the separate quantum target wire. -/
@[simp]
theorem runEmbeddedCNOTUpdates_apply_targetWire {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (edges : List (Fin controlCount × Fin controlCount))
    (input : Basis ambientWidth) :
    runEmbeddedCNOTUpdates layout edges input layout.targetWire =
      input layout.targetWire := by
  induction edges generalizing input with
  | nil => rfl
  | cons edge edges ih =>
      change runEmbeddedCNOTUpdates layout edges
          (embeddedCNOTUpdate layout edge.1 edge.2 input) layout.targetWire = _
      rw [ih, embeddedCNOTUpdate_apply_targetWire]

/-- Chronological circuit obtained from an ordered list of proved-valid logical edges. -/
def cnotEdgeCircuit {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (edges : List (ControlEdge controlCount)) : Circuit ambientWidth :=
  edges.map layout.cnotEdgePrimitive

/-- Forget proof fields from an ordered valid-edge list. -/
def controlEdgePairs {controlCount : ℕ} (edges : List (ControlEdge controlCount)) :
    List (Fin controlCount × Fin controlCount) :=
  edges.map ControlEdge.toPair

@[simp]
theorem length_cnotEdgeCircuit {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (edges : List (ControlEdge controlCount)) :
    (cnotEdgeCircuit layout edges).length = edges.length := by
  simp [cnotEdgeCircuit]

/-- Exact arbitrary-width basis action of any proved-valid logical CNOT edge circuit. -/
theorem eval_cnotEdgeCircuit_mulVec_basisKet {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (edges : List (ControlEdge controlCount)) (input : Basis ambientWidth) :
    (Circuit.eval (cnotEdgeCircuit layout edges) : Gate ambientWidth) *ᵥ
        basisKet input =
      basisKet
        (runEmbeddedCNOTUpdates layout (controlEdgePairs edges) input) := by
  induction edges generalizing input with
  | nil =>
      simp [cnotEdgeCircuit, controlEdgePairs]
  | cons edge edges ih =>
      simp only [cnotEdgeCircuit, controlEdgePairs, List.map_cons,
        Circuit.eval_cons, Submonoid.coe_mul]
      rw [← Matrix.mulVec_mulVec,
        cnotPrimitive_mulVec_basisKet layout edge.control edge.target edge.ne input,
        ih]
      rfl

end Barenco.MultiControl
