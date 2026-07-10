import Barenco.MultiControl.GrayAccumulator
import Barenco.MultiControl.Layout
import Barenco.OneQubit.Roots

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
  change cnotRaw (layout.controlWire control) (layout.controlWire target)
      (layout.controlWire_ne h) *ᵥ basisKet input = _
  simpa [embeddedCNOTUpdate] using
    cnotRaw_mulVec_basisKet (layout.controlWire control)
      (layout.controlWire target) (layout.controlWire_ne h) input

/-- Restricting an embedded logical CNOT is exactly the pure Boolean XOR update. -/
theorem restrictControls_embeddedCNOTUpdate {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (control target : Fin controlCount) (h : control ≠ target)
    (input : Basis ambientWidth) :
    layout.restrictControls (embeddedCNOTUpdate layout control target input) =
      xorWireUpdate control target (layout.restrictControls input) := by
  funext wire
  by_cases hwire : wire = target
  · subst wire
    cases hcontrol : input (layout.controlWire control) <;>
      cases htarget : input (layout.controlWire target) <;>
      simp [embeddedCNOTUpdate, OrderedControlLayout.restrictControls,
        xorWireUpdate, hcontrol, htarget, layout.controlWire_ne h]
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

end Barenco.MultiControl
