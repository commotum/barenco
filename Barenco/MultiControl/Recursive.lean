import Barenco.MultiControl.Layout
import Barenco.ControlledCircuit.Block
import Barenco.OneQubit.Roots
import Barenco.Cost

/-!
# Barenco Lemma 7.5: one recursive multi-control step

This module reconstructs the five-macro circuit from Lemma 7.5 on an ordered
family of controls embedded in an arbitrary ambient register.  For `prefix + 1`
controls, write `c` for the final ordered control.  The chronological circuit is

`C(c,V,target); MCX(prefix,c); C(c,V⁻¹,target); MCX(prefix,c);`
`MC-V(prefix,target)`.

The theorem is uniform at `prefix = 0`: the two empty-controlled X macros are
local X gates on `c`, and the final empty-controlled `V` macro is local on the
target.  A genuinely zero-control target gate is exposed separately as a local
base circuit.

All five nodes are retained as macros.  Consequently their structural count is
exact, but neither paper cost model accepts the unexpanded circuit.
-/

namespace Barenco.MultiControl

open Barenco.OneQubit
open Barenco.ControlledCircuit
open scoped Matrix

noncomputable section

namespace OrderedControlLayout

/-! ## Prefix and final-control projections -/

/-- The final ordered control wire in a nonempty control layout. -/
def lastControlWire {prefix ambientWidth : ℕ}
    (layout : OrderedControlLayout (prefix + 1) ambientWidth) : Fin ambientWidth :=
  layout.controlWire (Fin.last prefix)

/-- The first `prefix` controls, retaining the original target wire. -/
def prefixTargetLayout {prefix ambientWidth : ℕ}
    (layout : OrderedControlLayout (prefix + 1) ambientWidth) :
    OrderedControlLayout prefix ambientWidth where
  controlWire := Fin.castSuccEmb.trans layout.controlWire
  targetWire := layout.targetWire
  control_ne_target := fun control => layout.control_ne_target control.castSucc

/-- The first `prefix` controls, now targeting the final ordered control wire. -/
def prefixToLastLayout {prefix ambientWidth : ℕ}
    (layout : OrderedControlLayout (prefix + 1) ambientWidth) :
    OrderedControlLayout prefix ambientWidth where
  controlWire := Fin.castSuccEmb.trans layout.controlWire
  targetWire := layout.lastControlWire
  control_ne_target := fun control =>
    layout.controlWire_ne (Fin.castSucc_ne_last control)

@[simp]
theorem prefixTargetLayout_controlWire {prefix ambientWidth : ℕ}
    (layout : OrderedControlLayout (prefix + 1) ambientWidth)
    (control : Fin prefix) :
    layout.prefixTargetLayout.controlWire control =
      layout.controlWire control.castSucc := rfl

@[simp]
theorem prefixTargetLayout_targetWire {prefix ambientWidth : ℕ}
    (layout : OrderedControlLayout (prefix + 1) ambientWidth) :
    layout.prefixTargetLayout.targetWire = layout.targetWire := rfl

@[simp]
theorem prefixToLastLayout_controlWire {prefix ambientWidth : ℕ}
    (layout : OrderedControlLayout (prefix + 1) ambientWidth)
    (control : Fin prefix) :
    layout.prefixToLastLayout.controlWire control =
      layout.controlWire control.castSucc := rfl

@[simp]
theorem prefixToLastLayout_targetWire {prefix ambientWidth : ℕ}
    (layout : OrderedControlLayout (prefix + 1) ambientWidth) :
    layout.prefixToLastLayout.targetWire = layout.lastControlWire := rfl

@[simp]
theorem lastControlWire_ne_targetWire {prefix ambientWidth : ℕ}
    (layout : OrderedControlLayout (prefix + 1) ambientWidth) :
    layout.lastControlWire ≠ layout.targetWire :=
  layout.control_ne_target (Fin.last prefix)

/-! ## The five chronological macros -/

/-- A target gate controlled only by the final ordered control. -/
def lastControlledTarget {prefix ambientWidth : ℕ}
    (layout : OrderedControlLayout (prefix + 1) ambientWidth)
    (V : QubitUnitary) : Primitive ambientWidth :=
  Primitive.positiveControlled layout.targetWire
    ({⟨layout.lastControlWire, layout.lastControlWire_ne_targetWire⟩} :
      ControlSet layout.targetWire) V

/-- A prefix-controlled X whose target is the final ordered control. -/
def prefixControlledX {prefix ambientWidth : ℕ}
    (layout : OrderedControlLayout (prefix + 1) ambientWidth) :
    Primitive ambientWidth :=
  Primitive.positiveControlled layout.lastControlWire
    layout.prefixToLastLayout.controlSet pauliX

/-- A target gate controlled by all controls except the final ordered one. -/
def prefixControlledTarget {prefix ambientWidth : ℕ}
    (layout : OrderedControlLayout (prefix + 1) ambientWidth)
    (V : QubitUnitary) : Primitive ambientWidth :=
  Primitive.positiveControlled layout.targetWire
    layout.prefixTargetLayout.controlSet V

/-- The exact five-macro chronology of Barenco Lemma 7.5. -/
def recursiveViaSquareCircuit {prefix ambientWidth : ℕ}
    (layout : OrderedControlLayout (prefix + 1) ambientWidth)
    (V : QubitUnitary) : Circuit ambientWidth :=
  [layout.lastControlledTarget V,
    layout.prefixControlledX,
    layout.lastControlledTarget V⁻¹,
    layout.prefixControlledX,
    layout.prefixControlledTarget V]

/-- Lemma 7.5 specialized to the selected exact square root of `U`. -/
def recursiveRootCircuit {prefix ambientWidth : ℕ}
    (layout : OrderedControlLayout (prefix + 1) ambientWidth)
    (U : QubitUnitary) : Circuit ambientWidth :=
  layout.recursiveViaSquareCircuit (unitarySquareRoot U)

/-! ## Separate zero-control base -/

/-- A genuinely zero-control target gate is one local one-qubit primitive. -/
def zeroControlCircuit {ambientWidth : ℕ} (target : Fin ambientWidth)
    (U : QubitUnitary) : Circuit ambientWidth :=
  [Primitive.oneQubit target U]

@[simp]
theorem eval_zeroControlCircuit {ambientWidth : ℕ} (target : Fin ambientWidth)
    (U : QubitUnitary) :
    Circuit.eval (zeroControlCircuit target U) = localUnitary target U := by
  simp [zeroControlCircuit, Circuit.eval]

end OrderedControlLayout

end

end Barenco.MultiControl
