import Barenco.Circuit

/-!
# Ordered control-wire layouts

Section 7 repeatedly treats a named ordered family of pairwise-distinct controls
and one distinct target inside an arbitrary ambient register.  This small layout
type carries exactly those obligations and provides the bridges to `ControlSet`
and circuit primitives.  It does not prescribe that the wires are adjacent or in
increasing ambient order.
-/

namespace Barenco.MultiControl

/-- An ordered control register embedded disjointly from a named target wire. -/
structure OrderedControlLayout (controlCount ambientWidth : ℕ) where
  controlWire : Fin controlCount ↪ Fin ambientWidth
  targetWire : Fin ambientWidth
  control_ne_target : ∀ control, controlWire control ≠ targetWire

namespace OrderedControlLayout

/-- A control position viewed as a valid member of the target complement. -/
def controlComplement {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (control : Fin controlCount) : TargetComplement layout.targetWire :=
  ⟨layout.controlWire control, layout.control_ne_target control⟩

/-- The ordered control embedding, now targeting the target-complement type. -/
def controlComplementEmbedding {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth) :
    Fin controlCount ↪ TargetComplement layout.targetWire where
  toFun := layout.controlComplement
  inj' := by
    intro first second h
    apply layout.controlWire.injective
    exact congrArg Subtype.val h

/-- The unordered control set consumed by the established controlled-gate semantics. -/
def controlSet {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth) :
    ControlSet layout.targetWire :=
  Finset.univ.map layout.controlComplementEmbedding

@[simp]
theorem card_controlSet {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth) :
    layout.controlSet.card = controlCount := by
  simp [controlSet]

@[simp]
theorem controlComplement_mem_controlSet {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (control : Fin controlCount) :
    layout.controlComplement control ∈ layout.controlSet := by
  rw [controlSet, Finset.mem_map]
  exact ⟨control, Finset.mem_univ control, rfl⟩

theorem mem_controlSet_iff {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (wire : TargetComplement layout.targetWire) :
    wire ∈ layout.controlSet ↔
      ∃ control : Fin controlCount, layout.controlComplement control = wire := by
  constructor
  · rw [controlSet, Finset.mem_map]
    rintro ⟨control, _, hcontrol⟩
    exact ⟨control, hcontrol⟩
  · rintro ⟨control, rfl⟩
    exact layout.controlComplement_mem_controlSet control

/-- Restrict an ambient computational-basis assignment to the ordered controls. -/
def restrictControls {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (input : Basis ambientWidth) : Fin controlCount → Bool :=
  fun control => input (layout.controlWire control)

@[simp]
theorem restrictControls_apply {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (input : Basis ambientWidth) (control : Fin controlCount) :
    layout.restrictControls input control = input (layout.controlWire control) := rfl

/-- Distinct logical positions embed as distinct ambient control wires. -/
theorem controlWire_ne {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    {first second : Fin controlCount} (h : first ≠ second) :
    layout.controlWire first ≠ layout.controlWire second := by
  exact fun heq => h (layout.controlWire.injective heq)

/-- One CNOT between two distinct logical control positions. -/
def cnotPrimitive {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (control target : Fin controlCount) (h : control ≠ target) :
    Primitive ambientWidth :=
  Primitive.cnot (layout.controlWire control) (layout.controlWire target)
    (layout.controlWire_ne h)

@[simp]
theorem cnotPrimitive_kind {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (control target : Fin controlCount) (h : control ≠ target) :
    (layout.cnotPrimitive control target h).kind = .cnot := rfl

/-- A singly controlled target gate selected by one logical control position. -/
def controlledTargetPrimitive {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (control : Fin controlCount) (U : QubitUnitary) : Primitive ambientWidth :=
  Primitive.positiveControlled layout.targetWire
    ({layout.controlComplement control} : ControlSet layout.targetWire) U

@[simp]
theorem controlledTargetPrimitive_kind {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (control : Fin controlCount) (U : QubitUnitary) :
    (layout.controlledTargetPrimitive control U).kind = .controlledOneQubit 1 := by
  simp [controlledTargetPrimitive]

end OrderedControlLayout

end Barenco.MultiControl
