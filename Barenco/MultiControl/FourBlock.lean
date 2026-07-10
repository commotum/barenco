import Barenco.Cost
import Barenco.MultiControl.Layout
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Tactic

/-!
# Four-block dirty-wire construction

This module reconstructs Barenco et al., Lemma 7.3.  Its chronological circuit
is `A; B; A; B`.  Block `A` toggles one dirty borrowed wire from a first group
of controls.  Block `B` uses that dirty wire together with a nonempty second
group of controls to toggle the final target.  The two occurrences of `A`
restore the dirty wire, while the two occurrences of `B` cancel its unknown
initial value.

The source parameter satisfies `2 ≤ m ≤ n - 3`.  Instead of using truncated
subtraction in types, the layout below has `leftExtra + 2` controls in the first
group and `rightExtra + 1` data controls in the second group.  Thus both `A`
and `B` have at least two controls by construction.  The exact subtraction-free
form of the source bounds is proved below.

The four nodes are positive-controlled Pauli-X macros.  Their semantic equality
and their four-node syntax count are proved here; no one-qubit+CNOT cost is
assigned before a later explicit expansion.
-/

namespace Barenco.MultiControl

open scoped BigOperators BooleanRing Matrix

/--
Logical slots for the four-block construction: first controls, second controls,
and the pair `(dirty, target)`.
-/
abbrev FourBlockSlot (leftExtra rightExtra : ℕ) :=
  Fin (leftExtra + 2) ⊕ (Fin (rightExtra + 1) ⊕ Fin 2)

/-- Arbitrary nonadjacent placement of all data, dirty, and target wires. -/
structure FourBlockLayout (leftExtra rightExtra ambientWidth : ℕ) where
  wire : FourBlockSlot leftExtra rightExtra ↪ Fin ambientWidth

namespace FourBlockLayout

/-! ## Layout projections and source bounds -/

def leftControlWire {l r n : ℕ} (layout : FourBlockLayout l r n)
    (control : Fin (l + 2)) : Fin n :=
  layout.wire (Sum.inl control)

def rightControlWire {l r n : ℕ} (layout : FourBlockLayout l r n)
    (control : Fin (r + 1)) : Fin n :=
  layout.wire (Sum.inr (Sum.inl control))

/-- The borrowed wire may contain an arbitrary initial bit. -/
def dirtyWire {l r n : ℕ} (layout : FourBlockLayout l r n) : Fin n :=
  layout.wire (Sum.inr (Sum.inr 0))

/-- The final logical target. -/
def targetWire {l r n : ℕ} (layout : FourBlockLayout l r n) : Fin n :=
  layout.wire (Sum.inr (Sum.inr 1))

private theorem wire_ne_of_slot_ne {l r n : ℕ} (layout : FourBlockLayout l r n)
    {first second : FourBlockSlot l r} (h : first ≠ second) :
    layout.wire first ≠ layout.wire second :=
  fun heq => h (layout.wire.injective heq)

theorem leftControlWire_injective {l r n : ℕ} (layout : FourBlockLayout l r n) :
    Function.Injective layout.leftControlWire := by
  intro first second h
  have hslot : (Sum.inl first : FourBlockSlot l r) = Sum.inl second :=
    layout.wire.injective h
  exact Sum.inl.inj hslot

theorem rightControlWire_injective {l r n : ℕ} (layout : FourBlockLayout l r n) :
    Function.Injective layout.rightControlWire := by
  intro first second h
  have hslot : (Sum.inr (Sum.inl first) : FourBlockSlot l r) =
      Sum.inr (Sum.inl second) := layout.wire.injective h
  exact Sum.inl.inj (Sum.inr.inj hslot)

theorem leftControlWire_ne_rightControlWire {l r n : ℕ}
    (layout : FourBlockLayout l r n) (left : Fin (l + 2)) (right : Fin (r + 1)) :
    layout.leftControlWire left ≠ layout.rightControlWire right := by
  apply layout.wire_ne_of_slot_ne
  intro h
  cases h

theorem leftControlWire_ne_dirtyWire {l r n : ℕ}
    (layout : FourBlockLayout l r n) (control : Fin (l + 2)) :
    layout.leftControlWire control ≠ layout.dirtyWire := by
  apply layout.wire_ne_of_slot_ne
  intro h
  cases h

theorem leftControlWire_ne_targetWire {l r n : ℕ}
    (layout : FourBlockLayout l r n) (control : Fin (l + 2)) :
    layout.leftControlWire control ≠ layout.targetWire := by
  apply layout.wire_ne_of_slot_ne
  intro h
  cases h

theorem rightControlWire_ne_dirtyWire {l r n : ℕ}
    (layout : FourBlockLayout l r n) (control : Fin (r + 1)) :
    layout.rightControlWire control ≠ layout.dirtyWire := by
  apply layout.wire_ne_of_slot_ne
  intro h
  cases Sum.inr.inj h

theorem rightControlWire_ne_targetWire {l r n : ℕ}
    (layout : FourBlockLayout l r n) (control : Fin (r + 1)) :
    layout.rightControlWire control ≠ layout.targetWire := by
  apply layout.wire_ne_of_slot_ne
  intro h
  cases Sum.inr.inj h

theorem dirtyWire_ne_targetWire {l r n : ℕ} (layout : FourBlockLayout l r n) :
    layout.dirtyWire ≠ layout.targetWire := by
  apply layout.wire_ne_of_slot_ne
  intro h
  have : (0 : Fin 2) = 1 := Sum.inr.inj (Sum.inr.inj h)
  omega

/-- Number of wires used by the source construction, excluding ambient spectators. -/
def logicalWidth (leftExtra rightExtra : ℕ) : ℕ :=
  leftExtra + rightExtra + 5

/-- The source's first block has `m = leftExtra + 2` controls. -/
def sourceSplit (leftExtra : ℕ) : ℕ := leftExtra + 2

/-- The structural indices encode `2 ≤ m` and `m + 3 ≤ logicalWidth`. -/
theorem sourceSplit_bounds (leftExtra rightExtra : ℕ) :
    2 ≤ sourceSplit leftExtra ∧
      sourceSplit leftExtra + 3 ≤ logicalWidth leftExtra rightExtra := by
  simp [sourceSplit, logicalWidth]

/-- Any supplied placement has enough ambient wires for every logical slot. -/
theorem logicalWidth_le_ambientWidth {l r n : ℕ} (layout : FourBlockLayout l r n) :
    logicalWidth l r ≤ n := by
  have hcard := Fintype.card_le_of_injective layout.wire layout.wire.injective
  change l + r + 5 ≤ n
  simp [FourBlockSlot] at hcard
  omega

/-- Hence the paper's subtraction-free upper split bound holds in the ambient network. -/
theorem sourceSplit_add_three_le_ambientWidth {l r n : ℕ}
    (layout : FourBlockLayout l r n) :
    sourceSplit l + 3 ≤ n :=
  (sourceSplit_bounds l r).2.trans layout.logicalWidth_le_ambientWidth

/-! ## Ordered control layouts for A, B, and the intended final gate -/

def leftControlEmbedding {l r n : ℕ} (layout : FourBlockLayout l r n) :
    Fin (l + 2) ↪ Fin n where
  toFun := layout.leftControlWire
  inj' := layout.leftControlWire_injective

/-- Embed the sum of second-group controls and the singleton dirty slot. -/
def bControlSumEmbedding (l r : ℕ) :
    (Fin (r + 1) ⊕ Fin 1) ↪ FourBlockSlot l r where
  toFun
    | Sum.inl right => Sum.inr (Sum.inl right)
    | Sum.inr _ => Sum.inr (Sum.inr 0)
  inj' := by
    intro first second h
    cases first with
    | inl firstRight =>
        cases second with
        | inl secondRight =>
            simp only [Sum.inr.injEq, Sum.inl.injEq] at h
            exact congrArg Sum.inl h
        | inr secondDirty => cases Sum.inr.inj h
    | inr firstDirty =>
        cases second with
        | inl secondRight => cases Sum.inr.inj h
        | inr secondDirty =>
            exact congrArg Sum.inr (Subsingleton.elim firstDirty secondDirty)

/-- Controls of `B`: all second-group data controls, followed by the dirty wire. -/
def bControlSlotEmbedding (l r : ℕ) :
    Fin ((r + 1) + 1) ↪ FourBlockSlot l r :=
  (@finSumFinEquiv (r + 1) 1).symm.toEmbedding.trans
    (bControlSumEmbedding l r)

def bControlEmbedding {l r n : ℕ} (layout : FourBlockLayout l r n) :
    Fin ((r + 1) + 1) ↪ Fin n :=
  (bControlSlotEmbedding l r).trans layout.wire

/-- Embed the sum of both data-control groups into the logical slots. -/
def dataControlSumEmbedding (l r : ℕ) :
    (Fin (l + 2) ⊕ Fin (r + 1)) ↪ FourBlockSlot l r where
  toFun
    | Sum.inl left => Sum.inl left
    | Sum.inr right => Sum.inr (Sum.inl right)
  inj' := by
    intro first second h
    cases first with
    | inl firstLeft =>
        cases second with
        | inl secondLeft => exact congrArg Sum.inl (Sum.inl.inj h)
        | inr secondRight => cases h
    | inr firstRight =>
        cases second with
        | inl secondLeft => cases h
        | inr secondRight =>
            exact congrArg Sum.inr (Sum.inl.inj (Sum.inr.inj h))

/-- All logical data controls, first group followed by second group. -/
def dataControlSlotEmbedding (l r : ℕ) :
    Fin ((l + 2) + (r + 1)) ↪ FourBlockSlot l r :=
  (@finSumFinEquiv (l + 2) (r + 1)).symm.toEmbedding.trans
    (dataControlSumEmbedding l r)

def dataControlEmbedding {l r n : ℕ} (layout : FourBlockLayout l r n) :
    Fin ((l + 2) + (r + 1)) ↪ Fin n :=
  (dataControlSlotEmbedding l r).trans layout.wire

/-- Block A's controls and dirty target. -/
def aLayout {l r n : ℕ} (layout : FourBlockLayout l r n) :
    OrderedControlLayout (l + 2) n where
  controlWire := layout.leftControlEmbedding
  targetWire := layout.dirtyWire
  control_ne_target := layout.leftControlWire_ne_dirtyWire

/-- Block B's second-group-plus-dirty controls and final target. -/
def bLayout {l r n : ℕ} (layout : FourBlockLayout l r n) :
    OrderedControlLayout ((r + 1) + 1) n where
  controlWire := layout.bControlEmbedding
  targetWire := layout.targetWire
  control_ne_target := by
    intro control
    change layout.wire (bControlSlotEmbedding l r control) ≠ layout.targetWire
    apply layout.wire_ne_of_slot_ne
    cases hcontrol : finSumFinEquiv.symm control with
    | inl right =>
        simp [bControlSlotEmbedding, bControlSumEmbedding, hcontrol]
    | inr dirty =>
        have : dirty = 0 := Subsingleton.elim _ _
        simp [bControlSlotEmbedding, bControlSumEmbedding, hcontrol, this]

/-- Ordered controls of the intended final multi-controlled X. -/
def dataLayout {l r n : ℕ} (layout : FourBlockLayout l r n) :
    OrderedControlLayout ((l + 2) + (r + 1)) n where
  controlWire := layout.dataControlEmbedding
  targetWire := layout.targetWire
  control_ne_target := by
    intro control
    change layout.wire (dataControlSlotEmbedding l r control) ≠ layout.targetWire
    apply layout.wire_ne_of_slot_ne
    cases hcontrol : finSumFinEquiv.symm control with
    | inl left =>
        simp [dataControlSlotEmbedding, dataControlSumEmbedding, hcontrol]
    | inr right =>
        simp [dataControlSlotEmbedding, dataControlSumEmbedding, hcontrol]

/-! ## Four-node chronological syntax -/

/-- Compute/uncompute block on the dirty wire. -/
def blockA {l r n : ℕ} (layout : FourBlockLayout l r n) : Primitive n :=
  Primitive.positiveControlled layout.dirtyWire layout.aLayout.controlSet pauliX

/-- Target block controlled by the second group and dirty wire. -/
def blockB {l r n : ℕ} (layout : FourBlockLayout l r n) : Primitive n :=
  Primitive.positiveControlled layout.targetWire layout.bLayout.controlSet pauliX

/-- The source diagram in exact chronological order: `A; B; A; B`. -/
def fourBlockCircuit {l r n : ℕ} (layout : FourBlockLayout l r n) : Circuit n :=
  [layout.blockA, layout.blockB, layout.blockA, layout.blockB]

@[simp]
theorem blockA_kind {l r n : ℕ} (layout : FourBlockLayout l r n) :
    layout.blockA.kind = .controlledOneQubit (l + 2) := by
  simp [blockA, aLayout]

@[simp]
theorem blockB_kind {l r n : ℕ} (layout : FourBlockLayout l r n) :
    layout.blockB.kind = .controlledOneQubit (r + 2) := by
  simp [blockB, bLayout]

@[simp]
theorem fourBlockCircuit_gateCount {l r n : ℕ} (layout : FourBlockLayout l r n) :
    Circuit.gateCount layout.fourBlockCircuit = 4 := by
  rfl

/-- The syntax contains exactly the source's two A and two B occurrences. -/
theorem fourBlockCircuit_chronology {l r n : ℕ} (layout : FourBlockLayout l r n) :
    layout.fourBlockCircuit =
      [layout.blockA, layout.blockB, layout.blockA, layout.blockB] :=
  rfl

/-- Unexpanded multi-control macros have no one-qubit+CNOT cost. -/
@[simp]
theorem fourBlockCircuit_oneQubitCNOTCost {l r n : ℕ}
    (layout : FourBlockLayout l r n) :
    Circuit.cost CostModel.oneQubitCNOT layout.fourBlockCircuit = none := by
  simp [fourBlockCircuit, Circuit.cost, Circuit.addCost]

end FourBlockLayout

end Barenco.MultiControl
