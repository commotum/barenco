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

/-! ## Boolean full-state semantics -/

/-- Conjunction of the first group of data controls. -/
def leftProduct {l r n : ℕ} (layout : FourBlockLayout l r n)
    (input : Basis n) : Bool :=
  ∏ control, input (layout.leftControlWire control)

/-- Conjunction of the second group of data controls. -/
def rightProduct {l r n : ℕ} (layout : FourBlockLayout l r n)
    (input : Basis n) : Bool :=
  ∏ control, input (layout.rightControlWire control)

/-- Boolean action of block A. -/
def blockAUpdate {l r n : ℕ} (layout : FourBlockLayout l r n)
    (input : Basis n) : Basis n :=
  Function.update input layout.dirtyWire
    (input layout.dirtyWire + layout.leftProduct input)

/-- Boolean action of block B. -/
def blockBUpdate {l r n : ℕ} (layout : FourBlockLayout l r n)
    (input : Basis n) : Basis n :=
  Function.update input layout.targetWire
    (input layout.targetWire + layout.rightProduct input * input layout.dirtyWire)

/-- Execute `A;B;A;B` on an arbitrary ambient basis assignment. -/
def fourBlockUpdate {l r n : ℕ} (layout : FourBlockLayout l r n)
    (input : Basis n) : Basis n :=
  layout.blockBUpdate
    (layout.blockAUpdate (layout.blockBUpdate (layout.blockAUpdate input)))

private theorem leftProduct_update_of_outside {l r n : ℕ}
    (layout : FourBlockLayout l r n) (input : Basis n) (outside : Fin n)
    (bit : Bool) (houtside : ∀ control, outside ≠ layout.leftControlWire control) :
    layout.leftProduct (Function.update input outside bit) = layout.leftProduct input := by
  apply Finset.prod_congr rfl
  intro control _
  exact Function.update_of_ne (Ne.symm (houtside control)) _ _

private theorem rightProduct_update_of_outside {l r n : ℕ}
    (layout : FourBlockLayout l r n) (input : Basis n) (outside : Fin n)
    (bit : Bool) (houtside : ∀ control, outside ≠ layout.rightControlWire control) :
    layout.rightProduct (Function.update input outside bit) = layout.rightProduct input := by
  apply Finset.prod_congr rfl
  intro control _
  exact Function.update_of_ne (Ne.symm (houtside control)) _ _

@[simp]
theorem leftProduct_blockAUpdate {l r n : ℕ} (layout : FourBlockLayout l r n)
    (input : Basis n) :
    layout.leftProduct (layout.blockAUpdate input) = layout.leftProduct input := by
  apply leftProduct_update_of_outside
  exact fun control => (layout.leftControlWire_ne_dirtyWire control).symm

@[simp]
theorem leftProduct_blockBUpdate {l r n : ℕ} (layout : FourBlockLayout l r n)
    (input : Basis n) :
    layout.leftProduct (layout.blockBUpdate input) = layout.leftProduct input := by
  apply leftProduct_update_of_outside
  exact fun control => (layout.leftControlWire_ne_targetWire control).symm

@[simp]
theorem rightProduct_blockAUpdate {l r n : ℕ} (layout : FourBlockLayout l r n)
    (input : Basis n) :
    layout.rightProduct (layout.blockAUpdate input) = layout.rightProduct input := by
  apply rightProduct_update_of_outside
  exact fun control => (layout.rightControlWire_ne_dirtyWire control).symm

@[simp]
theorem rightProduct_blockBUpdate {l r n : ℕ} (layout : FourBlockLayout l r n)
    (input : Basis n) :
    layout.rightProduct (layout.blockBUpdate input) = layout.rightProduct input := by
  apply rightProduct_update_of_outside
  exact fun control => (layout.rightControlWire_ne_targetWire control).symm

@[simp]
theorem blockAUpdate_apply_dirtyWire {l r n : ℕ} (layout : FourBlockLayout l r n)
    (input : Basis n) :
    layout.blockAUpdate input layout.dirtyWire =
      input layout.dirtyWire + layout.leftProduct input := by
  simp [blockAUpdate]

@[simp]
theorem blockAUpdate_apply_of_ne {l r n : ℕ} (layout : FourBlockLayout l r n)
    (input : Basis n) (wire : Fin n) (hwire : wire ≠ layout.dirtyWire) :
    layout.blockAUpdate input wire = input wire := by
  exact Function.update_of_ne hwire _ _

@[simp]
theorem blockBUpdate_apply_targetWire {l r n : ℕ} (layout : FourBlockLayout l r n)
    (input : Basis n) :
    layout.blockBUpdate input layout.targetWire =
      input layout.targetWire + layout.rightProduct input * input layout.dirtyWire := by
  simp [blockBUpdate]

@[simp]
theorem blockBUpdate_apply_of_ne {l r n : ℕ} (layout : FourBlockLayout l r n)
    (input : Basis n) (wire : Fin n) (hwire : wire ≠ layout.targetWire) :
    layout.blockBUpdate input wire = input wire := by
  exact Function.update_of_ne hwire _ _

/--
The four blocks erase every dependence on the unknown dirty bit.  Only the final
target changes, by the conjunction of both data-control groups.
-/
theorem fourBlockUpdate_eq_update {l r n : ℕ} (layout : FourBlockLayout l r n)
    (input : Basis n) :
    layout.fourBlockUpdate input =
      Function.update input layout.targetWire
        (input layout.targetWire + layout.leftProduct input * layout.rightProduct input) := by
  funext wire
  by_cases htarget : wire = layout.targetWire
  · subst wire
    rw [fourBlockUpdate, Function.update_self]
    rw [blockBUpdate_apply_targetWire]
    rw [blockAUpdate_apply_of_ne layout _ layout.targetWire
      layout.dirtyWire_ne_targetWire.symm]
    rw [blockBUpdate_apply_targetWire]
    rw [blockAUpdate_apply_of_ne layout _ layout.targetWire
      layout.dirtyWire_ne_targetWire.symm]
    rw [blockAUpdate_apply_dirtyWire layout
      (layout.blockBUpdate (layout.blockAUpdate input))]
    rw [blockBUpdate_apply_of_ne layout (layout.blockAUpdate input)
      layout.dirtyWire layout.dirtyWire_ne_targetWire]
    rw [blockAUpdate_apply_dirtyWire layout input]
    simp only [rightProduct_blockAUpdate, rightProduct_blockBUpdate,
      leftProduct_blockAUpdate, leftProduct_blockBUpdate]
    rw [show input layout.dirtyWire + layout.leftProduct input +
        layout.leftProduct input = input layout.dirtyWire by simp [add_assoc]]
    rw [mul_add]
    rw [show
      input layout.targetWire +
            (layout.rightProduct input * input layout.dirtyWire +
              layout.rightProduct input * layout.leftProduct input) +
          layout.rightProduct input * input layout.dirtyWire =
        input layout.targetWire +
            layout.rightProduct input * layout.leftProduct input +
          (layout.rightProduct input * input layout.dirtyWire +
            layout.rightProduct input * input layout.dirtyWire) by ac_rfl]
    simp [mul_comm]
  · by_cases hdirty : wire = layout.dirtyWire
    · subst wire
      simp [fourBlockUpdate, htarget, add_assoc]
    · simp [fourBlockUpdate, htarget, hdirty]

/-- Every non-target wire, including the dirty wire, is restored exactly. -/
@[simp]
theorem fourBlockUpdate_apply_of_ne {l r n : ℕ} (layout : FourBlockLayout l r n)
    (input : Basis n) (wire : Fin n) (hwire : wire ≠ layout.targetWire) :
    layout.fourBlockUpdate input wire = input wire := by
  rw [fourBlockUpdate_eq_update]
  exact Function.update_of_ne hwire _ _

/-- Explicit dirty-wire restoration with no initialization assumption. -/
@[simp]
theorem fourBlockUpdate_apply_dirtyWire {l r n : ℕ}
    (layout : FourBlockLayout l r n) (input : Basis n) :
    layout.fourBlockUpdate input layout.dirtyWire = input layout.dirtyWire := by
  exact layout.fourBlockUpdate_apply_of_ne input layout.dirtyWire
    layout.dirtyWire_ne_targetWire

/-! ## Positive-controlled Pauli-X bridge -/

/-- Boolean product of an arbitrary ordered control register. -/
private def orderedControlProduct {controlCount n : ℕ}
    (layout : OrderedControlLayout controlCount n) (input : Basis n) : Bool :=
  ∏ control, input (layout.controlWire control)

private theorem boolFinsetProduct_eq_true_iff {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → Bool) :
    (∏ i ∈ s, f i) = true ↔ ∀ i ∈ s, f i = true := by
  induction s using Finset.induction_on with
  | empty => simp [Bool.one_eq_true]
  | @insert element s hnotMem ih =>
      rw [Finset.prod_insert hnotMem, Bool.mul_eq_and, Bool.and_eq_true, ih]
      simp

private theorem orderedControlProduct_eq_true_iff {controlCount n : ℕ}
    (layout : OrderedControlLayout controlCount n) (input : Basis n) :
    orderedControlProduct layout input = true ↔
      ∀ control, input (layout.controlWire control) = true := by
  rw [orderedControlProduct]
  simpa using boolFinsetProduct_eq_true_iff
    (Finset.univ : Finset (Fin controlCount))
    (fun control => input (layout.controlWire control))

private theorem all_controlSet_true_iff_orderedControlProduct_eq_true
    {controlCount n : ℕ} (layout : OrderedControlLayout controlCount n)
    (input : Basis n) :
    (∀ wire ∈ layout.controlSet, input wire = true) ↔
      orderedControlProduct layout input = true := by
  rw [layout.all_controls_iff]
  change (∀ control, input (layout.controlWire control) = true) ↔ _
  exact (orderedControlProduct_eq_true_iff layout input).symm

private theorem update_add_true_eq_setTarget_not {n : ℕ}
    (target : Fin n) (input : Basis n) :
    Function.update input target (input target + true) =
      setTarget target input (!input target) := by
  funext wire
  by_cases hwire : wire = target
  · subst wire
    rw [Function.update_self, setTarget_apply_target]
    cases input target <;> rfl
  · rw [Function.update_of_ne hwire,
      setTarget_apply_of_ne target input _ wire hwire]

private theorem update_add_false_eq_self {n : ℕ}
    (target : Fin n) (input : Basis n) :
    Function.update input target (input target + false) = input := by
  funext wire
  by_cases hwire : wire = target
  · subst wire
    rw [Function.update_self]
    cases input target <;> rfl
  · rw [Function.update_of_ne hwire]

/-- Exact basis action of positive-controlled Pauli-X for ordered controls. -/
private theorem positiveControlledPauliX_mulVec_basisKet {controlCount n : ℕ}
    (layout : OrderedControlLayout controlCount n) (input : Basis n) :
    (positiveControlledUnitary layout.targetWire layout.controlSet pauliX : Gate n) *ᵥ
        basisKet input =
      basisKet
        (Function.update input layout.targetWire
          (input layout.targetWire + orderedControlProduct layout input)) := by
  rw [coe_positiveControlledUnitary, positiveControlledRaw_truthTable]
  by_cases hall : ∀ wire ∈ layout.controlSet, input wire = true
  · rw [if_pos hall]
    have hproduct : orderedControlProduct layout input = true :=
      (all_controlSet_true_iff_orderedControlProduct_eq_true layout input).mp hall
    rw [hproduct, update_add_true_eq_setTarget_not]
    simpa [xRaw] using xRaw_mulVec_basisKet layout.targetWire input
  · rw [if_neg hall]
    have hproduct : orderedControlProduct layout input = false := by
      apply Bool.eq_false_of_not_eq_true
      intro htrue
      exact hall
        ((all_controlSet_true_iff_orderedControlProduct_eq_true layout input).mpr htrue)
    rw [hproduct, update_add_false_eq_self]

@[simp]
theorem orderedControlProduct_aLayout {l r n : ℕ}
    (layout : FourBlockLayout l r n) (input : Basis n) :
    orderedControlProduct layout.aLayout input = layout.leftProduct input := by
  rfl

@[simp]
theorem orderedControlProduct_bLayout {l r n : ℕ}
    (layout : FourBlockLayout l r n) (input : Basis n) :
    orderedControlProduct layout.bLayout input =
      layout.rightProduct input * input layout.dirtyWire := by
  rw [orderedControlProduct, Fin.prod_univ_add]
  simp [bLayout, bControlEmbedding, bControlSlotEmbedding,
    bControlSumEmbedding, rightProduct, dirtyWire, rightControlWire]

@[simp]
theorem orderedControlProduct_dataLayout {l r n : ℕ}
    (layout : FourBlockLayout l r n) (input : Basis n) :
    orderedControlProduct layout.dataLayout input =
      layout.leftProduct input * layout.rightProduct input := by
  rw [orderedControlProduct, Fin.prod_univ_add]
  simp [dataLayout, dataControlEmbedding, dataControlSlotEmbedding,
    dataControlSumEmbedding, leftProduct, rightProduct,
    leftControlWire, rightControlWire]

/-- Block A's macro denotation is exactly its Boolean dirty-wire update. -/
@[simp]
theorem blockA_denotation_mulVec_basisKet {l r n : ℕ}
    (layout : FourBlockLayout l r n) (input : Basis n) :
    (layout.blockA.denotation : Gate n) *ᵥ basisKet input =
      basisKet (layout.blockAUpdate input) := by
  rw [blockA, Primitive.positiveControlled_denotation]
  have haction := positiveControlledPauliX_mulVec_basisKet layout.aLayout input
  rw [orderedControlProduct_aLayout] at haction
  simpa [blockAUpdate, aLayout] using haction

/-- Block B's macro denotation is exactly its Boolean target update. -/
@[simp]
theorem blockB_denotation_mulVec_basisKet {l r n : ℕ}
    (layout : FourBlockLayout l r n) (input : Basis n) :
    (layout.blockB.denotation : Gate n) *ᵥ basisKet input =
      basisKet (layout.blockBUpdate input) := by
  rw [blockB, Primitive.positiveControlled_denotation]
  have haction := positiveControlledPauliX_mulVec_basisKet layout.bLayout input
  rw [orderedControlProduct_bLayout] at haction
  simpa [blockBUpdate, bLayout] using haction

/-- Exact arbitrary-width basis action of the chronological four-block circuit. -/
theorem eval_fourBlockCircuit_mulVec_basisKet {l r n : ℕ}
    (layout : FourBlockLayout l r n) (input : Basis n) :
    (Circuit.eval layout.fourBlockCircuit : Gate n) *ᵥ basisKet input =
      basisKet (layout.fourBlockUpdate input) := by
  simp only [fourBlockCircuit, Circuit.eval_cons, Circuit.eval_nil,
    Submonoid.coe_mul, Submonoid.coe_one, Matrix.one_mul]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [blockA_denotation_mulVec_basisKet,
    blockB_denotation_mulVec_basisKet,
    blockA_denotation_mulVec_basisKet,
    blockB_denotation_mulVec_basisKet]
  rfl

/--
Barenco Lemma 7.3: `A;B;A;B` is exactly the positive-controlled Pauli-X on all
logical data controls, on the full ambient register.
-/
@[simp]
theorem eval_fourBlockCircuit {l r n : ℕ} (layout : FourBlockLayout l r n) :
    Circuit.eval layout.fourBlockCircuit =
      positiveControlledUnitary layout.targetWire layout.dataLayout.controlSet pauliX := by
  apply Subtype.ext
  rw [matrix_eq_iff_mulVec_basisKet_eq]
  intro input
  rw [eval_fourBlockCircuit_mulVec_basisKet, fourBlockUpdate_eq_update]
  have haction := positiveControlledPauliX_mulVec_basisKet layout.dataLayout input
  rw [orderedControlProduct_dataLayout] at haction
  simpa [dataLayout] using haction.symm

end FourBlockLayout

end Barenco.MultiControl
