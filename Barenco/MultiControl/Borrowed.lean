import Barenco.Cost
import Barenco.MultiControl.Layout
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Tactic

/-!
# Dirty-borrowed inward Toffoli ladders

This module reconstructs the circuit in Barenco et al., Lemma 7.2.  A layout
with `b` borrowed wires has `b + 2` controls, `b` dirty borrowed wires, and one
target.  All of these logical slots are embedded injectively into an arbitrary
ambient register, so the construction neither assumes adjacent wires nor fixes
the values initially stored in the borrowed wires.

The circuit is recorded chronologically.  Its first, palindromic half toggles
the target by the conjunction of all controls while applying a smaller half to
the borrowed register.  Repeating that smaller half restores every borrowed
wire.  Consequently the final theorem is exact equality of full-register
unitaries, not merely agreement on classical data bits.

The paper's parameter `m` is the number of controls.  The public construction
below is indexed by `b + 1 = m - 2`, making the necessary boundary `m >= 3`
explicit and avoiding truncated subtraction in the recursive definitions.
-/

namespace Barenco.MultiControl

open scoped BigOperators Matrix

/-! ## Logical wire layout -/

/--
Logical slots for an inward ladder with `b` borrowed wires.

The left summand consists of the `b + 2` controls.  In the right summand, the
first `b` positions are dirty borrowed wires and the final position is the
logical target.
-/
abbrev InwardLadderSlot (b : ℕ) := Fin (b + 2) ⊕ Fin (b + 1)

/-- An arbitrary placement of all controls, borrowed wires, and target. -/
structure InwardLadderLayout (borrowedCount ambientWidth : ℕ) where
  wire : InwardLadderSlot borrowedCount ↪ Fin ambientWidth

namespace InwardLadderLayout

/-- Ambient wire occupied by one logical control. -/
def controlWire {b n : ℕ} (layout : InwardLadderLayout b n) (control : Fin (b + 2)) :
    Fin n :=
  layout.wire (Sum.inl control)

/-- Ambient wire occupied by a member of the work register. -/
def workWire {b n : ℕ} (layout : InwardLadderLayout b n) (work : Fin (b + 1)) :
    Fin n :=
  layout.wire (Sum.inr work)

/-- Ambient wire occupied by one dirty borrowed bit. -/
def borrowedWire {b n : ℕ} (layout : InwardLadderLayout b n) (borrowed : Fin b) :
    Fin n :=
  layout.workWire borrowed.castSucc

/-- Ambient target wire, stored at the final work-register position. -/
def targetWire {b n : ℕ} (layout : InwardLadderLayout b n) : Fin n :=
  layout.workWire (Fin.last b)

theorem controlWire_injective {b n : ℕ} (layout : InwardLadderLayout b n) :
    Function.Injective layout.controlWire := by
  intro first second h
  have : (Sum.inl first : InwardLadderSlot b) = Sum.inl second :=
    layout.wire.injective h
  exact Sum.inl.inj this

theorem workWire_injective {b n : ℕ} (layout : InwardLadderLayout b n) :
    Function.Injective layout.workWire := by
  intro first second h
  have : (Sum.inr first : InwardLadderSlot b) = Sum.inr second :=
    layout.wire.injective h
  exact Sum.inr.inj this

theorem controlWire_ne_workWire {b n : ℕ} (layout : InwardLadderLayout b n)
    (control : Fin (b + 2)) (work : Fin (b + 1)) :
    layout.controlWire control ≠ layout.workWire work := by
  intro h
  have : (Sum.inl control : InwardLadderSlot b) = Sum.inr work :=
    layout.wire.injective h
  cases this

theorem controlWire_ne {b n : ℕ} (layout : InwardLadderLayout b n)
    {first second : Fin (b + 2)} (h : first ≠ second) :
    layout.controlWire first ≠ layout.controlWire second :=
  fun heq => h (layout.controlWire_injective heq)

theorem workWire_ne {b n : ℕ} (layout : InwardLadderLayout b n)
    {first second : Fin (b + 1)} (h : first ≠ second) :
    layout.workWire first ≠ layout.workWire second :=
  fun heq => h (layout.workWire_injective heq)

theorem controlWire_ne_borrowedWire {b n : ℕ} (layout : InwardLadderLayout b n)
    (control : Fin (b + 2)) (borrowed : Fin b) :
    layout.controlWire control ≠ layout.borrowedWire borrowed :=
  layout.controlWire_ne_workWire control borrowed.castSucc

theorem controlWire_ne_targetWire {b n : ℕ} (layout : InwardLadderLayout b n)
    (control : Fin (b + 2)) :
    layout.controlWire control ≠ layout.targetWire :=
  layout.controlWire_ne_workWire control (Fin.last b)

theorem borrowedWire_ne_targetWire {b n : ℕ} (layout : InwardLadderLayout b n)
    (borrowed : Fin b) :
    layout.borrowedWire borrowed ≠ layout.targetWire := by
  exact layout.workWire_ne borrowed.castSucc_ne_last

/-- Insert a smaller ladder into the control and work prefixes of a larger one. -/
def prefixSlotEmbedding (b : ℕ) : InwardLadderSlot b ↪ InwardLadderSlot (b + 1) where
  toFun
    | Sum.inl control => Sum.inl control.castSucc
    | Sum.inr work => Sum.inr work.castSucc
  inj' := by
    intro first second h
    cases first with
    | inl first =>
        cases second with
        | inl second =>
            simp only [Sum.inl.injEq, Fin.castSucc_inj] at h
            exact congrArg Sum.inl h
        | inr second => cases h
    | inr first =>
        cases second with
        | inl second => cases h
        | inr second =>
            simp only [Sum.inr.injEq, Fin.castSucc_inj] at h
            exact congrArg Sum.inr h

/-- The smaller inward ladder whose target is the larger layout's last borrow. -/
def smaller {b n : ℕ} (layout : InwardLadderLayout (b + 1) n) :
    InwardLadderLayout b n where
  wire := (prefixSlotEmbedding b).trans layout.wire

@[simp]
theorem smaller_controlWire {b n : ℕ} (layout : InwardLadderLayout (b + 1) n)
    (control : Fin (b + 2)) :
    layout.smaller.controlWire control = layout.controlWire control.castSucc := rfl

@[simp]
theorem smaller_workWire {b n : ℕ} (layout : InwardLadderLayout (b + 1) n)
    (work : Fin (b + 1)) :
    layout.smaller.workWire work = layout.workWire work.castSucc := rfl

@[simp]
theorem smaller_borrowedWire {b n : ℕ} (layout : InwardLadderLayout (b + 1) n)
    (borrowed : Fin b) :
    layout.smaller.borrowedWire borrowed = layout.borrowedWire borrowed.castSucc := rfl

@[simp]
theorem smaller_targetWire {b n : ℕ} (layout : InwardLadderLayout (b + 1) n) :
    layout.smaller.targetWire = layout.borrowedWire (Fin.last b) := rfl

/-- Forget the borrowed register and expose the established ordered-control API. -/
def orderedControlLayout {b n : ℕ} (layout : InwardLadderLayout b n) :
    OrderedControlLayout (b + 2) n where
  controlWire :=
    ⟨layout.controlWire, layout.controlWire_injective⟩
  targetWire := layout.targetWire
  control_ne_target := layout.controlWire_ne_targetWire

/-- The unordered positive-control set denoted by the logical controls. -/
def controlSet {b n : ℕ} (layout : InwardLadderLayout b n) :
    ControlSet layout.targetWire :=
  layout.orderedControlLayout.controlSet

@[simp]
theorem card_controlSet {b n : ℕ} (layout : InwardLadderLayout b n) :
    layout.controlSet.card = b + 2 := by
  exact OrderedControlLayout.card_controlSet layout.orderedControlLayout

/-! ## Trusted Toffoli nodes and chronological syntax -/

/-- The unique Toffoli in the no-borrow, two-control half ladder. -/
def baseToffoli {n : ℕ} (layout : InwardLadderLayout 0 n) : Primitive n :=
  Primitive.toffoli (layout.controlWire 0) (layout.controlWire 1) layout.targetWire
    (layout.controlWire_ne (by decide))
    (layout.controlWire_ne_targetWire 0)
    (layout.controlWire_ne_targetWire 1)

/-- The outer Toffoli added when one more control and borrowed wire are present. -/
def outerToffoli {b n : ℕ} (layout : InwardLadderLayout (b + 1) n) : Primitive n :=
  Primitive.toffoli
    (layout.controlWire (Fin.last (b + 2)))
    (layout.borrowedWire (Fin.last b)) layout.targetWire
    (layout.controlWire_ne_borrowedWire _ _)
    (layout.controlWire_ne_targetWire _)
    (layout.borrowedWire_ne_targetWire _)

@[simp]
theorem baseToffoli_kind {n : ℕ} (layout : InwardLadderLayout 0 n) :
    layout.baseToffoli.kind = .toffoli := rfl

@[simp]
theorem outerToffoli_kind {b n : ℕ} (layout : InwardLadderLayout (b + 1) n) :
    layout.outerToffoli.kind = .toffoli := rfl

/--
The palindromic first half of the dirty-borrowed construction.

For `b + 2` controls this has chronology `outer; smallerHalf; outer`.  It
performs the desired target flip but leaves the smaller half applied to the work
register.
-/
def halfLadderCircuit {n : ℕ} :
    (b : ℕ) → InwardLadderLayout b n → Circuit n
  | 0, layout => [layout.baseToffoli]
  | b + 1, layout =>
      Circuit.append [layout.outerToffoli]
        (Circuit.append (halfLadderCircuit b layout.smaller) [layout.outerToffoli])

/--
Lemma 7.2's complete dirty-borrowed circuit.

The index `b + 1` is the positive number of borrowed wires.  The second half
repeats the smaller palindrome and restores all of them.
-/
def inwardLadderCircuit {b n : ℕ} (layout : InwardLadderLayout (b + 1) n) : Circuit n :=
  Circuit.append (halfLadderCircuit (b + 1) layout)
    (halfLadderCircuit b layout.smaller)

@[simp]
theorem halfLadderCircuit_gateCount {b n : ℕ} (layout : InwardLadderLayout b n) :
    Circuit.gateCount (halfLadderCircuit b layout) = 2 * b + 1 := by
  revert layout
  induction b with
  | zero => intro layout; simp [halfLadderCircuit, Circuit.gateCount]
  | succ b ih =>
      intro layout
      simp [halfLadderCircuit, ih layout.smaller, Circuit.gateCount, Circuit.append]
      omega

@[simp]
theorem halfLadderCircuit_toffoliCount {b n : ℕ}
    (layout : InwardLadderLayout b n) :
    Circuit.kindCount .toffoli (halfLadderCircuit b layout) = 2 * b + 1 := by
  revert layout
  induction b with
  | zero => intro layout; simp [halfLadderCircuit, Circuit.kindCount]
  | succ b ih =>
      intro layout
      simp [halfLadderCircuit, ih layout.smaller, Circuit.kindCount, Circuit.append]
      omega

@[simp]
theorem inwardLadderCircuit_gateCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    Circuit.gateCount (inwardLadderCircuit layout) = 4 * (b + 1) := by
  simp [inwardLadderCircuit]
  omega

@[simp]
theorem inwardLadderCircuit_toffoliCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    Circuit.kindCount .toffoli (inwardLadderCircuit layout) = 4 * (b + 1) := by
  simp [inwardLadderCircuit]
  omega

end InwardLadderLayout

end Barenco.MultiControl
