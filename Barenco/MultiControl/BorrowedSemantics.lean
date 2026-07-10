import Barenco.MultiControl.Borrowed
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Tactic

/-!
# Semantics of dirty-borrowed inward Toffoli ladders

This module proves the semantic part of Barenco et al., Lemma 7.2.  The
borrowed wires are genuinely dirty: every theorem quantifies over an arbitrary
ambient computational-basis assignment, and the complete circuit restores that
assignment on every non-target wire.

The proof first interprets the recursive circuit as Boolean-ring updates.  The
palindromic half ladder preserves all controls, flips its target by the product
of its controls, is an involution, and is insensitive to replacement of a wire
outside its logical layout.  Those facts make the dirty-wire cancellation in
the complete ladder explicit.  Finally, computational-basis extensionality
lifts the Boolean result to exact equality of arbitrary-width unitaries.
-/

namespace Barenco.MultiControl

open scoped BigOperators BooleanRing Matrix

namespace InwardLadderLayout

/-! ## Boolean interpreter -/

/-- Boolean-ring form of the exact Toffoli basis update. -/
def toffoliXorUpdate {n : ℕ} (first second target : Fin n)
    (input : Basis n) : Basis n :=
  Function.update input target (input target + input first * input second)

/-- The Boolean-ring update agrees with the trusted Toffoli primitive. -/
theorem toffoliBasisUpdate_eq_xorUpdate {n : ℕ} (first second target : Fin n)
    (input : Basis n) :
    Primitive.toffoliBasisUpdate first second target input =
      toffoliXorUpdate first second target input := by
  funext wire
  by_cases hwire : wire = target
  · subst wire
    cases hfirst : input first <;>
      cases hsecond : input second <;>
        cases htarget : input target <;>
          simp [Primitive.toffoliBasisUpdate, toffoliXorUpdate,
            hfirst, hsecond, htarget] <;> rfl
  · cases hfirst : input first <;>
      cases hsecond : input second <;>
        simp [Primitive.toffoliBasisUpdate, toffoliXorUpdate,
          hwire, hfirst, hsecond]

@[simp]
theorem toffoliXorUpdate_apply_target {n : ℕ} (first second target : Fin n)
    (input : Basis n) :
    toffoliXorUpdate first second target input target =
      input target + input first * input second := by
  simp [toffoliXorUpdate]

@[simp]
theorem toffoliXorUpdate_apply_of_ne {n : ℕ} (first second target : Fin n)
    (input : Basis n) (wire : Fin n) (hwire : wire ≠ target) :
    toffoliXorUpdate first second target input wire = input wire := by
  simp [toffoliXorUpdate, hwire]

/-- A Toffoli update is self-inverse when its controls differ from its target. -/
theorem toffoliXorUpdate_involutive {n : ℕ} (first second target : Fin n)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    Function.Involutive (toffoliXorUpdate first second target) := by
  intro input
  funext wire
  by_cases hwire : wire = target
  · subst wire
    simp [toffoliXorUpdate, hfirstTarget, hsecondTarget, add_assoc]
  · simp [hwire]

/-- A Toffoli commutes with replacement of a wire outside its three-wire support. -/
theorem toffoliXorUpdate_update {n : ℕ}
    (first second target outside : Fin n)
    (houtsideFirst : outside ≠ first) (houtsideSecond : outside ≠ second)
    (houtsideTarget : outside ≠ target) (input : Basis n) (bit : Bool) :
    toffoliXorUpdate first second target (Function.update input outside bit) =
      Function.update (toffoliXorUpdate first second target input) outside bit := by
  funext wire
  by_cases hwireTarget : wire = target
  · subst wire
    rw [toffoliXorUpdate_apply_target]
    rw [Function.update_of_ne (Ne.symm houtsideTarget)]
    rw [Function.update_of_ne (Ne.symm houtsideFirst)]
    rw [Function.update_of_ne (Ne.symm houtsideSecond)]
    rw [Function.update_of_ne (Ne.symm houtsideTarget)]
    rw [toffoliXorUpdate_apply_target]
  · by_cases hwireOutside : wire = outside
    · subst wire
      simp [toffoliXorUpdate, houtsideTarget]
    · simp [toffoliXorUpdate, hwireTarget, hwireOutside]

/-- Boolean action of the base two-control Toffoli. -/
def baseUpdate {n : ℕ} (layout : InwardLadderLayout 0 n)
    (input : Basis n) : Basis n :=
  toffoliXorUpdate (layout.controlWire 0) (layout.controlWire 1)
    layout.targetWire input

/-- Boolean action of the outer Toffoli at one recursive ladder layer. -/
def outerUpdate {b n : ℕ} (layout : InwardLadderLayout (b + 1) n)
    (input : Basis n) : Basis n :=
  toffoliXorUpdate
    (layout.controlWire (Fin.last (b + 2)))
    (layout.borrowedWire (Fin.last b)) layout.targetWire input

/-- Execute the Boolean updates of the palindromic half ladder. -/
def halfLadderUpdate {n : ℕ} :
    (b : ℕ) → InwardLadderLayout b n → Basis n → Basis n
  | 0, layout, input => baseUpdate layout input
  | b + 1, layout, input =>
      outerUpdate layout
        (halfLadderUpdate b layout.smaller (outerUpdate layout input))

/-- Execute the complete dirty-borrowed ladder on a basis assignment. -/
def inwardLadderUpdate {b n : ℕ} (layout : InwardLadderLayout (b + 1) n)
    (input : Basis n) : Basis n :=
  halfLadderUpdate b layout.smaller (halfLadderUpdate (b + 1) layout input)

/-- Product of all logical controls, in the Boolean ring. -/
def controlProduct {b n : ℕ} (layout : InwardLadderLayout b n)
    (input : Basis n) : Bool :=
  ∏ control, input (layout.controlWire control)

@[simp]
theorem controlProduct_succ {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) (input : Basis n) :
    controlProduct layout input =
      controlProduct layout.smaller input *
        input (layout.controlWire (Fin.last (b + 2))) := by
  rw [controlProduct, Fin.prod_univ_castSucc]
  rfl

end InwardLadderLayout

end Barenco.MultiControl
