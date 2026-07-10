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

/-! ## Structural half-ladder invariants -/

@[simp]
theorem baseUpdate_apply_target {n : ℕ} (layout : InwardLadderLayout 0 n)
    (input : Basis n) :
    baseUpdate layout input layout.targetWire =
      input layout.targetWire +
        input (layout.controlWire 0) * input (layout.controlWire 1) := by
  simp [baseUpdate]

@[simp]
theorem outerUpdate_apply_target {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) (input : Basis n) :
    outerUpdate layout input layout.targetWire =
      input layout.targetWire +
        input (layout.controlWire (Fin.last (b + 2))) *
          input (layout.borrowedWire (Fin.last b)) := by
  simp [outerUpdate]

@[simp]
theorem outerUpdate_apply_of_ne {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) (input : Basis n)
    (wire : Fin n) (hwire : wire ≠ layout.targetWire) :
    outerUpdate layout input wire = input wire := by
  simp [outerUpdate, hwire]

/-- Every half ladder changes only its work-register wires. -/
theorem halfLadderUpdate_apply_of_not_work {b n : ℕ}
    (layout : InwardLadderLayout b n) (input : Basis n) (wire : Fin n)
    (hwork : ∀ work, wire ≠ layout.workWire work) :
    halfLadderUpdate b layout input wire = input wire := by
  revert layout input
  induction b with
  | zero =>
      intro layout input hwork
      exact toffoliXorUpdate_apply_of_ne _ _ _ _ wire (hwork (Fin.last 0))
  | succ b ih =>
      intro layout input hwork
      have htarget : wire ≠ layout.targetWire := hwork (Fin.last (b + 1))
      rw [halfLadderUpdate, outerUpdate_apply_of_ne layout _ wire htarget]
      rw [ih layout.smaller (outerUpdate layout input)]
      · exact outerUpdate_apply_of_ne layout input wire htarget
      · intro work
        simpa using hwork work.castSucc

/-- In particular, a half ladder preserves every logical control. -/
@[simp]
theorem halfLadderUpdate_apply_controlWire {b n : ℕ}
    (layout : InwardLadderLayout b n) (input : Basis n)
    (control : Fin (b + 2)) :
    halfLadderUpdate b layout input (layout.controlWire control) =
      input (layout.controlWire control) := by
  apply halfLadderUpdate_apply_of_not_work
  exact fun work => layout.controlWire_ne_workWire control work

/-- Consequently, the conjunction of the controls is invariant under a half ladder. -/
@[simp]
theorem controlProduct_halfLadderUpdate {b n : ℕ}
    (layout : InwardLadderLayout b n) (input : Basis n) :
    controlProduct layout (halfLadderUpdate b layout input) =
      controlProduct layout input := by
  apply Finset.prod_congr rfl
  intro control _
  exact halfLadderUpdate_apply_controlWire layout input control

/-- An outer update preserves the conjunction of the controls of its smaller layout. -/
@[simp]
theorem smaller_controlProduct_outerUpdate {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) (input : Basis n) :
    controlProduct layout.smaller (outerUpdate layout input) =
      controlProduct layout.smaller input := by
  apply Finset.prod_congr rfl
  intro control _
  rw [smaller_controlWire]
  exact outerUpdate_apply_of_ne layout input _
    (layout.controlWire_ne_targetWire control.castSucc)

/-- The base half ladder is an involution. -/
theorem baseUpdate_involutive {n : ℕ} (layout : InwardLadderLayout 0 n) :
    Function.Involutive (baseUpdate layout) := by
  exact toffoliXorUpdate_involutive _ _ _
    (layout.controlWire_ne_targetWire 0)
    (layout.controlWire_ne_targetWire 1)

/-- Every outer Toffoli update is an involution. -/
theorem outerUpdate_involutive {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    Function.Involutive (outerUpdate layout) := by
  exact toffoliXorUpdate_involutive _ _ _
    (layout.controlWire_ne_targetWire _)
    (layout.borrowedWire_ne_targetWire _)

/-- The recursive palindrome is self-inverse on the full ambient assignment. -/
theorem halfLadderUpdate_involutive {b n : ℕ}
    (layout : InwardLadderLayout b n) :
    Function.Involutive (halfLadderUpdate b layout) := by
  revert layout
  induction b with
  | zero =>
      intro layout
      exact baseUpdate_involutive layout
  | succ b ih =>
      intro layout input
      simp only [halfLadderUpdate]
      rw [outerUpdate_involutive layout]
      rw [ih layout.smaller]
      rw [outerUpdate_involutive layout]

/--
A half ladder commutes with replacement of any ambient wire outside all of its
logical controls and work wires.
-/
theorem halfLadderUpdate_update_of_outside {b n : ℕ}
    (layout : InwardLadderLayout b n) (outside : Fin n)
    (hcontrol : ∀ control, outside ≠ layout.controlWire control)
    (hwork : ∀ work, outside ≠ layout.workWire work)
    (input : Basis n) (bit : Bool) :
    halfLadderUpdate b layout (Function.update input outside bit) =
      Function.update (halfLadderUpdate b layout input) outside bit := by
  revert layout input
  induction b with
  | zero =>
      intro layout hcontrol hwork input
      exact toffoliXorUpdate_update _ _ _ outside
        (hcontrol 0) (hcontrol 1) (hwork (Fin.last 0)) input bit
  | succ b ih =>
      intro layout hcontrol hwork input
      have houter : ∀ state : Basis n,
          outerUpdate layout (Function.update state outside bit) =
            Function.update (outerUpdate layout state) outside bit := by
        intro state
        exact toffoliXorUpdate_update _ _ _ outside
          (hcontrol (Fin.last (b + 2)))
          (hwork (Fin.last b).castSucc)
          (hwork (Fin.last (b + 1))) state bit
      have hsmallControl : ∀ control,
          outside ≠ layout.smaller.controlWire control := by
        intro control
        simpa using hcontrol control.castSucc
      have hsmallWork : ∀ work,
          outside ≠ layout.smaller.workWire work := by
        intro work
        simpa using hwork work.castSucc
      simp only [halfLadderUpdate]
      rw [houter input]
      rw [ih layout.smaller hsmallControl hsmallWork (outerUpdate layout input)]
      rw [houter (halfLadderUpdate b layout.smaller (outerUpdate layout input))]

@[simp]
theorem controlProduct_zero {n : ℕ} (layout : InwardLadderLayout 0 n)
    (input : Basis n) :
    controlProduct layout input =
      input (layout.controlWire 0) * input (layout.controlWire 1) := by
  rw [controlProduct, Fin.prod_univ_two]

/-- The larger target is disjoint from every control of the prefix layout. -/
theorem targetWire_ne_smaller_controlWire {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) (control : Fin (b + 2)) :
    layout.targetWire ≠ layout.smaller.controlWire control := by
  simpa using (layout.controlWire_ne_targetWire control.castSucc).symm

/-- The larger target is disjoint from every work wire of the prefix layout. -/
theorem targetWire_ne_smaller_workWire {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) (work : Fin (b + 1)) :
    layout.targetWire ≠ layout.smaller.workWire work := by
  change layout.workWire (Fin.last (b + 1)) ≠ layout.workWire work.castSucc
  exact (layout.workWire_ne work.castSucc_ne_last).symm

/-- The outer Toffoli is literally a single update of the larger target. -/
theorem outerUpdate_eq_update {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) (input : Basis n) :
    outerUpdate layout input =
      Function.update input layout.targetWire
        (input layout.targetWire +
          input (layout.controlWire (Fin.last (b + 2))) *
            input (layout.borrowedWire (Fin.last b))) := by
  rfl

/--
The half ladder flips its target by the conjunction of all its controls.  It may
also change borrowed wires; their exact intermediate values are intentionally
not part of this invariant.
-/
@[simp]
theorem halfLadderUpdate_apply_target {b n : ℕ}
    (layout : InwardLadderLayout b n) (input : Basis n) :
    halfLadderUpdate b layout input layout.targetWire =
      input layout.targetWire + controlProduct layout input := by
  revert layout input
  induction b with
  | zero =>
      intro layout input
      simp [halfLadderUpdate]
  | succ b ih =>
      intro layout input
      let firstOuter := outerUpdate layout input
      let smallerHalf := halfLadderUpdate b layout.smaller firstOuter
      have hlargeTarget : smallerHalf layout.targetWire =
          firstOuter layout.targetWire := by
        apply halfLadderUpdate_apply_of_not_work
        exact targetWire_ne_smaller_workWire layout
      have hlastControl :
          smallerHalf (layout.controlWire (Fin.last (b + 2))) =
            input (layout.controlWire (Fin.last (b + 2))) := by
        calc
          smallerHalf (layout.controlWire (Fin.last (b + 2))) =
              firstOuter (layout.controlWire (Fin.last (b + 2))) := by
                apply halfLadderUpdate_apply_of_not_work
                intro work
                exact layout.controlWire_ne_workWire _ work.castSucc
          _ = input (layout.controlWire (Fin.last (b + 2))) := by
                apply outerUpdate_apply_of_ne
                exact layout.controlWire_ne_targetWire _
      have hsmallerTarget :
          smallerHalf (layout.borrowedWire (Fin.last b)) =
            input (layout.borrowedWire (Fin.last b)) +
              controlProduct layout.smaller input := by
        change halfLadderUpdate b layout.smaller firstOuter
            layout.smaller.targetWire =
          input layout.smaller.targetWire + controlProduct layout.smaller input
        rw [ih layout.smaller firstOuter]
        rw [smaller_controlProduct_outerUpdate]
        dsimp [firstOuter]
        rw [outerUpdate_apply_of_ne]
        exact layout.borrowedWire_ne_targetWire _
      change outerUpdate layout smallerHalf layout.targetWire = _
      rw [outerUpdate_apply_target, hlargeTarget, hlastControl, hsmallerTarget]
      dsimp [firstOuter]
      rw [outerUpdate_apply_target]
      rw [controlProduct_succ]
      rw [mul_add]
      calc
        (input layout.targetWire +
              input (layout.controlWire (Fin.last (b + 2))) *
                input (layout.borrowedWire (Fin.last b))) +
            (input (layout.controlWire (Fin.last (b + 2))) *
                input (layout.borrowedWire (Fin.last b)) +
              input (layout.controlWire (Fin.last (b + 2))) *
                controlProduct layout.smaller input) =
            input layout.targetWire +
                (input (layout.controlWire (Fin.last (b + 2))) *
                    input (layout.borrowedWire (Fin.last b)) +
                  input (layout.controlWire (Fin.last (b + 2))) *
                    input (layout.borrowedWire (Fin.last b))) +
              input (layout.controlWire (Fin.last (b + 2))) *
                controlProduct layout.smaller input := by abel
        _ = input layout.targetWire +
              input (layout.controlWire (Fin.last (b + 2))) *
                controlProduct layout.smaller input := by simp
        _ = input layout.targetWire +
              controlProduct layout.smaller input *
                input (layout.controlWire (Fin.last (b + 2))) := by
              rw [mul_comm]

/--
Recursive normal form for a positive half ladder: the smaller half remains on
the prefix work register, while the larger target receives exactly the full
control product.
-/
theorem halfLadderUpdate_succ_eq_update {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) (input : Basis n) :
    halfLadderUpdate (b + 1) layout input =
      Function.update (halfLadderUpdate b layout.smaller input)
        layout.targetWire
        (input layout.targetWire + controlProduct layout input) := by
  funext wire
  by_cases hwire : wire = layout.targetWire
  · subst wire
    simp
  · rw [halfLadderUpdate, outerUpdate_apply_of_ne layout _ wire hwire]
    rw [outerUpdate_eq_update]
    rw [halfLadderUpdate_update_of_outside layout.smaller layout.targetWire
      (targetWire_ne_smaller_controlWire layout)
      (targetWire_ne_smaller_workWire layout)]
    simp [hwire]

/-! ## Complete dirty-wire restoration -/

/--
Exact Boolean action of the complete dirty-borrowed construction.  Only the
named target changes; every borrowed wire and every spectator is restored.
-/
theorem inwardLadderUpdate_eq_update {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) (input : Basis n) :
    inwardLadderUpdate layout input =
      Function.update input layout.targetWire
        (input layout.targetWire + controlProduct layout input) := by
  rw [inwardLadderUpdate, halfLadderUpdate_succ_eq_update]
  rw [halfLadderUpdate_update_of_outside layout.smaller layout.targetWire
    (targetWire_ne_smaller_controlWire layout)
    (targetWire_ne_smaller_workWire layout)]
  rw [halfLadderUpdate_involutive]

/-- Every non-target ambient wire is restored, with no clean-borrow assumption. -/
@[simp]
theorem inwardLadderUpdate_apply_of_ne {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) (input : Basis n)
    (wire : Fin n) (hwire : wire ≠ layout.targetWire) :
    inwardLadderUpdate layout input wire = input wire := by
  rw [inwardLadderUpdate_eq_update]
  exact Function.update_of_ne hwire _ _

/-- The complete ladder flips the target by the product of all controls. -/
@[simp]
theorem inwardLadderUpdate_apply_target {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) (input : Basis n) :
    inwardLadderUpdate layout input layout.targetWire =
      input layout.targetWire + controlProduct layout input := by
  rw [inwardLadderUpdate_eq_update, Function.update_self]

/-- Every dirty borrowed wire is returned to its arbitrary initial value. -/
@[simp]
theorem inwardLadderUpdate_apply_borrowedWire {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) (input : Basis n)
    (borrowed : Fin (b + 1)) :
    inwardLadderUpdate layout input (layout.borrowedWire borrowed) =
      input (layout.borrowedWire borrowed) := by
  apply inwardLadderUpdate_apply_of_ne
  exact layout.borrowedWire_ne_targetWire borrowed

/-! ## Circuit-to-Boolean bridge -/

/-- The trusted base primitive realizes the Boolean base update exactly. -/
@[simp]
theorem baseToffoli_denotation_mulVec_basisKet {n : ℕ}
    (layout : InwardLadderLayout 0 n) (input : Basis n) :
    (layout.baseToffoli.denotation : Gate n) *ᵥ basisKet input =
      basisKet (baseUpdate layout input) := by
  rw [baseToffoli, Primitive.toffoli_denotation_mulVec_basisKet,
    toffoliBasisUpdate_eq_xorUpdate]
  rfl

/-- Every trusted outer primitive realizes its Boolean outer update exactly. -/
@[simp]
theorem outerToffoli_denotation_mulVec_basisKet {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) (input : Basis n) :
    (layout.outerToffoli.denotation : Gate n) *ᵥ basisKet input =
      basisKet (outerUpdate layout input) := by
  rw [outerToffoli, Primitive.toffoli_denotation_mulVec_basisKet,
    toffoliBasisUpdate_eq_xorUpdate]
  rfl

/-- Exact arbitrary-width basis action of every palindromic half circuit. -/
theorem eval_halfLadderCircuit_mulVec_basisKet {b n : ℕ}
    (layout : InwardLadderLayout b n) (input : Basis n) :
    (Circuit.eval (halfLadderCircuit b layout) : Gate n) *ᵥ basisKet input =
      basisKet (halfLadderUpdate b layout input) := by
  revert layout input
  induction b with
  | zero =>
      intro layout input
      rw [halfLadderCircuit, Circuit.eval_singleton,
        baseToffoli_denotation_mulVec_basisKet]
      rfl
  | succ b ih =>
      intro layout input
      rw [halfLadderCircuit, Circuit.eval_append, Circuit.eval_append]
      simp only [Submonoid.coe_mul, Circuit.eval_singleton]
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      rw [outerToffoli_denotation_mulVec_basisKet]
      rw [ih layout.smaller]
      rw [outerToffoli_denotation_mulVec_basisKet]
      rfl

/-- Exact arbitrary-width basis action of the complete dirty-borrowed circuit. -/
theorem eval_inwardLadderCircuit_mulVec_basisKet {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) (input : Basis n) :
    (Circuit.eval (inwardLadderCircuit layout) : Gate n) *ᵥ basisKet input =
      basisKet (inwardLadderUpdate layout input) := by
  rw [inwardLadderCircuit, Circuit.eval_append]
  simp only [Submonoid.coe_mul]
  rw [← Matrix.mulVec_mulVec]
  rw [eval_halfLadderCircuit_mulVec_basisKet]
  rw [eval_halfLadderCircuit_mulVec_basisKet]
  rfl

/-! ## Identification with positive-controlled Pauli-X -/

private theorem boolFinsetProduct_eq_true_iff {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → Bool) :
    (∏ i ∈ s, f i) = true ↔ ∀ i ∈ s, f i = true := by
  induction s using Finset.induction_on with
  | empty => simp [Bool.one_eq_true]
  | @insert element s hnotMem ih =>
      rw [Finset.prod_insert hnotMem, Bool.mul_eq_and, Bool.and_eq_true, ih]
      simp

/-- The Boolean control product is true exactly when every logical control is true. -/
theorem controlProduct_eq_true_iff {b n : ℕ}
    (layout : InwardLadderLayout b n) (input : Basis n) :
    controlProduct layout input = true ↔
      ∀ control, input (layout.controlWire control) = true := by
  rw [controlProduct]
  simpa using boolFinsetProduct_eq_true_iff
    (Finset.univ : Finset (Fin (b + 2)))
    (fun control => input (layout.controlWire control))

/-- The unordered `ControlSet` truth condition is the same Boolean product. -/
theorem all_controlSet_true_iff_controlProduct_eq_true {b n : ℕ}
    (layout : InwardLadderLayout b n) (input : Basis n) :
    (∀ wire ∈ layout.controlSet, input wire = true) ↔
      controlProduct layout input = true := by
  change (∀ wire ∈ layout.orderedControlLayout.controlSet,
      input wire = true) ↔ _
  rw [layout.orderedControlLayout.all_controls_iff]
  change (∀ control, input (layout.controlWire control) = true) ↔ _
  exact (controlProduct_eq_true_iff layout input).symm

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

/--
The library's positive-controlled Pauli-X has exactly the Boolean action used by
the dirty-borrowed construction.
-/
theorem positiveControlledUnitary_pauliX_mulVec_basisKet {b n : ℕ}
    (layout : InwardLadderLayout b n) (input : Basis n) :
    (positiveControlledUnitary layout.targetWire layout.controlSet pauliX : Gate n) *ᵥ
        basisKet input =
      basisKet
        (Function.update input layout.targetWire
          (input layout.targetWire + controlProduct layout input)) := by
  rw [coe_positiveControlledUnitary, positiveControlledRaw_truthTable]
  by_cases hall : ∀ wire ∈ layout.controlSet, input wire = true
  · rw [if_pos hall]
    have hproduct : controlProduct layout input = true :=
      (all_controlSet_true_iff_controlProduct_eq_true layout input).mp hall
    rw [hproduct, update_add_true_eq_setTarget_not]
    simpa [xRaw] using xRaw_mulVec_basisKet layout.targetWire input
  · rw [if_neg hall]
    have hproduct : controlProduct layout input = false := by
      apply Bool.eq_false_of_not_eq_true
      intro htrue
      exact hall
        ((all_controlSet_true_iff_controlProduct_eq_true layout input).mpr htrue)
    rw [hproduct, update_add_false_eq_self]

/--
Barenco Lemma 7.2: for every positive number of dirty borrowed wires, the
counted recursive circuit is exactly the corresponding positive multi-controlled
Pauli-X on the full ambient register.
-/
@[simp]
theorem eval_inwardLadderCircuit {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    Circuit.eval (inwardLadderCircuit layout) =
      positiveControlledUnitary layout.targetWire layout.controlSet pauliX := by
  apply Subtype.ext
  rw [matrix_eq_iff_mulVec_basisKet_eq]
  intro input
  rw [eval_inwardLadderCircuit_mulVec_basisKet, inwardLadderUpdate_eq_update,
    positiveControlledUnitary_pauliX_mulVec_basisKet]

end InwardLadderLayout

end Barenco.MultiControl
