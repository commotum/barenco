import Barenco.MultiControl.BorrowedSemantics
import Barenco.ThreeQubit.RelativePhase

/-!
# Signed relative-phase inward ladders

This module replaces every trusted Toffoli occurrence in the inward ladder by
the first seven-node relative-phase Toffoli circuit from Section 6.2.  It stops
at the signed half/full-ladder layer: no hybrid target block and no contextual
four-block cancellation is defined here.

The exact basis action records both the unchanged classical Toffoli permutation
and the input-dependent sign.  All phase exponents are values in Bool's Boolean
ring, so addition is XOR and multiplication is conjunction.
-/

namespace Barenco.MultiControl

open Barenco.ThreeQubit
open scoped BigOperators BooleanRing Matrix

namespace InwardLadderLayout

noncomputable section

/-! ## Boolean exponents and signs -/

/-- Convert a Boolean exponent to the complex sign `(-1)^exponent`. -/
def relativePhaseSign (exponent : Bool) : ℂ :=
  if exponent then -1 else 1

@[simp]
theorem relativePhaseSign_false : relativePhaseSign false = 1 := rfl

@[simp]
theorem relativePhaseSign_true : relativePhaseSign true = -1 := rfl

/-- XOR of Boolean exponents multiplies their signs. -/
theorem relativePhaseSign_add (first second : Bool) :
    relativePhaseSign (first + second) =
      relativePhaseSign first * relativePhaseSign second := by
  cases first <;> cases second <;> simp [relativePhaseSign]

/-- The `101` exponent of one relative-phase Toffoli occurrence. -/
def relativeToffoliExponent {n : ℕ} (first second target : Fin n)
    (input : Basis n) : Bool :=
  input first * (1 + input second) * input target

/-- The Circle-valued Section 6 witness is exactly the Boolean-ring sign. -/
theorem relativeToffoliPhase_eq_sign {n : ℕ}
    (first second target : Fin n) (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target) (input : Basis n) :
    (relativeToffoliPhase first second target hfirstTarget hsecondTarget
        (splitTarget target input).2 (input target) : ℂ) =
      relativePhaseSign (relativeToffoliExponent first second target input) := by
  rw [relativeToffoliPhase_input]
  cases hfirst : input first <;>
    cases hsecond : input second <;>
      cases htarget : input target <;>
        simp_all [relativeToffoliExponent, relativePhaseSign,
          Bool.add_eq_xor, Bool.mul_eq_and]

/-! ## Exact Boolean permutation bridge -/

/-- The Section 6 Toffoli output is the Boolean-ring update used by Lemma 7.2. -/
theorem toffoliOutput_eq_toffoliXorUpdate {n : ℕ}
    (first second target : Fin n) (input : Basis n) :
    toffoliOutput first second target input =
      toffoliXorUpdate first second target input := by
  rw [← toffoliBasisUpdate_eq_xorUpdate]
  cases hfirst : input first <;> cases hsecond : input second <;>
    simp [toffoliOutput, Primitive.toffoliBasisUpdate, hfirst, hsecond]

/-! ## Relative base and outer circuits -/

/-- Seven-node relative implementation of the base Toffoli. -/
def relativeBaseCircuit {n : ℕ} (layout : InwardLadderLayout 0 n) : Circuit n :=
  relativePhaseToffoliACircuit
    (layout.controlWire 0) (layout.controlWire 1) layout.targetWire
    (layout.controlWire_ne_targetWire 0)
    (layout.controlWire_ne_targetWire 1)

/-- Seven-node relative implementation of one recursive outer Toffoli. -/
def relativeOuterCircuit {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) : Circuit n :=
  relativePhaseToffoliACircuit
    (layout.controlWire (Fin.last (b + 2)))
    (layout.borrowedWire (Fin.last b)) layout.targetWire
    (layout.controlWire_ne_targetWire _)
    (layout.borrowedWire_ne_targetWire _)

/-- Closed Boolean exponent of the relative base occurrence. -/
def relativeBaseExponent {n : ℕ} (layout : InwardLadderLayout 0 n)
    (input : Basis n) : Bool :=
  input (layout.controlWire 0) *
    (1 + input (layout.controlWire 1)) * input layout.targetWire

/-- Boolean exponent of one relative outer occurrence. -/
def relativeOuterExponent {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) (input : Basis n) : Bool :=
  input (layout.controlWire (Fin.last (b + 2))) *
    (1 + input (layout.borrowedWire (Fin.last b))) *
      input layout.targetWire

/-- Exact signed basis action of the relative base circuit. -/
theorem eval_relativeBaseCircuit_mulVec_basisKet {n : ℕ}
    (layout : InwardLadderLayout 0 n) (input : Basis n) :
    (Circuit.eval layout.relativeBaseCircuit : Gate n) *ᵥ basisKet input =
      relativePhaseSign (layout.relativeBaseExponent input) •
        basisKet (baseUpdate layout input) := by
  rw [relativeBaseCircuit,
    relativePhaseToffoliACircuit_mulVec_basisKet _ _ _
      (layout.controlWire_ne (by decide))
      (layout.controlWire_ne_targetWire 0)
      (layout.controlWire_ne_targetWire 1)]
  rw [relativeToffoliPhase_eq_sign]
  rw [toffoliOutput_eq_toffoliXorUpdate]
  rfl

/-- Exact signed basis action of every relative outer circuit. -/
theorem eval_relativeOuterCircuit_mulVec_basisKet {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) (input : Basis n) :
    (Circuit.eval layout.relativeOuterCircuit : Gate n) *ᵥ basisKet input =
      relativePhaseSign (layout.relativeOuterExponent input) •
        basisKet (outerUpdate layout input) := by
  rw [relativeOuterCircuit,
    relativePhaseToffoliACircuit_mulVec_basisKet _ _ _
      (layout.controlWire_ne_borrowedWire _ _)
      (layout.controlWire_ne_targetWire _)
      (layout.borrowedWire_ne_targetWire _)]
  rw [relativeToffoliPhase_eq_sign]
  rw [toffoliOutput_eq_toffoliXorUpdate]
  rfl

/-! ## Recursive all-relative syntax -/

/--
Palindromic relative half: `outer; smallerHalf; outer`, with the seven-node
relative implementation substituted at every Toffoli occurrence.
-/
def relativeHalfLadderCircuit {n : ℕ} :
    (b : ℕ) → InwardLadderLayout b n → Circuit n
  | 0, layout => layout.relativeBaseCircuit
  | b + 1, layout =>
      Circuit.append layout.relativeOuterCircuit
        (Circuit.append (relativeHalfLadderCircuit b layout.smaller)
          layout.relativeOuterCircuit)

/-- Complete all-relative inward ladder for a positive borrowed count. -/
def relativeInwardLadderCircuit {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) : Circuit n :=
  Circuit.append (relativeHalfLadderCircuit (b + 1) layout)
    (relativeHalfLadderCircuit b layout.smaller)

/-! ## Syntax-derived occurrence and primitive counts -/

/-- Number of relative-Toffoli occurrences before seven-node expansion. -/
def relativeHalfOccurrenceCount : ℕ → ℕ
  | 0 => 1
  | b + 1 => relativeHalfOccurrenceCount b + 2

@[simp]
theorem relativeHalfOccurrenceCount_eq (b : ℕ) :
    relativeHalfOccurrenceCount b = 2 * b + 1 := by
  induction b with
  | zero => rfl
  | succ b ih => simp [relativeHalfOccurrenceCount, ih]; omega

/-- A half contains `2b+1` expanded relative-Toffoli occurrences. -/
@[simp]
theorem relativeHalfLadderCircuit_gateCount {b n : ℕ}
    (layout : InwardLadderLayout b n) :
    Circuit.gateCount (relativeHalfLadderCircuit b layout) =
      7 * (2 * b + 1) := by
  revert layout
  induction b with
  | zero => intro layout; simp [relativeHalfLadderCircuit, relativeBaseCircuit]
  | succ b ih =>
      intro layout
      simp [relativeHalfLadderCircuit, relativeOuterCircuit, ih]
      omega

@[simp]
theorem relativeHalfLadderCircuit_oneQubitCount {b n : ℕ}
    (layout : InwardLadderLayout b n) :
    Circuit.kindCount .oneQubit (relativeHalfLadderCircuit b layout) =
      4 * (2 * b + 1) := by
  revert layout
  induction b with
  | zero => intro layout; simp [relativeHalfLadderCircuit, relativeBaseCircuit]
  | succ b ih =>
      intro layout
      simp [relativeHalfLadderCircuit, relativeOuterCircuit, ih]
      omega

@[simp]
theorem relativeHalfLadderCircuit_cnotCount {b n : ℕ}
    (layout : InwardLadderLayout b n) :
    Circuit.kindCount .cnot (relativeHalfLadderCircuit b layout) =
      3 * (2 * b + 1) := by
  revert layout
  induction b with
  | zero => intro layout; simp [relativeHalfLadderCircuit, relativeBaseCircuit]
  | succ b ih =>
      intro layout
      simp [relativeHalfLadderCircuit, relativeOuterCircuit, ih]
      omega

@[simp]
theorem relativeHalfLadderCircuit_oneQubitCNOTCost {b n : ℕ}
    (layout : InwardLadderLayout b n) :
    Circuit.cost CostModel.oneQubitCNOT (relativeHalfLadderCircuit b layout) =
      some (7 * (2 * b + 1)) := by
  revert layout
  induction b with
  | zero => intro layout; simp [relativeHalfLadderCircuit, relativeBaseCircuit]
  | succ b ih =>
      intro layout
      simp [relativeHalfLadderCircuit, relativeOuterCircuit,
        Circuit.cost_append, Circuit.addCost, ih]
      omega

/-- A positive full ladder contains exactly `4(b+1)` relative occurrences. -/
def relativeInwardOccurrenceCount (b : ℕ) : ℕ :=
  relativeHalfOccurrenceCount (b + 1) + relativeHalfOccurrenceCount b

@[simp]
theorem relativeInwardOccurrenceCount_eq (b : ℕ) :
    relativeInwardOccurrenceCount b = 4 * (b + 1) := by
  simp [relativeInwardOccurrenceCount]
  omega

@[simp]
theorem relativeInwardLadderCircuit_gateCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    Circuit.gateCount (relativeInwardLadderCircuit layout) = 28 * (b + 1) := by
  simp [relativeInwardLadderCircuit]
  omega

@[simp]
theorem relativeInwardLadderCircuit_oneQubitCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    Circuit.kindCount .oneQubit (relativeInwardLadderCircuit layout) =
      16 * (b + 1) := by
  simp [relativeInwardLadderCircuit]
  omega

@[simp]
theorem relativeInwardLadderCircuit_cnotCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    Circuit.kindCount .cnot (relativeInwardLadderCircuit layout) =
      12 * (b + 1) := by
  simp [relativeInwardLadderCircuit]
  omega

@[simp]
theorem relativeInwardLadderCircuit_oneQubitCNOTCost {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    Circuit.cost CostModel.oneQubitCNOT (relativeInwardLadderCircuit layout) =
      some (28 * (b + 1)) := by
  simp [relativeInwardLadderCircuit, Circuit.cost_append, Circuit.addCost]
  omega

/-! ## Closed half-phase invariant -/

/--
Closed phase exponent of a relative half.  The successor term is the product of
all controls times the XOR of the newly linked work pair.
-/
def relativeHalfPhaseExponent {n : ℕ} :
    (b : ℕ) → InwardLadderLayout b n → Basis n → Bool
  | 0, layout, input => layout.relativeBaseExponent input
  | b + 1, layout, input =>
      relativeHalfPhaseExponent b layout.smaller input +
        controlProduct layout input *
          (input (layout.borrowedWire (Fin.last b)) + input layout.targetWire)

@[simp]
theorem relativeHalfPhaseExponent_zero {n : ℕ}
    (layout : InwardLadderLayout 0 n) (input : Basis n) :
    relativeHalfPhaseExponent 0 layout input = layout.relativeBaseExponent input :=
  rfl

/-- The audit recurrence for a positive relative half. -/
@[simp]
theorem relativeHalfPhaseExponent_succ {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) (input : Basis n) :
    relativeHalfPhaseExponent (b + 1) layout input =
      relativeHalfPhaseExponent b layout.smaller input +
        controlProduct layout input *
          (input (layout.borrowedWire (Fin.last b)) + input layout.targetWire) :=
  rfl

private theorem controlProduct_update_of_not_control {b n : ℕ}
    (layout : InwardLadderLayout b n) (outside : Fin n)
    (hcontrol : ∀ control, outside ≠ layout.controlWire control)
    (input : Basis n) (bit : Bool) :
    controlProduct layout (Function.update input outside bit) =
      controlProduct layout input := by
  apply Finset.prod_congr rfl
  intro control _
  exact Function.update_of_ne (Ne.symm (hcontrol control)) _ _

/-- The closed exponent ignores replacement of any wire outside its logical layout. -/
theorem relativeHalfPhaseExponent_update_of_outside {b n : ℕ}
    (layout : InwardLadderLayout b n) (outside : Fin n)
    (hcontrol : ∀ control, outside ≠ layout.controlWire control)
    (hwork : ∀ work, outside ≠ layout.workWire work)
    (input : Basis n) (bit : Bool) :
    relativeHalfPhaseExponent b layout (Function.update input outside bit) =
      relativeHalfPhaseExponent b layout input := by
  revert layout
  induction b with
  | zero =>
      intro layout
      rw [relativeHalfPhaseExponent_zero, relativeHalfPhaseExponent_zero]
      simp [relativeBaseExponent,
        Function.update_of_ne (Ne.symm (hcontrol 0)),
        Function.update_of_ne (Ne.symm (hcontrol 1)),
        Function.update_of_ne (Ne.symm (hwork (Fin.last 0)))]
  | succ b ih =>
      intro layout
      have hsmallControl : ∀ control,
          outside ≠ layout.smaller.controlWire control := by
        intro control
        simpa using hcontrol control.castSucc
      have hsmallWork : ∀ work,
          outside ≠ layout.smaller.workWire work := by
        intro work
        simpa using hwork work.castSucc
      have hborrowed : outside ≠ layout.borrowedWire (Fin.last b) :=
        hwork (Fin.last b).castSucc
      have htarget : outside ≠ layout.targetWire :=
        hwork (Fin.last (b + 1))
      rw [relativeHalfPhaseExponent_succ, relativeHalfPhaseExponent_succ]
      rw [ih layout.smaller hsmallControl hsmallWork]
      rw [controlProduct_update_of_not_control layout outside hcontrol]
      rw [Function.update_of_ne (Ne.symm hborrowed)]
      rw [Function.update_of_ne (Ne.symm htarget)]

/-- An outer update changes only a wire outside the smaller half's phase support. -/
@[simp]
theorem smaller_relativeHalfPhaseExponent_outerUpdate {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) (input : Basis n) :
    relativeHalfPhaseExponent b layout.smaller (outerUpdate layout input) =
      relativeHalfPhaseExponent b layout.smaller input := by
  rw [outerUpdate_eq_update]
  exact relativeHalfPhaseExponent_update_of_outside layout.smaller
    layout.targetWire (targetWire_ne_smaller_controlWire layout)
    (targetWire_ne_smaller_workWire layout) input _

/--
The two relative outer occurrences contribute exactly the new term in the
closed successor recurrence.
-/
theorem relativeOuterExponent_pair {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) (input : Basis n) :
    relativeOuterExponent layout input +
        relativeOuterExponent layout
          (halfLadderUpdate b layout.smaller (outerUpdate layout input)) =
      controlProduct layout input *
        (input (layout.borrowedWire (Fin.last b)) + input layout.targetWire) := by
  let afterOuter := outerUpdate layout input
  let afterSmaller := halfLadderUpdate b layout.smaller afterOuter
  have hlastControl :
      afterSmaller (layout.controlWire (Fin.last (b + 2))) =
        input (layout.controlWire (Fin.last (b + 2))) := by
    calc
      afterSmaller (layout.controlWire (Fin.last (b + 2))) =
          afterOuter (layout.controlWire (Fin.last (b + 2))) := by
            apply halfLadderUpdate_apply_of_not_work
            intro work
            exact layout.controlWire_ne_workWire _ work.castSucc
      _ = input (layout.controlWire (Fin.last (b + 2))) := by
            apply outerUpdate_apply_of_ne
            exact layout.controlWire_ne_targetWire _
  have hlastBorrow :
      afterSmaller (layout.borrowedWire (Fin.last b)) =
        input (layout.borrowedWire (Fin.last b)) +
          controlProduct layout.smaller input := by
    change halfLadderUpdate b layout.smaller afterOuter
        layout.smaller.targetWire = _
    rw [halfLadderUpdate_apply_target]
    rw [smaller_controlProduct_outerUpdate]
    dsimp [afterOuter]
    rw [outerUpdate_apply_of_ne]
    exact layout.borrowedWire_ne_targetWire _
  have htarget : afterSmaller layout.targetWire =
      input layout.targetWire +
        input (layout.controlWire (Fin.last (b + 2))) *
          input (layout.borrowedWire (Fin.last b)) := by
    calc
      afterSmaller layout.targetWire = afterOuter layout.targetWire := by
        apply halfLadderUpdate_apply_of_not_work
        exact targetWire_ne_smaller_workWire layout
      _ = _ := by
        dsimp [afterOuter]
        rw [outerUpdate_apply_target]
  dsimp [afterSmaller]
  rw [relativeOuterExponent, relativeOuterExponent,
    hlastControl, hlastBorrow, htarget, controlProduct_succ]
  generalize controlProduct layout.smaller input = q
  generalize input (layout.controlWire (Fin.last (b + 2))) = lastControl
  generalize input (layout.borrowedWire (Fin.last b)) = lastBorrow
  generalize input layout.targetWire = target
  cases q <;> cases lastControl <;> cases lastBorrow <;> cases target <;>
    decide

/-- The closed half exponent is invariant under the exact half permutation. -/
@[simp]
theorem relativeHalfPhaseExponent_halfLadderUpdate {b n : ℕ}
    (layout : InwardLadderLayout b n) (input : Basis n) :
    relativeHalfPhaseExponent b layout (halfLadderUpdate b layout input) =
      relativeHalfPhaseExponent b layout input := by
  revert layout input
  induction b with
  | zero =>
      intro layout input
      cases hfirst : input (layout.controlWire 0) <;>
        cases hsecond : input (layout.controlWire 1) <;>
          cases htarget : input layout.targetWire <;>
            simp [relativeHalfPhaseExponent, relativeBaseExponent,
              halfLadderUpdate, baseUpdate, toffoliXorUpdate,
              layout.controlWire_ne_targetWire 0,
              layout.controlWire_ne_targetWire 1,
              hfirst, hsecond, htarget, Bool.add_eq_xor, Bool.mul_eq_and]
  | succ b ih =>
      intro layout input
      have hsmallPhase :
          relativeHalfPhaseExponent b layout.smaller
              (halfLadderUpdate (b + 1) layout input) =
            relativeHalfPhaseExponent b layout.smaller input := by
        rw [halfLadderUpdate_succ_eq_update]
        rw [relativeHalfPhaseExponent_update_of_outside layout.smaller
          layout.targetWire (targetWire_ne_smaller_controlWire layout)
          (targetWire_ne_smaller_workWire layout)]
        exact ih layout.smaller input
      have hborrowed :
          halfLadderUpdate (b + 1) layout input
              (layout.borrowedWire (Fin.last b)) =
            input (layout.borrowedWire (Fin.last b)) +
              controlProduct layout.smaller input := by
        rw [halfLadderUpdate_succ_eq_update]
        rw [Function.update_of_ne (layout.borrowedWire_ne_targetWire _)]
        change halfLadderUpdate b layout.smaller input layout.smaller.targetWire = _
        rw [halfLadderUpdate_apply_target]
      rw [relativeHalfPhaseExponent_succ, relativeHalfPhaseExponent_succ]
      rw [hsmallPhase, controlProduct_halfLadderUpdate, hborrowed,
        halfLadderUpdate_apply_target, controlProduct_succ]
      generalize controlProduct layout.smaller input = q
      generalize input (layout.controlWire (Fin.last (b + 2))) = lastControl
      generalize input (layout.borrowedWire (Fin.last b)) = lastBorrow
      generalize input layout.targetWire = target
      cases q <;> cases lastControl <;> cases lastBorrow <;> cases target <;>
        decide

end

end InwardLadderLayout

end Barenco.MultiControl
