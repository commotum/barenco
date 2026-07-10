import Barenco.ControlledCircuit.Phase
import Barenco.OneQubit.Roots
import Barenco.Cost

/-!
# Barenco Lemma 6.1: a doubly controlled one-qubit gate

This file reconstructs the five-node macro circuit from Barenco et al., Lemma
6.1 on three named, pairwise distinct wires in an arbitrary ambient register.
The circuit list is chronological:

`C₂(V); CNOT(1,2); C₂(V⁻¹); CNOT(1,2); C₁(V)`.

Here `Cᵢ` controls the final target from control wire `i`; the two CNOTs act
from the first control onto the second.  They restore the second wire exactly.
The selected-root wrapper uses the finite-unitary square root from Stage 4.

The controlled nodes in this file are deliberate macros.  Their five-node
structural count is not a one-qubit+CNOT cost; Corollary 6.2 requires a separate
explicit expansion.
-/

namespace Barenco.ThreeQubit

open Barenco.OneQubit
open Barenco.ControlledCircuit
open scoped Matrix

noncomputable section

/-- The unordered pair of positive controls used by a doubly controlled gate. -/
def twoControlSet {n : ℕ} (first second target : Fin n)
    (hfirst : first ≠ target) (hsecond : second ≠ target) : ControlSet target :=
  {⟨first, hfirst⟩, ⟨second, hsecond⟩}

/-! ## Disjoint-wire and CNOT conjugation algebra -/

/-- Expand a target-local basis column as a sum over its two output target bits. -/
private theorem localRaw_mulVec_basisKet_eq_sum {n : ℕ} (target : Fin n)
    (U : QubitMatrix) (x : Basis n) :
    localRaw target U *ᵥ basisKet x =
      ∑ bit : Bool, U bit (x target) • basisKet (setTarget target x bit) := by
  rw [localRaw_mulVec_basisKet]
  funext row
  by_cases hagree : AgreeOff target row x
  · rw [if_pos hagree]
    have heq : ∀ bit : Bool,
        row = setTarget target x bit ↔ row target = bit := by
      intro bit
      exact (eq_setTarget_iff target x row bit).trans (and_iff_right hagree)
    cases hrow : row target <;>
      simp [basisKet_apply, heq, hrow]
  · rw [if_neg hagree]
    have hne : ∀ bit : Bool, row ≠ setTarget target x bit := by
      intro bit hrow
      apply hagree
      rw [hrow]
      intro i hi
      exact setTarget_apply_of_ne target x bit i hi
    simp [basisKet_apply, hne]

/-- Computational-basis update performed by a CNOT. -/
private def cnotUpdate {n : ℕ} (control target : Fin n) (x : Basis n) : Basis n :=
  if x control then setTarget target x (!x target) else x

@[simp]
private theorem cnotUpdate_apply_control {n : ℕ} (control target : Fin n)
    (h : control ≠ target) (x : Basis n) :
    cnotUpdate control target x control = x control := by
  cases hcontrol : x control <;> simp [cnotUpdate, hcontrol, h]

@[simp]
private theorem cnotUpdate_apply_target {n : ℕ} (control target : Fin n)
    (x : Basis n) :
    cnotUpdate control target x target =
      if x control then !x target else x target := by
  cases hcontrol : x control <;> simp [cnotUpdate, hcontrol]

@[simp]
private theorem cnotUpdate_apply_of_ne {n : ℕ} (control target : Fin n)
    (x : Basis n) (wire : Fin n) (h : wire ≠ target) :
    cnotUpdate control target x wire = x wire := by
  cases hcontrol : x control <;> simp [cnotUpdate, hcontrol, h]

@[simp]
private theorem cnotUpdate_involutive {n : ℕ} (control target : Fin n)
    (h : control ≠ target) (x : Basis n) :
    cnotUpdate control target (cnotUpdate control target x) = x := by
  funext wire
  by_cases hw : wire = target
  · subst wire
    cases hcontrol : x control <;> simp [h, hcontrol, cnotUpdate]
  · simp [hw]

@[simp]
private theorem cnotRaw_mulVec_basisKet' {n : ℕ} (control target : Fin n)
    (h : control ≠ target) (x : Basis n) :
    cnotRaw control target h *ᵥ basisKet x =
      basisKet (cnotUpdate control target x) := by
  simpa [cnotUpdate] using cnotRaw_mulVec_basisKet control target h x

/--
A CNOT commutes with a one-qubit matrix on a third, distinct wire.

This disjoint-support law is also used to justify the cancellations in
Corollary 6.2; the paper's cancellable gates are separated by such CNOTs in the
serialized circuit.
-/
theorem cnotRaw_commute_localRaw {n : ℕ}
    (control cnotTarget localTarget : Fin n)
    (hct : control ≠ cnotTarget) (hcl : control ≠ localTarget)
    (htl : cnotTarget ≠ localTarget) (U : QubitMatrix) :
    cnotRaw control cnotTarget hct * localRaw localTarget U =
      localRaw localTarget U * cnotRaw control cnotTarget hct := by
  rw [matrix_eq_iff_mulVec_basisKet_eq]
  intro x
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    localRaw_mulVec_basisKet_eq_sum, cnotRaw_mulVec_basisKet']
  rw [Matrix.mulVec_sum]
  simp_rw [Matrix.mulVec_smul, cnotRaw_mulVec_basisKet']
  rw [localRaw_mulVec_basisKet_eq_sum]
  apply Finset.sum_congr rfl
  intro bit _hbit
  rw [cnotUpdate_apply_of_ne control cnotTarget x localTarget htl.symm]
  congr 1
  apply congrArg basisKet
  funext wire
  by_cases hw : wire = cnotTarget
  · subst wire
    simp [hcl, htl]
  · by_cases hlocal : wire = localTarget
    · subst wire
      rw [cnotUpdate_apply_of_ne control cnotTarget _ localTarget hw]
      simp
    · simp [hw, hlocal]

/-- Certified-unitary form of `cnotRaw_commute_localRaw`. -/
theorem cnotUnitary_commute_localUnitary {n : ℕ}
    (control cnotTarget localTarget : Fin n)
    (hct : control ≠ cnotTarget) (hcl : control ≠ localTarget)
    (htl : cnotTarget ≠ localTarget) (U : QubitUnitary) :
    cnotUnitary control cnotTarget hct * localUnitary localTarget U =
      localUnitary localTarget U * cnotUnitary control cnotTarget hct := by
  apply Subtype.ext
  simpa using cnotRaw_commute_localRaw control cnotTarget localTarget
    hct hcl htl (U : QubitMatrix)

/-- Target-local one-qubit matrices on distinct wires commute exactly. -/
theorem localRaw_commute_of_ne {n : ℕ} (first second : Fin n)
    (h : first ≠ second) (U V : QubitMatrix) :
    localRaw first U * localRaw second V =
      localRaw second V * localRaw first U := by
  rw [matrix_eq_iff_mulVec_basisKet_eq]
  intro x
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    localRaw_mulVec_basisKet_eq_sum, localRaw_mulVec_basisKet_eq_sum,
    Matrix.mulVec_sum, Matrix.mulVec_sum]
  simp_rw [Matrix.mulVec_smul, localRaw_mulVec_basisKet_eq_sum,
    Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro firstBit _hfirstBit
  apply Finset.sum_congr rfl
  intro secondBit _hsecondBit
  rw [setTarget_apply_of_ne second x secondBit first h,
    setTarget_apply_of_ne first x firstBit second h.symm]
  rw [smul_smul, smul_smul, mul_comm]
  congr 1
  apply congrArg basisKet
  funext wire
  by_cases hfirst : wire = first
  · subst wire
    simp [h]
  · by_cases hsecond : wire = second
    · subst wire
      rw [setTarget_apply_of_ne first _ _ second h.symm]
      simp
    · simp [hfirst, hsecond]

/-- Certified-unitary form of `localRaw_commute_of_ne`. -/
theorem localUnitary_commute_of_ne {n : ℕ} (first second : Fin n)
    (h : first ≠ second) (U V : QubitUnitary) :
    localUnitary first U * localUnitary second V =
      localUnitary second V * localUnitary first U := by
  apply Subtype.ext
  simpa using localRaw_commute_of_ne first second h
    (U : QubitMatrix) (V : QubitMatrix)

private theorem cnotRaw_mulVec_localRaw_basisKet {n : ℕ}
    (control cnotTarget localTarget : Fin n)
    (hct : control ≠ cnotTarget) (hcl : control ≠ localTarget)
    (htl : cnotTarget ≠ localTarget) (U : QubitMatrix) (x : Basis n) :
    cnotRaw control cnotTarget hct *ᵥ
        (localRaw localTarget U *ᵥ basisKet x) =
      localRaw localTarget U *ᵥ
        basisKet (cnotUpdate control cnotTarget x) := by
  rw [Matrix.mulVec_mulVec,
    cnotRaw_commute_localRaw control cnotTarget localTarget hct hcl htl,
    ← Matrix.mulVec_mulVec, cnotRaw_mulVec_basisKet']

/-- Update the complementary assignment induced by a CNOT avoiding `localTarget`. -/
private def cnotComplementUpdate {n : ℕ} {localTarget : Fin n}
    (control cnotTarget : TargetComplement localTarget)
    (rest : ComplementBasis localTarget) : ComplementBasis localTarget :=
  if rest control then Function.update rest cnotTarget (!rest cnotTarget) else rest

@[simp]
private theorem cnotComplementUpdate_apply_control {n : ℕ}
    {localTarget : Fin n}
    (control cnotTarget : TargetComplement localTarget)
    (h : (control : Fin n) ≠ cnotTarget) (rest : ComplementBasis localTarget) :
    cnotComplementUpdate control cnotTarget rest control = rest control := by
  have hsub : control ≠ cnotTarget := by
    intro heq
    exact h (congrArg Subtype.val heq)
  cases hcontrol : rest control <;>
    simp [cnotComplementUpdate, hcontrol, Function.update_of_ne hsub]

@[simp]
private theorem cnotComplementUpdate_apply_target {n : ℕ}
    {localTarget : Fin n}
    (control cnotTarget : TargetComplement localTarget)
    (rest : ComplementBasis localTarget) :
    cnotComplementUpdate control cnotTarget rest cnotTarget =
      if rest control then !rest cnotTarget else rest cnotTarget := by
  cases hcontrol : rest control <;>
    simp [cnotComplementUpdate, hcontrol]

private theorem splitTarget_snd_cnotUpdate {n : ℕ}
    (control cnotTarget localTarget : Fin n)
    (hcl : control ≠ localTarget) (htl : cnotTarget ≠ localTarget)
    (x : Basis n) :
    (splitTarget localTarget (cnotUpdate control cnotTarget x)).2 =
      cnotComplementUpdate ⟨control, hcl⟩ ⟨cnotTarget, htl⟩
        (splitTarget localTarget x).2 := by
  funext wire
  cases hcontrol : x control
  · simp [cnotUpdate, cnotComplementUpdate, hcontrol]
  · by_cases hw : (wire : Fin n) = cnotTarget
    · subst cnotTarget
      simp [cnotUpdate, cnotComplementUpdate, hcontrol]
    · have hsub : wire ≠ (⟨cnotTarget, htl⟩ : TargetComplement localTarget) := by
        intro heq
        exact hw (congrArg Subtype.val heq)
      simp [cnotUpdate, cnotComplementUpdate, hcontrol, hw,
        Function.update_of_ne hsub]

private theorem targetBlockRaw_mulVec_basisKet_eq_local {n : ℕ}
    (target : Fin n) (F : ComplementBasis target → QubitMatrix)
    (x : Basis n) :
    targetBlockRaw target F *ᵥ basisKet x =
      localRaw target (F (splitTarget target x).2) *ᵥ basisKet x := by
  funext row
  rw [mulVec_basisKet_apply, targetBlockRaw_apply,
    localRaw_mulVec_basisKet]
  change (if (splitTarget target row).2 = (splitTarget target x).2 then
      F (splitTarget target row).2 (row target) (x target) else 0) =
    if AgreeOff target row x then
      F (splitTarget target x).2 (row target) (x target) else 0
  by_cases hrest : (splitTarget target row).2 = (splitTarget target x).2
  · have hagree : AgreeOff target row x :=
      (splitTarget_snd_eq_iff target row x).1 hrest
    rw [if_pos hrest, if_pos hagree, hrest]
  · have hagree : ¬AgreeOff target row x := by
      exact fun h => hrest ((splitTarget_snd_eq_iff target row x).2 h)
    rw [if_neg hrest, if_neg hagree]

/-- Conjugating target blocks by a disjoint CNOT permutes their block index. -/
private theorem cnotRaw_conjugate_targetBlockRaw {n : ℕ}
    (control cnotTarget localTarget : Fin n)
    (hct : control ≠ cnotTarget) (hcl : control ≠ localTarget)
    (htl : cnotTarget ≠ localTarget)
    (F : ComplementBasis localTarget → QubitMatrix) :
    cnotRaw control cnotTarget hct * targetBlockRaw localTarget F *
        cnotRaw control cnotTarget hct =
      targetBlockRaw localTarget (fun rest =>
        F (cnotComplementUpdate ⟨control, hcl⟩ ⟨cnotTarget, htl⟩ rest)) := by
  rw [matrix_eq_iff_mulVec_basisKet_eq]
  intro x
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    cnotRaw_mulVec_basisKet', targetBlockRaw_mulVec_basisKet_eq_local,
    cnotRaw_mulVec_localRaw_basisKet control cnotTarget localTarget hct hcl htl,
    cnotUpdate_involutive control cnotTarget hct,
    targetBlockRaw_mulVec_basisKet_eq_local,
    splitTarget_snd_cnotUpdate control cnotTarget localTarget hcl htl]

/--
The chronological five-node macro circuit displayed in Lemma 6.1.

The inverse is the certified unitary-group inverse of the same `V`; it is not an
independently chosen witness.
-/
def doubleControlledViaSquareCircuit {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (V : QubitUnitary) : Circuit n :=
  [Primitive.positiveControlled target
      ({⟨second, hsecondTarget⟩} : ControlSet target) V,
    Primitive.cnot first second hfirstSecond,
    Primitive.positiveControlled target
      ({⟨second, hsecondTarget⟩} : ControlSet target) V⁻¹,
    Primitive.cnot first second hfirstSecond,
    Primitive.positiveControlled target
      ({⟨first, hfirstTarget⟩} : ControlSet target) V]

/-- Lemma 6.1 specialized to the selected exact square root of `U`. -/
def doubleControlledRootCircuit {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (U : QubitUnitary) : Circuit n :=
  doubleControlledViaSquareCircuit first second target hfirstSecond
    hfirstTarget hsecondTarget (unitarySquareRoot U)

/-! ## Exact evaluator semantics -/

/-- Full-register raw matrix product of the five chronological macro nodes. -/
theorem eval_doubleControlledViaSquareCircuit_raw {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (V : QubitUnitary) :
    (Circuit.eval
        (doubleControlledViaSquareCircuit first second target hfirstSecond
          hfirstTarget hsecondTarget V) : Gate n) =
      positiveControlledRaw target
          ({⟨first, hfirstTarget⟩} : ControlSet target) V *
        cnotRaw first second hfirstSecond *
        positiveControlledRaw target
          ({⟨second, hsecondTarget⟩} : ControlSet target)
          (star (V : QubitMatrix)) *
        cnotRaw first second hfirstSecond *
        positiveControlledRaw target
          ({⟨second, hsecondTarget⟩} : ControlSet target) V := by
  simp [doubleControlledViaSquareCircuit, Circuit.eval]

/--
The Lemma 6.1 circuit always implements a double control of `V ^ 2`.

This is exact equality of certified full-register unitaries. In particular, both
intermediate CNOTs restore the second control and every spectator wire is fixed.
-/
theorem eval_doubleControlledViaSquareCircuit_pow_two {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (V : QubitUnitary) :
    Circuit.eval
        (doubleControlledViaSquareCircuit first second target hfirstSecond
          hfirstTarget hsecondTarget V) =
      positiveControlledUnitary target
        (twoControlSet first second target hfirstTarget hsecondTarget) (V ^ 2) := by
  apply Subtype.ext
  rw [eval_doubleControlledViaSquareCircuit_raw,
    coe_positiveControlledUnitary]
  have hgroup :
      positiveControlledRaw target
            ({⟨first, hfirstTarget⟩} : ControlSet target) V *
          cnotRaw first second hfirstSecond *
          positiveControlledRaw target
            ({⟨second, hsecondTarget⟩} : ControlSet target)
            (star (V : QubitMatrix)) *
          cnotRaw first second hfirstSecond *
          positiveControlledRaw target
            ({⟨second, hsecondTarget⟩} : ControlSet target) V =
        positiveControlledRaw target
            ({⟨first, hfirstTarget⟩} : ControlSet target) V *
          (cnotRaw first second hfirstSecond *
            positiveControlledRaw target
              ({⟨second, hsecondTarget⟩} : ControlSet target)
              (star (V : QubitMatrix)) *
            cnotRaw first second hfirstSecond) *
          positiveControlledRaw target
            ({⟨second, hsecondTarget⟩} : ControlSet target) V := by
    noncomm_ring
  rw [hgroup]
  rw [positiveControlledRaw_singleton_eq_targetBlockRaw,
    positiveControlledRaw_singleton_eq_targetBlockRaw]
  rw [positiveControlledRaw_singleton_eq_targetBlockRaw,
    cnotRaw_conjugate_targetBlockRaw first second target hfirstSecond
      hfirstTarget hsecondTarget]
  rw [targetBlockRaw_mul, targetBlockRaw_mul]
  rw [twoControlSet, positiveControlledRaw, controlledRaw_eq_targetBlockRaw]
  congr 1
  funext rest
  have hstar_mul : star (V : QubitMatrix) * (V : QubitMatrix) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp V.prop
  have hmul_star : (V : QubitMatrix) * star (V : QubitMatrix) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp V.prop
  cases hfirst : rest ⟨first, hfirstTarget⟩ <;>
    cases hsecond : rest ⟨second, hsecondTarget⟩ <;>
      simp [hfirst, hsecond, positiveControlsEnabled, pow_two,
        hstar_mul, hmul_star]

/-- Parameterized Lemma 6.1: any certified square witness implements `U`. -/
theorem eval_doubleControlledViaSquareCircuit_of_sq_eq {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (U V : QubitUnitary) (hV : V ^ 2 = U) :
    Circuit.eval
        (doubleControlledViaSquareCircuit first second target hfirstSecond
          hfirstTarget hsecondTarget V) =
      positiveControlledUnitary target
        (twoControlSet first second target hfirstTarget hsecondTarget) U := by
  rw [eval_doubleControlledViaSquareCircuit_pow_two, hV]

/-- Barenco Lemma 6.1 using the library's selected exact unitary square root. -/
@[simp]
theorem eval_doubleControlledRootCircuit {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (U : QubitUnitary) :
    Circuit.eval
        (doubleControlledRootCircuit first second target hfirstSecond
          hfirstTarget hsecondTarget U) =
      positiveControlledUnitary target
        (twoControlSet first second target hfirstTarget hsecondTarget) U := by
  rw [doubleControlledRootCircuit,
    eval_doubleControlledViaSquareCircuit_pow_two,
    unitarySquareRoot_pow_two]

/-- Existential form of Lemma 6.1, retaining the explicit square witness. -/
theorem doubleControlledViaSquareCircuit_exists {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (U : QubitUnitary) :
    ∃ V : QubitUnitary, V ^ 2 = U ∧
      Circuit.eval
          (doubleControlledViaSquareCircuit first second target hfirstSecond
            hfirstTarget hsecondTarget V) =
        positiveControlledUnitary target
          (twoControlSet first second target hfirstTarget hsecondTarget) U := by
  refine ⟨unitarySquareRoot U, unitarySquareRoot_pow_two U, ?_⟩
  exact eval_doubleControlledRootCircuit first second target hfirstSecond
    hfirstTarget hsecondTarget U

/-! ## Macro-level structural resources -/

@[simp]
theorem doubleControlledViaSquareCircuit_gateCount {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (V : QubitUnitary) :
    Circuit.gateCount
      (doubleControlledViaSquareCircuit first second target hfirstSecond
        hfirstTarget hsecondTarget V) = 5 := by
  rfl

@[simp]
theorem doubleControlledViaSquareCircuit_cnotCount {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (V : QubitUnitary) :
    Circuit.kindCount .cnot
      (doubleControlledViaSquareCircuit first second target hfirstSecond
        hfirstTarget hsecondTarget V) = 2 := by
  simp [doubleControlledViaSquareCircuit, Circuit.kindCount]

@[simp]
theorem doubleControlledViaSquareCircuit_controlledCount {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (V : QubitUnitary) :
    Circuit.kindCount (.controlledOneQubit 1)
      (doubleControlledViaSquareCircuit first second target hfirstSecond
        hfirstTarget hsecondTarget V) = 3 := by
  simp [doubleControlledViaSquareCircuit, Circuit.kindCount]

@[simp]
theorem doubleControlledViaSquareCircuit_oneQubitCount {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (V : QubitUnitary) :
    Circuit.kindCount .oneQubit
      (doubleControlledViaSquareCircuit first second target hfirstSecond
        hfirstTarget hsecondTarget V) = 0 := by
  simp [doubleControlledViaSquareCircuit, Circuit.kindCount]

/-- The Section 3–7 basic-gate model rejects the unexpanded controlled macros. -/
@[simp]
theorem doubleControlledViaSquareCircuit_oneQubitCNOTCost {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (V : QubitUnitary) :
    Circuit.cost CostModel.oneQubitCNOT
      (doubleControlledViaSquareCircuit first second target hfirstSecond
        hfirstTarget hsecondTarget V) = none := by
  simp [doubleControlledViaSquareCircuit, Circuit.cost, Circuit.addCost]

end

end Barenco.ThreeQubit
