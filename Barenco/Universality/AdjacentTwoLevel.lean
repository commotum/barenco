import Barenco.Universality.PatternControl
import Barenco.Universality.TwoLevel
import Barenco.Universality.BasisPath

/-!
# Adjacent computational-basis two-level circuits

When two basis assignments differ at exactly one wire, a mixed-polarity fully
controlled one-qubit gate acts on exactly their two-dimensional span. The local
qubit order is always `false,true`, while the ordered two-level pair may run
`true,false`; `endpointOrientedUnitary` inserts the required `X U X` conjugation
in that reversed case.

This is the formal repair of the endpoint-orientation omission in the paper's
Section 8 Gray-path argument.
-/

namespace Barenco.Universality

open scoped Matrix

noncomputable section

/-- Transport an ordered endpoint block into canonical target-bit order. -/
def endpointOrientedUnitary (firstBit : Bool) (U : QubitUnitary) : QubitUnitary :=
  if firstBit then pauliX * U * pauliX else U

@[simp]
theorem endpointOrientedUnitary_apply (firstBit row col : Bool)
    (U : QubitUnitary) :
    endpointOrientedUnitary firstBit U row col =
      U (if firstBit then !row else row) (if firstBit then !col else col) := by
  cases firstBit <;> cases row <;> cases col <;>
    simp [endpointOrientedUnitary, Matrix.mul_apply]

@[simp]
theorem setTarget_setTarget {n : ℕ} (target : Fin n) (input : Basis n)
    (firstBit secondBit : Bool) :
    setTarget target (setTarget target input firstBit) secondBit =
      setTarget target input secondBit := by
  apply (splitTarget target).injective
  simp

/-- Explicit two-term action of a target-local one-qubit matrix. -/
theorem localRaw_mulVec_basisKet_eq_pair {n : ℕ} (target : Fin n)
    (U : QubitMatrix) (input : Basis n) :
    localRaw target U *ᵥ basisKet input =
      U false (input target) • basisKet (setTarget target input false) +
        U true (input target) • basisKet (setTarget target input true) := by
  rw [localRaw_mulVec_basisKet]
  funext row
  by_cases hagree : AgreeOff target row input
  · rw [if_pos hagree]
    cases hrow : row target
    · have heq : row = setTarget target input false :=
        (eq_setTarget_iff target input row false).2 ⟨hagree, hrow⟩
      have hne : row ≠ setTarget target input true := by
        intro h
        have := congrFun h target
        simp [hrow] at this
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, basisKet_apply]
      rw [if_pos heq, if_neg hne]
      simp
    · have heq : row = setTarget target input true :=
        (eq_setTarget_iff target input row true).2 ⟨hagree, hrow⟩
      have hne : row ≠ setTarget target input false := by
        intro h
        have := congrFun h target
        simp [hrow] at this
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, basisKet_apply]
      rw [if_neg hne, if_pos heq]
      simp
  · rw [if_neg hagree]
    have hfalse : row ≠ setTarget target input false := by
      intro hrow
      exact hagree ((eq_setTarget_iff target input row false).1 hrow).1
    have htrue : row ≠ setTarget target input true := by
      intro hrow
      exact hagree ((eq_setTarget_iff target input row true).1 hrow).1
    simp [basisKet_apply, hfalse, htrue]

theorem BasisStepAt.agreeOff {n : ℕ} {target : Fin n}
    {first second : Basis n} (hstep : BasisStepAt target first second) :
    AgreeOff target first second := by
  intro wire hwire
  exact hstep.2 wire hwire

theorem BasisStepAt.second_target_eq_not {n : ℕ} {target : Fin n}
    {first second : Basis n} (hstep : BasisStepAt target first second) :
    second target = !first target := by
  cases hfirst : first target <;> cases hsecond : second target
  · exact (hstep.1 (hfirst.trans hsecond.symm)).elim
  · simp
  · simp
  · exact (hstep.1 (hfirst.trans hsecond.symm)).elim

/-- The second endpoint is obtained by flipping the unique changed wire. -/
theorem BasisStepAt.second_eq_setTarget_not {n : ℕ} {target : Fin n}
    {first second : Basis n} (hstep : BasisStepAt target first second) :
    second = setTarget target first (!first target) := by
  funext wire
  by_cases hwire : wire = target
  · subst wire
    simp [hstep.second_target_eq_not]
  · rw [setTarget_apply_of_ne target first _ wire hwire]
    exact (hstep.agreeOff wire hwire).symm

theorem BasisStepAt.complement_eq {n : ℕ} {target : Fin n}
    {first second : Basis n} (hstep : BasisStepAt target first second) :
    (splitTarget target first).2 = (splitTarget target second).2 := by
  exact (splitTarget_snd_eq_iff target first second).2 hstep.agreeOff

/-- Any assignment with the endpoints' complementary pattern is one endpoint. -/
theorem BasisStepAt.eq_first_or_second_of_complement_eq {n : ℕ}
    {target : Fin n} {first second input : Basis n}
    (hstep : BasisStepAt target first second)
    (hrest : (splitTarget target input).2 = (splitTarget target first).2) :
    input = first ∨ input = second := by
  by_cases htarget : input target = first target
  · left
    apply (splitTarget target).injective
    apply Prod.ext
    · exact htarget
    · exact hrest
  · right
    apply (splitTarget target).injective
    apply Prod.ext
    · have hnot := hstep.second_target_eq_not
      cases hinput : input target <;> cases hfirst : first target <;>
        simp_all
    · exact hrest.trans hstep.complement_eq

/-- Exact target-local action on the first ordered endpoint. -/
theorem local_endpointOriented_mulVec_first {n : ℕ} (target : Fin n)
    (first second : Basis n) (hstep : BasisStepAt target first second)
    (U : QubitUnitary) :
    localRaw target (endpointOrientedUnitary (first target) U) *ᵥ basisKet first =
      U false false • basisKet first + U true false • basisKet second := by
  rw [localRaw_mulVec_basisKet_eq_pair]
  have hsecond := hstep.second_eq_setTarget_not
  have hself := setTarget_self target first
  cases hfirst : first target
  · have hsetFalse : setTarget target first false = first := by
      simpa [hfirst] using hself
    have hsetTrue : setTarget target first true = second := by
      simpa [hfirst] using hsecond.symm
    rw [hsetFalse, hsetTrue]
    simp
  · have hsetTrue : setTarget target first true = first := by
      simpa [hfirst] using hself
    have hsetFalse : setTarget target first false = second := by
      simpa [hfirst] using hsecond.symm
    rw [hsetFalse, hsetTrue]
    simp [add_comm]

/-- Exact target-local action on the second ordered endpoint. -/
theorem local_endpointOriented_mulVec_second {n : ℕ} (target : Fin n)
    (first second : Basis n) (hstep : BasisStepAt target first second)
    (U : QubitUnitary) :
    localRaw target (endpointOrientedUnitary (first target) U) *ᵥ basisKet second =
      U false true • basisKet first + U true true • basisKet second := by
  have hsecond := hstep.second_eq_setTarget_not
  have hself := setTarget_self target first
  rw [localRaw_mulVec_basisKet_eq_pair]
  cases hfirst : first target
  · have hsetFalse : setTarget target first false = first := by
      simpa [hfirst] using hself
    have hsetTrue : setTarget target first true = second := by
      simpa [hfirst] using hsecond.symm
    rw [hsecond, setTarget_setTarget, setTarget_setTarget,
      hsetFalse, hsetTrue]
    simp [hfirst]
    exact congrArg (fun state => U true true • basisKet state) hsetTrue.symm
  · have hsetTrue : setTarget target first true = first := by
      simpa [hfirst] using hself
    have hsetFalse : setTarget target first false = second := by
      simpa [hfirst] using hsecond.symm
    rw [hsecond, setTarget_setTarget, setTarget_setTarget,
      hsetTrue, hsetFalse]
    simp [hfirst, add_comm]
    exact congrArg (fun state => U true true • basisKet state) hsetFalse.symm

/-- Literal circuit for an adjacent ordered two-level unitary. -/
def adjacentTwoLevelCircuit (controlCount : ℕ)
    (target : Fin (controlCount + 1)) (first second : Basis (controlCount + 1))
    (_hstep : BasisStepAt target first second) (U : QubitUnitary) :
    Circuit (controlCount + 1) :=
  patternControlledCircuit controlCount target (splitTarget target first).2
    (endpointOrientedUnitary (first target) U)

/-- Exact evaluator of the adjacent ordered two-level circuit. -/
@[simp]
theorem eval_adjacentTwoLevelCircuit (controlCount : ℕ)
    (target : Fin (controlCount + 1)) (first second : Basis (controlCount + 1))
    (hstep : BasisStepAt target first second) (U : QubitUnitary) :
    Circuit.eval (adjacentTwoLevelCircuit controlCount target first second hstep U) =
      twoLevelUnitary first second hstep.ne U := by
  apply Subtype.ext
  rw [matrix_eq_iff_mulVec_basisKet_eq]
  intro input
  rw [adjacentTwoLevelCircuit, eval_patternControlledCircuit,
    coe_patternControlledUnitary, controlledRaw_truthTable]
  simp only [exactPatternEnabled, decide_eq_true_eq]
  by_cases hrest : (splitTarget target input).2 = (splitTarget target first).2
  · rw [if_pos hrest]
    rcases hstep.eq_first_or_second_of_complement_eq hrest with hinput | hinput
    · subst input
      exact (local_endpointOriented_mulVec_first target first second hstep U).trans
        (twoLevelUnitary_mulVec_basisKet_first first second hstep.ne U).symm
    · subst input
      exact (local_endpointOriented_mulVec_second target first second hstep U).trans
        (twoLevelUnitary_mulVec_basisKet_second first second hstep.ne U).symm
  · rw [if_neg hrest]
    have hinputFirst : input ≠ first := by
      intro h
      exact hrest (congrArg (fun state => (splitTarget target state).2) h)
    have hinputSecond : input ≠ second := by
      intro h
      apply hrest
      rw [h, ← hstep.complement_eq]
    rw [twoLevelUnitary_mulVec_basisKet_outside first second input hstep.ne U
      hinputFirst hinputSecond]

/-- Exact accepted cost of an adjacent ordered two-level circuit. -/
@[simp]
theorem adjacentTwoLevelCircuit_oneQubitCNOTCost (controlCount : ℕ)
    (target : Fin (controlCount + 1)) (first second : Basis (controlCount + 1))
    (hstep : BasisStepAt target first second) (U : QubitUnitary) :
    Circuit.cost CostModel.oneQubitCNOT
        (adjacentTwoLevelCircuit controlCount target first second hstep U) =
      some (2 * patternFlipCount (splitTarget target first).2 +
        fullControlCircuitCost controlCount) := by
  exact patternControlledCircuit_oneQubitCNOTCost controlCount target
    (splitTarget target first).2 (endpointOrientedUnitary (first target) U)

end

end Barenco.Universality
