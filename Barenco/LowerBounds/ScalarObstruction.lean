import Barenco.LowerBounds.PartitionFactorization
import Barenco.OneQubit.Certified
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Scalar obstruction to factorizing a controlled gate

A controlled one-qubit gate can factor across a partition separating its target
from one of its controls only when the target matrix is scalar.  The proof is
entrywise: an inactive control block supplies a nonzero diagonal factor, which
can then be cancelled from the active and inactive entries without division.

The final specialization treats a fully controlled gate.  Its proper-cut
hypothesis is explicit because a cut containing every wire has no separated
control and hence presents no obstruction.
-/

namespace Barenco.LowerBounds

open Matrix
open Barenco.OneQubit
open scoped Kronecker

noncomputable section

/-! ## Scalar one-qubit matrices -/

/-- A raw one-qubit matrix is scalar when it is a complex multiple of identity. -/
def IsScalarQubitMatrix (U : QubitMatrix) : Prop :=
  ∃ z : ℂ, U = z • (1 : QubitMatrix)

/-- Entrywise characterization of scalar Bool-indexed matrices. -/
theorem isScalarQubitMatrix_iff_entries (U : QubitMatrix) :
    IsScalarQubitMatrix U ↔
      U false true = 0 ∧ U true false = 0 ∧ U false false = U true true := by
  constructor
  · rintro ⟨z, rfl⟩
    simp
  · rintro ⟨hft, htf, hdiag⟩
    refine ⟨U false false, ?_⟩
    ext row col
    cases row <;> cases col <;> simp [hft, htf, hdiag]

/-- A certified one-qubit unitary is scalar exactly when it is a scalar phase. -/
theorem isScalarQubitMatrix_coe_iff_exists_phaseShiftUnitary (U : QubitUnitary) :
    IsScalarQubitMatrix (U : QubitMatrix) ↔
      ∃ delta : ℝ, U = phaseShiftUnitary delta := by
  constructor
  · rintro ⟨z, hz⟩
    have hunitary :
        star (z • (1 : QubitMatrix)) * (z • (1 : QubitMatrix)) = 1 := by
      rw [← hz]
      exact Matrix.mem_unitaryGroup_iff'.mp U.property
    have hscalarNormSq : ‖z‖ * ‖z‖ = 1 := by
      have hentry := congrFun (congrFun hunitary false) false
      have hcomplex : star z * z = 1 := by
        simpa [Matrix.mul_apply] using hentry
      have := congrArg norm hcomplex
      simpa [norm_mul] using this
    have hnorm : ‖z‖ = 1 := by
      nlinarith [norm_nonneg z]
    obtain ⟨delta, hdelta⟩ := (Complex.norm_eq_one_iff z).mp hnorm
    have hcis : cis delta = z := by
      simpa [cis] using hdelta
    refine ⟨delta, Subtype.ext ?_⟩
    rw [hz, coe_phaseShiftUnitary]
    ext row col
    cases row <;> cases col <;> simp [hcis]
  · rintro ⟨delta, rfl⟩
    refine ⟨cis delta, ?_⟩
    rw [coe_phaseShiftUnitary]
    ext row col
    cases row <;> cases col <;> simp

/-! ## Test assignments crossing a partition -/

/--
A basis assignment varying only the target and one distinguished control.
Every other wire is set to `true`, so the `outsideBit = true` assignments
activate every positive control.
-/
private def scalarObstructionBasis {n : ℕ} (target outsideControl : Fin n)
    (targetBit outsideBit : Bool) : Basis n := fun wire =>
  if wire = target then targetBit
  else if wire = outsideControl then outsideBit
  else true

@[simp]
private theorem scalarObstructionBasis_target {n : ℕ} (target outsideControl : Fin n)
    (targetBit outsideBit : Bool) :
    scalarObstructionBasis target outsideControl targetBit outsideBit target =
      targetBit := by
  simp [scalarObstructionBasis]

@[simp]
private theorem scalarObstructionBasis_outsideControl {n : ℕ}
    (target outsideControl : Fin n) (houtsideTarget : outsideControl ≠ target)
    (targetBit outsideBit : Bool) :
    scalarObstructionBasis target outsideControl targetBit outsideBit outsideControl =
      outsideBit := by
  simp [scalarObstructionBasis, houtsideTarget]

private theorem scalarObstructionBasis_agreeOff {n : ℕ}
    (target outsideControl : Fin n) (rowBit colBit outsideBit : Bool) :
    AgreeOff target
      (scalarObstructionBasis target outsideControl rowBit outsideBit)
      (scalarObstructionBasis target outsideControl colBit outsideBit) := by
  intro wire hwire
  simp [scalarObstructionBasis, hwire]

private theorem scalarObstructionBasis_all_controls_true {n : ℕ}
    (target : Fin n) (controls : ControlSet target)
    (outsideControl : TargetComplement target) (targetBit : Bool) :
    ∀ control ∈ controls,
      scalarObstructionBasis target outsideControl targetBit true control = true := by
  intro control _
  simp [scalarObstructionBasis, control.property]

private theorem scalarObstructionBasis_not_all_controls_true {n : ℕ}
    (target : Fin n) (controls : ControlSet target)
    (outsideControl : TargetComplement target) (hcontrol : outsideControl ∈ controls)
    (targetBit : Bool) :
    ¬∀ control ∈ controls,
      scalarObstructionBasis target outsideControl targetBit false control = true := by
  intro hall
  have := hall outsideControl hcontrol
  simp [scalarObstructionBasis, outsideControl.property] at this

private theorem scalarObstructionBasis_cut_irrel_outsideBit {n : ℕ}
    (cut : Finset (Fin n)) (target outsideControl : Fin n)
    (houtside : outsideControl ∉ cut) (targetBit outsideBit₁ outsideBit₂ : Bool) :
    (wireSplit cut
      (scalarObstructionBasis target outsideControl targetBit outsideBit₁)).1 =
    (wireSplit cut
      (scalarObstructionBasis target outsideControl targetBit outsideBit₂)).1 := by
  funext wire
  have hwire : (wire : Fin n) ≠ outsideControl := by
    intro heq
    exact houtside (heq ▸ wire.property)
  simp [scalarObstructionBasis, hwire]

private theorem scalarObstructionBasis_complement_irrel_targetBit {n : ℕ}
    (cut : Finset (Fin n)) (target outsideControl : Fin n)
    (htarget : target ∈ cut) (targetBit₁ targetBit₂ outsideBit : Bool) :
    (wireSplit cut
      (scalarObstructionBasis target outsideControl targetBit₁ outsideBit)).2 =
    (wireSplit cut
      (scalarObstructionBasis target outsideControl targetBit₂ outsideBit)).2 := by
  funext wire
  have hwire : (wire : Fin n) ≠ target := by
    intro heq
    exact wire.property (heq ▸ htarget)
  simp [scalarObstructionBasis, hwire]

/-! ## The separated-control obstruction -/

/--
If a positive controlled gate factors across a cut containing its target but
excluding one listed control, then its one-qubit target matrix is scalar.

No invertibility hypothesis on `U` is needed.  The inactive block is an identity
block, and its diagonal entry proves that the complementary tensor factor being
cancelled is nonzero.
-/
theorem isScalarQubitMatrix_of_tensorFactorsAcross_positiveControlledRaw {n : ℕ}
    (cut : Finset (Fin n)) (target : Fin n) (controls : ControlSet target)
    (U : QubitMatrix) (htarget : target ∈ cut)
    (outsideControl : TargetComplement target)
    (hcontrol : outsideControl ∈ controls)
    (houtside : (outsideControl : Fin n) ∉ cut)
    (hfactor : TensorFactorsAcross cut
      (positiveControlledRaw target controls U)) :
    IsScalarQubitMatrix U := by
  rcases hfactor with ⟨left, right, hfactor⟩
  let x : Bool → Bool → Basis n := fun targetBit outsideBit =>
    scalarObstructionBasis target outsideControl targetBit outsideBit
  have hx_target (targetBit outsideBit : Bool) :
      x targetBit outsideBit target = targetBit := by
    simp [x]
  have hx_agreeOff (rowBit colBit outsideBit : Bool) :
      AgreeOff target (x rowBit outsideBit) (x colBit outsideBit) := by
    simpa [x] using scalarObstructionBasis_agreeOff target
      (outsideControl : Fin n) rowBit colBit outsideBit
  have hx_active (targetBit : Bool) :
      ∀ control ∈ controls, x targetBit true control = true := by
    simpa [x] using scalarObstructionBasis_all_controls_true target controls
      outsideControl targetBit
  have hx_inactive (targetBit : Bool) :
      ¬∀ control ∈ controls, x targetBit false control = true := by
    simpa [x] using scalarObstructionBasis_not_all_controls_true target controls
      outsideControl hcontrol targetBit
  have hx_cut (targetBit outsideBit₁ outsideBit₂ : Bool) :
      (wireSplit cut (x targetBit outsideBit₁)).1 =
        (wireSplit cut (x targetBit outsideBit₂)).1 := by
    simpa [x] using scalarObstructionBasis_cut_irrel_outsideBit cut target
      (outsideControl : Fin n) houtside targetBit outsideBit₁ outsideBit₂
  have hx_complement (targetBit₁ targetBit₂ outsideBit : Bool) :
      (wireSplit cut (x targetBit₁ outsideBit)).2 =
        (wireSplit cut (x targetBit₂ outsideBit)).2 := by
    simpa [x] using scalarObstructionBasis_complement_irrel_targetBit cut target
      (outsideControl : Fin n) htarget targetBit₁ targetBit₂ outsideBit
  have hentry (rowBit colBit outsideBit : Bool) :
      positiveControlledRaw target controls U
          (x rowBit outsideBit) (x colBit outsideBit) =
        left (wireSplit cut (x rowBit outsideBit)).1
            (wireSplit cut (x colBit outsideBit)).1 *
          right (wireSplit cut (x rowBit outsideBit)).2
            (wireSplit cut (x colBit outsideBit)).2 := by
    have h := congrFun (congrFun hfactor
      (wireSplit cut (x rowBit outsideBit)))
      (wireSplit cut (x colBit outsideBit))
    simpa [Matrix.kronecker_apply] using h
  have hactive (rowBit colBit : Bool) :
      positiveControlledRaw target controls U (x rowBit true) (x colBit true) =
        U rowBit colBit := by
    rw [positiveControlledRaw, controlledRaw_apply_eq_if_agreeOff,
      if_pos (hx_agreeOff rowBit colBit true)]
    have henabled :
        positiveControlsEnabled controls (splitTarget target (x rowBit true)).2 = true :=
      (positiveControlsEnabled_splitTarget_eq_true_iff controls (x rowBit true)).2
        (hx_active rowBit)
    simp [henabled, hx_target]
  have hinactive (rowBit colBit : Bool) :
      positiveControlledRaw target controls U (x rowBit false) (x colBit false) =
        (1 : QubitMatrix) rowBit colBit := by
    rw [positiveControlledRaw, controlledRaw_apply_eq_if_agreeOff,
      if_pos (hx_agreeOff rowBit colBit false)]
    have henabled :
        positiveControlsEnabled controls (splitTarget target (x rowBit false)).2 = false := by
      cases hvalue :
          positiveControlsEnabled controls (splitTarget target (x rowBit false)).2
      · rfl
      · exact (hx_inactive rowBit
          ((positiveControlsEnabled_splitTarget_eq_true_iff controls
            (x rowBit false)).1 hvalue)).elim
    rw [henabled, hx_target rowBit false, hx_target colBit false]
    simp

  let cutFalse := (wireSplit cut (x false false)).1
  let cutTrue := (wireSplit cut (x true false)).1
  let complementInactive := (wireSplit cut (x false false)).2
  let complementActive := (wireSplit cut (x false true)).2

  have hInactiveFalse :
      left cutFalse cutFalse * right complementInactive complementInactive = 1 := by
    have h := (hentry false false false).symm.trans (hinactive false false)
    simpa [cutFalse, complementInactive] using h
  have hInactiveTrue :
      left cutTrue cutTrue * right complementInactive complementInactive = 1 := by
    have h := (hentry true true false).symm.trans (hinactive true true)
    simpa [cutTrue, complementInactive, hx_complement true false false] using h
  have hRightInactive : right complementInactive complementInactive ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hInactiveFalse
    exact zero_ne_one hInactiveFalse
  have hLeftDiagonal : left cutFalse cutFalse = left cutTrue cutTrue := by
    apply mul_right_cancel₀ hRightInactive
    exact hInactiveFalse.trans hInactiveTrue.symm

  have hOffDiagonalFalseTrue : left cutFalse cutTrue = 0 := by
    have hzero :
        left cutFalse cutTrue * right complementInactive complementInactive = 0 := by
      have h := (hentry false true false).symm.trans (hinactive false true)
      simpa [cutFalse, cutTrue, complementInactive,
        hx_complement true false false] using h
    exact (mul_eq_zero.mp hzero).resolve_right hRightInactive
  have hOffDiagonalTrueFalse : left cutTrue cutFalse = 0 := by
    have hzero :
        left cutTrue cutFalse * right complementInactive complementInactive = 0 := by
      have h := (hentry true false false).symm.trans (hinactive true false)
      simpa [cutFalse, cutTrue, complementInactive,
        hx_complement true false false] using h
    exact (mul_eq_zero.mp hzero).resolve_right hRightInactive

  rw [isScalarQubitMatrix_iff_entries]
  constructor
  · have h := (hactive false true).symm.trans (hentry false true true)
    rw [hx_cut false true false, hx_cut true true false,
      hx_complement true false true] at h
    simpa [cutFalse, cutTrue, complementActive,
      hOffDiagonalFalseTrue] using h
  constructor
  · have h := (hactive true false).symm.trans (hentry true false true)
    rw [hx_cut true true false, hx_cut false true false,
      hx_complement true false true] at h
    simpa [cutFalse, cutTrue, complementActive,
      hOffDiagonalTrueFalse] using h
  · have hfalse := (hactive false false).symm.trans (hentry false false true)
    have htrue := (hactive true true).symm.trans (hentry true true true)
    rw [hx_cut false true false] at hfalse
    rw [hx_cut true true false, hx_complement true false true] at htrue
    calc
      U false false = left cutFalse cutFalse *
          right complementActive complementActive := by
        simpa [cutFalse, complementActive] using hfalse
      _ = left cutTrue cutTrue * right complementActive complementActive := by
        rw [hLeftDiagonal]
      _ = U true true := by
        simpa [cutTrue, complementActive] using htrue.symm

/-! ## Fully controlled specialization -/

/--
A fully controlled nonscalar unitary cannot factor across a cut containing its
target when the complementary side contains a wire.  The existential hypothesis
records the exact nonempty-complement boundary used by the proof.
-/
theorem not_tensorFactorsAcross_fullyControlled_of_exists_not_mem_of_not_scalar
    {n : ℕ}
    (cut : Finset (Fin n)) (target : Fin n) (U : QubitUnitary)
    (htarget : target ∈ cut) (hexists : ∃ wire : Fin n, wire ∉ cut)
    (hnonscalar : ¬IsScalarQubitMatrix (U : QubitMatrix)) :
    ¬TensorFactorsAcross cut
      (positiveControlledRaw target (Finset.univ : ControlSet target) U) := by
  intro hfactor
  obtain ⟨wire, hwire⟩ := hexists
  have hwireTarget : wire ≠ target := by
    intro heq
    exact hwire (heq ▸ htarget)
  let outsideControl : TargetComplement target := ⟨wire, hwireTarget⟩
  apply hnonscalar
  exact isScalarQubitMatrix_of_tensorFactorsAcross_positiveControlledRaw
    cut target Finset.univ U htarget outsideControl (by simp) hwire hfactor

/--
A fully controlled nonscalar unitary cannot factor across a proper cut containing
its target.  Properness is equivalent here to the explicitly nonempty complement
used by `not_tensorFactorsAcross_fullyControlled_of_exists_not_mem_of_not_scalar`.
-/
theorem not_tensorFactorsAcross_fullyControlled_of_not_scalar {n : ℕ}
    (cut : Finset (Fin n)) (target : Fin n) (U : QubitUnitary)
    (htarget : target ∈ cut) (hproper : cut ≠ Finset.univ)
    (hnonscalar : ¬IsScalarQubitMatrix (U : QubitMatrix)) :
    ¬TensorFactorsAcross cut
      (positiveControlledRaw target (Finset.univ : ControlSet target) U) := by
  apply not_tensorFactorsAcross_fullyControlled_of_exists_not_mem_of_not_scalar
    cut target U htarget
  · by_contra h
    push Not at h
    exact hproper (Finset.eq_univ_of_forall h)
  · exact hnonscalar

end

end Barenco.LowerBounds
