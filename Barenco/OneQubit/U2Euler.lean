import Barenco.OneQubit.Euler
import Barenco.OneQubit.GlobalPhase

/-!
# Full U(2) Euler decomposition

This leaf completes Barenco et al., Lemma 4.1 by combining the exact determinant
phase split with the proved `SU(2)` Euler theorem.  Both the paper-row expression
and the library's standard-column expression are exported.

The proof does not infer that the scalar phase of a special unitary is literally
zero.  In the paper's factorization, determinant one only gives
`exp(2 i delta) = 1`, so the scalar can also be `-1`; the independently proved
special-unitary Euler theorem already absorbs that case into its Z angles.  At
the paper level the explicit repair is to replace `alpha` by `alpha + 2*pi`, since
this negates `paperRz alpha`.  The formal proof below does not need to select
between these two scalar representatives.

The two exported existential statements do not claim that their outer witnesses
have the same names.  The paper theorem uses the row-action order
`paperRz alpha * paperRy theta * paperRz beta`.  Transposition reverses those
outer factors, and the standard-column theorem uses the already-renamed semantic
order `rz alpha * ry theta * rz beta`.  The scalar phase is central, so retaining
it as the leftmost matrix factor is exact in either convention.
-/

namespace Barenco.OneQubit

noncomputable section

/-! ## The paper's special-unitary scalar ambiguity -/

/-- For the paper's scalar representative `delta = pi`, its phase is `Rz(2*pi)`. -/
theorem paperPhase_pi_eq_paperRz_two_pi :
    paperPhase Real.pi = paperRz (2 * Real.pi) := by
  have hpos : cis Real.pi = -1 := by
    simpa only [cis] using Complex.exp_pi_mul_I
  have hneg : cis (-Real.pi) = -1 := by
    simpa only [cis, Complex.ofReal_neg, neg_mul] using Complex.exp_neg_pi_mul_I
  rw [paperPhase, paperRz]
  have hp : 2 * Real.pi / 2 = Real.pi := by ring
  have hn : -(2 * Real.pi) / 2 = -Real.pi := by ring
  rw [hp, hn, hpos, hneg]

/-- The paper's possible scalar `-1` is absorbed by shifting the first Z angle by `2*pi`. -/
theorem paperPhase_pi_mul_paperRz (alpha : ℝ) :
    paperPhase Real.pi * paperRz alpha = paperRz (alpha + 2 * Real.pi) := by
  rw [paperPhase_pi_eq_paperRz_two_pi, paperRz_mul]
  congr 1
  ring

/-! ## Full unitary Euler existence -/

/--
Every one-qubit unitary is a scalar phase times the paper's row-action Euler
expression.  The middle rotation angle is chosen in `[0, pi]`.
-/
theorem unitary_exists_paperPhase_mul_paperEuler (U : QubitUnitary) :
    ∃ delta alpha theta beta : ℝ,
      theta ∈ Set.Icc 0 Real.pi ∧
        (U : QubitMatrix) = paperPhase delta * paperEuler alpha theta beta := by
  obtain ⟨alpha, theta, beta, htheta, hspecial⟩ :=
    specialUnitary_exists_paperEuler (specialUnitaryPart U)
  refine ⟨determinantPhaseAngle U, alpha, theta, beta, htheta, ?_⟩
  calc
    (U : QubitMatrix) =
        phaseShift (determinantPhaseAngle U) *
          (specialUnitaryPart U : QubitMatrix) :=
      (phaseShift_mul_specialUnitaryPart U).symm
    _ = paperPhase (determinantPhaseAngle U) * paperEuler alpha theta beta := by
      rw [phaseShift_eq_paperPhase, hspecial]

/--
Every one-qubit unitary is a scalar phase times a standard-column `Rz Ry Rz`
Euler expression, with the middle angle in `[0, pi]`.
-/
theorem unitary_exists_phaseShift_mul_rz_mul_ry_mul_rz (U : QubitUnitary) :
    ∃ delta alpha theta beta : ℝ,
      theta ∈ Set.Icc 0 Real.pi ∧
        (U : QubitMatrix) =
          phaseShift delta * (rz alpha * ry theta * rz beta) := by
  obtain ⟨alpha, theta, beta, htheta, hspecial⟩ :=
    specialUnitary_exists_rz_mul_ry_mul_rz (specialUnitaryPart U)
  refine ⟨determinantPhaseAngle U, alpha, theta, beta, htheta, ?_⟩
  calc
    (U : QubitMatrix) =
        phaseShift (determinantPhaseAngle U) *
          (specialUnitaryPart U : QubitMatrix) :=
      (phaseShift_mul_specialUnitaryPart U).symm
    _ = phaseShift (determinantPhaseAngle U) *
          (rz alpha * ry theta * rz beta) := by rw [hspecial]

end

end Barenco.OneQubit
