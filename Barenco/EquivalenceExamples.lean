import Barenco.Equivalence.Measurement

/-!
# Diagnostic separations between equivalence relations

These examples are intentionally outside the public root API. They prevent future
proofs from silently replacing basis-dependent phase by global/channel equality.
-/

namespace Barenco
namespace EquivalenceExamples

open Matrix

/-- The one-qubit diagonal matrix with entries `1,-1`. -/
def phaseZ : QubitMatrix :=
  Matrix.diagonal fun bit => if bit then -1 else 1

/-- `phaseZ` differs from identity by an input-dependent column phase. -/
theorem one_basisPhaseEq_phaseZ :
    BasisPhaseEq (1 : QubitMatrix) phaseZ := by
  refine ⟨fun bit => if bit then (-1 : Circle) else 1, ?_⟩
  intro row input
  cases row <;> cases input <;>
    norm_num [phaseZ, Matrix.diagonal_apply]

/-- An unnormalized plus-state density matrix; normalization is irrelevant to inequality. -/
def plusDensity : QubitMatrix := fun _ _ => 1

/-- Identity and `phaseZ` do not define the same conjugation channel. -/
theorem not_channelEq_one_phaseZ :
    ¬ChannelEq (1 : QubitMatrix) phaseZ := by
  intro h
  have hentry := congrArg (fun M : QubitMatrix => M false true) (h plusDensity)
  norm_num [conjugationChannel, phaseZ, plusDensity, Matrix.diagonal_apply,
    Matrix.mul_apply] at hentry

/-- Basis-dependent phase does not imply equality of all measurement behavior. -/
theorem basisPhaseEq_not_allMeasurementEq :
    BasisPhaseEq (1 : QubitMatrix) phaseZ ∧
      ¬AllMeasurementEq (1 : QubitMatrix) phaseZ := by
  refine ⟨one_basisPhaseEq_phaseZ, ?_⟩
  intro h
  exact not_channelEq_one_phaseZ h.toChannelEq

end EquivalenceExamples
end Barenco
