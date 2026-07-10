import Barenco.Circuit
import Barenco.Cost
import Barenco.Equivalence.Measurement
import Barenco.Equivalence.OperatorNorm
import Barenco.Equivalence.Phase
import Barenco.OneQubit.CircuitBridge
import Barenco.OneQubit.Lemma43
import Barenco.OneQubit.Roots
import Barenco.OneQubit.U2Euler

/-!
# Kernel axiom audit

Run this module with `lake env lean Barenco/AxiomAudit.lean`. The output is copied
to `docs/axiom-audit.md` at stage boundaries.
-/

#print axioms Barenco.fromPaper_mul
#print axioms Barenco.fromPaper_mem_unitaryGroup_iff
#print axioms Barenco.evalGates_append
#print axioms Barenco.fromPaper_paperProduct
#print axioms Barenco.gate_mul_one
#print axioms Barenco.reindex_mem_unitaryGroup_iff
#print axioms Barenco.blockDiagonal_mem_unitaryGroup_iff
#print axioms Barenco.localRaw_mem_unitaryGroup
#print axioms Barenco.positiveControlledRaw_truthTable
#print axioms Barenco.cnotRaw_mulVec_basisKet
#print axioms Barenco.Primitive.positiveControlled_support_card
#print axioms Barenco.Circuit.eval_append
#print axioms Barenco.Circuit.eval_adjoint
#print axioms Barenco.GlobalPhaseEq.mul
#print axioms Barenco.BasisPhaseEq.postcompose
#print axioms Barenco.BasisPhaseEq.toBasisMeasurementEq
#print axioms Barenco.GlobalPhaseEq.toChannelEq
#print axioms Barenco.channelEq_iff_allMeasurementEq
#print axioms Barenco.ChannelEq.toBasisMeasurementEq
#print axioms Barenco.operatorDistance_unitary_mul_left
#print axioms Barenco.operatorDistance_unitary_mul_right
#print axioms Barenco.operatorDistance_mul_unitary_le
#print axioms Barenco.operatorDistance_action_le
#print axioms Barenco.operatorDistance_basisOutcomeProbability_le
#print axioms Barenco.operatorDistance_unitary_le_two
#print axioms Barenco.Circuit.cost_append
#print axioms Barenco.Circuit.cost_adjoint
#print axioms Barenco.Circuit.touchedSupport_card_le_registerWidth
#print axioms Barenco.Primitive.namedModels_reject_unclassified_of_mem
#print axioms Barenco.OneQubit.paperRy_mul
#print axioms Barenco.OneQubit.paperX_mul_paperRy_mul_paperX
#print axioms Barenco.OneQubit.ry_mem_specialUnitaryGroup
#print axioms Barenco.OneQubit.sigmaX_mul_ry_mul_sigmaX
#print axioms Barenco.OneQubit.paperA_mul_paperB_mul_paperC
#print axioms Barenco.OneQubit.paperA_mul_X_mul_paperB_mul_X_mul_paperC
#print axioms Barenco.OneQubit.specialUnitary_canonical
#print axioms Barenco.OneQubit.specialUnitary_eq_paperEuler_arg
#print axioms Barenco.OneQubit.specialUnitary_exists_rz_mul_ry_mul_rz
#print axioms Barenco.OneQubit.removeGlobalPhase_det
#print axioms Barenco.OneQubit.phaseShift_mul_specialUnitaryPart
#print axioms Barenco.OneQubit.unitary_exists_phaseShift_mul_rz_mul_ry_mul_rz
#print axioms Barenco.OneQubit.specialUnitary_exists_paperABC
#print axioms Barenco.OneQubit.specialUnitary_exists_columnChronologicalABC
#print axioms Barenco.OneQubit.unitaryRoot_pow
#print axioms Barenco.OneQubit.unitaryRoot_pow_two_pow
#print axioms Barenco.OneQubit.sigmaXUnitary_eq_pauliX
