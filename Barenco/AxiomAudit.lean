import Barenco.Circuit
import Barenco.Cost
import Barenco.Equivalence.Measurement
import Barenco.Equivalence.OperatorNorm
import Barenco.Equivalence.Phase

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
#print axioms Barenco.operatorDistance_unitary_le_two
#print axioms Barenco.Circuit.cost_append
#print axioms Barenco.Circuit.cost_adjoint
#print axioms Barenco.Circuit.touchedSupport_card_le_registerWidth
#print axioms Barenco.Primitive.namedModels_reject_unclassified_of_mem
