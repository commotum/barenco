import Barenco.Circuit

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
