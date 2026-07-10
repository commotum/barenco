import Barenco.Basic

/-!
# Kernel axiom audit

Run this module with `lake env lean Barenco/AxiomAudit.lean`. The output is copied
to `docs/axiom-audit.md` at stage boundaries.
-/

#print axioms Barenco.fromPaper_mul
#print axioms Barenco.fromPaper_mem_unitaryGroup_iff
#print axioms Barenco.evalGates_append
#print axioms Barenco.gate_mul_one
