import Barenco.Optimization.EarlyNormalize
import Barenco.Optimization.Section8Normalize

/-!
# Exact normalization policy facade

This module is the stable import point for the two exact optimizer policies:

* `normalizeEarly` and `normalizeEarlyProgram` retain literal CNOT syntax; and
* `section8Normalize` and `section8NormalizeProgram` may promote a CNOT to a
  certified arbitrary two-qubit payload before fusing adjacent operations.

Both mixed-program passes treat every opaque barrier as a hard separator and
preserve exact full-register evaluation.  The implementations and their proofs
remain in the policy-specific modules imported above; this facade deliberately
adds no rewrite logic.
-/
