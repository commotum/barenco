import Barenco.Universality.SynthesisResources
import Barenco.Universality.Section8BasicResources

/-!
# Resource sanity checks

Small, root-excluded examples for the fixed non-pruning exact-synthesis schedule.
They make the control-count convention visible: `controlCount = k` means register
width `k + 1`.
-/

namespace Barenco.Universality

noncomputable section

example : exactSynthesisBenchmark 0 = 1 := by
  norm_num [exactSynthesisBenchmark]

example : exactSynthesisBenchmark 1 = 16 := by
  norm_num [exactSynthesisBenchmark]

example : exactSynthesisBenchmark 2 = 144 := by
  norm_num [exactSynthesisBenchmark]

/-- Width one schedules one two-level factor and one diagonal pattern. -/
example : Nat.choose (2 ^ (0 + 1)) 2 + 2 ^ 0 = 2 := by
  norm_num [Nat.choose]

/-- Width two schedules six two-level factors and two diagonal patterns. -/
example : Nat.choose (2 ^ (1 + 1)) 2 + 2 ^ 1 = 8 := by
  norm_num [Nat.choose]

/-- Width three schedules twenty-eight factors and four diagonal patterns. -/
example : Nat.choose (2 ^ (2 + 1)) 2 + 2 ^ 2 = 32 := by
  norm_num [Nat.choose]

/-- Concrete specialization of the uniform width-two finite sandwich. -/
example (U : UnitaryGate 2) :
    16 ≤ exactSynthesisCost 1 U ∧ exactSynthesisCost 1 U ≤ 1792 := by
  simpa [exactSynthesisBenchmark] using exactSynthesisCost_bounds 1 U

end

end Barenco.Universality
