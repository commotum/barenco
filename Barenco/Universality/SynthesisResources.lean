import Barenco.Universality.DiagonalResources
import Barenco.Universality.EliminationResources
import Barenco.Universality.ExactSynthesis
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Aggregate resources of exact positive-width synthesis

The Stage 11 eliminator is deliberately non-pruning: in Hilbert dimension `d`
it emits all `d.choose 2` scheduled two-level factors, even when a factor is the
identity for a particular input.  Each factor and each diagonal-pattern block
has a syntax-derived quadratic cost envelope.  This module aggregates those
facts into a uniform finite sandwich and asymptotic theorems.

The resulting `Theta` theorem describes this fixed, non-pruning implementation.
It is not a lower bound on arbitrary circuits, not an optimal synthesis theorem,
and not the paper's unsupported `Theta(n^3 * 4^n)` argument.
-/

namespace Barenco.Universality

open Filter Asymptotics

noncomputable section

/-! ## Finite factor-list sums -/

/-- Every listed factor contributes at least register-width squared. -/
theorem length_mul_sq_succ_le_finiteFactorCircuitsCost (controlCount : ℕ) :
    ∀ factors : List (FiniteTwoLevelFactor (Basis (controlCount + 1))),
      factors.length * (controlCount + 1) ^ 2 ≤
        finiteFactorCircuitsCost controlCount factors
  | [] => by simp [finiteFactorCircuitsCost]
  | factor :: factors => by
      rw [finiteFactorCircuitsCost_cons, List.length_cons, Nat.add_mul]
      calc
        factors.length * (controlCount + 1) ^ 2 +
            1 * (controlCount + 1) ^ 2 ≤
          finiteFactorCircuitsCost controlCount factors +
            factor.circuitCost controlCount :=
          Nat.add_le_add
            (length_mul_sq_succ_le_finiteFactorCircuitsCost controlCount factors)
            (by simpa using factor.sq_succ_le_circuitCost controlCount)
        _ = factor.circuitCost controlCount +
            finiteFactorCircuitsCost controlCount factors := Nat.add_comm _ _

/-- Every listed factor is bounded by the common `56 * width²` envelope. -/
theorem finiteFactorCircuitsCost_le_length_mul_sq_succ (controlCount : ℕ) :
    ∀ factors : List (FiniteTwoLevelFactor (Basis (controlCount + 1))),
      finiteFactorCircuitsCost controlCount factors ≤
        factors.length * (56 * (controlCount + 1) ^ 2)
  | [] => by simp [finiteFactorCircuitsCost]
  | factor :: factors => by
      rw [finiteFactorCircuitsCost_cons, List.length_cons, Nat.add_mul]
      calc
        factor.circuitCost controlCount +
            finiteFactorCircuitsCost controlCount factors ≤
          1 * (56 * (controlCount + 1) ^ 2) +
            factors.length * (56 * (controlCount + 1) ^ 2) :=
          Nat.add_le_add
            (by simpa using factor.circuitCost_le_sq_succ controlCount)
            (finiteFactorCircuitsCost_le_length_mul_sq_succ controlCount factors)
        _ = factors.length * (56 * (controlCount + 1) ^ 2) +
            1 * (56 * (controlCount + 1) ^ 2) := Nat.add_comm _ _

/-! ## Component-count arithmetic -/

/-- The fixed factor schedule plus the diagonal schedule has `2 * 4^k` blocks. -/
theorem choose_two_pow_succ_add_pow (controlCount : ℕ) :
    Nat.choose (2 ^ (controlCount + 1)) 2 + 2 ^ controlCount =
      2 * 4 ^ controlCount := by
  rw [choose_two_pow_succ]
  let a := 2 ^ controlCount
  let b := 2 ^ (controlCount + 1)
  have hb : 1 ≤ b := by
    simp [b]
  calc
    a * (b - 1) + a = a * ((b - 1) + 1) := by ring
    _ = a * b := by rw [Nat.sub_add_cancel hb]
    _ = 2 * 4 ^ controlCount := by
      simp [a, b, pow_succ, show (4 : ℕ) = 2 * 2 by decide, mul_pow]
      ring

/-- The non-pruning two-level factor schedule alone has at least `4^k` factors. -/
theorem four_pow_le_choose_two_pow_succ (controlCount : ℕ) :
    4 ^ controlCount ≤ Nat.choose (2 ^ (controlCount + 1)) 2 := by
  rw [choose_two_pow_succ]
  have hpow : 1 ≤ 2 ^ controlCount := by simp
  have hright : 2 ^ controlCount ≤ 2 ^ (controlCount + 1) - 1 := by
    rw [pow_succ]
    omega
  calc
    4 ^ controlCount = 2 ^ controlCount * 2 ^ controlCount := by
      rw [show (4 : ℕ) = 2 * 2 by decide, mul_pow]
    _ ≤ 2 ^ controlCount * (2 ^ (controlCount + 1) - 1) :=
      Nat.mul_le_mul_left _ hright

/-! ## Pointwise exact-synthesis sandwich -/

/-- Natural benchmark in control-count indexing (`width = controlCount + 1`). -/
def exactSynthesisBenchmark (controlCount : ℕ) : ℕ :=
  (controlCount + 1) ^ 2 * 4 ^ controlCount

/-- Every input pays the complete non-pruning factor schedule. -/
theorem exactSynthesisBenchmark_le_cost (controlCount : ℕ)
    (U : UnitaryGate (controlCount + 1)) :
    exactSynthesisBenchmark controlCount ≤ exactSynthesisCost controlCount U := by
  let decomposition := decomposeFiniteUnitary U
  have hfactor := length_mul_sq_succ_le_finiteFactorCircuitsCost
    controlCount decomposition.factors
  have hlength : 4 ^ controlCount ≤ decomposition.factors.length := by
    rw [decomposeQubitUnitary_factors_length]
    exact four_pow_le_choose_two_pow_succ controlCount
  change (controlCount + 1) ^ 2 * 4 ^ controlCount ≤
    finiteFactorCircuitsCost controlCount decomposition.factors +
      diagonalPatternCircuitsCost (Fin.last controlCount)
        (allComplementPatterns (Fin.last controlCount))
  calc
    (controlCount + 1) ^ 2 * 4 ^ controlCount =
        4 ^ controlCount * (controlCount + 1) ^ 2 := Nat.mul_comm _ _
    _ ≤ decomposition.factors.length * (controlCount + 1) ^ 2 :=
      Nat.mul_le_mul_right _ hlength
    _ ≤ finiteFactorCircuitsCost controlCount decomposition.factors := hfactor
    _ ≤ finiteFactorCircuitsCost controlCount decomposition.factors +
        diagonalPatternCircuitsCost (Fin.last controlCount)
          (allComplementPatterns (Fin.last controlCount)) := Nat.le_add_right _ _

/-- Uniform finite upper bound for every exact synthesized unitary. -/
theorem exactSynthesisCost_le_benchmark (controlCount : ℕ)
    (U : UnitaryGate (controlCount + 1)) :
    exactSynthesisCost controlCount U ≤
      112 * exactSynthesisBenchmark controlCount := by
  let decomposition := decomposeFiniteUnitary U
  have hfactor := finiteFactorCircuitsCost_le_length_mul_sq_succ
    controlCount decomposition.factors
  have hdiagonal := diagonalCircuitCost_le_pow_two_mul_sq_succ controlCount
    (Fin.last controlCount)
  have hlength : decomposition.factors.length =
      Nat.choose (2 ^ (controlCount + 1)) 2 := by
    exact decomposeQubitUnitary_factors_length U
  change finiteFactorCircuitsCost controlCount decomposition.factors +
      diagonalPatternCircuitsCost (Fin.last controlCount)
        (allComplementPatterns (Fin.last controlCount)) ≤
      112 * ((controlCount + 1) ^ 2 * 4 ^ controlCount)
  calc
    finiteFactorCircuitsCost controlCount decomposition.factors +
        diagonalPatternCircuitsCost (Fin.last controlCount)
          (allComplementPatterns (Fin.last controlCount)) ≤
      decomposition.factors.length * (56 * (controlCount + 1) ^ 2) +
        2 ^ controlCount * (56 * (controlCount + 1) ^ 2) :=
      Nat.add_le_add hfactor hdiagonal
    _ = (decomposition.factors.length + 2 ^ controlCount) *
        (56 * (controlCount + 1) ^ 2) := by rw [Nat.add_mul]
    _ = 112 * ((controlCount + 1) ^ 2 * 4 ^ controlCount) := by
      rw [hlength, choose_two_pow_succ_add_pow]
      ring

/-- The exact finite sandwich for the selected, non-pruning syntax. -/
theorem exactSynthesisCost_bounds (controlCount : ℕ)
    (U : UnitaryGate (controlCount + 1)) :
    exactSynthesisBenchmark controlCount ≤ exactSynthesisCost controlCount U ∧
      exactSynthesisCost controlCount U ≤
        112 * exactSynthesisBenchmark controlCount :=
  ⟨exactSynthesisBenchmark_le_cost controlCount U,
    exactSynthesisCost_le_benchmark controlCount U⟩

/-! ## Family-level asymptotics -/

/-- Explicit Big-O constant for any successor-width unitary family. -/
theorem exactSynthesisCost_isBigOWith_fixedSchedule
    (family : ∀ controlCount : ℕ, UnitaryGate (controlCount + 1)) :
    IsBigOWith 112 atTop
      (fun controlCount : ℕ =>
        (exactSynthesisCost controlCount (family controlCount) : ℝ))
      (fun controlCount : ℕ => (exactSynthesisBenchmark controlCount : ℝ)) := by
  rw [isBigOWith_iff]
  filter_upwards [] with controlCount
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast exactSynthesisCost_le_benchmark controlCount (family controlCount)

/-- Reverse constant-one bound for the fixed non-pruning schedule. -/
theorem exactSynthesisBenchmark_isBigOWith_cost
    (family : ∀ controlCount : ℕ, UnitaryGate (controlCount + 1)) :
    IsBigOWith 1 atTop
      (fun controlCount : ℕ => (exactSynthesisBenchmark controlCount : ℝ))
      (fun controlCount : ℕ =>
        (exactSynthesisCost controlCount (family controlCount) : ℝ)) := by
  rw [isBigOWith_iff]
  filter_upwards [] with controlCount
  simp only [Real.norm_eq_abs, one_mul]
  rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast exactSynthesisBenchmark_le_cost controlCount (family controlCount)

/--
The exact cost of this deliberately non-pruning implementation is
`Theta((k+1)^2 * 4^k)`. This is not an optimal target-complexity theorem.
-/
theorem exactSynthesisCost_isTheta_fixedSchedule
    (family : ∀ controlCount : ℕ, UnitaryGate (controlCount + 1)) :
    (fun controlCount : ℕ =>
      (exactSynthesisCost controlCount (family controlCount) : ℝ)) =Θ[atTop]
      (fun controlCount : ℕ => (exactSynthesisBenchmark controlCount : ℝ)) :=
  ⟨(exactSynthesisCost_isBigOWith_fixedSchedule family).isBigO,
    (exactSynthesisBenchmark_isBigOWith_cost family).isBigO⟩

/-- Ordinary Big-O projection of the explicit constant theorem. -/
theorem exactSynthesisCost_isBigO_fixedSchedule
    (family : ∀ controlCount : ℕ, UnitaryGate (controlCount + 1)) :
    (fun controlCount : ℕ =>
      (exactSynthesisCost controlCount (family controlCount) : ℝ)) =O[atTop]
      (fun controlCount : ℕ => (exactSynthesisBenchmark controlCount : ℝ)) :=
  (exactSynthesisCost_isBigOWith_fixedSchedule family).isBigO

end

end Barenco.Universality
