import Barenco.Universality.DiagonalCircuit
import Barenco.Universality.TwoLevelResources

/-!
# Structural resources for exact diagonal synthesis

For a register of width `controlCount + 1`, the exact diagonal construction has
one mixed-polarity block for every assignment of the `controlCount` complementary
wires.  This module proves that cardinality and bounds the exact finite sum from
`DiagonalCircuit` directly.

Every statement counts the named literal syntax.  No resource conclusion is
inferred from the evaluator equality `eval_diagonalCircuit`.
-/

namespace Barenco.Universality

noncomputable section

/-! ## Complementary-pattern cardinality -/

/-- There are exactly `controlCount` wires other than a selected target. -/
theorem card_targetComplement (controlCount : ℕ)
    (target : Fin (controlCount + 1)) :
    Fintype.card (TargetComplement target) = controlCount := by
  calc
    Fintype.card (TargetComplement target) = Fintype.card (Fin controlCount) :=
      (Fintype.card_congr (finSuccAboveEquiv target)).symm
    _ = controlCount := Fintype.card_fin controlCount

/-- Complementary Boolean assignments number `2^controlCount`. -/
theorem card_complementBasis (controlCount : ℕ)
    (target : Fin (controlCount + 1)) :
    Fintype.card (ComplementBasis target) = 2 ^ controlCount := by
  rw [Fintype.card_fun, card_targetComplement]
  norm_num

/-- The complete diagonal schedule contains every complementary pattern once. -/
@[simp]
theorem allComplementPatterns_length (controlCount : ℕ)
    (target : Fin (controlCount + 1)) :
    (allComplementPatterns target).length = 2 ^ controlCount := by
  rw [allComplementPatterns, Finset.length_toList, Finset.card_univ,
    card_complementBasis]

/-! ## Per-pattern bounds -/

/-- A negative-control prefix flips at most all complementary wires. -/
theorem patternFlipCount_le_controlCount {controlCount : ℕ}
    {target : Fin (controlCount + 1)} (pattern : ComplementBasis target) :
    patternFlipCount pattern ≤ controlCount := by
  rw [patternFlipCount, falsePatternWires, List.length_map,
    falsePatternControls, Finset.length_toList]
  calc
    (Finset.univ.filter fun wire : TargetComplement target =>
      pattern wire = false).card ≤
        (Finset.univ : Finset (TargetComplement target)).card :=
      Finset.card_filter_le _ _
    _ = Fintype.card (TargetComplement target) := Finset.card_univ
    _ = controlCount := card_targetComplement controlCount target

/-- Exact numeric cost contributed by one complementary pattern. -/
def diagonalPatternCost (controlCount : ℕ)
    {target : Fin (controlCount + 1)}
    (pattern : ComplementBasis target) : ℕ :=
  2 * patternFlipCount pattern + fullControlCircuitCost controlCount

/-- Every scheduled pattern contains at least the quadratic full-control block. -/
theorem sq_succ_le_diagonalPatternCost (controlCount : ℕ)
    {target : Fin (controlCount + 1)}
    (pattern : ComplementBasis target) :
    (controlCount + 1) ^ 2 ≤ diagonalPatternCost controlCount pattern := by
  rw [diagonalPatternCost]
  have hfull := sq_succ_le_fullControlCircuitCost controlCount
  omega

/-- The same `56 * width²` envelope absorbs all negative-control flips. -/
theorem diagonalPatternCost_le_sq_succ (controlCount : ℕ)
    {target : Fin (controlCount + 1)}
    (pattern : ComplementBasis target) :
    diagonalPatternCost controlCount pattern ≤
      56 * (controlCount + 1) ^ 2 := by
  rw [diagonalPatternCost]
  have hflip := patternFlipCount_le_controlCount pattern
  have hfull := fullControlCircuitCost_add_linear_le_sq_succ controlCount
  omega

/-! ## Finite schedules -/

/-- The existing exact finite-sum definition is the sum of `diagonalPatternCost`. -/
theorem diagonalPatternCircuitsCost_eq_map_sum (controlCount : ℕ)
    (target : Fin (controlCount + 1))
    (patterns : List (ComplementBasis target)) :
    diagonalPatternCircuitsCost target patterns =
      (patterns.map (diagonalPatternCost controlCount)).sum := rfl

/-- Lower bound from the actual number of scheduled pattern blocks. -/
theorem length_mul_sq_succ_le_diagonalPatternCircuitsCost (controlCount : ℕ)
    (target : Fin (controlCount + 1)) :
    ∀ patterns : List (ComplementBasis target),
      patterns.length * (controlCount + 1) ^ 2 ≤
        diagonalPatternCircuitsCost target patterns
  | [] => by simp [diagonalPatternCircuitsCost]
  | pattern :: patterns => by
      rw [diagonalPatternCircuitsCost, List.map_cons, List.sum_cons]
      change (patterns.length + 1) * (controlCount + 1) ^ 2 ≤
        diagonalPatternCost controlCount pattern +
          (patterns.map (diagonalPatternCost controlCount)).sum
      rw [Nat.add_mul]
      calc
        patterns.length * (controlCount + 1) ^ 2 +
            1 * (controlCount + 1) ^ 2 ≤
          (patterns.map (diagonalPatternCost controlCount)).sum +
            diagonalPatternCost controlCount pattern :=
          Nat.add_le_add
            (length_mul_sq_succ_le_diagonalPatternCircuitsCost
              controlCount target patterns)
            (by simpa using
              sq_succ_le_diagonalPatternCost controlCount pattern)
        _ = diagonalPatternCost controlCount pattern +
            (patterns.map (diagonalPatternCost controlCount)).sum := Nat.add_comm _ _

/-- Upper bound from the actual number of scheduled pattern blocks. -/
theorem diagonalPatternCircuitsCost_le_length_mul_sq_succ (controlCount : ℕ)
    (target : Fin (controlCount + 1)) :
    ∀ patterns : List (ComplementBasis target),
      diagonalPatternCircuitsCost target patterns ≤
        patterns.length * (56 * (controlCount + 1) ^ 2)
  | [] => by simp [diagonalPatternCircuitsCost]
  | pattern :: patterns => by
      rw [diagonalPatternCircuitsCost, List.map_cons, List.sum_cons]
      change diagonalPatternCost controlCount pattern +
          (patterns.map (diagonalPatternCost controlCount)).sum ≤
        (patterns.length + 1) * (56 * (controlCount + 1) ^ 2)
      rw [Nat.add_mul]
      calc
        diagonalPatternCost controlCount pattern +
            (patterns.map (diagonalPatternCost controlCount)).sum ≤
          1 * (56 * (controlCount + 1) ^ 2) +
            patterns.length * (56 * (controlCount + 1) ^ 2) :=
          Nat.add_le_add
            (by simpa using diagonalPatternCost_le_sq_succ controlCount pattern)
            (diagonalPatternCircuitsCost_le_length_mul_sq_succ
              controlCount target patterns)
        _ = patterns.length * (56 * (controlCount + 1) ^ 2) +
            1 * (56 * (controlCount + 1) ^ 2) := Nat.add_comm _ _

/-- Exact complete diagonal cost is bounded below by its `2^k` quadratic blocks. -/
theorem pow_two_mul_sq_succ_le_diagonalCircuitCost (controlCount : ℕ)
    (target : Fin (controlCount + 1)) :
    2 ^ controlCount * (controlCount + 1) ^ 2 ≤
      diagonalPatternCircuitsCost target (allComplementPatterns target) := by
  simpa using
    length_mul_sq_succ_le_diagonalPatternCircuitsCost controlCount target
      (allComplementPatterns target)

/-- Exact complete diagonal cost has the matching componentwise quadratic envelope. -/
theorem diagonalCircuitCost_le_pow_two_mul_sq_succ (controlCount : ℕ)
    (target : Fin (controlCount + 1)) :
    diagonalPatternCircuitsCost target (allComplementPatterns target) ≤
      2 ^ controlCount * (56 * (controlCount + 1) ^ 2) := by
  simpa using
    diagonalPatternCircuitsCost_le_length_mul_sq_succ controlCount target
      (allComplementPatterns target)

end

end Barenco.Universality
