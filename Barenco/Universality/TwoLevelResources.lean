import Barenco.Universality.TwoLevelCircuit

/-!
# Uniform resources for synthesized two-level unitaries

This module bounds the exact syntax-derived cost of the Stage 11 affine
two-level construction.  If `controlCount = k`, the register width is `k + 1`.
The selected full-control implementation lies between `(k+1)^2` and
`56 * (k+1)^2`.  Its unused upper-envelope slack also absorbs the literal
affine transport and negative-control conjugations, so every complete
two-level factor satisfies the same sandwich.

These are bounds for the named construction, not optimality or lower bounds
for arbitrary implementations of the same unitary.
-/

namespace Barenco.Universality

noncomputable section

/-! ## Full-control polynomial envelope -/

/-- The selected full-control construction costs at least the square of its width. -/
theorem sq_succ_le_fullControlCircuitCost :
    ∀ controlCount : ℕ,
      (controlCount + 1) ^ 2 ≤ fullControlCircuitCost controlCount
  | 0 => by norm_num [fullControlCircuitCost]
  | 1 => by norm_num [fullControlCircuitCost]
  | 2 => by norm_num [fullControlCircuitCost]
  | 3 => by norm_num [fullControlCircuitCost]
  | 4 => by norm_num [fullControlCircuitCost]
  | 5 => by norm_num [fullControlCircuitCost]
  | depth + 6 => by
      simp only [fullControlCircuitCost]
      nlinarith

/-- The selected full-control construction costs at most `56` times width squared. -/
theorem fullControlCircuitCost_le_sq_succ :
    ∀ controlCount : ℕ,
      fullControlCircuitCost controlCount ≤ 56 * (controlCount + 1) ^ 2
  | 0 => by norm_num [fullControlCircuitCost]
  | 1 => by norm_num [fullControlCircuitCost]
  | 2 => by norm_num [fullControlCircuitCost]
  | 3 => by norm_num [fullControlCircuitCost]
  | 4 => by norm_num [fullControlCircuitCost]
  | 5 => by norm_num [fullControlCircuitCost]
  | depth + 6 => by
      simp only [fullControlCircuitCost]
      nlinarith

/-!
The complete factor adds at most `6k+2` primitives around the full-control
block.  The following strengthened bound records that the same `56(k+1)^2`
envelope still absorbs those nodes.
-/
theorem fullControlCircuitCost_add_linear_le_sq_succ :
    ∀ controlCount : ℕ,
      fullControlCircuitCost controlCount + (6 * controlCount + 2) ≤
        56 * (controlCount + 1) ^ 2
  | 0 => by norm_num [fullControlCircuitCost]
  | 1 => by norm_num [fullControlCircuitCost]
  | 2 => by norm_num [fullControlCircuitCost]
  | 3 => by norm_num [fullControlCircuitCost]
  | 4 => by norm_num [fullControlCircuitCost]
  | 5 => by norm_num [fullControlCircuitCost]
  | depth + 6 => by
      simp only [fullControlCircuitCost]
      nlinarith

/-! ## Affine transport bounds -/

/-- An assignment has at most one true bit per register wire. -/
theorem trueBitCount_le_width {width : ℕ} (input : Basis width) :
    trueBitCount input ≤ width := by
  simpa [trueBitCount, trueWireList] using
    (Finset.card_le_univ
      (s := Finset.univ.filter fun wire : Fin width => input wire = true))

/-- Removing the required differing pivot leaves at most `controlCount` CNOTs. -/
theorem affinePairCNOTCount_le_controlCount {controlCount : ℕ}
    (first second : Basis (controlCount + 1))
    (hfirstSecond : first ≠ second) :
    affinePairCNOTCount first second hfirstSecond ≤ controlCount := by
  rw [affinePairCNOTCount_eq]
  have hdist : hammingDist first second ≤ controlCount + 1 := by
    simpa using hammingDist_le_card_fintype (x := first) (y := second)
  have hpositive : 1 ≤ hammingDist first second :=
    (hammingDist_pos.mpr hfirstSecond)
  omega

/-- The affine normalization uses at most `2k+1` primitives on `k+1` wires. -/
theorem affinePairGateCount_le {controlCount : ℕ}
    (first second : Basis (controlCount + 1))
    (hfirstSecond : first ≠ second) :
    affinePairGateCount first second hfirstSecond ≤ 2 * controlCount + 1 := by
  rw [affinePairGateCount]
  have htrue := trueBitCount_le_width first
  have hcnot := affinePairCNOTCount_le_controlCount first second hfirstSecond
  omega

/-! ## Canonical adjacent cost -/

/-- Every complementary bit of the all-zero basis assignment is false. -/
theorem splitTarget_allZero_complement_apply {controlCount : ℕ}
    (target : Fin (controlCount + 1))
    (wire : TargetComplement target) :
    (splitTarget target (allZeroBasis : Basis (controlCount + 1))).2 wire = false := rfl

/-- The canonical adjacent block flips every one of the `controlCount` controls. -/
@[simp]
theorem patternFlipCount_splitTarget_allZero {controlCount : ℕ}
    (target : Fin (controlCount + 1)) :
    patternFlipCount
      ((splitTarget target (allZeroBasis : Basis (controlCount + 1))).2) =
        controlCount := by
  rw [patternFlipCount, falsePatternWires, List.length_map,
    falsePatternControls, Finset.length_toList]
  have hall :
      (Finset.univ.filter fun wire : TargetComplement target =>
        (splitTarget target (allZeroBasis : Basis (controlCount + 1))).2 wire = false) =
        Finset.univ := by
    ext wire
    simp
  rw [hall, Finset.card_univ]
  calc
    Fintype.card (TargetComplement target) = Fintype.card (Fin controlCount) :=
      (Fintype.card_congr (finSuccAboveEquiv target)).symm
    _ = controlCount := Fintype.card_fin controlCount

/-- Closed cost of the canonical all-zero/singleton adjacent block. -/
@[simp]
theorem canonicalAdjacentTwoLevelCircuitCost_eq (controlCount : ℕ)
    (pivot : Fin (controlCount + 1)) :
    canonicalAdjacentTwoLevelCircuitCost controlCount pivot =
      2 * controlCount + fullControlCircuitCost controlCount := by
  simp [canonicalAdjacentTwoLevelCircuitCost]

/-! ## Complete two-level factor sandwich -/

/-- Every selected two-level circuit costs at least register-width squared. -/
theorem sq_succ_le_twoLevelCircuitCost (controlCount : ℕ)
    (first second : Basis (controlCount + 1))
    (hfirstSecond : first ≠ second) :
    (controlCount + 1) ^ 2 ≤
      twoLevelCircuitCost controlCount first second hfirstSecond := by
  rw [twoLevelCircuitCost, canonicalAdjacentTwoLevelCircuitCost_eq]
  have hfull := sq_succ_le_fullControlCircuitCost controlCount
  omega

/-- Every selected two-level circuit costs at most `56` times width squared. -/
theorem twoLevelCircuitCost_le_sq_succ (controlCount : ℕ)
    (first second : Basis (controlCount + 1))
    (hfirstSecond : first ≠ second) :
    twoLevelCircuitCost controlCount first second hfirstSecond ≤
      56 * (controlCount + 1) ^ 2 := by
  rw [twoLevelCircuitCost, canonicalAdjacentTwoLevelCircuitCost_eq]
  have haffine := affinePairGateCount_le first second hfirstSecond
  have hfull := fullControlCircuitCost_add_linear_le_sq_succ controlCount
  omega

/-- Combined pointwise sandwich for the exact cost of a synthesized two-level block. -/
theorem twoLevelCircuitCost_bounds (controlCount : ℕ)
    (first second : Basis (controlCount + 1))
    (hfirstSecond : first ≠ second) :
    (controlCount + 1) ^ 2 ≤
        twoLevelCircuitCost controlCount first second hfirstSecond ∧
      twoLevelCircuitCost controlCount first second hfirstSecond ≤
        56 * (controlCount + 1) ^ 2 :=
  ⟨sq_succ_le_twoLevelCircuitCost controlCount first second hfirstSecond,
    twoLevelCircuitCost_le_sq_succ controlCount first second hfirstSecond⟩

namespace FiniteTwoLevelFactor

/-- Every transported finite two-level factor inherits the same cost sandwich. -/
theorem circuitCost_bounds (controlCount : ℕ)
    (factor : FiniteTwoLevelFactor (Basis (controlCount + 1))) :
    (controlCount + 1) ^ 2 ≤ factor.circuitCost controlCount ∧
      factor.circuitCost controlCount ≤ 56 * (controlCount + 1) ^ 2 := by
  exact twoLevelCircuitCost_bounds controlCount factor.first factor.second factor.distinct

/-- Lower half of `circuitCost_bounds`. -/
theorem sq_succ_le_circuitCost (controlCount : ℕ)
    (factor : FiniteTwoLevelFactor (Basis (controlCount + 1))) :
    (controlCount + 1) ^ 2 ≤ factor.circuitCost controlCount :=
  (factor.circuitCost_bounds controlCount).1

/-- Upper half of `circuitCost_bounds`. -/
theorem circuitCost_le_sq_succ (controlCount : ℕ)
    (factor : FiniteTwoLevelFactor (Basis (controlCount + 1))) :
    factor.circuitCost controlCount ≤ 56 * (controlCount + 1) ^ 2 :=
  (factor.circuitCost_bounds controlCount).2

end FiniteTwoLevelFactor

end

end Barenco.Universality
