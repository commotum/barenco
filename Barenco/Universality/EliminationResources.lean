import Barenco.Universality.FiniteBridge
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Resource counts for finite-unitary elimination

The constructive elimination algorithm uses a fixed, non-pruning schedule.  This
file proves the exact number of recorded two-level factors without assigning a
cost to the factors themselves.  In dimension `d` the schedule records exactly
`d.choose 2` factors, including factors whose selected block happens to be the
identity for a particular input unitary.

Transport from `Fin d` to an arbitrary finite index type is only a list map, so
it preserves this algebraic factor count.  The final qubit specialization uses
the Hilbert-space dimension `2 ^ width`.
-/

namespace Barenco.Universality

open Matrix

noncomputable section

/-- Reversing and inverting a factor list preserves its length. -/
@[simp]
theorem inverseFactors_length {dimension : ℕ}
    (factors : List (FinTwoLevelFactor dimension)) :
    (inverseFactors factors).length = factors.length := by
  induction factors with
  | nil => rfl
  | cons factor factors ih =>
      simp [inverseFactors, ih]

/-- Embedding every factor into a successor dimension preserves list length. -/
@[simp]
theorem castSuccFactors_length {dimension : ℕ}
    (factors : List (FinTwoLevelFactor dimension)) :
    (castSuccFactors factors).length = factors.length := by
  simp [castSuccFactors]

/-- A pivot sweep records exactly one factor for every scheduled index. -/
@[simp]
theorem pivotEliminate_factors_length {dimension : ℕ} (pivot : Fin dimension)
    (indices : List {index : Fin dimension // index ≠ pivot})
    (U : Matrix.unitaryGroup (Fin dimension) ℂ) :
    (pivotEliminate pivot indices U).factors.length = indices.length := by
  induction indices generalizing U with
  | nil => rfl
  | cons index indices ih =>
      simp [pivotEliminate, ih]

/-- The successor pivot schedule visits every earlier coordinate exactly once. -/
@[simp]
theorem successorPivotSchedule_length (dimension : ℕ) :
    (successorPivotSchedule dimension).length = dimension := by
  simp [successorPivotSchedule]

/-- Eliminating the last column in dimension `dimension + 1` records `dimension` factors. -/
@[simp]
theorem eliminateLastColumn_factors_length {dimension : ℕ}
    (U : Matrix.unitaryGroup (Fin (dimension + 1)) ℂ) :
    (eliminateLastColumn U).factors.length = dimension := by
  simp [eliminateLastColumn]

/-- A recursive successor step adds the complete last-column sweep to the smaller list. -/
theorem successorFinTwoLevelDecomposition_factors_length {dimension : ℕ}
    (U : Matrix.unitaryGroup (Fin (dimension + 1)) ℂ)
    (smaller : FinTwoLevelDecomposition (eliminatedUpperUnitary U)) :
    (successorFinTwoLevelDecomposition U smaller).factors.length =
      dimension + smaller.factors.length := by
  simp [successorFinTwoLevelDecomposition, List.length_append]

/-- The triangular-number recurrence in the form used by the elimination recursion. -/
theorem choose_two_succ (dimension : ℕ) :
    Nat.choose (dimension + 1) 2 = dimension + Nat.choose dimension 2 := by
  rw [Nat.choose_succ_succ]
  simp

/--
The canonical non-pruning elimination in dimension `dimension` records exactly
one factor for every unordered pair of coordinates.
-/
@[simp]
theorem decomposeFinUnitary_factors_length (dimension : ℕ)
    (U : Matrix.unitaryGroup (Fin dimension) ℂ) :
    (decomposeFinUnitary dimension U).factors.length = Nat.choose dimension 2 := by
  induction dimension with
  | zero => rfl
  | succ dimension ih =>
      rw [decomposeFinUnitary]
      rw [successorFinTwoLevelDecomposition_factors_length]
      rw [ih]
      exact (choose_two_succ dimension).symm

/-- Reindexing the canonical decomposition onto an arbitrary finite type preserves its length. -/
@[simp]
theorem decomposeFiniteUnitary_factors_length {ι : Type*}
    [Fintype ι] [DecidableEq ι] (U : Matrix.unitaryGroup ι ℂ) :
    (decomposeFiniteUnitary U).factors.length = Nat.choose (Fintype.card ι) 2 := by
  simp [decomposeFiniteUnitary]

/-- The fixed elimination schedule for a `width`-qubit unitary has `choose (2^width) 2` factors. -/
theorem decomposeQubitUnitary_factors_length {width : ℕ} (U : UnitaryGate width) :
    (decomposeFiniteUnitary U).factors.length = Nat.choose (2 ^ width) 2 := by
  rw [decomposeFiniteUnitary_factors_length, card_basis]

/-- Closed product form for the factor count at a positive qubit width. -/
theorem choose_two_pow_succ (controlCount : ℕ) :
    Nat.choose (2 ^ (controlCount + 1)) 2 =
      2 ^ controlCount * (2 ^ (controlCount + 1) - 1) := by
  rw [Nat.choose_two_right, pow_succ]
  calc
    2 ^ controlCount * 2 * (2 ^ controlCount * 2 - 1) / 2 =
        2 * (2 ^ controlCount * (2 ^ controlCount * 2 - 1)) / 2 := by
          congr 1
          ac_rfl
    _ = 2 ^ controlCount * (2 ^ controlCount * 2 - 1) := by
      exact Nat.mul_div_cancel_left _ (by decide)

/-- Product-form factor count for a register with `controlCount + 1` wires. -/
theorem decomposeQubitUnitary_factors_length_succ (controlCount : ℕ)
    (U : UnitaryGate (controlCount + 1)) :
    (decomposeFiniteUnitary U).factors.length =
      2 ^ controlCount * (2 ^ (controlCount + 1) - 1) := by
  rw [decomposeQubitUnitary_factors_length, choose_two_pow_succ]

/-- A convenient square-dimension envelope for the fixed qubit factor count. -/
theorem choose_two_pow_le_four_pow (width : ℕ) :
    Nat.choose (2 ^ width) 2 ≤ 4 ^ width := by
  calc
    Nat.choose (2 ^ width) 2 ≤ (2 ^ width) ^ 2 := Nat.choose_le_pow _ _
    _ = 4 ^ width := by
      rw [pow_two, show 4 = 2 * 2 by decide, mul_pow]

/-- The factor list of every `width`-qubit input is bounded by `4^width`. -/
theorem decomposeQubitUnitary_factors_length_le_four_pow {width : ℕ}
    (U : UnitaryGate width) :
    (decomposeFiniteUnitary U).factors.length ≤ 4 ^ width := by
  rw [decomposeQubitUnitary_factors_length]
  exact choose_two_pow_le_four_pow width

end

end Barenco.Universality
