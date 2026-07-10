import Barenco.MultiControl.RecursiveExpansion
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Resources of the recursive exact multi-control construction

This module packages the exact syntax counts already proved for
`recursivePrimitiveCircuit` as reusable natural-number functions.  Depth zero
is the directly expanded six-control Gray circuit, so depth `d` represents a
logical source width of `d + 7` qubits.

Every equality below counts the named construction.  The resulting `O(n²)`
theorems are construction-specific upper bounds; they do not state that optimal
exact synthesis has quadratic complexity, and no `Θ(n²)` optimality claim is
made.
-/

namespace Barenco.MultiControl

open Filter Asymptotics

/-! ## Exact depth-indexed count functions -/

/-- Exact one-qubit count of the named depth-`depth` primitive construction. -/
def recursivePrimitiveOneQubitCount (depth : ℕ) : ℕ :=
  32 * depth ^ 2 + 200 * depth + 252

/-- Exact CNOT count of the named depth-`depth` primitive construction. -/
def recursivePrimitiveCNOTCount (depth : ℕ) : ℕ :=
  24 * depth ^ 2 + 164 * depth + 188

/-- Exact total primitive count, and early-basic cost, of the named construction. -/
def recursivePrimitiveTotalCount (depth : ℕ) : ℕ :=
  56 * depth ^ 2 + 364 * depth + 440

@[simp]
theorem recursivePrimitiveOneQubitCount_zero :
    recursivePrimitiveOneQubitCount 0 = 252 := by
  norm_num [recursivePrimitiveOneQubitCount]

@[simp]
theorem recursivePrimitiveCNOTCount_zero :
    recursivePrimitiveCNOTCount 0 = 188 := by
  norm_num [recursivePrimitiveCNOTCount]

@[simp]
theorem recursivePrimitiveTotalCount_zero :
    recursivePrimitiveTotalCount 0 = 440 := by
  norm_num [recursivePrimitiveTotalCount]

/-- One recursive level adds the two selected controlled gates and two MCX expansions. -/
@[simp]
theorem recursivePrimitiveOneQubitCount_succ (depth : ℕ) :
    recursivePrimitiveOneQubitCount (depth + 1) =
      recursivePrimitiveOneQubitCount depth + 64 * depth + 232 := by
  simp [recursivePrimitiveOneQubitCount]
  ring

@[simp]
theorem recursivePrimitiveCNOTCount_succ (depth : ℕ) :
    recursivePrimitiveCNOTCount (depth + 1) =
      recursivePrimitiveCNOTCount depth + 48 * depth + 188 := by
  simp [recursivePrimitiveCNOTCount]
  ring

@[simp]
theorem recursivePrimitiveTotalCount_succ (depth : ℕ) :
    recursivePrimitiveTotalCount (depth + 1) =
      recursivePrimitiveTotalCount depth + 112 * depth + 420 := by
  simp [recursivePrimitiveTotalCount]
  ring

/-- The named primitive syntax contains only the counted one-qubit and CNOT nodes. -/
@[simp]
theorem recursivePrimitiveTotalCount_eq_add (depth : ℕ) :
    recursivePrimitiveTotalCount depth =
      recursivePrimitiveOneQubitCount depth + recursivePrimitiveCNOTCount depth := by
  simp [recursivePrimitiveTotalCount, recursivePrimitiveOneQubitCount,
    recursivePrimitiveCNOTCount]
  ring

/-! ## Exact linkage to circuit syntax -/

namespace OrderedControlLayout

/-- The numerical one-qubit function is exactly the circuit's structural count. -/
@[simp]
theorem recursivePrimitiveCircuit_oneQubitCount_eq_resource
    {depth ambientWidth : ℕ}
    (layout : OrderedControlLayout (depth + 6) ambientWidth)
    (U : QubitUnitary) :
    Circuit.kindCount .oneQubit (recursivePrimitiveCircuit depth layout U) =
      recursivePrimitiveOneQubitCount depth := by
  simpa [recursivePrimitiveOneQubitCount] using
    recursivePrimitiveCircuit_oneQubitCount depth layout U

/-- The numerical CNOT function is exactly the circuit's structural count. -/
@[simp]
theorem recursivePrimitiveCircuit_cnotCount_eq_resource
    {depth ambientWidth : ℕ}
    (layout : OrderedControlLayout (depth + 6) ambientWidth)
    (U : QubitUnitary) :
    Circuit.kindCount .cnot (recursivePrimitiveCircuit depth layout U) =
      recursivePrimitiveCNOTCount depth := by
  simpa [recursivePrimitiveCNOTCount] using
    recursivePrimitiveCircuit_cnotCount depth layout U

/-- The numerical total function is exactly the circuit's primitive-node count. -/
@[simp]
theorem recursivePrimitiveCircuit_gateCount_eq_resource
    {depth ambientWidth : ℕ}
    (layout : OrderedControlLayout (depth + 6) ambientWidth)
    (U : QubitUnitary) :
    Circuit.gateCount (recursivePrimitiveCircuit depth layout U) =
      recursivePrimitiveTotalCount depth := by
  simpa [recursivePrimitiveTotalCount] using
    recursivePrimitiveCircuit_gateCount depth layout U

/-- The same total is accepted exactly by the Sections 3–7 cost model. -/
@[simp]
theorem recursivePrimitiveCircuit_oneQubitCNOTCost_eq_resource
    {depth ambientWidth : ℕ}
    (layout : OrderedControlLayout (depth + 6) ambientWidth)
    (U : QubitUnitary) :
    Circuit.cost CostModel.oneQubitCNOT (recursivePrimitiveCircuit depth layout U) =
      some (recursivePrimitiveTotalCount depth) := by
  simpa [recursivePrimitiveTotalCount] using
    recursivePrimitiveCircuit_oneQubitCNOTCost depth layout U

end OrderedControlLayout

/-! ## Source-width views -/

/-- One-qubit count indexed by logical source width; meaningful synthesis starts at seven. -/
def recursivePrimitiveOneQubitCountAtWidth (sourceWidth : ℕ) : ℕ :=
  recursivePrimitiveOneQubitCount (sourceWidth - 7)

/-- CNOT count indexed by logical source width; meaningful synthesis starts at seven. -/
def recursivePrimitiveCNOTCountAtWidth (sourceWidth : ℕ) : ℕ :=
  recursivePrimitiveCNOTCount (sourceWidth - 7)

/-- Total primitive count indexed by logical source width. -/
def recursivePrimitiveTotalCountAtWidth (sourceWidth : ℕ) : ℕ :=
  recursivePrimitiveTotalCount (sourceWidth - 7)

/-- Nat-safe width form of the exact one-qubit count. -/
theorem recursivePrimitiveOneQubitCountAtWidth_eq (sourceWidth : ℕ)
    (hwidth : 7 ≤ sourceWidth) :
    recursivePrimitiveOneQubitCountAtWidth sourceWidth =
      32 * sourceWidth ^ 2 + 420 - 248 * sourceWidth := by
  obtain ⟨depth, rfl⟩ := Nat.exists_eq_add_of_le hwidth
  simp only [recursivePrimitiveOneQubitCountAtWidth, Nat.add_sub_cancel_left]
  apply Nat.eq_sub_of_add_eq
  simp [recursivePrimitiveOneQubitCount]
  ring

/-- Nat-safe width form of the exact CNOT count. -/
theorem recursivePrimitiveCNOTCountAtWidth_eq (sourceWidth : ℕ)
    (hwidth : 7 ≤ sourceWidth) :
    recursivePrimitiveCNOTCountAtWidth sourceWidth =
      24 * sourceWidth ^ 2 + 216 - 172 * sourceWidth := by
  obtain ⟨depth, rfl⟩ := Nat.exists_eq_add_of_le hwidth
  simp only [recursivePrimitiveCNOTCountAtWidth, Nat.add_sub_cancel_left]
  apply Nat.eq_sub_of_add_eq
  simp [recursivePrimitiveCNOTCount]
  ring

/--
Nat-safe width form of the exact total.  The addition precedes subtraction so
the statement does not suffer from an intermediate truncated subtraction.
-/
theorem recursivePrimitiveTotalCountAtWidth_eq (sourceWidth : ℕ)
    (hwidth : 7 ≤ sourceWidth) :
    recursivePrimitiveTotalCountAtWidth sourceWidth =
      56 * sourceWidth ^ 2 + 636 - 420 * sourceWidth := by
  obtain ⟨depth, rfl⟩ := Nat.exists_eq_add_of_le hwidth
  simp only [recursivePrimitiveTotalCountAtWidth, Nat.add_sub_cancel_left]
  apply Nat.eq_sub_of_add_eq
  simp [recursivePrimitiveTotalCount]
  ring

@[simp]
theorem recursivePrimitiveTotalCountAtWidth_eq_add (sourceWidth : ℕ) :
    recursivePrimitiveTotalCountAtWidth sourceWidth =
      recursivePrimitiveOneQubitCountAtWidth sourceWidth +
        recursivePrimitiveCNOTCountAtWidth sourceWidth := by
  simp [recursivePrimitiveTotalCountAtWidth,
    recursivePrimitiveOneQubitCountAtWidth,
    recursivePrimitiveCNOTCountAtWidth]

/-! ## Width-indexed successor recurrences -/

theorem recursivePrimitiveOneQubitCountAtWidth_succ (sourceWidth : ℕ)
    (hwidth : 7 ≤ sourceWidth) :
    recursivePrimitiveOneQubitCountAtWidth (sourceWidth + 1) =
      recursivePrimitiveOneQubitCountAtWidth sourceWidth +
        (64 * sourceWidth - 216) := by
  simp only [recursivePrimitiveOneQubitCountAtWidth]
  have hdepth : sourceWidth + 1 - 7 = (sourceWidth - 7) + 1 := by
    omega
  rw [hdepth, recursivePrimitiveOneQubitCount_succ]
  congr 1
  omega

theorem recursivePrimitiveCNOTCountAtWidth_succ (sourceWidth : ℕ)
    (hwidth : 7 ≤ sourceWidth) :
    recursivePrimitiveCNOTCountAtWidth (sourceWidth + 1) =
      recursivePrimitiveCNOTCountAtWidth sourceWidth +
        (48 * sourceWidth - 148) := by
  simp only [recursivePrimitiveCNOTCountAtWidth]
  have hdepth : sourceWidth + 1 - 7 = (sourceWidth - 7) + 1 := by
    omega
  rw [hdepth, recursivePrimitiveCNOTCount_succ]
  congr 1
  omega

/-- The exact named construction adds `112n-364` primitives from width `n` to `n+1`. -/
theorem recursivePrimitiveTotalCountAtWidth_succ (sourceWidth : ℕ)
    (hwidth : 7 ≤ sourceWidth) :
    recursivePrimitiveTotalCountAtWidth (sourceWidth + 1) =
      recursivePrimitiveTotalCountAtWidth sourceWidth +
        (112 * sourceWidth - 364) := by
  simp only [recursivePrimitiveTotalCountAtWidth]
  have hdepth : sourceWidth + 1 - 7 = (sourceWidth - 7) + 1 := by
    omega
  rw [hdepth, recursivePrimitiveTotalCount_succ]
  congr 1
  omega

/-! ## Construction-specific quadratic upper bounds -/

/-- Explicit eventual quadratic bound in recursion depth. -/
theorem recursivePrimitiveTotalCount_isBigOWith_depth :
    IsBigOWith 860 atTop
      (fun depth : ℕ => (recursivePrimitiveTotalCount depth : ℝ))
      (fun depth : ℕ => (depth : ℝ) ^ 2) := by
  rw [isBigOWith_iff]
  filter_upwards [eventually_ge_atTop 1] with depth hdepth
  simp only [recursivePrimitiveTotalCount, Real.norm_eq_abs]
  push_cast
  have hpoly :
      (0 : ℝ) ≤ 56 * (depth : ℝ) ^ 2 + 364 * depth + 440 := by
    positivity
  rw [abs_of_nonneg hpoly, abs_of_nonneg (sq_nonneg (depth : ℝ))]
  have hdepthOne : 1 ≤ (depth : ℝ) := by
    exact_mod_cast hdepth
  have hdepthLeSq : (depth : ℝ) ≤ (depth : ℝ) ^ 2 := by
    nlinarith
  have honeLeSq : (1 : ℝ) ≤ (depth : ℝ) ^ 2 := by
    nlinarith
  nlinarith

/-- The exact count of this named algorithm is `O(depth²)`. -/
theorem recursivePrimitiveTotalCount_isBigO_depth :
    (fun depth : ℕ => (recursivePrimitiveTotalCount depth : ℝ)) =O[atTop]
      (fun depth : ℕ => (depth : ℝ) ^ 2) :=
  recursivePrimitiveTotalCount_isBigOWith_depth.isBigO

/-- For every legal width, the exact count is at most `56 * width²`. -/
theorem recursivePrimitiveTotalCountAtWidth_le_sq (sourceWidth : ℕ)
    (hwidth : 7 ≤ sourceWidth) :
    recursivePrimitiveTotalCountAtWidth sourceWidth ≤ 56 * sourceWidth ^ 2 := by
  rw [recursivePrimitiveTotalCountAtWidth_eq sourceWidth hwidth]
  omega

/-- Explicit eventual quadratic bound in logical source width. -/
theorem recursivePrimitiveTotalCount_isBigOWith_width :
    IsBigOWith 56 atTop
      (fun sourceWidth : ℕ =>
        (recursivePrimitiveTotalCountAtWidth sourceWidth : ℝ))
      (fun sourceWidth : ℕ => (sourceWidth : ℝ) ^ 2) := by
  rw [isBigOWith_iff]
  filter_upwards [eventually_ge_atTop 7] with sourceWidth hwidth
  have hle := recursivePrimitiveTotalCountAtWidth_le_sq sourceWidth hwidth
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ (recursivePrimitiveTotalCountAtWidth sourceWidth : ℝ)),
    abs_of_nonneg (sq_nonneg (sourceWidth : ℝ))]
  exact_mod_cast hle

/-- The exact count of this named width-indexed algorithm is `O(width²)`. -/
theorem recursivePrimitiveTotalCount_isBigO_width :
    (fun sourceWidth : ℕ =>
      (recursivePrimitiveTotalCountAtWidth sourceWidth : ℝ)) =O[atTop]
      (fun sourceWidth : ℕ => (sourceWidth : ℝ) ^ 2) :=
  recursivePrimitiveTotalCount_isBigOWith_width.isBigO

end Barenco.MultiControl
