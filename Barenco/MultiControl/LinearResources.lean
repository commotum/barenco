import Barenco.MultiControl.CleanAncillaExpansion
import Barenco.MultiControl.LinearSpecialUnitaryExpansion
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Resources of the linear multi-control constructions

This module packages the exact primitive-syntax counts proved for the two
Stage 8 constructions as functions of their logical source width.

* `linearSU2*CountAtWidth` counts the exact fully controlled special-unitary
  circuit reconstructed from Lemma 7.9.
* `cleanAncilla*CountAtWidth` counts the exact one-clean-ancilla circuit
  reconstructed from Lemma 7.11.

Both selected primitive expansions are available from width seven onward.  All
equalities below count these named circuits.  The resulting `O(n)` theorems are
construction-specific upper bounds: they do not assert that optimal synthesis
has linear complexity, and no `Theta(n)` or matching lower-bound claim is made.
-/

namespace Barenco.MultiControl

open Filter Asymptotics

/-! ## Fully controlled special-unitary count functions -/

/--
Exact one-qubit count of the named Lemma 7.9 construction at logical width
`sourceWidth`; its selected expansion is meaningful when `7 ≤ sourceWidth`.
-/
def linearSU2OneQubitCountAtWidth (sourceWidth : ℕ) : ℕ :=
  64 * (sourceWidth - 2) - 151

/-- Exact CNOT count of the named Lemma 7.9 construction. -/
def linearSU2CNOTCountAtWidth (sourceWidth : ℕ) : ℕ :=
  48 * (sourceWidth - 2) - 98

/-- Exact total primitive count, and early-basic cost, of the named construction. -/
def linearSU2TotalCountAtWidth (sourceWidth : ℕ) : ℕ :=
  112 * (sourceWidth - 2) - 249

/-- Nat-safe logical-width form of the exact one-qubit count. -/
theorem linearSU2OneQubitCountAtWidth_eq (sourceWidth : ℕ)
    (hwidth : 7 ≤ sourceWidth) :
    linearSU2OneQubitCountAtWidth sourceWidth =
      64 * sourceWidth - 279 := by
  simp only [linearSU2OneQubitCountAtWidth]
  omega

/-- Nat-safe logical-width form of the exact CNOT count. -/
theorem linearSU2CNOTCountAtWidth_eq (sourceWidth : ℕ)
    (hwidth : 7 ≤ sourceWidth) :
    linearSU2CNOTCountAtWidth sourceWidth =
      48 * sourceWidth - 194 := by
  simp only [linearSU2CNOTCountAtWidth]
  omega

/-- Nat-safe logical-width form of the exact total primitive count. -/
theorem linearSU2TotalCountAtWidth_eq (sourceWidth : ℕ)
    (hwidth : 7 ≤ sourceWidth) :
    linearSU2TotalCountAtWidth sourceWidth =
      112 * sourceWidth - 473 := by
  simp only [linearSU2TotalCountAtWidth]
  omega

/-- The total is exactly the sum of the two primitive component counts. -/
theorem linearSU2TotalCountAtWidth_eq_add (sourceWidth : ℕ)
    (hwidth : 7 ≤ sourceWidth) :
    linearSU2TotalCountAtWidth sourceWidth =
      linearSU2OneQubitCountAtWidth sourceWidth +
        linearSU2CNOTCountAtWidth sourceWidth := by
  rw [linearSU2TotalCountAtWidth_eq sourceWidth hwidth,
    linearSU2OneQubitCountAtWidth_eq sourceWidth hwidth,
    linearSU2CNOTCountAtWidth_eq sourceWidth hwidth]
  omega

/-! ## One-clean-ancilla count functions -/

/--
Exact one-qubit count of the named Lemma 7.11 construction at logical width
`sourceWidth`; its selected expansion is meaningful when `7 ≤ sourceWidth`.
-/
def cleanAncillaOneQubitCountAtWidth (sourceWidth : ℕ) : ℕ :=
  64 * (sourceWidth - 2) - 156

/-- Exact CNOT count of the named one-clean-ancilla construction. -/
def cleanAncillaCNOTCountAtWidth (sourceWidth : ℕ) : ℕ :=
  48 * (sourceWidth - 2) - 102

/-- Exact total primitive count, and early-basic cost, of the named construction. -/
def cleanAncillaTotalCountAtWidth (sourceWidth : ℕ) : ℕ :=
  112 * (sourceWidth - 2) - 258

/-- Nat-safe logical-width form of the exact one-qubit count. -/
theorem cleanAncillaOneQubitCountAtWidth_eq (sourceWidth : ℕ)
    (hwidth : 7 ≤ sourceWidth) :
    cleanAncillaOneQubitCountAtWidth sourceWidth =
      64 * sourceWidth - 284 := by
  simp only [cleanAncillaOneQubitCountAtWidth]
  omega

/-- Nat-safe logical-width form of the exact CNOT count. -/
theorem cleanAncillaCNOTCountAtWidth_eq (sourceWidth : ℕ)
    (hwidth : 7 ≤ sourceWidth) :
    cleanAncillaCNOTCountAtWidth sourceWidth =
      48 * sourceWidth - 198 := by
  simp only [cleanAncillaCNOTCountAtWidth]
  omega

/-- Nat-safe logical-width form of the exact total primitive count. -/
theorem cleanAncillaTotalCountAtWidth_eq (sourceWidth : ℕ)
    (hwidth : 7 ≤ sourceWidth) :
    cleanAncillaTotalCountAtWidth sourceWidth =
      112 * sourceWidth - 482 := by
  simp only [cleanAncillaTotalCountAtWidth]
  omega

/-- The total is exactly the sum of the two primitive component counts. -/
theorem cleanAncillaTotalCountAtWidth_eq_add (sourceWidth : ℕ)
    (hwidth : 7 ≤ sourceWidth) :
    cleanAncillaTotalCountAtWidth sourceWidth =
      cleanAncillaOneQubitCountAtWidth sourceWidth +
        cleanAncillaCNOTCountAtWidth sourceWidth := by
  rw [cleanAncillaTotalCountAtWidth_eq sourceWidth hwidth,
    cleanAncillaOneQubitCountAtWidth_eq sourceWidth hwidth,
    cleanAncillaCNOTCountAtWidth_eq sourceWidth hwidth]
  omega

/-! ## Exact linkage to primitive circuit syntax -/

namespace OrderedControlLayout

/-- The numerical one-qubit function is exactly the Lemma 7.9 circuit count. -/
@[simp]
theorem expandedLinearSU2Circuit_oneQubitCount_eq_resource
    {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) (W : QubitSpecialUnitary) :
    Circuit.kindCount .oneQubit
        (layout.expandedLinearSU2Circuit hwidth W) =
      linearSU2OneQubitCountAtWidth (p + 2) := by
  rw [expandedLinearSU2Circuit_oneQubitCount]
  simp [linearSU2OneQubitCountAtWidth]

/-- The numerical CNOT function is exactly the Lemma 7.9 circuit count. -/
@[simp]
theorem expandedLinearSU2Circuit_cnotCount_eq_resource
    {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) (W : QubitSpecialUnitary) :
    Circuit.kindCount .cnot (layout.expandedLinearSU2Circuit hwidth W) =
      linearSU2CNOTCountAtWidth (p + 2) := by
  rw [expandedLinearSU2Circuit_cnotCount]
  simp [linearSU2CNOTCountAtWidth]

/-- The numerical total function is exactly the Lemma 7.9 primitive-node count. -/
@[simp]
theorem expandedLinearSU2Circuit_gateCount_eq_resource
    {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) (W : QubitSpecialUnitary) :
    Circuit.gateCount (layout.expandedLinearSU2Circuit hwidth W) =
      linearSU2TotalCountAtWidth (p + 2) := by
  rw [expandedLinearSU2Circuit_gateCount]
  simp [linearSU2TotalCountAtWidth]

/-- The same Lemma 7.9 total is accepted exactly by the early-basic cost model. -/
@[simp]
theorem expandedLinearSU2Circuit_oneQubitCNOTCost_eq_resource
    {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) (W : QubitSpecialUnitary) :
    Circuit.cost CostModel.oneQubitCNOT
        (layout.expandedLinearSU2Circuit hwidth W) =
      some (linearSU2TotalCountAtWidth (p + 2)) := by
  rw [expandedLinearSU2Circuit_oneQubitCNOTCost]
  simp [linearSU2TotalCountAtWidth]

/-- The numerical one-qubit function is exactly the clean-ancilla circuit count. -/
@[simp]
theorem expandedCleanAncillaCircuit_oneQubitCount_eq_resource
    {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) (U : QubitUnitary) :
    Circuit.kindCount .oneQubit
        (layout.expandedCleanAncillaCircuit hwidth U) =
      cleanAncillaOneQubitCountAtWidth (p + 2) := by
  rw [expandedCleanAncillaCircuit_oneQubitCount]
  simp [cleanAncillaOneQubitCountAtWidth]

/-- The numerical CNOT function is exactly the clean-ancilla circuit count. -/
@[simp]
theorem expandedCleanAncillaCircuit_cnotCount_eq_resource
    {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) (U : QubitUnitary) :
    Circuit.kindCount .cnot (layout.expandedCleanAncillaCircuit hwidth U) =
      cleanAncillaCNOTCountAtWidth (p + 2) := by
  rw [expandedCleanAncillaCircuit_cnotCount]
  simp [cleanAncillaCNOTCountAtWidth]

/-- The numerical total function is exactly the clean-ancilla primitive count. -/
@[simp]
theorem expandedCleanAncillaCircuit_gateCount_eq_resource
    {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) (U : QubitUnitary) :
    Circuit.gateCount (layout.expandedCleanAncillaCircuit hwidth U) =
      cleanAncillaTotalCountAtWidth (p + 2) := by
  rw [expandedCleanAncillaCircuit_gateCount]
  simp [cleanAncillaTotalCountAtWidth]

/-- The same clean-ancilla total is accepted exactly by the early-basic model. -/
@[simp]
theorem expandedCleanAncillaCircuit_oneQubitCNOTCost_eq_resource
    {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) (U : QubitUnitary) :
    Circuit.cost CostModel.oneQubitCNOT
        (layout.expandedCleanAncillaCircuit hwidth U) =
      some (cleanAncillaTotalCountAtWidth (p + 2)) := by
  rw [expandedCleanAncillaCircuit_oneQubitCNOTCost]
  simp [cleanAncillaTotalCountAtWidth]

end OrderedControlLayout

/-! ## Construction-specific linear upper bounds -/

/-- The exact Lemma 7.9 construction count is at most `112 * sourceWidth`. -/
theorem linearSU2TotalCountAtWidth_le (sourceWidth : ℕ)
    (hwidth : 7 ≤ sourceWidth) :
    linearSU2TotalCountAtWidth sourceWidth ≤ 112 * sourceWidth := by
  rw [linearSU2TotalCountAtWidth_eq sourceWidth hwidth]
  omega

/-- Explicit eventual linear bound for the named Lemma 7.9 construction. -/
theorem linearSU2TotalCount_isBigOWith_width :
    IsBigOWith 112 atTop
      (fun sourceWidth : ℕ =>
        (linearSU2TotalCountAtWidth sourceWidth : ℝ))
      (fun sourceWidth : ℕ => (sourceWidth : ℝ)) := by
  rw [isBigOWith_iff]
  filter_upwards [eventually_ge_atTop 7] with sourceWidth hwidth
  have hle := linearSU2TotalCountAtWidth_le sourceWidth hwidth
  have hcountNonneg :
      (0 : ℝ) ≤ (linearSU2TotalCountAtWidth sourceWidth : ℝ) :=
    Nat.cast_nonneg _
  have hwidthNonneg : (0 : ℝ) ≤ (sourceWidth : ℝ) := Nat.cast_nonneg _
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg hcountNonneg, abs_of_nonneg hwidthNonneg]
  exact_mod_cast hle

/-- The exact count of the named Lemma 7.9 algorithm is `O(sourceWidth)`. -/
theorem linearSU2TotalCount_isBigO_width :
    (fun sourceWidth : ℕ =>
      (linearSU2TotalCountAtWidth sourceWidth : ℝ)) =O[atTop]
      (fun sourceWidth : ℕ => (sourceWidth : ℝ)) :=
  linearSU2TotalCount_isBigOWith_width.isBigO

/-- The exact clean-ancilla construction count is at most `112 * sourceWidth`. -/
theorem cleanAncillaTotalCountAtWidth_le (sourceWidth : ℕ)
    (hwidth : 7 ≤ sourceWidth) :
    cleanAncillaTotalCountAtWidth sourceWidth ≤ 112 * sourceWidth := by
  rw [cleanAncillaTotalCountAtWidth_eq sourceWidth hwidth]
  omega

/-- Explicit eventual linear bound for the named one-clean-ancilla construction. -/
theorem cleanAncillaTotalCount_isBigOWith_width :
    IsBigOWith 112 atTop
      (fun sourceWidth : ℕ =>
        (cleanAncillaTotalCountAtWidth sourceWidth : ℝ))
      (fun sourceWidth : ℕ => (sourceWidth : ℝ)) := by
  rw [isBigOWith_iff]
  filter_upwards [eventually_ge_atTop 7] with sourceWidth hwidth
  have hle := cleanAncillaTotalCountAtWidth_le sourceWidth hwidth
  have hcountNonneg :
      (0 : ℝ) ≤ (cleanAncillaTotalCountAtWidth sourceWidth : ℝ) :=
    Nat.cast_nonneg _
  have hwidthNonneg : (0 : ℝ) ≤ (sourceWidth : ℝ) := Nat.cast_nonneg _
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg hcountNonneg, abs_of_nonneg hwidthNonneg]
  exact_mod_cast hle

/-- The exact count of the named clean-ancilla algorithm is `O(sourceWidth)`. -/
theorem cleanAncillaTotalCount_isBigO_width :
    (fun sourceWidth : ℕ =>
      (cleanAncillaTotalCountAtWidth sourceWidth : ℝ)) =O[atTop]
      (fun sourceWidth : ℕ => (sourceWidth : ℝ)) :=
  cleanAncillaTotalCount_isBigOWith_width.isBigO

end Barenco.MultiControl
