import Barenco.MultiControl.Resources

/-!
# Diagnostic boundaries for the recursive multi-control construction

This root-excluded leaf pins the one-control semantic boundary and the first two
levels of the fully primitive recursion.  These specializations are sanity
checks only; the public arbitrary-width evaluator and count proofs live in
`Recursive`, `RecursiveExpansion`, and `Resources`.
-/

namespace Barenco.MultiControl.RecursiveExamples

open Barenco
open OrderedControlLayout

noncomputable section

/-- Consecutive controls `0,…,k-1` followed by target wire `k`. -/
def consecutiveLayout (controlCount : ℕ) :
    OrderedControlLayout controlCount (controlCount + 1) where
  controlWire := Fin.castSuccEmb
  targetWire := Fin.last controlCount
  control_ne_target := Fin.castSucc_ne_last

/-! ## Zero- and one-control semantic boundaries -/

def oneControlLayout : OrderedControlLayout 1 2 := consecutiveLayout 1

/-- Lemma 7.5 genuinely specializes to a single positive control. -/
theorem oneControl_eval (U : QubitUnitary) :
    Circuit.eval (oneControlLayout.recursiveRootCircuit U) =
      positiveControlledUnitary oneControlLayout.targetWire
        oneControlLayout.controlSet U := by
  exact eval_recursiveRootCircuit oneControlLayout U

/-- At the boundary, two macros have arity one and three have arity zero. -/
theorem oneControl_macroProfile (V : QubitUnitary) :
    Circuit.gateCount (oneControlLayout.recursiveViaSquareCircuit V) = 5 ∧
      Circuit.kindCount (.controlledOneQubit 1)
          (oneControlLayout.recursiveViaSquareCircuit V) = 2 ∧
      Circuit.kindCount (.controlledOneQubit 0)
          (oneControlLayout.recursiveViaSquareCircuit V) = 3 ∧
      Circuit.cost CostModel.oneQubitCNOT
          (oneControlLayout.recursiveViaSquareCircuit V) = none := by
  constructor
  · exact recursiveViaSquareCircuit_gateCount oneControlLayout V
  constructor
  · simpa using recursiveViaSquareCircuit_kindCount oneControlLayout V
      (.controlledOneQubit 1)
  constructor
  · simpa using recursiveViaSquareCircuit_kindCount oneControlLayout V
      (.controlledOneQubit 0)
  · exact recursiveViaSquareCircuit_oneQubitCNOTCost oneControlLayout V

/-- Zero controls are a separate one-node local circuit, not a Gray recursion. -/
theorem zeroControl_profile (U : QubitUnitary) :
    Circuit.eval (zeroControlCircuit (0 : Fin 1) U) = localUnitary 0 U ∧
      Circuit.gateCount (zeroControlCircuit (0 : Fin 1) U) = 1 ∧
      Circuit.cost CostModel.oneQubitCNOT
          (zeroControlCircuit (0 : Fin 1) U) = some 1 := by
  simp

/-! ## Direct base and first primitive recursive step -/

def depthZeroLayout : OrderedControlLayout 6 7 := consecutiveLayout 6
def depthOneLayout : OrderedControlLayout 7 8 := consecutiveLayout 7

/-- The first recursive step uses wire seven as dirty target and wire six as MCX target. -/
theorem depthOne_workspaceRoles :
    (depthOneLayout.recursivePrefixFourBlockLayout (by decide)).dirtyWire =
        depthOneLayout.targetWire ∧
      (depthOneLayout.recursivePrefixFourBlockLayout (by decide)).targetWire =
        depthOneLayout.lastControlWire := by
  constructor <;> simp

theorem depthZero_eval (U : QubitUnitary) :
    Circuit.eval (recursivePrimitiveCircuit 0 depthZeroLayout U) =
      positiveControlledUnitary depthZeroLayout.targetWire
        depthZeroLayout.controlSet U := by
  exact eval_recursivePrimitiveCircuit 0 depthZeroLayout U

theorem depthOne_eval (U : QubitUnitary) :
    Circuit.eval (recursivePrimitiveCircuit 1 depthOneLayout U) =
      positiveControlledUnitary depthOneLayout.targetWire
        depthOneLayout.controlSet U := by
  exact eval_recursivePrimitiveCircuit 1 depthOneLayout U

theorem depthZero_resources (U : QubitUnitary) :
    Circuit.kindCount .oneQubit
        (recursivePrimitiveCircuit 0 depthZeroLayout U) = 252 ∧
      Circuit.kindCount .cnot
        (recursivePrimitiveCircuit 0 depthZeroLayout U) = 188 ∧
      Circuit.gateCount (recursivePrimitiveCircuit 0 depthZeroLayout U) = 440 ∧
      Circuit.cost CostModel.oneQubitCNOT
        (recursivePrimitiveCircuit 0 depthZeroLayout U) = some 440 := by
  exact recursivePrimitiveCircuit_depth_zero_resources depthZeroLayout U

theorem depthOne_resources (U : QubitUnitary) :
    Circuit.kindCount .oneQubit
        (recursivePrimitiveCircuit 1 depthOneLayout U) = 484 ∧
      Circuit.kindCount .cnot
        (recursivePrimitiveCircuit 1 depthOneLayout U) = 376 ∧
      Circuit.gateCount (recursivePrimitiveCircuit 1 depthOneLayout U) = 860 ∧
      Circuit.cost CostModel.oneQubitCNOT
        (recursivePrimitiveCircuit 1 depthOneLayout U) = some 860 := by
  exact recursivePrimitiveCircuit_depth_one_resources depthOneLayout U

/-- The width-indexed resource API agrees at its smallest two legal widths. -/
theorem widthSevenEight_resources :
    recursivePrimitiveOneQubitCountAtWidth 7 = 252 ∧
      recursivePrimitiveCNOTCountAtWidth 7 = 188 ∧
      recursivePrimitiveTotalCountAtWidth 7 = 440 ∧
      recursivePrimitiveOneQubitCountAtWidth 8 = 484 ∧
      recursivePrimitiveCNOTCountAtWidth 8 = 376 ∧
      recursivePrimitiveTotalCountAtWidth 8 = 860 := by
  norm_num [recursivePrimitiveOneQubitCountAtWidth,
    recursivePrimitiveCNOTCountAtWidth, recursivePrimitiveTotalCountAtWidth,
    recursivePrimitiveOneQubitCount, recursivePrimitiveCNOTCount,
    recursivePrimitiveTotalCount]

end

end Barenco.MultiControl.RecursiveExamples
