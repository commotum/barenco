import Barenco.MultiControl.GrayMergers

/-!
# Diagnostics for the certified Gray boundary merger

This root-excluded leaf specializes the general syntax-derived formulas at one,
two, and three controls.  It also exercises exact semantics and literal CNOT
chronology on a reordered, nonconsecutive width-six layout with two spectator
wires.  The public parameterized proofs live in `GrayMergers`.
-/

namespace Barenco.MultiControl.GrayMergerExamples

open Barenco
open Barenco.Optimization
open OrderedControlLayout

noncomputable section

/-- Consecutive controls followed by their target, for small count checks. -/
def consecutiveLayout (controlCount : ℕ) :
    OrderedControlLayout controlCount (controlCount + 1) where
  controlWire := Fin.castSuccEmb
  targetWire := Fin.last controlCount
  control_ne_target := Fin.castSucc_ne_last

def oneControlLayout : OrderedControlLayout 1 2 := consecutiveLayout 1
def twoControlLayout : OrderedControlLayout 2 3 := consecutiveLayout 2
def threeControlLayout : OrderedControlLayout 3 4 := consecutiveLayout 3

/-- The single-root boundary remains the ordinary six-node implementation. -/
theorem oneControl_profile (U : QubitUnitary) :
    FusionCircuit.oneQubitCount
          (mergedGrayControlledFusionCircuit (tail := 0) oneControlLayout U) = 4 ∧
      FusionCircuit.cnotCount
          (mergedGrayControlledFusionCircuit (tail := 0) oneControlLayout U) = 2 ∧
      FusionCircuit.gateCount
          (mergedGrayControlledFusionCircuit (tail := 0) oneControlLayout U) = 6 := by
  rcases mergedGrayControlledFusionCircuit_profile oneControlLayout U with
    ⟨hone, hcnot, _, hgate, _⟩
  norm_num at hone hcnot hgate
  exact ⟨hone, hcnot, hgate⟩

/-- Two controls exercise both alternating signs and both merger orientations. -/
theorem twoControl_profile (U : QubitUnitary) :
    FusionCircuit.oneQubitCount
          (mergedGrayControlledFusionCircuit (tail := 1) twoControlLayout U) = 8 ∧
      FusionCircuit.cnotCount
          (mergedGrayControlledFusionCircuit (tail := 1) twoControlLayout U) = 8 ∧
      FusionCircuit.gateCount
          (mergedGrayControlledFusionCircuit (tail := 1) twoControlLayout U) = 16 := by
  rcases mergedGrayControlledFusionCircuit_profile twoControlLayout U with
    ⟨hone, hcnot, _, hgate, _⟩
  norm_num at hone hcnot hgate
  exact ⟨hone, hcnot, hgate⟩

/-- The paper's seven-root example has the checked post-merger profile. -/
theorem threeControl_profile (U : QubitUnitary) :
    FusionCircuit.oneQubitCount
          (mergedGrayControlledFusionCircuit (tail := 2) threeControlLayout U) = 16 ∧
      FusionCircuit.cnotCount
          (mergedGrayControlledFusionCircuit (tail := 2) threeControlLayout U) = 20 ∧
      FusionCircuit.gateCount
          (mergedGrayControlledFusionCircuit (tail := 2) threeControlLayout U) = 36 := by
  rcases mergedGrayControlledFusionCircuit_profile threeControlLayout U with
    ⟨hone, hcnot, _, hgate, _⟩
  norm_num at hone hcnot hgate
  exact ⟨hone, hcnot, hgate⟩

/--
Controls `4,0,5` and target `2`: reordered orientations, nonadjacency, and two
spectator wires all occur in the same width-six diagnostic.
-/
def reorderedPaddedLayout : OrderedControlLayout 3 6 where
  controlWire :=
    { toFun := ![4, 0, 5]
      inj' := by
        intro first second h
        fin_cases first <;> fin_cases second <;> simp at h ⊢ }
  targetWire := 2
  control_ne_target := by
    intro control
    fin_cases control <;> decide

/-- The general resource result is independent of ambient ordering and padding. -/
theorem reorderedPadded_profile (U : QubitUnitary) :
    FusionCircuit.oneQubitCount
          (mergedGrayControlledFusionCircuit (tail := 2)
            reorderedPaddedLayout U) = 16 ∧
      FusionCircuit.cnotCount
          (mergedGrayControlledFusionCircuit (tail := 2)
            reorderedPaddedLayout U) = 20 ∧
      FusionCircuit.gateCount
          (mergedGrayControlledFusionCircuit (tail := 2)
            reorderedPaddedLayout U) = 36 := by
  rcases mergedGrayControlledFusionCircuit_profile reorderedPaddedLayout U with
    ⟨hone, hcnot, _, hgate, _⟩
  norm_num at hone hcnot hgate
  exact ⟨hone, hcnot, hgate⟩

/-- Exact arbitrary-register semantics, including both spectator wires. -/
theorem reorderedPadded_eval (U : QubitUnitary) :
    Circuit.eval
        (mergedGrayControlledCircuit (tail := 2) reorderedPaddedLayout U) =
      positiveControlledUnitary reorderedPaddedLayout.targetWire
        reorderedPaddedLayout.controlSet U := by
  exact eval_mergedGrayControlledCircuit reorderedPaddedLayout U

/-- The complete oriented CNOT trace is unchanged by every merger. -/
theorem reorderedPadded_cnotTrace (V : QubitUnitary) :
    SymbolicCircuit.cnotTrace
        (mergedGrayControlledViaRootSymbolicCircuit
          (tail := 2) reorderedPaddedLayout) =
      SymbolicCircuit.cnotTrace
        (coherentGrayControlledViaRootCircuit reorderedPaddedLayout V) := by
  exact cnotTrace_mergedGrayControlledViaRootSymbolicCircuit_eq_raw
    reorderedPaddedLayout V

/-- The counted circuit is literally the executable merger's emitted output. -/
theorem reorderedPadded_output_is_normalForm :
    mergedGrayControlledViaRootSymbolicCircuit
        (tail := 2) reorderedPaddedLayout =
      mergedGrayControlledViaRootNormalForm reorderedPaddedLayout := by
  exact mergedGrayControlledViaRootSymbolicCircuit_eq_normalForm
    reorderedPaddedLayout

end

end Barenco.MultiControl.GrayMergerExamples
