import Barenco.MultiControl.Borrowed

/-!
# Diagnostic examples for the dirty-borrowed inward ladder

This file pins the smallest instance of Barenco et al., Lemma 7.2 and the
paper's displayed `n = 9`, `m = 5` instance. It is intentionally excluded from
the public root: the general construction, semantics, and resource theorems live
in `Borrowed`, `BorrowedSemantics`, and `BorrowedResources`.
-/

namespace Barenco.MultiControl.BorrowedExamples

open Barenco
open Barenco.MultiControl
open InwardLadderLayout

/-! ## Smallest supported boundary: three controls and one dirty wire -/

/-- Controls occupy `0,1,2`, the dirty borrow is `3`, and the target is `4`. -/
def threeControlLayout : InwardLadderLayout 1 5 where
  wire := finSumFinEquiv.toEmbedding

private def threeControlQ1 : Primitive 5 :=
  threeControlLayout.outerToffoli

private def threeControlQ2 : Primitive 5 :=
  threeControlLayout.smaller.baseToffoli

/-- At the `m = 3` boundary the chronology is `q₁;q₂;q₁;q₂`. -/
theorem threeControl_chronology :
    inwardLadderCircuit threeControlLayout =
      [threeControlQ1, threeControlQ2, threeControlQ1, threeControlQ2] := by
  rfl

/-- The outer node uses the last control, dirty wire, and final target. -/
theorem threeControlQ1_support :
    threeControlQ1.support = {(2 : Fin 5), 3, 4} := by
  decide

/-- The inner node computes the conjunction of the first two controls. -/
theorem threeControlQ2_support :
    threeControlQ2.support = {(0 : Fin 5), 1, 3} := by
  decide

/-- The smallest valid construction contains exactly four Toffoli macros. -/
theorem threeControl_counts :
    Circuit.gateCount (inwardLadderCircuit threeControlLayout) = 4 ∧
      Circuit.kindCount .toffoli (inwardLadderCircuit threeControlLayout) = 4 := by
  simp

/-! ## The source's displayed nine-wire, five-control ladder -/

/--
The canonical nine-wire placement uses controls `0,…,4`, dirty wires `5,6,7`,
and target `8`.  These are the paper's one-indexed wires `1,…,9` shifted by one.
-/
def fiveControlNineWireLayout : InwardLadderLayout 3 9 where
  wire := finSumFinEquiv.toEmbedding

private def sourceQ1 : Primitive 9 :=
  fiveControlNineWireLayout.outerToffoli

private def sourceQ2 : Primitive 9 :=
  fiveControlNineWireLayout.smaller.outerToffoli

private def sourceQ3 : Primitive 9 :=
  fiveControlNineWireLayout.smaller.smaller.outerToffoli

private def sourceQ4 : Primitive 9 :=
  fiveControlNineWireLayout.smaller.smaller.smaller.baseToffoli

/-- `q₁ = T(4,7 → 8)` in zero-based wire numbering. -/
theorem sourceQ1_support : sourceQ1.support = {(4 : Fin 9), 7, 8} := by
  decide

/-- `q₂ = T(3,6 → 7)` in zero-based wire numbering. -/
theorem sourceQ2_support : sourceQ2.support = {(3 : Fin 9), 6, 7} := by
  decide

/-- `q₃ = T(2,5 → 6)` in zero-based wire numbering. -/
theorem sourceQ3_support : sourceQ3.support = {(2 : Fin 9), 5, 6} := by
  decide

/-- `q₄ = T(0,1 → 5)` in zero-based wire numbering. -/
theorem sourceQ4_support : sourceQ4.support = {(0 : Fin 9), 1, 5} := by
  decide

/--
Exact reconstruction of the twelve-node diagram, stored in execution order.
-/
theorem fiveControlNineWire_chronology :
    inwardLadderCircuit fiveControlNineWireLayout =
      [sourceQ1, sourceQ2, sourceQ3, sourceQ4, sourceQ3, sourceQ2,
        sourceQ1, sourceQ2, sourceQ3, sourceQ4, sourceQ3, sourceQ2] := by
  rfl

/-- The displayed circuit contains twelve gates and all twelve are Toffolis. -/
theorem fiveControlNineWire_counts :
    Circuit.gateCount (inwardLadderCircuit fiveControlNineWireLayout) = 12 ∧
      Circuit.kindCount .toffoli (inwardLadderCircuit fiveControlNineWireLayout) = 12 := by
  simp

/-! ## Executable dirty-bit diagnostics -/

private def sourceUpdates : List (Basis 9 → Basis 9) :=
  [ Primitive.toffoliBasisUpdate 4 7 8,
    Primitive.toffoliBasisUpdate 3 6 7,
    Primitive.toffoliBasisUpdate 2 5 6,
    Primitive.toffoliBasisUpdate 0 1 5,
    Primitive.toffoliBasisUpdate 2 5 6,
    Primitive.toffoliBasisUpdate 3 6 7,
    Primitive.toffoliBasisUpdate 4 7 8,
    Primitive.toffoliBasisUpdate 3 6 7,
    Primitive.toffoliBasisUpdate 2 5 6,
    Primitive.toffoliBasisUpdate 0 1 5,
    Primitive.toffoliBasisUpdate 2 5 6,
    Primitive.toffoliBasisUpdate 3 6 7 ]

private def runSourceUpdates (input : Basis 9) : Basis 9 :=
  sourceUpdates.foldl (fun state update => update state) input

private def activeDirtyInput : Basis 9 := fun wire =>
  decide (wire ∈ ({0, 1, 2, 3, 4, 5, 7} : Finset (Fin 9)))

private def activeDirtyOutput : Basis 9 := fun wire =>
  decide (wire ∈ ({0, 1, 2, 3, 4, 5, 7, 8} : Finset (Fin 9)))

/-- Arbitrary dirty pattern `101` is restored while all five controls flip the target. -/
example : runSourceUpdates activeDirtyInput = activeDirtyOutput := by
  decide

private def inactiveDirtyInput : Basis 9 := fun wire =>
  decide (wire ∈ ({0, 1, 2, 4, 6, 8} : Finset (Fin 9)))

/-- With one control false, a different dirty pattern is restored and the target is unchanged. -/
example : runSourceUpdates inactiveDirtyInput = inactiveDirtyInput := by
  decide

end Barenco.MultiControl.BorrowedExamples
