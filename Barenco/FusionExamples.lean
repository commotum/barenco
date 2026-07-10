import Barenco.ControlledCircuit.CanonicalSelected
import Barenco.ThreeQubit.RelativePhaseFusion

/-!
# Payload-preserving fusion diagnostics

This root-excluded leaf exercises the exact lowering, chronology, barrier, model,
and paper-input boundaries of the fusion IR.  These checks are intentionally not
part of the public `Barenco` import surface.
-/

namespace Barenco.FusionExamples

open Barenco.Optimization

/-! ## Ordered-pair visible lowering -/

private theorem fin2_zero_ne_one : (0 : Fin 2) ≠ 1 := by decide

/-- Canonical ordered pair `(0,1)` at width two. -/
def widthTwoPair : OrderedWirePair 2 :=
  ⟨0, 1, fin2_zero_ne_one⟩

/-- One optimizer-visible arbitrary `U(4)` node at width two. -/
def widthTwoVisibleSingleton (U : TwoQubitUnitary) : FusionCircuit 2 :=
  [FusionPrimitive.twoQubit widthTwoPair U]

/-- Width-two lowering uses the trusted arbitrary-two-qubit constructor exactly. -/
@[simp]
theorem lower_widthTwoVisibleSingleton (U : TwoQubitUnitary) :
    (widthTwoVisibleSingleton U).lower =
      [Primitive.twoQubit widthTwoPair U] := rfl

/-- The independent fusion evaluator agrees with the certified two-wire embedding. -/
@[simp]
theorem eval_widthTwoVisibleSingleton (U : TwoQubitUnitary) :
    (widthTwoVisibleSingleton U).eval = twoWireUnitary widthTwoPair U := by
  simp [widthTwoVisibleSingleton, FusionCircuit.eval,
    FusionPrimitive.denotation]

private theorem fin5_four_ne_one : (4 : Fin 5) ≠ 1 := by decide

/-- Nonadjacent, oriented width-five pair `(4,1)`. -/
def nonAdjacentPair : OrderedWirePair 5 :=
  ⟨4, 1, fin5_four_ne_one⟩

/-- One visible arbitrary two-wire node on the nonadjacent pair. -/
def nonAdjacentVisibleSingleton (U : TwoQubitUnitary) : FusionCircuit 5 :=
  [FusionPrimitive.twoQubit nonAdjacentPair U]

/-- Nonadjacent lowering retains pair orientation and the complete local payload. -/
@[simp]
theorem lower_nonAdjacentVisibleSingleton (U : TwoQubitUnitary) :
    (nonAdjacentVisibleSingleton U).lower =
      [Primitive.twoQubit nonAdjacentPair U] := rfl

/-- The nonadjacent singleton has exact arbitrary-width certified semantics. -/
@[simp]
theorem eval_nonAdjacentVisibleSingleton (U : TwoQubitUnitary) :
    (nonAdjacentVisibleSingleton U).eval =
      twoWireUnitary nonAdjacentPair U := by
  simp [nonAdjacentVisibleSingleton, FusionCircuit.eval,
    FusionPrimitive.denotation]

/-! ## Head-first chronology -/

/-- Two local payloads on the same pair, listed in execution order `U;V`. -/
def widthTwoChronology (U V : TwoQubitUnitary) : FusionCircuit 2 :=
  [FusionPrimitive.twoQubit widthTwoPair U,
    FusionPrimitive.twoQubit widthTwoPair V]

/-- Head-first syntax `U;V` denotes the chronological local product `V * U`. -/
theorem eval_widthTwoChronology (U V : TwoQubitUnitary) :
    (widthTwoChronology U V).eval =
      twoWireUnitary widthTwoPair (V * U) := by
  simp only [widthTwoChronology, FusionCircuit.eval_cons,
    FusionCircuit.eval_nil, FusionPrimitive.denotation, one_mul]
  exact twoWireUnitary_chronological widthTwoPair U V

/-! ## Exact opaque-barrier preservation -/

private theorem fin3_zero_ne_one : (0 : Fin 3) ≠ 1 := by decide
private theorem fin3_zero_ne_two : (0 : Fin 3) ≠ 2 := by decide
private theorem fin3_one_ne_two : (1 : Fin 3) ≠ 2 := by decide

/-- A trusted Toffoli macro, unsupported by both named paper cost models. -/
def unsupportedToffoli : Primitive 3 :=
  Primitive.toffoli 0 1 2 fin3_zero_ne_one fin3_zero_ne_two fin3_one_ne_two

/-- Preserve the trusted unsupported node through the explicit barrier path. -/
def unsupportedBarrierProgram : FusionProgram 3 :=
  FusionProgram.barriers [unsupportedToffoli]

/-- All-barrier lowering is an exact syntax round trip. -/
@[simp]
theorem lower_unsupportedBarrierProgram :
    unsupportedBarrierProgram.lower = [unsupportedToffoli] := by
  simp [unsupportedBarrierProgram]

/-- Barrier evaluation is exactly the original trusted circuit evaluation. -/
@[simp]
theorem eval_unsupportedBarrierProgram :
    unsupportedBarrierProgram.eval = Circuit.eval [unsupportedToffoli] := by
  simp [unsupportedBarrierProgram]

/-- A barrier preserves rejection by both named models; it is never priced optimistically. -/
theorem unsupportedBarrierProgram_namedModelCosts :
    FusionProgram.cost CostModel.oneQubitCNOT unsupportedBarrierProgram = none ∧
      FusionProgram.cost CostModel.arbitraryTwoQubit unsupportedBarrierProgram = none := by
  constructor <;> rfl

/-! ## Named-model separation -/

/-- The same visible `U(4)` node is rejected early and costs one in Section 8. -/
theorem widthTwoVisibleSingleton_modelSeparation (U : TwoQubitUnitary) :
    FusionCircuit.cost CostModel.oneQubitCNOT
        (widthTwoVisibleSingleton U) = none ∧
      FusionCircuit.cost CostModel.arbitraryTwoQubit
        (widthTwoVisibleSingleton U) = some 1 := by
  constructor <;> rfl

/-! ## Transparent controlled-U boundary -/

/--
At width two the transparent selected controlled-`U` builder has its exact
full-register evaluator and literal `(4,2,6)` profile.
-/
theorem canonicalControlledU_widthTwo_profile (U : QubitUnitary) :
    (ControlledCircuit.canonicalSelectedControlledU2FusionCircuit
        (0 : Fin 2) (1 : Fin 2) fin2_zero_ne_one U).eval =
        positiveControlledUnitary (1 : Fin 2)
          ({⟨(0 : Fin 2), fin2_zero_ne_one⟩} : ControlSet (1 : Fin 2)) U ∧
      FusionCircuit.oneQubitCount
        (ControlledCircuit.canonicalSelectedControlledU2FusionCircuit
          (0 : Fin 2) (1 : Fin 2) fin2_zero_ne_one U) = 4 ∧
      FusionCircuit.cnotCount
        (ControlledCircuit.canonicalSelectedControlledU2FusionCircuit
          (0 : Fin 2) (1 : Fin 2) fin2_zero_ne_one U) = 2 ∧
      FusionCircuit.gateCount
        (ControlledCircuit.canonicalSelectedControlledU2FusionCircuit
          (0 : Fin 2) (1 : Fin 2) fin2_zero_ne_one U) = 6 := by
  constructor
  · exact ControlledCircuit.eval_canonicalSelectedControlledU2FusionCircuit
      0 1 fin2_zero_ne_one U
  · simp

/-! ## Relative-phase A input -/

/-- The concrete three-wire relative-A input retains exact semantics and `(4,3,7)`. -/
theorem relativeA_threeWire_profile :
    (ThreeQubit.relativePhaseToffoliAFusionCircuit
        (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)
        fin3_zero_ne_two fin3_one_ne_two).eval =
        ThreeQubit.relativeToffoliUnitary (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)
          fin3_zero_ne_two fin3_one_ne_two ∧
      FusionCircuit.oneQubitCount
        (ThreeQubit.relativePhaseToffoliAFusionCircuit
          (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)
          fin3_zero_ne_two fin3_one_ne_two) = 4 ∧
      FusionCircuit.cnotCount
        (ThreeQubit.relativePhaseToffoliAFusionCircuit
          (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)
          fin3_zero_ne_two fin3_one_ne_two) = 3 ∧
      FusionCircuit.gateCount
        (ThreeQubit.relativePhaseToffoliAFusionCircuit
          (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)
          fin3_zero_ne_two fin3_one_ne_two) = 7 := by
  constructor
  · exact ThreeQubit.eval_relativePhaseToffoliAFusionCircuit
      0 1 2 fin3_zero_ne_two fin3_one_ne_two
  · simp

end Barenco.FusionExamples
