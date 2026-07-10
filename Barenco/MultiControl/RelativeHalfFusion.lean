import Barenco.MultiControl.RelativeHalf
import Barenco.ThreeQubit.RelativePhaseFusion

/-!
# Transparent fusion syntax for relative-phase inward ladders

This leaf reifies every seven-node relative-phase Toffoli occurrence in the
dirty-borrowed half and complete inward ladders.  The recursive list chronology
is definitionally the established construction after trusted lowering, while
every one-qubit payload remains visible to later exact normalization.
-/

namespace Barenco.MultiControl

open Barenco.Optimization
open Barenco.ThreeQubit

noncomputable section

namespace InwardLadderLayout

/-- Transparent relative implementation of the base occurrence. -/
def relativeBaseFusionCircuit {n : ℕ}
    (layout : InwardLadderLayout 0 n) : FusionCircuit n :=
  relativePhaseToffoliAFusionCircuit
    (layout.controlWire 0) (layout.controlWire 1) layout.targetWire
    (layout.controlWire_ne_targetWire 0)
    (layout.controlWire_ne_targetWire 1)

@[simp]
theorem lower_relativeBaseFusionCircuit {n : ℕ}
    (layout : InwardLadderLayout 0 n) :
    layout.relativeBaseFusionCircuit.lower = layout.relativeBaseCircuit := rfl

/-- Transparent relative implementation of one recursive outer occurrence. -/
def relativeOuterFusionCircuit {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) : FusionCircuit n :=
  relativePhaseToffoliAFusionCircuit
    (layout.controlWire (Fin.last (b + 2)))
    (layout.borrowedWire (Fin.last b)) layout.targetWire
    (layout.controlWire_ne_targetWire _)
    (layout.borrowedWire_ne_targetWire _)

@[simp]
theorem lower_relativeOuterFusionCircuit {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    layout.relativeOuterFusionCircuit.lower = layout.relativeOuterCircuit := rfl

/-- Recursive transparent reification of a relative half ladder. -/
def relativeHalfLadderFusionCircuit {n : ℕ} :
    (b : ℕ) → InwardLadderLayout b n → FusionCircuit n
  | 0, layout => layout.relativeBaseFusionCircuit
  | b + 1, layout =>
      FusionCircuit.append layout.relativeOuterFusionCircuit
        (FusionCircuit.append
          (relativeHalfLadderFusionCircuit b layout.smaller)
          layout.relativeOuterFusionCircuit)

@[simp]
theorem lower_relativeHalfLadderFusionCircuit {b n : ℕ}
    (layout : InwardLadderLayout b n) :
    (relativeHalfLadderFusionCircuit b layout).lower =
      relativeHalfLadderCircuit b layout := by
  induction b with
  | zero => rfl
  | succ b ih =>
      simp [relativeHalfLadderFusionCircuit, relativeHalfLadderCircuit, ih]

@[simp]
theorem eval_relativeHalfLadderFusionCircuit {b n : ℕ}
    (layout : InwardLadderLayout b n) :
    (relativeHalfLadderFusionCircuit b layout).eval =
      Circuit.eval (relativeHalfLadderCircuit b layout) := by
  rw [← FusionCircuit.eval_lower,
    lower_relativeHalfLadderFusionCircuit]

/-- Transparent complete all-relative inward ladder. -/
def relativeInwardLadderFusionCircuit {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) : FusionCircuit n :=
  FusionCircuit.append (relativeHalfLadderFusionCircuit (b + 1) layout)
    (relativeHalfLadderFusionCircuit b layout.smaller)

@[simp]
theorem lower_relativeInwardLadderFusionCircuit {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    layout.relativeInwardLadderFusionCircuit.lower =
      relativeInwardLadderCircuit layout := by
  simp [relativeInwardLadderFusionCircuit, relativeInwardLadderCircuit]

@[simp]
theorem eval_relativeInwardLadderFusionCircuit {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    layout.relativeInwardLadderFusionCircuit.eval =
      Circuit.eval (relativeInwardLadderCircuit layout) := by
  rw [← FusionCircuit.eval_lower,
    lower_relativeInwardLadderFusionCircuit]

/-! ## Literal raw resources -/

@[simp]
theorem relativeHalfLadderFusionCircuit_oneQubitCount {b n : ℕ}
    (layout : InwardLadderLayout b n) :
    FusionCircuit.oneQubitCount (relativeHalfLadderFusionCircuit b layout) =
      4 * (2 * b + 1) := by
  rw [← FusionCircuit.oneQubitCount_lower,
    lower_relativeHalfLadderFusionCircuit,
    relativeHalfLadderCircuit_oneQubitCount]

@[simp]
theorem relativeHalfLadderFusionCircuit_cnotCount {b n : ℕ}
    (layout : InwardLadderLayout b n) :
    FusionCircuit.cnotCount (relativeHalfLadderFusionCircuit b layout) =
      3 * (2 * b + 1) := by
  rw [← FusionCircuit.cnotCount_lower,
    lower_relativeHalfLadderFusionCircuit,
    relativeHalfLadderCircuit_cnotCount]

@[simp]
theorem relativeHalfLadderFusionCircuit_gateCount {b n : ℕ}
    (layout : InwardLadderLayout b n) :
    FusionCircuit.gateCount (relativeHalfLadderFusionCircuit b layout) =
      7 * (2 * b + 1) := by
  rw [← FusionCircuit.gateCount_lower,
    lower_relativeHalfLadderFusionCircuit,
    relativeHalfLadderCircuit_gateCount]

@[simp]
theorem relativeInwardLadderFusionCircuit_oneQubitCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    FusionCircuit.oneQubitCount layout.relativeInwardLadderFusionCircuit =
      16 * (b + 1) := by
  rw [← FusionCircuit.oneQubitCount_lower,
    lower_relativeInwardLadderFusionCircuit,
    relativeInwardLadderCircuit_oneQubitCount]

@[simp]
theorem relativeInwardLadderFusionCircuit_cnotCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    FusionCircuit.cnotCount layout.relativeInwardLadderFusionCircuit =
      12 * (b + 1) := by
  rw [← FusionCircuit.cnotCount_lower,
    lower_relativeInwardLadderFusionCircuit,
    relativeInwardLadderCircuit_cnotCount]

@[simp]
theorem relativeInwardLadderFusionCircuit_gateCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    FusionCircuit.gateCount layout.relativeInwardLadderFusionCircuit =
      28 * (b + 1) := by
  rw [← FusionCircuit.gateCount_lower,
    lower_relativeInwardLadderFusionCircuit,
    relativeInwardLadderCircuit_gateCount]

end InwardLadderLayout

end

end Barenco.MultiControl
