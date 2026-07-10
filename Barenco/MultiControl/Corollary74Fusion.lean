import Barenco.MultiControl.RelativeHalfFusion
import Barenco.MultiControl.RelativePhase
import Barenco.ThreeQubit.ExpansionFusion

/-!
# Transparent fusion input for corrected Corollary 7.4

This module replaces the four opaque exact-Toffoli witnesses in the corrected
phase-safe Corollary 7.4 construction by one explicit selected sixteen-node
factor schedule per occurrence.  Every relative occurrence is also reified, so
the complete `A; B; A†; B` chronology is optimizer-visible.

No merger is performed here.  The resulting raw profile agrees with the older
opaque expansion, but literal lowering targets a new transparent `Circuit`
surface because two classically selected whole circuits cannot be expected to be
syntactically equal.  Their exact full-register evaluators do agree.
-/

namespace Barenco.MultiControl

open Barenco.OneQubit
open Barenco.ControlledCircuit
open Barenco.Optimization
open Barenco.ThreeQubit

noncomputable section

namespace InwardLadderLayout

/-- Role-preserving explicit selected exact outer occurrence. -/
def expandedOuterFusionCircuit {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) : FusionCircuit n :=
  selectedDoubleControlledExpansion16FusionCircuit
    (layout.controlWire (Fin.last (b + 2)))
    (layout.borrowedWire (Fin.last b)) layout.targetWire
    (layout.controlWire_ne_borrowedWire _ _)
    (layout.controlWire_ne_targetWire _)
    (layout.borrowedWire_ne_targetWire _) pauliX

/-- Trusted primitive syntax produced by the transparent exact outer builder. -/
def transparentExpandedOuterCircuit {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) : Circuit n :=
  let V := unitarySquareRoot pauliX
  let factors := selectedColumnABCFactors (specialUnitaryPart V)
  doubleControlledExpansion16Circuit
    (layout.controlWire (Fin.last (b + 2)))
    (layout.borrowedWire (Fin.last b)) layout.targetWire
    (layout.controlWire_ne_borrowedWire _ _)
    (layout.controlWire_ne_targetWire _)
    (layout.borrowedWire_ne_targetWire _)
    (determinantPhaseAngle V)
    (specialUnitaryAsUnitary factors.A)
    (specialUnitaryAsUnitary factors.B)
    (specialUnitaryAsUnitary factors.C)

@[simp]
theorem lower_expandedOuterFusionCircuit {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    layout.expandedOuterFusionCircuit.lower =
      layout.transparentExpandedOuterCircuit := by
  simp [expandedOuterFusionCircuit, transparentExpandedOuterCircuit]

@[simp]
theorem eval_expandedOuterFusionCircuit {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    layout.expandedOuterFusionCircuit.eval = layout.outerToffoli.denotation := by
  rw [expandedOuterFusionCircuit,
    eval_selectedDoubleControlledExpansion16FusionCircuit]
  rw [outerToffoli, Primitive.toffoli_denotation, twoControlSet]

@[simp]
theorem expandedOuterFusionCircuit_oneQubitCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    FusionCircuit.oneQubitCount layout.expandedOuterFusionCircuit = 8 := by
  simp [expandedOuterFusionCircuit]

@[simp]
theorem expandedOuterFusionCircuit_cnotCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    FusionCircuit.cnotCount layout.expandedOuterFusionCircuit = 8 := by
  simp [expandedOuterFusionCircuit]

@[simp]
theorem expandedOuterFusionCircuit_gateCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    FusionCircuit.gateCount layout.expandedOuterFusionCircuit = 16 := by
  simp [expandedOuterFusionCircuit]

/-! ## Transparent raw hybrid B -/

/-- Exact outer, relative smaller half, exact outer, relative smaller half. -/
def expandedHybridInwardLadderFusionCircuit {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) : FusionCircuit n :=
  FusionCircuit.append layout.expandedOuterFusionCircuit
    (FusionCircuit.append
      (relativeHalfLadderFusionCircuit b layout.smaller)
      (FusionCircuit.append layout.expandedOuterFusionCircuit
        (relativeHalfLadderFusionCircuit b layout.smaller)))

/-- Trusted `Circuit` surface for the complete transparent hybrid syntax. -/
def transparentExpandedHybridInwardLadderCircuit {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) : Circuit n :=
  Circuit.append layout.transparentExpandedOuterCircuit
    (Circuit.append (relativeHalfLadderCircuit b layout.smaller)
      (Circuit.append layout.transparentExpandedOuterCircuit
        (relativeHalfLadderCircuit b layout.smaller)))

@[simp]
theorem lower_expandedHybridInwardLadderFusionCircuit {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    layout.expandedHybridInwardLadderFusionCircuit.lower =
      layout.transparentExpandedHybridInwardLadderCircuit := by
  simp [expandedHybridInwardLadderFusionCircuit,
    transparentExpandedHybridInwardLadderCircuit]

@[simp]
theorem eval_expandedHybridInwardLadderFusionCircuit {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    layout.expandedHybridInwardLadderFusionCircuit.eval =
      Circuit.eval (hybridInwardLadderCircuit layout) := by
  simp [expandedHybridInwardLadderFusionCircuit, hybridInwardLadderCircuit,
    FusionCircuit.eval_append, Circuit.eval_append,
    eval_expandedOuterFusionCircuit]

@[simp]
theorem expandedHybridInwardLadderFusionCircuit_oneQubitCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    FusionCircuit.oneQubitCount
        layout.expandedHybridInwardLadderFusionCircuit =
      8 * (2 * b + 1) + 16 := by
  simp [expandedHybridInwardLadderFusionCircuit]
  omega

@[simp]
theorem expandedHybridInwardLadderFusionCircuit_cnotCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    FusionCircuit.cnotCount layout.expandedHybridInwardLadderFusionCircuit =
      6 * (2 * b + 1) + 16 := by
  simp [expandedHybridInwardLadderFusionCircuit]
  omega

@[simp]
theorem expandedHybridInwardLadderFusionCircuit_gateCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    FusionCircuit.gateCount layout.expandedHybridInwardLadderFusionCircuit =
      14 * (2 * b + 1) + 32 := by
  simp [expandedHybridInwardLadderFusionCircuit]
  omega

end InwardLadderLayout

namespace FourBlockLayout

/-! ## Complete transparent corrected chronology -/

/-- Transparent all-relative implementation of A. -/
def relativeCorollary74AFusionCircuit {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hcapacity : leftTail ≤ rightTail + 2) : FusionCircuit n :=
  InwardLadderLayout.relativeInwardLadderFusionCircuit
    (layout.corollary74ALayout hcapacity)

@[simp]
theorem lower_relativeCorollary74AFusionCircuit
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hcapacity : leftTail ≤ rightTail + 2) :
    (layout.relativeCorollary74AFusionCircuit hcapacity).lower =
      layout.relativeCorollary74AImplementation hcapacity := by
  simp [relativeCorollary74AFusionCircuit,
    relativeCorollary74AImplementation]

@[simp]
theorem eval_relativeCorollary74AFusionCircuit
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hcapacity : leftTail ≤ rightTail + 2) :
    (layout.relativeCorollary74AFusionCircuit hcapacity).eval =
      Circuit.eval (layout.relativeCorollary74AImplementation hcapacity) := by
  rw [← FusionCircuit.eval_lower,
    lower_relativeCorollary74AFusionCircuit]

/-- Transparent phase-safe hybrid implementation of B. -/
def expandedHybridCorollary74BFusionCircuit {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hcapacity : rightTail ≤ leftTail + 2) : FusionCircuit n :=
  InwardLadderLayout.expandedHybridInwardLadderFusionCircuit
    (layout.corollary74BLayout hcapacity)

@[simp]
theorem eval_expandedHybridCorollary74BFusionCircuit
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hcapacity : rightTail ≤ leftTail + 2) :
    (layout.expandedHybridCorollary74BFusionCircuit hcapacity).eval =
      Circuit.eval (layout.hybridCorollary74BImplementation hcapacity) := by
  simp [expandedHybridCorollary74BFusionCircuit,
    hybridCorollary74BImplementation]

/-- Complete corrected `A; B; A†; B` chronology in visible syntax. -/
def expandedRelativeCorollary74FusionCircuit {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2) : FusionCircuit n :=
  let a := layout.relativeCorollary74AFusionCircuit hleft
  let b := layout.expandedHybridCorollary74BFusionCircuit hright
  FusionCircuit.append a
    (FusionCircuit.append b (FusionCircuit.append a.adjoint b))

/-- Trusted lowered syntax for the complete transparent chronology. -/
def transparentExpandedRelativeCorollary74Circuit
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2) : Circuit n :=
  let a := layout.relativeCorollary74AImplementation hleft
  let b :=
    InwardLadderLayout.transparentExpandedHybridInwardLadderCircuit
      (layout.corollary74BLayout hright)
  Circuit.append a
    (Circuit.append b (Circuit.append (Circuit.adjoint a) b))

@[simp]
theorem lower_expandedRelativeCorollary74FusionCircuit
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2) :
    (layout.expandedRelativeCorollary74FusionCircuit hleft hright).lower =
      layout.transparentExpandedRelativeCorollary74Circuit hleft hright := by
  simp [expandedRelativeCorollary74FusionCircuit,
    transparentExpandedRelativeCorollary74Circuit,
    expandedHybridCorollary74BFusionCircuit]

@[simp]
theorem eval_expandedRelativeCorollary74FusionCircuit_eq_relative
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2) :
    (layout.expandedRelativeCorollary74FusionCircuit hleft hright).eval =
      Circuit.eval (layout.relativeCorollary74Circuit hleft hright) := by
  simp [expandedRelativeCorollary74FusionCircuit,
    relativeCorollary74Circuit, FusionCircuit.eval_append,
    Circuit.eval_append]

@[simp]
theorem eval_expandedRelativeCorollary74FusionCircuit
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2)
    (htargetFree : leftTail ≤ rightTail + 1) :
    (layout.expandedRelativeCorollary74FusionCircuit hleft hright).eval =
      positiveControlledUnitary layout.targetWire layout.dataLayout.controlSet
        pauliX := by
  rw [eval_expandedRelativeCorollary74FusionCircuit_eq_relative]
  exact eval_relativeCorollary74Circuit layout hleft hright htargetFree

/-! ## Raw literal resources -/

@[simp]
theorem expandedRelativeCorollary74FusionCircuit_oneQubitCount
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2) :
    FusionCircuit.oneQubitCount
        (layout.expandedRelativeCorollary74FusionCircuit hleft hright) =
      4 * (8 * (leftTail + rightTail) + 12) + 32 := by
  let a := layout.relativeCorollary74AFusionCircuit hleft
  let b := layout.expandedHybridCorollary74BFusionCircuit hright
  change FusionCircuit.oneQubitCount
      (FusionCircuit.append a
        (FusionCircuit.append b (FusionCircuit.append a.adjoint b))) = _
  rw [FusionCircuit.oneQubitCount_append,
    FusionCircuit.oneQubitCount_append,
    FusionCircuit.oneQubitCount_append]
  rw [show FusionCircuit.oneQubitCount a.adjoint =
      FusionCircuit.oneQubitCount a by
    exact FusionCircuit.kindCount_adjoint .oneQubit a]
  simp [a, b, relativeCorollary74AFusionCircuit,
    expandedHybridCorollary74BFusionCircuit]
  omega

@[simp]
theorem expandedRelativeCorollary74FusionCircuit_cnotCount
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2) :
    FusionCircuit.cnotCount
        (layout.expandedRelativeCorollary74FusionCircuit hleft hright) =
      3 * (8 * (leftTail + rightTail) + 12) + 32 := by
  let a := layout.relativeCorollary74AFusionCircuit hleft
  let b := layout.expandedHybridCorollary74BFusionCircuit hright
  change FusionCircuit.cnotCount
      (FusionCircuit.append a
        (FusionCircuit.append b (FusionCircuit.append a.adjoint b))) = _
  rw [FusionCircuit.cnotCount_append, FusionCircuit.cnotCount_append,
    FusionCircuit.cnotCount_append]
  rw [show FusionCircuit.cnotCount a.adjoint = FusionCircuit.cnotCount a by
    exact FusionCircuit.kindCount_adjoint .cnot a]
  simp [a, b, relativeCorollary74AFusionCircuit,
    expandedHybridCorollary74BFusionCircuit]
  omega

@[simp]
theorem expandedRelativeCorollary74FusionCircuit_gateCount
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2) :
    FusionCircuit.gateCount
        (layout.expandedRelativeCorollary74FusionCircuit hleft hright) =
      7 * (8 * (leftTail + rightTail) + 12) + 64 := by
  let a := layout.relativeCorollary74AFusionCircuit hleft
  let b := layout.expandedHybridCorollary74BFusionCircuit hright
  change FusionCircuit.gateCount
      (FusionCircuit.append a
        (FusionCircuit.append b (FusionCircuit.append a.adjoint b))) = _
  rw [FusionCircuit.gateCount_append, FusionCircuit.gateCount_append,
    FusionCircuit.gateCount_append, FusionCircuit.gateCount_adjoint]
  simp [a, b, relativeCorollary74AFusionCircuit,
    expandedHybridCorollary74BFusionCircuit]
  omega

/-- Balanced transparent raw input for the executable merger stage. -/
def balancedExpandedRelativeCorollary74FusionCircuit (sourceWidth : ℕ)
    (hwidth : 7 ≤ sourceWidth) : FusionCircuit sourceWidth :=
  (balancedLayout sourceWidth hwidth).expandedRelativeCorollary74FusionCircuit
    (balancedLeftCapacity hwidth) (balancedRightCapacity hwidth)

@[simp]
theorem eval_balancedExpandedRelativeCorollary74FusionCircuit
    (sourceWidth : ℕ) (hwidth : 7 ≤ sourceWidth) :
    (balancedExpandedRelativeCorollary74FusionCircuit sourceWidth hwidth).eval =
      positiveControlledUnitary
        (balancedLayout sourceWidth hwidth).targetWire
        (balancedLayout sourceWidth hwidth).dataLayout.controlSet pauliX := by
  apply eval_expandedRelativeCorollary74FusionCircuit
  exact balancedLeftTail_le_right_add_one hwidth

@[simp]
theorem balancedExpandedRelativeCorollary74FusionCircuit_oneQubitCount
    (sourceWidth : ℕ) (hwidth : 7 ≤ sourceWidth) :
    FusionCircuit.oneQubitCount
        (balancedExpandedRelativeCorollary74FusionCircuit sourceWidth hwidth) =
      32 * sourceWidth - 144 := by
  rw [balancedExpandedRelativeCorollary74FusionCircuit,
    expandedRelativeCorollary74FusionCircuit_oneQubitCount]
  have hsum := balancedTails_add_seven hwidth
  omega

@[simp]
theorem balancedExpandedRelativeCorollary74FusionCircuit_cnotCount
    (sourceWidth : ℕ) (hwidth : 7 ≤ sourceWidth) :
    FusionCircuit.cnotCount
        (balancedExpandedRelativeCorollary74FusionCircuit sourceWidth hwidth) =
      24 * sourceWidth - 100 := by
  rw [balancedExpandedRelativeCorollary74FusionCircuit,
    expandedRelativeCorollary74FusionCircuit_cnotCount]
  have hsum := balancedTails_add_seven hwidth
  omega

@[simp]
theorem balancedExpandedRelativeCorollary74FusionCircuit_gateCount
    (sourceWidth : ℕ) (hwidth : 7 ≤ sourceWidth) :
    FusionCircuit.gateCount
        (balancedExpandedRelativeCorollary74FusionCircuit sourceWidth hwidth) =
      56 * sourceWidth - 244 := by
  rw [balancedExpandedRelativeCorollary74FusionCircuit,
    expandedRelativeCorollary74FusionCircuit_gateCount]
  have hsum := balancedTails_add_seven hwidth
  omega

end FourBlockLayout

end

end Barenco.MultiControl
