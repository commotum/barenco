import Barenco.MultiControl.RelativePhase
import Barenco.ThreeQubit.Expansion

/-!
# Literal primitive expansion of corrected Corollary 7.4

This module replaces the four exact Toffoli macros left by
`RelativePhase` with four literal copies of a selected sixteen-node witness from
Corollary 6.2.  It deliberately performs no cross-boundary cancellation or
gate merging.  Consequently the balanced construction has the directly
checkable raw cost `56 * n - 244`, not the paper's separately claimed optimized
constant.

The selected witnesses are noncomputable only because Section 5 supplies their
one-qubit factors existentially.  Every exported semantic and resource theorem
is recovered from the witness specification.
-/

namespace Barenco.MultiControl

open Barenco.OneQubit
open Barenco.ThreeQubit

noncomputable section

/-! ## A selected sixteen-node exact Toffoli expansion -/

/--
The complete specification used to select one sixteen-node expansion of an
exact Toffoli on three named wires.
-/
def ExactToffoliExpansionSpec {n : ℕ}
    (first second target : Fin n)
    (_hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target) (circuit : Circuit n) : Prop :=
  Circuit.eval circuit =
      positiveControlledUnitary target
        (twoControlSet first second target hfirstTarget hsecondTarget) pauliX ∧
    Circuit.gateCount circuit = 16 ∧
    Circuit.kindCount .oneQubit circuit = 8 ∧
    Circuit.kindCount .cnot circuit = 8 ∧
    Circuit.cost CostModel.oneQubitCNOT circuit = some 16

/--
One fixed sixteen-node primitive circuit implementing the specified Toffoli.
The mathematical result is independent of which Section 5 factorization
classical choice selects.
-/
def exactToffoliExpansionCircuit {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target) : Circuit n :=
  Classical.choose
    (doubleControlledUnitary_has_sixteenPrimitiveCircuit first second target
      hfirstSecond hfirstTarget hsecondTarget pauliX)

/-- The selected circuit satisfies its full semantic and resource contract. -/
theorem exactToffoliExpansionCircuit_spec {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target) :
    ExactToffoliExpansionSpec first second target hfirstSecond hfirstTarget
      hsecondTarget
      (exactToffoliExpansionCircuit first second target hfirstSecond
        hfirstTarget hsecondTarget) := by
  simpa only [ExactToffoliExpansionSpec, exactToffoliExpansionCircuit] using
    (Classical.choose_spec
      (doubleControlledUnitary_has_sixteenPrimitiveCircuit first second target
        hfirstSecond hfirstTarget hsecondTarget pauliX))

@[simp]
theorem eval_exactToffoliExpansionCircuit {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target) :
    Circuit.eval
        (exactToffoliExpansionCircuit first second target hfirstSecond
          hfirstTarget hsecondTarget) =
      positiveControlledUnitary target
        (twoControlSet first second target hfirstTarget hsecondTarget) pauliX :=
  (exactToffoliExpansionCircuit_spec first second target hfirstSecond
    hfirstTarget hsecondTarget).1

@[simp]
theorem exactToffoliExpansionCircuit_gateCount {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target) :
    Circuit.gateCount
        (exactToffoliExpansionCircuit first second target hfirstSecond
          hfirstTarget hsecondTarget) = 16 :=
  (exactToffoliExpansionCircuit_spec first second target hfirstSecond
    hfirstTarget hsecondTarget).2.1

@[simp]
theorem exactToffoliExpansionCircuit_oneQubitCount {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target) :
    Circuit.kindCount .oneQubit
        (exactToffoliExpansionCircuit first second target hfirstSecond
          hfirstTarget hsecondTarget) = 8 :=
  (exactToffoliExpansionCircuit_spec first second target hfirstSecond
    hfirstTarget hsecondTarget).2.2.1

@[simp]
theorem exactToffoliExpansionCircuit_cnotCount {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target) :
    Circuit.kindCount .cnot
        (exactToffoliExpansionCircuit first second target hfirstSecond
          hfirstTarget hsecondTarget) = 8 :=
  (exactToffoliExpansionCircuit_spec first second target hfirstSecond
    hfirstTarget hsecondTarget).2.2.2.1

@[simp]
theorem exactToffoliExpansionCircuit_oneQubitCNOTCost {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target) :
    Circuit.cost CostModel.oneQubitCNOT
        (exactToffoliExpansionCircuit first second target hfirstSecond
          hfirstTarget hsecondTarget) = some 16 :=
  (exactToffoliExpansionCircuit_spec first second target hfirstSecond
    hfirstTarget hsecondTarget).2.2.2.2

namespace InwardLadderLayout

/-! ## Expanding an outer Toffoli in its ambient layout -/

/-- The selected sixteen-node implementation of a ladder's outer Toffoli. -/
def expandedOuterCircuit {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) : Circuit n :=
  exactToffoliExpansionCircuit
    (layout.controlWire (Fin.last (b + 2)))
    (layout.borrowedWire (Fin.last b)) layout.targetWire
    (layout.controlWire_ne_borrowedWire _ _)
    (layout.controlWire_ne_targetWire _)
    (layout.borrowedWire_ne_targetWire _)

/-- Expansion preserves the full-register evaluator of the trusted outer node. -/
@[simp]
theorem eval_expandedOuterCircuit {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    Circuit.eval layout.expandedOuterCircuit = layout.outerToffoli.denotation := by
  rw [expandedOuterCircuit, eval_exactToffoliExpansionCircuit,
    outerToffoli, Primitive.toffoli_denotation, twoControlSet]

@[simp]
theorem expandedOuterCircuit_gateCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    Circuit.gateCount layout.expandedOuterCircuit = 16 := by
  simp [expandedOuterCircuit]

@[simp]
theorem expandedOuterCircuit_oneQubitCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    Circuit.kindCount .oneQubit layout.expandedOuterCircuit = 8 := by
  simp [expandedOuterCircuit]

@[simp]
theorem expandedOuterCircuit_cnotCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    Circuit.kindCount .cnot layout.expandedOuterCircuit = 8 := by
  simp [expandedOuterCircuit]

@[simp]
theorem expandedOuterCircuit_oneQubitCNOTCost {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    Circuit.cost CostModel.oneQubitCNOT layout.expandedOuterCircuit = some 16 := by
  simp [expandedOuterCircuit]

/-! ## Fully primitive hybrid B ladder -/

/-- Replace both exact outer macros of the hybrid B ladder by selected witnesses. -/
def expandedHybridInwardLadderCircuit {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) : Circuit n :=
  Circuit.append layout.expandedOuterCircuit
    (Circuit.append (relativeHalfLadderCircuit b layout.smaller)
      (Circuit.append layout.expandedOuterCircuit
        (relativeHalfLadderCircuit b layout.smaller)))

/-- Literal expansion does not alter the hybrid ladder's ambient evaluator. -/
@[simp]
theorem eval_expandedHybridInwardLadderCircuit {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    Circuit.eval (expandedHybridInwardLadderCircuit layout) =
      Circuit.eval (hybridInwardLadderCircuit layout) := by
  simp [expandedHybridInwardLadderCircuit, hybridInwardLadderCircuit,
    Circuit.eval_append]

@[simp]
theorem expandedHybridInwardLadderCircuit_oneQubitCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    Circuit.kindCount .oneQubit (expandedHybridInwardLadderCircuit layout) =
      8 * (2 * b + 1) + 16 := by
  simp [expandedHybridInwardLadderCircuit]
  omega

@[simp]
theorem expandedHybridInwardLadderCircuit_cnotCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    Circuit.kindCount .cnot (expandedHybridInwardLadderCircuit layout) =
      6 * (2 * b + 1) + 16 := by
  simp [expandedHybridInwardLadderCircuit]
  omega

@[simp]
theorem expandedHybridInwardLadderCircuit_gateCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    Circuit.gateCount (expandedHybridInwardLadderCircuit layout) =
      14 * (2 * b + 1) + 32 := by
  simp [expandedHybridInwardLadderCircuit]
  omega

@[simp]
theorem expandedHybridInwardLadderCircuit_oneQubitCNOTCost {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    Circuit.cost CostModel.oneQubitCNOT
        (expandedHybridInwardLadderCircuit layout) =
      some (14 * (2 * b + 1) + 32) := by
  simp [expandedHybridInwardLadderCircuit, Circuit.cost_append,
    Circuit.addCost]
  omega

end InwardLadderLayout

namespace FourBlockLayout

/-! ## Fully primitive contextual construction -/

/-- The fully expanded version of the phase-safe hybrid B implementation. -/
def expandedHybridCorollary74BImplementation {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hcapacity : rightTail ≤ leftTail + 2) : Circuit n :=
  InwardLadderLayout.expandedHybridInwardLadderCircuit
    (layout.corollary74BLayout hcapacity)

/-- Expanding B preserves its full-register evaluator. -/
@[simp]
theorem eval_expandedHybridCorollary74BImplementation
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hcapacity : rightTail ≤ leftTail + 2) :
    Circuit.eval (layout.expandedHybridCorollary74BImplementation hcapacity) =
      Circuit.eval (layout.hybridCorollary74BImplementation hcapacity) := by
  simp [expandedHybridCorollary74BImplementation,
    hybridCorollary74BImplementation]

/--
Literal primitive expansion of the corrected contextual chronology
`Arel; Bexpanded; adjoint Arel; Bexpanded`.
-/
def expandedRelativeCorollary74Circuit {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2) (hright : rightTail ≤ leftTail + 2) :
    Circuit n :=
  let a := layout.relativeCorollary74AImplementation hleft
  let b := layout.expandedHybridCorollary74BImplementation hright
  Circuit.append a
    (Circuit.append b (Circuit.append (Circuit.adjoint a) b))

/-- Literal primitive expansion preserves the corrected contextual evaluator. -/
@[simp]
theorem eval_expandedRelativeCorollary74Circuit_eq_relative
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2) (hright : rightTail ≤ leftTail + 2) :
    Circuit.eval (layout.expandedRelativeCorollary74Circuit hleft hright) =
      Circuit.eval (layout.relativeCorollary74Circuit hleft hright) := by
  simp [expandedRelativeCorollary74Circuit, relativeCorollary74Circuit,
    Circuit.eval_append]

/-- Exact semantics on every ambient register satisfying the target-free A bound. -/
@[simp]
theorem eval_expandedRelativeCorollary74Circuit
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2) (hright : rightTail ≤ leftTail + 2)
    (htargetFree : leftTail ≤ rightTail + 1) :
    Circuit.eval (layout.expandedRelativeCorollary74Circuit hleft hright) =
      positiveControlledUnitary layout.targetWire layout.dataLayout.controlSet
        pauliX := by
  rw [eval_expandedRelativeCorollary74Circuit_eq_relative]
  exact eval_relativeCorollary74Circuit layout hleft hright htargetFree

@[simp]
theorem expandedRelativeCorollary74Circuit_oneQubitCount
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2) (hright : rightTail ≤ leftTail + 2) :
    Circuit.kindCount .oneQubit
        (layout.expandedRelativeCorollary74Circuit hleft hright) =
      4 * (8 * (leftTail + rightTail) + 12) + 32 := by
  simp [expandedRelativeCorollary74Circuit,
    expandedHybridCorollary74BImplementation,
    relativeCorollary74AImplementation]
  omega

@[simp]
theorem expandedRelativeCorollary74Circuit_cnotCount
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2) (hright : rightTail ≤ leftTail + 2) :
    Circuit.kindCount .cnot
        (layout.expandedRelativeCorollary74Circuit hleft hright) =
      3 * (8 * (leftTail + rightTail) + 12) + 32 := by
  simp [expandedRelativeCorollary74Circuit,
    expandedHybridCorollary74BImplementation,
    relativeCorollary74AImplementation]
  omega

@[simp]
theorem expandedRelativeCorollary74Circuit_gateCount
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2) (hright : rightTail ≤ leftTail + 2) :
    Circuit.gateCount
        (layout.expandedRelativeCorollary74Circuit hleft hright) =
      7 * (8 * (leftTail + rightTail) + 12) + 64 := by
  simp [expandedRelativeCorollary74Circuit,
    expandedHybridCorollary74BImplementation,
    relativeCorollary74AImplementation]
  omega

@[simp]
theorem expandedRelativeCorollary74Circuit_oneQubitCNOTCost
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2) (hright : rightTail ≤ leftTail + 2) :
    Circuit.cost CostModel.oneQubitCNOT
        (layout.expandedRelativeCorollary74Circuit hleft hright) =
      some (7 * (8 * (leftTail + rightTail) + 12) + 64) := by
  simp [expandedRelativeCorollary74Circuit,
    expandedHybridCorollary74BImplementation,
    relativeCorollary74AImplementation, Circuit.cost_append, Circuit.addCost]
  omega

/-! ## Balanced source-width wrapper and raw resource formula -/

/-- Fully primitive corrected Corollary 7.4 circuit on exactly `sourceWidth` wires. -/
def balancedExpandedRelativeCorollary74Circuit (sourceWidth : ℕ)
    (hwidth : 7 ≤ sourceWidth) : Circuit sourceWidth :=
  (balancedLayout sourceWidth hwidth).expandedRelativeCorollary74Circuit
    (balancedLeftCapacity hwidth) (balancedRightCapacity hwidth)

/-- Exact multi-controlled-X semantics of the fully expanded balanced circuit. -/
@[simp]
theorem eval_balancedExpandedRelativeCorollary74Circuit (sourceWidth : ℕ)
    (hwidth : 7 ≤ sourceWidth) :
    Circuit.eval (balancedExpandedRelativeCorollary74Circuit sourceWidth hwidth) =
      positiveControlledUnitary
        (balancedLayout sourceWidth hwidth).targetWire
        (balancedLayout sourceWidth hwidth).dataLayout.controlSet pauliX := by
  apply eval_expandedRelativeCorollary74Circuit
  exact balancedLeftTail_le_right_add_one hwidth

/-- Raw one-qubit count: relative occurrences plus four eight-node contributions. -/
@[simp]
theorem balancedExpandedRelativeCorollary74Circuit_oneQubitCount
    (sourceWidth : ℕ) (hwidth : 7 ≤ sourceWidth) :
    Circuit.kindCount .oneQubit
        (balancedExpandedRelativeCorollary74Circuit sourceWidth hwidth) =
      32 * sourceWidth - 144 := by
  rw [balancedExpandedRelativeCorollary74Circuit,
    expandedRelativeCorollary74Circuit_oneQubitCount]
  have hsum := balancedTails_add_seven hwidth
  omega

/-- Raw CNOT count: relative occurrences plus four eight-node contributions. -/
@[simp]
theorem balancedExpandedRelativeCorollary74Circuit_cnotCount
    (sourceWidth : ℕ) (hwidth : 7 ≤ sourceWidth) :
    Circuit.kindCount .cnot
        (balancedExpandedRelativeCorollary74Circuit sourceWidth hwidth) =
      24 * sourceWidth - 100 := by
  rw [balancedExpandedRelativeCorollary74Circuit,
    expandedRelativeCorollary74Circuit_cnotCount]
  have hsum := balancedTails_add_seven hwidth
  omega

/-- Literal unmerged primitive count, with no appeal to the paper's optimization. -/
@[simp]
theorem balancedExpandedRelativeCorollary74Circuit_gateCount
    (sourceWidth : ℕ) (hwidth : 7 ≤ sourceWidth) :
    Circuit.gateCount
        (balancedExpandedRelativeCorollary74Circuit sourceWidth hwidth) =
      56 * sourceWidth - 244 := by
  rw [balancedExpandedRelativeCorollary74Circuit,
    expandedRelativeCorollary74Circuit_gateCount]
  have hsum := balancedTails_add_seven hwidth
  omega

/-- The literal expansion is accepted by the one-qubit+CNOT cost model. -/
@[simp]
theorem balancedExpandedRelativeCorollary74Circuit_oneQubitCNOTCost
    (sourceWidth : ℕ) (hwidth : 7 ≤ sourceWidth) :
    Circuit.cost CostModel.oneQubitCNOT
        (balancedExpandedRelativeCorollary74Circuit sourceWidth hwidth) =
      some (56 * sourceWidth - 244) := by
  rw [balancedExpandedRelativeCorollary74Circuit,
    expandedRelativeCorollary74Circuit_oneQubitCNOTCost]
  have hsum := balancedTails_add_seven hwidth
  exact congrArg some (by omega)

/-- Width-seven sanity check for the complete literal expansion. -/
theorem balancedExpandedRelativeCorollary74Circuit_seven_resources :
    Circuit.kindCount .oneQubit
        (balancedExpandedRelativeCorollary74Circuit 7 (by omega)) = 80 ∧
      Circuit.kindCount .cnot
        (balancedExpandedRelativeCorollary74Circuit 7 (by omega)) = 68 ∧
      Circuit.gateCount
        (balancedExpandedRelativeCorollary74Circuit 7 (by omega)) = 148 ∧
      Circuit.cost CostModel.oneQubitCNOT
        (balancedExpandedRelativeCorollary74Circuit 7 (by omega)) = some 148 := by
  norm_num

end FourBlockLayout

end

end Barenco.MultiControl
