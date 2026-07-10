import Barenco.MultiControl.Corollary74
import Barenco.MultiControl.RelativeHalf

/-!
# Contextual relative-phase version of Corollary 7.4

This module separates the contextual phase argument from the signed ladder
calculation in `RelativeHalf`.  The B implementation keeps the two outer
Toffolis that target the final wire exact and replaces only the repeated
smaller half by the seven-node relative-phase implementation.  The full
four-block chronology is `Arel; Bhybrid; adjoint Arel; Bhybrid`: using the same
all-relative A circuit twice is not correct for the ordered Section 6 phase.

The first section records syntax-derived counts.  Semantic theorems below use
the signed basis actions; no phase-relaxed congruence is used as a substitute
for exact contextual equality.
-/

namespace Barenco.MultiControl

open scoped Matrix

namespace InwardLadderLayout

noncomputable section

/-! ## Hybrid final-target ladder -/

/--
The phase-safe B ladder.  Its chronology is
`exactOuter; relativeSmallerHalf; exactOuter; relativeSmallerHalf`.

Only the two outer occurrences target the ladder's final target.  The repeated
smaller half is a signed involution on wires disjoint from that target.
-/
def hybridInwardLadderCircuit {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) : Circuit n :=
  Circuit.append [layout.outerToffoli]
    (Circuit.append (relativeHalfLadderCircuit b layout.smaller)
      (Circuit.append [layout.outerToffoli]
        (relativeHalfLadderCircuit b layout.smaller)))

/-- One trusted outer node has the expected structural kind. -/
@[simp]
theorem outerToffoli_singleton_toffoliCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    Circuit.kindCount .toffoli [layout.outerToffoli] = 1 := rfl

@[simp]
theorem outerToffoli_singleton_oneQubitCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    Circuit.kindCount .oneQubit [layout.outerToffoli] = 0 := rfl

@[simp]
theorem outerToffoli_singleton_cnotCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    Circuit.kindCount .cnot [layout.outerToffoli] = 0 := rfl

/-- A trusted outer macro contributes one node to the mixed syntax. -/
@[simp]
theorem outerToffoli_singleton_gateCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    Circuit.gateCount [layout.outerToffoli] = 1 := rfl

/-- A seven-node relative base contains no trusted Toffoli macro. -/
@[simp]
theorem relativeBaseCircuit_toffoliCount {n : ℕ}
    (layout : InwardLadderLayout 0 n) :
    Circuit.kindCount .toffoli layout.relativeBaseCircuit = 0 := rfl

/-- A seven-node relative outer circuit contains no trusted Toffoli macro. -/
@[simp]
theorem relativeOuterCircuit_toffoliCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    Circuit.kindCount .toffoli layout.relativeOuterCircuit = 0 := rfl

/-- Expanded relative halves contain no trusted Toffoli macro nodes. -/
@[simp]
theorem relativeHalfLadderCircuit_toffoliCount {b n : ℕ}
    (layout : InwardLadderLayout b n) :
    Circuit.kindCount .toffoli (relativeHalfLadderCircuit b layout) = 0 := by
  revert layout
  induction b with
  | zero =>
      intro layout
      simp [relativeHalfLadderCircuit]
  | succ b ih =>
      intro layout
      simp [relativeHalfLadderCircuit, ih]

/-- A complete all-relative ladder also contains no trusted Toffoli macros. -/
@[simp]
theorem relativeInwardLadderCircuit_toffoliCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    Circuit.kindCount .toffoli (relativeInwardLadderCircuit layout) = 0 := by
  simp [relativeInwardLadderCircuit]

/-- The hybrid syntax contains exactly the two retained exact Toffoli macros. -/
@[simp]
theorem hybridInwardLadderCircuit_toffoliCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    Circuit.kindCount .toffoli (hybridInwardLadderCircuit layout) = 2 := by
  simp [hybridInwardLadderCircuit]

/-- One-qubit primitives contributed by the two relative smaller halves. -/
@[simp]
theorem hybridInwardLadderCircuit_oneQubitCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    Circuit.kindCount .oneQubit (hybridInwardLadderCircuit layout) =
      8 * (2 * b + 1) := by
  simp [hybridInwardLadderCircuit]
  omega

/-- CNOT primitives contributed by the two relative smaller halves. -/
@[simp]
theorem hybridInwardLadderCircuit_cnotCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    Circuit.kindCount .cnot (hybridInwardLadderCircuit layout) =
      6 * (2 * b + 1) := by
  simp [hybridInwardLadderCircuit]
  omega

/-- Total nodes before the two exact Toffolis are expanded. -/
@[simp]
theorem hybridInwardLadderCircuit_gateCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    Circuit.gateCount (hybridInwardLadderCircuit layout) =
      14 * (2 * b + 1) + 2 := by
  simp only [hybridInwardLadderCircuit, Circuit.gateCount_append,
    outerToffoli_singleton_gateCount, relativeHalfLadderCircuit_gateCount]
  omega

/-- The mixed syntax is deliberately unsupported by the one-qubit+CNOT model. -/
@[simp]
theorem hybridInwardLadderCircuit_oneQubitCNOTCost {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    Circuit.cost CostModel.oneQubitCNOT (hybridInwardLadderCircuit layout) = none := by
  simp [hybridInwardLadderCircuit, Circuit.cost_append, Circuit.addCost]

end

end InwardLadderLayout

namespace FourBlockLayout

noncomputable section

/-! ## Correct contextual four-block syntax -/

/-- All-relative implementation of A on the checked Corollary 7.4 layout. -/
def relativeCorollary74AImplementation {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hcapacity : leftTail ≤ rightTail + 2) : Circuit n :=
  InwardLadderLayout.relativeInwardLadderCircuit
    (layout.corollary74ALayout hcapacity)

/-- Hybrid B: exact only at its two final-target outer occurrences. -/
def hybridCorollary74BImplementation {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hcapacity : rightTail ≤ leftTail + 2) : Circuit n :=
  InwardLadderLayout.hybridInwardLadderCircuit
    (layout.corollary74BLayout hcapacity)

/--
Phase-corrected contextual chronology.  The second A occurrence is the circuit
adjoint, not a second forward copy.
-/
def relativeCorollary74Circuit {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2) (hright : rightTail ≤ leftTail + 2) :
    Circuit n :=
  let a := layout.relativeCorollary74AImplementation hleft
  let b := layout.hybridCorollary74BImplementation hright
  Circuit.append a
    (Circuit.append b (Circuit.append (Circuit.adjoint a) b))

@[simp]
theorem relativeCorollary74Circuit_toffoliCount {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2) (hright : rightTail ≤ leftTail + 2) :
    Circuit.kindCount .toffoli (layout.relativeCorollary74Circuit hleft hright) = 4 := by
  simp [relativeCorollary74Circuit, relativeCorollary74AImplementation,
    hybridCorollary74BImplementation]

/--
The number of seven-node relative-Toffoli occurrences, witnessed by their four
one-qubit primitives per occurrence.
-/
@[simp]
theorem relativeCorollary74Circuit_oneQubitCount {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2) (hright : rightTail ≤ leftTail + 2) :
    Circuit.kindCount .oneQubit (layout.relativeCorollary74Circuit hleft hright) =
      4 * (8 * (leftTail + rightTail) + 12) := by
  simp [relativeCorollary74Circuit, relativeCorollary74AImplementation,
    hybridCorollary74BImplementation]
  omega

/-- Three CNOTs occur in every seven-node relative-Toffoli implementation. -/
@[simp]
theorem relativeCorollary74Circuit_cnotCount {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2) (hright : rightTail ≤ leftTail + 2) :
    Circuit.kindCount .cnot (layout.relativeCorollary74Circuit hleft hright) =
      3 * (8 * (leftTail + rightTail) + 12) := by
  simp [relativeCorollary74Circuit, relativeCorollary74AImplementation,
    hybridCorollary74BImplementation]
  omega

/-- Total mixed-syntax nodes: four exact macros plus seven nodes per relative occurrence. -/
@[simp]
theorem relativeCorollary74Circuit_gateCount {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2) (hright : rightTail ≤ leftTail + 2) :
    Circuit.gateCount (layout.relativeCorollary74Circuit hleft hright) =
      7 * (8 * (leftTail + rightTail) + 12) + 4 := by
  simp [relativeCorollary74Circuit, relativeCorollary74AImplementation,
    hybridCorollary74BImplementation]
  omega

@[simp]
theorem relativeCorollary74Circuit_oneQubitCNOTCost {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2) (hright : rightTail ≤ leftTail + 2) :
    Circuit.cost CostModel.oneQubitCNOT
        (layout.relativeCorollary74Circuit hleft hright) = none := by
  simp [relativeCorollary74Circuit, relativeCorollary74AImplementation,
    hybridCorollary74BImplementation, Circuit.cost_append, Circuit.addCost]

end


end FourBlockLayout

end Barenco.MultiControl
