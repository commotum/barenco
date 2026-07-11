import Barenco.MultiControl.Corollary74Mergers

/-!
# Complete exact mergers for corrected Corollary 7.4

This leaf exposes the recursive normal forms needed at the three remaining
four-block boundaries. Two relative-inverse/phase pairs are fused by the real
target-directed symbolic normalizer. One exact A-inverse/A pair is deleted
across a circuit proved structurally disjoint from the final target.

Every bridge is exact on the complete ambient register. The construction emits
literal one-qubit/CNOT syntax and makes no optimality or completeness claim.
-/


namespace Barenco.MultiControl

open Barenco.OneQubit
open Barenco.ControlledCircuit
open Barenco.Optimization
open Barenco.ThreeQubit

noncomputable section

private theorem corollary74MergerEraseAppend
    (valuation : Corollary74FactorAtom → QubitUnitary)
    (first second : SymbolicCircuit Corollary74FactorAtom n) :
    SymbolicCircuit.erase valuation (first ++ second) =
      FusionCircuit.append (SymbolicCircuit.erase valuation first)
        (SymbolicCircuit.erase valuation second) := by
  simp [SymbolicCircuit.erase, FusionCircuit.append]

namespace InwardLadderLayout

def corollary74MergerExactForwardPrefixAfterPhase {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target) :
    SymbolicCircuit Corollary74FactorAtom n :=
  (exactToffoliForwardPrefixSymbolicCircuit first second target
    hfirstSecond hfirstTarget hsecondTarget).tail

@[simp]
theorem corollary74MergerExactForwardPrefix_eq_phase_after {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target) :
    exactToffoliForwardPrefixSymbolicCircuit first second target
        hfirstSecond hfirstTarget hsecondTarget =
      SymbolicPrimitive.atom second .phase ::
        corollary74MergerExactForwardPrefixAfterPhase first second target
          hfirstSecond hfirstTarget hsecondTarget := by
  rfl

@[simp]
theorem corollary74MergerExactForwardPrefixAfterPhase_oneQubitCount {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target) :
    SymbolicCircuit.oneQubitCount
        (corollary74MergerExactForwardPrefixAfterPhase first second target
          hfirstSecond hfirstTarget hsecondTarget) = 6 := by
  rfl

@[simp]
theorem corollary74MergerExactForwardPrefixAfterPhase_cnotCount {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target) :
    SymbolicCircuit.cnotCount
        (corollary74MergerExactForwardPrefixAfterPhase first second target
          hfirstSecond hfirstTarget hsecondTarget) = 8 := by
  rfl

def corollary74MergerExactForwardPrefixAfterPhaseA {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target) :
    SymbolicCircuit Corollary74FactorAtom n :=
  (corollary74MergerExactForwardPrefixAfterPhase first second target
    hfirstSecond hfirstTarget hsecondTarget).tail

@[simp]
theorem corollary74MergerExactForwardPrefixAfterPhase_eq_A_after {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target) :
    corollary74MergerExactForwardPrefixAfterPhase first second target
        hfirstSecond hfirstTarget hsecondTarget =
      SymbolicPrimitive.atom target .A ::
        corollary74MergerExactForwardPrefixAfterPhaseA first second target
          hfirstSecond hfirstTarget hsecondTarget := by
  rfl

@[simp]
theorem corollary74MergerExactForwardPrefixAfterPhaseA_oneQubitCount {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target) :
    SymbolicCircuit.oneQubitCount
        (corollary74MergerExactForwardPrefixAfterPhaseA first second target
          hfirstSecond hfirstTarget hsecondTarget) = 5 := by
  rfl

@[simp]
theorem corollary74MergerExactForwardPrefixAfterPhaseA_cnotCount {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target) :
    SymbolicCircuit.cnotCount
        (corollary74MergerExactForwardPrefixAfterPhaseA first second target
          hfirstSecond hfirstTarget hsecondTarget) = 8 := by
  rfl

def corollary74MergerExactAdjointMiddleBeforeAInverse {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target) :
    SymbolicCircuit Corollary74FactorAtom n :=
  (exactToffoliAdjointMiddleSymbolicCircuit first second target
    hfirstSecond hfirstTarget hsecondTarget).take 13

@[simp]
theorem corollary74MergerExactAdjointMiddle_eq_before_AInverse {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target) :
    exactToffoliAdjointMiddleSymbolicCircuit first second target
        hfirstSecond hfirstTarget hsecondTarget =
      corollary74MergerExactAdjointMiddleBeforeAInverse first second target
          hfirstSecond hfirstTarget hsecondTarget ++
        [SymbolicPrimitive.inverseAtom target .A] := by
  rfl

@[simp]
theorem corollary74MergerExactAdjointMiddleBeforeAInverse_oneQubitCount {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target) :
    SymbolicCircuit.oneQubitCount
        (corollary74MergerExactAdjointMiddleBeforeAInverse first second target
          hfirstSecond hfirstTarget hsecondTarget) = 5 := by
  rfl

@[simp]
theorem corollary74MergerExactAdjointMiddleBeforeAInverse_cnotCount {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target) :
    SymbolicCircuit.cnotCount
        (corollary74MergerExactAdjointMiddleBeforeAInverse first second target
          hfirstSecond hfirstTarget hsecondTarget) = 8 := by
  rfl

/-- Prefix of a selective half normal form before its final relative inverse. -/
def corollary74MergerRelativeHalfInitial {n : ℕ} :
    (b : ℕ) → InwardLadderLayout b n →
      SymbolicCircuit Corollary74FactorAtom n
  | 0, layout =>
      [relativeToffoliStartSymbolic layout.targetWire] ++
        layout.relativeBaseCoreSymbolicCircuit
  | b + 1, layout =>
      layout.relativeOuterPrefixSymbolicCircuit ++
        selectiveRelativeHalfNormalForm b layout.smaller ++
          relativeToffoliCoreSymbolicCircuit
            (layout.controlWire (Fin.last (b + 2)))
            (layout.borrowedWire (Fin.last b)) layout.targetWire
            (layout.controlWire_ne_targetWire _)
            (layout.borrowedWire_ne_targetWire _)

@[simp]
theorem corollary74MergerRelativeHalfNormalForm_eq_initial_end {b n : ℕ}
    (layout : InwardLadderLayout b n) :
    selectiveRelativeHalfNormalForm b layout =
      corollary74MergerRelativeHalfInitial b layout ++
        [relativeToffoliEndSymbolic layout.targetWire] := by
  cases b with
  | zero => rfl
  | succ b =>
      simp [selectiveRelativeHalfNormalForm, corollary74MergerRelativeHalfInitial,
        relativeToffoliTailSymbolicCircuit, List.append_assoc]

@[simp]
theorem corollary74MergerRelativeHalfInitial_oneQubitCount {b n : ℕ}
    (layout : InwardLadderLayout b n) :
    SymbolicCircuit.oneQubitCount (corollary74MergerRelativeHalfInitial b layout) =
      6 * b + 3 := by
  have h := selectiveRelativeHalfNormalForm_oneQubitCount layout
  rw [corollary74MergerRelativeHalfNormalForm_eq_initial_end,
    SymbolicCircuit.oneQubitCount_append] at h
  change SymbolicCircuit.oneQubitCount (corollary74MergerRelativeHalfInitial b layout) + 1 =
    6 * b + 4 at h
  omega

@[simp]
theorem corollary74MergerRelativeHalfInitial_cnotCount {b n : ℕ}
    (layout : InwardLadderLayout b n) :
    SymbolicCircuit.cnotCount (corollary74MergerRelativeHalfInitial b layout) =
      6 * b + 3 := by
  have h := selectiveRelativeHalfNormalForm_cnotCount layout
  rw [corollary74MergerRelativeHalfNormalForm_eq_initial_end,
    SymbolicCircuit.cnotCount_append] at h
  simpa [relativeToffoliEndSymbolic, SymbolicPrimitive.inverseAtom,
    SymbolicCircuit.cnotWeight] using h

/-- Unnormalized relative-inverse/phase boundary across the smaller half. -/
def corollary74MergerRelativePhaseAcrossSmallerInput {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    SymbolicCircuit Corollary74FactorAtom n :=
  [relativeToffoliEndSymbolic layout.targetWire] ++
    selectiveRelativeHalfNormalForm b layout.smaller ++
      [SymbolicPrimitive.atom layout.targetWire .phase]

/-- Real target-directed fusion of a relative inverse with a later phase word. -/
def corollary74MergerRelativePhaseAcrossSmaller {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    SymbolicCircuit Corollary74FactorAtom n :=
  SymbolicCircuit.normalizeAtWire layout.targetWire
    (corollary74MergerRelativePhaseAcrossSmallerInput layout)

def corollary74MergerRelativePhaseAcrossSmallerNormalForm {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    SymbolicCircuit Corollary74FactorAtom n :=
  selectiveRelativeHalfNormalForm b layout.smaller ++
    [.oneQubit layout.targetWire
      (FreeGroup.of Corollary74FactorAtom.phase *
        (FreeGroup.of Corollary74FactorAtom.relative)⁻¹)]

@[simp]
theorem corollary74MergerRelativePhaseAcrossSmaller_eq_normalForm {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    corollary74MergerRelativePhaseAcrossSmaller layout =
      corollary74MergerRelativePhaseAcrossSmallerNormalForm layout := by
  unfold corollary74MergerRelativePhaseAcrossSmaller corollary74MergerRelativePhaseAcrossSmallerInput
  simp only [relativeToffoliEndSymbolic,
    SymbolicPrimitive.inverseAtom, SymbolicPrimitive.atom]
  apply SymbolicCircuit.normalizeAtWire_words_across_avoiding
  · exact selectiveRelativeHalfNormalForm_smaller_avoids_target layout
  · exact selectiveRelativeHalfNormalForm_stable layout.smaller
  · decide

@[simp]
theorem corollary74MergerRelativePhaseAcrossSmaller_oneQubitCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    SymbolicCircuit.oneQubitCount (corollary74MergerRelativePhaseAcrossSmaller layout) =
      6 * b + 5 := by
  rw [corollary74MergerRelativePhaseAcrossSmaller_eq_normalForm]
  simp [corollary74MergerRelativePhaseAcrossSmallerNormalForm,
    relativeToffoliStartSymbolic, SymbolicPrimitive.atom,
    SymbolicCircuit.oneQubitWeight]
  omega

@[simp]
theorem corollary74MergerRelativePhaseAcrossSmaller_cnotCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    SymbolicCircuit.cnotCount (corollary74MergerRelativePhaseAcrossSmaller layout) =
      6 * b + 3 := by
  rw [corollary74MergerRelativePhaseAcrossSmaller_eq_normalForm]
  simp [corollary74MergerRelativePhaseAcrossSmallerNormalForm,
    relativeToffoliStartSymbolic, SymbolicPrimitive.atom,
    SymbolicCircuit.cnotWeight]

@[simp]
theorem corollary74MergerEvalEraseRelativePhaseAcrossSmaller {b n : ℕ}
    (valuation : Corollary74FactorAtom → QubitUnitary)
    (layout : InwardLadderLayout (b + 1) n) :
    FusionCircuit.eval
        (SymbolicCircuit.erase valuation
          (corollary74MergerRelativePhaseAcrossSmaller layout)) =
      FusionCircuit.eval
        (SymbolicCircuit.erase valuation
          (corollary74MergerRelativePhaseAcrossSmallerInput layout)) := by
  exact SymbolicCircuit.eval_erase_normalizeAtWire valuation
    layout.targetWire _

/-- Adjacent instance used at the end of the literal adjoint A block. -/
def corollary74MergerRelativePhaseAdjacentInput {n : ℕ} (wire : Fin n) :
    SymbolicCircuit Corollary74FactorAtom n :=
  [relativeToffoliEndSymbolic wire,
    SymbolicPrimitive.atom wire .phase]

def corollary74MergerRelativePhaseAdjacent {n : ℕ} (wire : Fin n) :
    SymbolicCircuit Corollary74FactorAtom n :=
  SymbolicCircuit.normalizeAtWire wire (corollary74MergerRelativePhaseAdjacentInput wire)

@[simp]
theorem corollary74MergerRelativePhaseAdjacent_eq {n : ℕ} (wire : Fin n) :
    corollary74MergerRelativePhaseAdjacent wire =
      [.oneQubit wire
        (FreeGroup.of Corollary74FactorAtom.phase *
          (FreeGroup.of Corollary74FactorAtom.relative)⁻¹)] := by
  change SymbolicCircuit.normalizeAtWire wire
      ([.oneQubit wire (FreeGroup.of Corollary74FactorAtom.relative)⁻¹] ++
        ([] : SymbolicCircuit Corollary74FactorAtom n) ++
          [.oneQubit wire (FreeGroup.of Corollary74FactorAtom.phase)]) = _
  apply SymbolicCircuit.normalizeAtWire_words_across_avoiding
  · simp
  · trivial
  · decide

@[simp]
theorem corollary74MergerEvalEraseRelativePhaseAdjacent
    (valuation : Corollary74FactorAtom → QubitUnitary)
    {n : ℕ} (wire : Fin n) :
    FusionCircuit.eval
        (SymbolicCircuit.erase valuation
          (corollary74MergerRelativePhaseAdjacent wire)) =
      FusionCircuit.eval
        (SymbolicCircuit.erase valuation
          (corollary74MergerRelativePhaseAdjacentInput wire)) := by
  exact SymbolicCircuit.eval_erase_normalizeAtWire valuation wire _

@[simp]
theorem corollary74MergerRelativePhaseAdjacent_oneQubitCount {n : ℕ} (wire : Fin n) :
    SymbolicCircuit.oneQubitCount (corollary74MergerRelativePhaseAdjacent wire) = 1 := by
  rw [corollary74MergerRelativePhaseAdjacent_eq]
  rfl

@[simp]
theorem corollary74MergerRelativePhaseAdjacent_cnotCount {n : ℕ} (wire : Fin n) :
    SymbolicCircuit.cnotCount (corollary74MergerRelativePhaseAdjacent wire) = 0 := by
  rw [corollary74MergerRelativePhaseAdjacent_eq]
  rfl

/-- Literal adjoint of A before its final relative inverse on A's target. -/
def corollary74MergerRelativeInwardAdjointBeforeEnd {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    SymbolicCircuit Corollary74FactorAtom n :=
  (selectiveRelativeHalfNormalForm b layout.smaller).adjoint ++
    (selectiveRelativeHalfNormalTail (b + 1) layout).adjoint

@[simp]
theorem corollary74MergerSelectiveRelativeInwardAdjoint_eq_before_end {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    (selectiveMergedRelativeInwardSymbolicCircuit layout).adjoint =
      corollary74MergerRelativeInwardAdjointBeforeEnd layout ++
        [relativeToffoliEndSymbolic layout.targetWire] := by
  rw [selectiveMergedRelativeInwardSymbolicCircuit_eq_normalForm]
  simp [selectiveMergedRelativeInwardNormalForm,
    corollary74MergerRelativeInwardAdjointBeforeEnd,
    selectiveRelativeHalfNormalForm_eq_start_tail,
    relativeToffoliStartSymbolic, relativeToffoliEndSymbolic,
    SymbolicPrimitive.atom, SymbolicPrimitive.inverseAtom,
    SymbolicCircuit.adjoint, SymbolicPrimitive.adjoint,
    List.append_assoc]

@[simp]
theorem corollary74MergerRelativeInwardAdjointBeforeEnd_oneQubitCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    SymbolicCircuit.oneQubitCount
        (corollary74MergerRelativeInwardAdjointBeforeEnd layout) = 12 * b + 13 := by
  simp [corollary74MergerRelativeInwardAdjointBeforeEnd,
    relativeToffoliStartSymbolic, SymbolicPrimitive.atom,
    SymbolicCircuit.oneQubitWeight]
  omega

@[simp]
theorem corollary74MergerRelativeInwardAdjointBeforeEnd_cnotCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    SymbolicCircuit.cnotCount
        (corollary74MergerRelativeInwardAdjointBeforeEnd layout) = 12 * b + 12 := by
  simp [corollary74MergerRelativeInwardAdjointBeforeEnd,
    relativeToffoliStartSymbolic, SymbolicPrimitive.atom,
    SymbolicCircuit.cnotWeight]
  omega

def corollary74MergerSwappedForwardPrefixAfterPhase {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    SymbolicCircuit Corollary74FactorAtom n :=
  corollary74MergerExactForwardPrefixAfterPhase
    (layout.borrowedWire (Fin.last b))
    (layout.controlWire (Fin.last (b + 2))) layout.targetWire
    (layout.controlWire_ne_borrowedWire _ _).symm
    (layout.borrowedWire_ne_targetWire _)
    (layout.controlWire_ne_targetWire _)

def corollary74MergerSwappedForwardPrefixAfterPhaseA {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    SymbolicCircuit Corollary74FactorAtom n :=
  corollary74MergerExactForwardPrefixAfterPhaseA
    (layout.borrowedWire (Fin.last b))
    (layout.controlWire (Fin.last (b + 2))) layout.targetWire
    (layout.controlWire_ne_borrowedWire _ _).symm
    (layout.borrowedWire_ne_targetWire _)
    (layout.controlWire_ne_targetWire _)

def corollary74MergerStandardAdjointMiddleBeforeAInverse {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    SymbolicCircuit Corollary74FactorAtom n :=
  corollary74MergerExactAdjointMiddleBeforeAInverse
    (layout.controlWire (Fin.last (b + 2)))
    (layout.borrowedWire (Fin.last b)) layout.targetWire
    (layout.controlWire_ne_borrowedWire _ _)
    (layout.controlWire_ne_targetWire _)
    (layout.borrowedWire_ne_targetWire _)

/-- Mixed B after removing the initial phase on its last control. -/
def corollary74MergerMixedAfterInitialPhase {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    SymbolicCircuit Corollary74FactorAtom n :=
  corollary74MergerSwappedForwardPrefixAfterPhase layout ++
    selectiveRelativeHalfNormalForm b layout.smaller ++
      exactToffoliAdjointMiddleSymbolicCircuit
        (layout.controlWire (Fin.last (b + 2)))
        (layout.borrowedWire (Fin.last b)) layout.targetWire
        (layout.controlWire_ne_borrowedWire _ _)
        (layout.controlWire_ne_targetWire _)
        (layout.borrowedWire_ne_targetWire _) ++
        phaseRelativeBoundaryNormalForm
          (layout.borrowedWire (Fin.last b)) ++
          selectiveRelativeHalfNormalTail b layout.smaller

@[simp]
theorem selectiveMixedNormalForm_eq_phase_after {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    selectiveMergedMixedHybridNormalForm layout =
      SymbolicPrimitive.atom
          (layout.controlWire (Fin.last (b + 2))) .phase ::
        corollary74MergerMixedAfterInitialPhase layout := by
  simp [selectiveMergedMixedHybridNormalForm,
    corollary74MergerMixedAfterInitialPhase, corollary74MergerSwappedForwardPrefixAfterPhase,
    List.append_assoc]

@[simp]
theorem corollary74MergerMixedAfterInitialPhase_oneQubitCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    SymbolicCircuit.oneQubitCount (corollary74MergerMixedAfterInitialPhase layout) =
      12 * b + 20 := by
  simp [corollary74MergerMixedAfterInitialPhase,
    corollary74MergerSwappedForwardPrefixAfterPhase,
    relativeToffoliStartSymbolic, SymbolicPrimitive.atom,
    SymbolicPrimitive.inverseAtom,
    SymbolicCircuit.oneQubitWeight]
  omega

@[simp]
theorem corollary74MergerMixedAfterInitialPhase_cnotCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    SymbolicCircuit.cnotCount (corollary74MergerMixedAfterInitialPhase layout) =
      12 * b + 22 := by
  simp [corollary74MergerMixedAfterInitialPhase,
    corollary74MergerSwappedForwardPrefixAfterPhase,
    relativeToffoliStartSymbolic, SymbolicPrimitive.atom,
    SymbolicPrimitive.inverseAtom,
    SymbolicCircuit.cnotWeight]
  omega

/-- Prefix of mixed B after its initial phase and before its final exact A⁻¹. -/
def corollary74MergerMixedAfterPhaseBeforeAInverse {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    SymbolicCircuit Corollary74FactorAtom n :=
  corollary74MergerSwappedForwardPrefixAfterPhase layout ++
    selectiveRelativeHalfNormalForm b layout.smaller ++
      corollary74MergerStandardAdjointMiddleBeforeAInverse layout

/-- Suffix of mixed B following its final exact A⁻¹. -/
def corollary74MergerMixedAfterAInverseTail {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    SymbolicCircuit Corollary74FactorAtom n :=
  phaseRelativeBoundaryNormalForm
      (layout.borrowedWire (Fin.last b)) ++
    selectiveRelativeHalfNormalTail b layout.smaller

@[simp]
theorem corollary74MergerMixedAfterInitialPhase_eq_splitAInverse {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    corollary74MergerMixedAfterInitialPhase layout =
      corollary74MergerMixedAfterPhaseBeforeAInverse layout ++
        [SymbolicPrimitive.inverseAtom layout.targetWire .A] ++
          corollary74MergerMixedAfterAInverseTail layout := by
  rw [corollary74MergerMixedAfterInitialPhase,
    corollary74MergerMixedAfterPhaseBeforeAInverse,
    corollary74MergerMixedAfterAInverseTail,
    corollary74MergerStandardAdjointMiddleBeforeAInverse,
    corollary74MergerExactAdjointMiddle_eq_before_AInverse]
  simp only [List.append_assoc]

@[simp]
theorem corollary74MergerMixedAfterPhaseBeforeAInverse_oneQubitCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    SymbolicCircuit.oneQubitCount
        (corollary74MergerMixedAfterPhaseBeforeAInverse layout) = 6 * b + 15 := by
  simp [corollary74MergerMixedAfterPhaseBeforeAInverse,
    corollary74MergerSwappedForwardPrefixAfterPhase,
    corollary74MergerStandardAdjointMiddleBeforeAInverse,
    relativeToffoliStartSymbolic, SymbolicPrimitive.atom,
    SymbolicCircuit.oneQubitWeight]
  omega

@[simp]
theorem corollary74MergerMixedAfterPhaseBeforeAInverse_cnotCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    SymbolicCircuit.cnotCount
        (corollary74MergerMixedAfterPhaseBeforeAInverse layout) = 6 * b + 19 := by
  simp [corollary74MergerMixedAfterPhaseBeforeAInverse,
    corollary74MergerSwappedForwardPrefixAfterPhase,
    corollary74MergerStandardAdjointMiddleBeforeAInverse,
    relativeToffoliStartSymbolic, SymbolicPrimitive.atom,
    SymbolicCircuit.cnotWeight]
  omega

@[simp]
theorem corollary74MergerMixedAfterAInverseTail_oneQubitCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    SymbolicCircuit.oneQubitCount (corollary74MergerMixedAfterAInverseTail layout) =
      6 * b + 4 := by
  simp [corollary74MergerMixedAfterAInverseTail]
  omega

@[simp]
theorem corollary74MergerMixedAfterAInverseTail_cnotCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    SymbolicCircuit.cnotCount (corollary74MergerMixedAfterAInverseTail layout) =
      6 * b + 3 := by
  simp [corollary74MergerMixedAfterAInverseTail]

/-- Mixed-B suffix after removing both the initial phase and following A factor. -/
def corollary74MergerMixedAfterInitialPhaseA {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    SymbolicCircuit Corollary74FactorAtom n :=
  corollary74MergerSwappedForwardPrefixAfterPhaseA layout ++
    selectiveRelativeHalfNormalForm b layout.smaller ++
      exactToffoliAdjointMiddleSymbolicCircuit
        (layout.controlWire (Fin.last (b + 2)))
        (layout.borrowedWire (Fin.last b)) layout.targetWire
        (layout.controlWire_ne_borrowedWire _ _)
        (layout.controlWire_ne_targetWire _)
        (layout.borrowedWire_ne_targetWire _) ++
        phaseRelativeBoundaryNormalForm
          (layout.borrowedWire (Fin.last b)) ++
          selectiveRelativeHalfNormalTail b layout.smaller

@[simp]
theorem corollary74MergerMixedAfterInitialPhase_eq_A_after {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    corollary74MergerMixedAfterInitialPhase layout =
      SymbolicPrimitive.atom layout.targetWire .A ::
        corollary74MergerMixedAfterInitialPhaseA layout := by
  simp [corollary74MergerMixedAfterInitialPhase,
    corollary74MergerMixedAfterInitialPhaseA,
    corollary74MergerSwappedForwardPrefixAfterPhase,
    corollary74MergerSwappedForwardPrefixAfterPhaseA,
    List.append_assoc]

@[simp]
theorem corollary74MergerMixedAfterInitialPhaseA_oneQubitCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    SymbolicCircuit.oneQubitCount (corollary74MergerMixedAfterInitialPhaseA layout) =
      12 * b + 19 := by
  simp [corollary74MergerMixedAfterInitialPhaseA,
    corollary74MergerSwappedForwardPrefixAfterPhaseA,
    relativeToffoliStartSymbolic, SymbolicPrimitive.atom,
    SymbolicPrimitive.inverseAtom,
    SymbolicCircuit.oneQubitWeight]
  omega

@[simp]
theorem corollary74MergerMixedAfterInitialPhaseA_cnotCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    SymbolicCircuit.cnotCount (corollary74MergerMixedAfterInitialPhaseA layout) =
      12 * b + 22 := by
  simp [corollary74MergerMixedAfterInitialPhaseA,
    corollary74MergerSwappedForwardPrefixAfterPhaseA,
    relativeToffoliStartSymbolic, SymbolicPrimitive.atom,
    SymbolicPrimitive.inverseAtom,
    SymbolicCircuit.cnotWeight]
  omega

end InwardLadderLayout

namespace FourBlockLayout

open InwardLadderLayout

private theorem corollary74MergerAvoidsWire_adjoint_iff {Atom : Type*} {n : ℕ}
    (wire : Fin n) (gate : SymbolicPrimitive Atom n) :
    SymbolicPrimitive.AvoidsWire wire gate.adjoint ↔
      SymbolicPrimitive.AvoidsWire wire gate := by
  cases gate <;>
    simp [SymbolicPrimitive.AvoidsWire, SymbolicPrimitive.adjoint]

private theorem corollary74MergerAdjoint_all_avoids {Atom : Type*} {n : ℕ}
    (wire : Fin n) (circuit : SymbolicCircuit Atom n)
    (havoid : ∀ gate ∈ circuit, SymbolicPrimitive.AvoidsWire wire gate) :
    ∀ gate ∈ circuit.adjoint, SymbolicPrimitive.AvoidsWire wire gate := by
  intro gate hgate
  simp only [SymbolicCircuit.adjoint, List.mem_map, List.mem_reverse] at hgate
  rcases hgate with ⟨original, horiginal, rfl⟩
  exact (corollary74MergerAvoidsWire_adjoint_iff wire original).2
    (havoid original horiginal)

def corollary74MergerBoundaryWire {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2) : Fin n :=
  (layout.corollary74ALayout hleft).targetWire

theorem corollary74MergerBoundaryWire_eq_bLast {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2) :
    layout.corollary74MergerBoundaryWire hleft =
      (layout.corollary74BLayout hright).controlWire
        (Fin.last (rightTail + 2)) := by
  simp [corollary74MergerBoundaryWire, corollary74ALayout, corollary74BLayout,
    aInwardLadderLayout, bInwardLadderLayout,
    InwardLadderLayout.targetWire, InwardLadderLayout.controlWire,
    InwardLadderLayout.workWire, bLadderSlotEmbedding,
    bControlSlotEmbedding, bControlSumEmbedding,
    aLadderSlotEmbedding, aWorkSlotEmbedding, aWorkSumEmbedding]

theorem corollary74MergerBoundaryWire_ne_target {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2) :
    layout.corollary74MergerBoundaryWire hleft ≠ layout.targetWire := by
  simpa [corollary74MergerBoundaryWire, corollary74ALayout] using
    layout.dirtyWire_ne_targetWire

def corollary74MergerFinalCancellationMiddle {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2) :
    SymbolicCircuit Corollary74FactorAtom n :=
  let aLayout := layout.corollary74ALayout hleft
  let bLayout := layout.corollary74BLayout hright
  bLayout.corollary74MergerMixedAfterAInverseTail ++
    aLayout.corollary74MergerRelativeInwardAdjointBeforeEnd ++
      InwardLadderLayout.corollary74MergerRelativePhaseAdjacent
        (layout.corollary74MergerBoundaryWire hleft)

theorem corollary74MergerFinalCancellationMiddle_all_avoids {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2)
    (htargetFree : leftTail ≤ rightTail + 1) :
    ∀ gate ∈ layout.corollary74MergerFinalCancellationMiddle hleft hright,
      SymbolicPrimitive.AvoidsWire
        (layout.corollary74BLayout hright).targetWire gate := by
  let aLayout := layout.corollary74ALayout hleft
  let bLayout := layout.corollary74BLayout hright
  have htargetEq : bLayout.targetWire = layout.targetWire := by
    simp [bLayout, corollary74BLayout]
  have haNotMem : layout.targetWire ∉ aLayout.logicalSupport := by
    simpa [aLayout, corollary74ALayout] using
      layout.targetWire_not_mem_aInwardLadderLogicalSupport
        (by omega) (by omega)
  have haControl : ∀ control, layout.targetWire ≠ aLayout.controlWire control := by
    intro control heq
    apply haNotMem
    exact (congrArg (· ∈ aLayout.logicalSupport) heq).mpr
      (aLayout.controlWire_mem_logicalSupport control)
  have haWork : ∀ work, layout.targetWire ≠ aLayout.workWire work := by
    intro work heq
    apply haNotMem
    exact (congrArg (· ∈ aLayout.logicalSupport) heq).mpr
      (aLayout.workWire_mem_logicalSupport work)
  have haLarge : ∀ candidate ∈
      selectiveRelativeHalfNormalForm (leftTail + 1) aLayout,
      SymbolicPrimitive.AvoidsWire layout.targetWire candidate :=
    selectiveRelativeHalfNormalForm_all_avoids aLayout layout.targetWire
      haControl haWork
  have haSmall : ∀ candidate ∈
      selectiveRelativeHalfNormalForm leftTail aLayout.smaller,
      SymbolicPrimitive.AvoidsWire layout.targetWire candidate := by
    apply selectiveRelativeHalfNormalForm_all_avoids
    · intro control
      simpa using haControl control.castSucc
    · intro work
      simpa using haWork work.castSucc
  have haTail : ∀ candidate ∈
      selectiveRelativeHalfNormalTail (leftTail + 1) aLayout,
      SymbolicPrimitive.AvoidsWire layout.targetWire candidate := by
    intro candidate hcandidate
    exact haLarge candidate (by
      rw [selectiveRelativeHalfNormalForm_eq_start_tail]
      simp [hcandidate])
  have haAdj : ∀ candidate ∈
      aLayout.corollary74MergerRelativeInwardAdjointBeforeEnd,
      SymbolicPrimitive.AvoidsWire layout.targetWire candidate := by
    intro candidate hcandidate
    simp only [InwardLadderLayout.corollary74MergerRelativeInwardAdjointBeforeEnd,
      List.mem_append] at hcandidate
    rcases hcandidate with hsmall | htail
    · exact corollary74MergerAdjoint_all_avoids layout.targetWire _ haSmall
        candidate hsmall
    · exact corollary74MergerAdjoint_all_avoids layout.targetWire _ haTail
        candidate htail
  have hbHalf : ∀ candidate ∈
      selectiveRelativeHalfNormalForm rightTail bLayout.smaller,
      SymbolicPrimitive.AvoidsWire bLayout.targetWire candidate :=
    selectiveRelativeHalfNormalForm_smaller_avoids_target bLayout
  have hbTail : ∀ candidate ∈
      selectiveRelativeHalfNormalTail rightTail bLayout.smaller,
      SymbolicPrimitive.AvoidsWire bLayout.targetWire candidate := by
    intro candidate hcandidate
    exact hbHalf candidate (by
      rw [selectiveRelativeHalfNormalForm_eq_start_tail]
      simp [hcandidate])
  intro gate hgate
  simp only [corollary74MergerFinalCancellationMiddle, List.mem_append] at hgate
  rcases hgate with (hb | ha) | hadjacent
  · simp only [InwardLadderLayout.corollary74MergerMixedAfterAInverseTail,
      List.mem_append] at hb
    rcases hb with hphase | htail
    · simp only [phaseRelativeBoundaryNormalForm, List.mem_singleton] at hphase
      subst gate
      simp only [SymbolicPrimitive.AvoidsWire]
      exact bLayout.borrowedWire_ne_targetWire (Fin.last rightTail)
    · exact hbTail gate htail
  · rw [htargetEq]
    exact haAdj gate ha
  · rw [InwardLadderLayout.corollary74MergerRelativePhaseAdjacent_eq] at hadjacent
    simp only [List.mem_singleton] at hadjacent
    subst gate
    simp only [SymbolicPrimitive.AvoidsWire]
    intro heq
    exact layout.corollary74MergerBoundaryWire_ne_target hleft (heq.trans htargetEq)

@[simp]
theorem corollary74MergerFinalCancellationMiddle_oneQubitCount
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2) :
    SymbolicCircuit.oneQubitCount
        (layout.corollary74MergerFinalCancellationMiddle hleft hright) =
      12 * leftTail + 6 * rightTail + 18 := by
  simp [corollary74MergerFinalCancellationMiddle, SymbolicCircuit.oneQubitWeight]
  omega

@[simp]
theorem corollary74MergerFinalCancellationMiddle_cnotCount
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2) :
    SymbolicCircuit.cnotCount
        (layout.corollary74MergerFinalCancellationMiddle hleft hright) =
      12 * leftTail + 6 * rightTail + 15 := by
  simp [corollary74MergerFinalCancellationMiddle, SymbolicCircuit.cnotWeight]
  omega

/--
Complete literal Corollary output after the two dirty-wire word fusions and the
certified final-target exact-factor cancellation.
-/
def completeMergedRelativeCorollary74SymbolicCircuit {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2) :
    SymbolicCircuit Corollary74FactorAtom n :=
  let aLayout := layout.corollary74ALayout hleft
  let bLayout := layout.corollary74BLayout hright
  corollary74MergerRelativeHalfInitial (leftTail + 1) aLayout ++
    corollary74MergerRelativePhaseAcrossSmaller aLayout ++
      corollary74MergerMixedAfterPhaseBeforeAInverse bLayout ++
        layout.corollary74MergerFinalCancellationMiddle hleft hright ++
          corollary74MergerMixedAfterInitialPhaseA bLayout

/-- Same chronology before deleting the cross-block exact A⁻¹/A pair. -/
def corollary74MergerCompleteExactPairRegroupedSymbolicCircuit
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2) :
    SymbolicCircuit Corollary74FactorAtom n :=
  let aLayout := layout.corollary74ALayout hleft
  let bLayout := layout.corollary74BLayout hright
  corollary74MergerRelativeHalfInitial (leftTail + 1) aLayout ++
    corollary74MergerRelativePhaseAcrossSmaller aLayout ++
      corollary74MergerMixedAfterPhaseBeforeAInverse bLayout ++
        ([SymbolicPrimitive.inverseAtom bLayout.targetWire .A] ++
          layout.corollary74MergerFinalCancellationMiddle hleft hright ++
            [SymbolicPrimitive.atom bLayout.targetWire .A]) ++
          corollary74MergerMixedAfterInitialPhaseA bLayout

/-- The explicit cross-block exact-factor deletion preserves exact evaluation. -/
theorem corollary74MergerEvalEraseCompleteMerged_eq_exactPair
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2)
    (htargetFree : leftTail ≤ rightTail + 1) :
    FusionCircuit.eval
        (SymbolicCircuit.erase corollary74FactorValuation
          (layout.completeMergedRelativeCorollary74SymbolicCircuit hleft hright)) =
      FusionCircuit.eval
        (SymbolicCircuit.erase corollary74FactorValuation
          (layout.corollary74MergerCompleteExactPairRegroupedSymbolicCircuit
            hleft hright)) := by
  have hdelete :=
    SymbolicCircuit.eval_erase_delete_inverse_across_avoiding
      corollary74FactorValuation
      (layout.corollary74BLayout hright).targetWire
      Corollary74FactorAtom.A
      (layout.corollary74MergerFinalCancellationMiddle hleft hright)
      (layout.corollary74MergerFinalCancellationMiddle_all_avoids
        hleft hright htargetFree)
  simp only [corollary74MergerEraseAppend, FusionCircuit.eval_append] at hdelete
  simp only [completeMergedRelativeCorollary74SymbolicCircuit,
    corollary74MergerCompleteExactPairRegroupedSymbolicCircuit,
    corollary74MergerEraseAppend, FusionCircuit.eval_append]
  rw [hdelete]

@[simp]
theorem completeMergedRelativeCorollary74SymbolicCircuit_oneQubitCount
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2) :
    SymbolicCircuit.oneQubitCount
        (layout.completeMergedRelativeCorollary74SymbolicCircuit hleft hright) =
      24 * (leftTail + rightTail) + 66 := by
  simp only [completeMergedRelativeCorollary74SymbolicCircuit,
    SymbolicCircuit.oneQubitCount_append,
    corollary74MergerRelativeHalfInitial_oneQubitCount,
    corollary74MergerRelativePhaseAcrossSmaller_oneQubitCount,
    corollary74MergerMixedAfterPhaseBeforeAInverse_oneQubitCount,
    corollary74MergerFinalCancellationMiddle_oneQubitCount,
    corollary74MergerMixedAfterInitialPhaseA_oneQubitCount]
  omega

@[simp]
theorem completeMergedRelativeCorollary74SymbolicCircuit_cnotCount
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2) :
    SymbolicCircuit.cnotCount
        (layout.completeMergedRelativeCorollary74SymbolicCircuit hleft hright) =
      24 * (leftTail + rightTail) + 68 := by
  simp only [completeMergedRelativeCorollary74SymbolicCircuit,
    SymbolicCircuit.cnotCount_append,
    corollary74MergerRelativeHalfInitial_cnotCount,
    corollary74MergerRelativePhaseAcrossSmaller_cnotCount,
    corollary74MergerMixedAfterPhaseBeforeAInverse_cnotCount,
    corollary74MergerFinalCancellationMiddle_cnotCount,
    corollary74MergerMixedAfterInitialPhaseA_cnotCount]
  omega

@[simp]
theorem completeMergedRelativeCorollary74SymbolicCircuit_gateCount
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2) :
    SymbolicCircuit.gateCount
        (layout.completeMergedRelativeCorollary74SymbolicCircuit hleft hright) =
      48 * (leftTail + rightTail) + 134 := by
  rw [SymbolicCircuit.gateCount_eq_componentCounts,
    completeMergedRelativeCorollary74SymbolicCircuit_oneQubitCount,
    completeMergedRelativeCorollary74SymbolicCircuit_cnotCount]
  omega

end FourBlockLayout

end

end Barenco.MultiControl

namespace Barenco.MultiControl

open Barenco.OneQubit
open Barenco.ControlledCircuit
open Barenco.Optimization
open Barenco.ThreeQubit

noncomputable section

namespace FourBlockLayout

open InwardLadderLayout

/-- The complete chronology before either dirty-wire fusion or the final-target
inverse/atom deletion. -/
def corollary74MergerCompleteRegroupedSymbolicCircuit {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2) :
    SymbolicCircuit Corollary74FactorAtom n :=
  let aLayout := layout.corollary74ALayout hleft
  let bLayout := layout.corollary74BLayout hright
  corollary74MergerRelativeHalfInitial (leftTail + 1) aLayout ++
    [relativeToffoliEndSymbolic (layout.corollary74MergerBoundaryWire hleft)] ++
      selectiveRelativeHalfNormalForm leftTail aLayout.smaller ++
        [SymbolicPrimitive.atom (layout.corollary74MergerBoundaryWire hleft) .phase] ++
          corollary74MergerMixedAfterPhaseBeforeAInverse bLayout ++
            [SymbolicPrimitive.inverseAtom bLayout.targetWire .A] ++
              corollary74MergerMixedAfterAInverseTail bLayout ++
                corollary74MergerRelativeInwardAdjointBeforeEnd aLayout ++
                  [relativeToffoliEndSymbolic
                    (layout.corollary74MergerBoundaryWire hleft)] ++
                    [SymbolicPrimitive.atom
                      (layout.corollary74MergerBoundaryWire hleft) .phase] ++
                      [SymbolicPrimitive.atom bLayout.targetWire .A] ++
                        corollary74MergerMixedAfterInitialPhaseA bLayout

/-- The four already-certified selective blocks in the paper's `A;B;A†;B`
chronology. -/
def corollary74MergerSelectedFourBlockSymbolicCircuit {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2) :
    SymbolicCircuit Corollary74FactorAtom n :=
  let a := selectiveMergedRelativeInwardSymbolicCircuit
    (layout.corollary74ALayout hleft)
  let b := selectiveMergedMixedHybridSymbolicCircuit
    (layout.corollary74BLayout hright)
  a ++ b ++ a.adjoint ++ b

theorem corollary74MergerCompleteRegrouped_eq_selected {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2) :
    layout.corollary74MergerCompleteRegroupedSymbolicCircuit hleft hright =
      layout.corollary74MergerSelectedFourBlockSymbolicCircuit hleft hright := by
  let aLayout := layout.corollary74ALayout hleft
  let bLayout := layout.corollary74BLayout hright
  have ha : selectiveMergedRelativeInwardSymbolicCircuit aLayout =
      corollary74MergerRelativeHalfInitial (leftTail + 1) aLayout ++
        [relativeToffoliEndSymbolic aLayout.targetWire] ++
          selectiveRelativeHalfNormalForm leftTail aLayout.smaller := by
    rw [selectiveMergedRelativeInwardSymbolicCircuit_eq_normalForm]
    simp only [selectiveMergedRelativeInwardNormalForm,
      corollary74MergerRelativeHalfNormalForm_eq_initial_end, List.append_assoc]
  have hbFirst : selectiveMergedMixedHybridSymbolicCircuit bLayout =
      [SymbolicPrimitive.atom
          (bLayout.controlWire (Fin.last (rightTail + 2))) .phase] ++
        corollary74MergerMixedAfterPhaseBeforeAInverse bLayout ++
          [SymbolicPrimitive.inverseAtom bLayout.targetWire .A] ++
            corollary74MergerMixedAfterAInverseTail bLayout := by
    rw [selectiveMergedMixedHybridSymbolicCircuit_eq_normalForm,
      selectiveMixedNormalForm_eq_phase_after,
      corollary74MergerMixedAfterInitialPhase_eq_splitAInverse]
    simp [List.append_assoc]
  have hbSecond : selectiveMergedMixedHybridSymbolicCircuit bLayout =
      [SymbolicPrimitive.atom
          (bLayout.controlWire (Fin.last (rightTail + 2))) .phase] ++
        [SymbolicPrimitive.atom bLayout.targetWire .A] ++
          corollary74MergerMixedAfterInitialPhaseA bLayout := by
    rw [selectiveMergedMixedHybridSymbolicCircuit_eq_normalForm,
      selectiveMixedNormalForm_eq_phase_after,
      corollary74MergerMixedAfterInitialPhase_eq_A_after]
    simp
  have hwire : aLayout.targetWire =
      bLayout.controlWire (Fin.last (rightTail + 2)) := by
    exact layout.corollary74MergerBoundaryWire_eq_bLast hleft hright
  rw [corollary74MergerCompleteRegroupedSymbolicCircuit,
    corollary74MergerSelectedFourBlockSymbolicCircuit]
  change corollary74MergerRelativeHalfInitial (leftTail + 1) aLayout ++
      [relativeToffoliEndSymbolic aLayout.targetWire] ++
        selectiveRelativeHalfNormalForm leftTail aLayout.smaller ++
          [SymbolicPrimitive.atom aLayout.targetWire .phase] ++
            corollary74MergerMixedAfterPhaseBeforeAInverse bLayout ++
              [SymbolicPrimitive.inverseAtom bLayout.targetWire .A] ++
                corollary74MergerMixedAfterAInverseTail bLayout ++
                  corollary74MergerRelativeInwardAdjointBeforeEnd aLayout ++
                    [relativeToffoliEndSymbolic aLayout.targetWire] ++
                      [SymbolicPrimitive.atom aLayout.targetWire .phase] ++
                        [SymbolicPrimitive.atom bLayout.targetWire .A] ++
                          corollary74MergerMixedAfterInitialPhaseA bLayout =
    selectiveMergedRelativeInwardSymbolicCircuit aLayout ++
      selectiveMergedMixedHybridSymbolicCircuit bLayout ++
        (selectiveMergedRelativeInwardSymbolicCircuit aLayout).adjoint ++
          selectiveMergedMixedHybridSymbolicCircuit bLayout
  nth_rewrite 1 [ha]
  nth_rewrite 1 [hbFirst]
  rw [corollary74MergerSelectiveRelativeInwardAdjoint_eq_before_end]
  nth_rewrite 1 [hbSecond]
  rw [hwire]
  simp only [List.append_assoc]

/-- Expanding the two dirty-wire normalizer calls recovers the completely
unnormalized four-block chronology. -/
theorem corollary74MergerEvalEraseExactPair_eq_completeRegrouped
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2) :
    FusionCircuit.eval
        (SymbolicCircuit.erase corollary74FactorValuation
          (layout.corollary74MergerCompleteExactPairRegroupedSymbolicCircuit
            hleft hright)) =
      FusionCircuit.eval
        (SymbolicCircuit.erase corollary74FactorValuation
          (layout.corollary74MergerCompleteRegroupedSymbolicCircuit hleft hright)) := by
  have hadjacent :
      FusionCircuit.eval
          (SymbolicCircuit.erase corollary74FactorValuation
            (InwardLadderLayout.corollary74MergerRelativePhaseAdjacentInput
              (layout.corollary74MergerBoundaryWire hleft))) =
        FusionCircuit.eval
            (SymbolicCircuit.erase corollary74FactorValuation
              [SymbolicPrimitive.atom
                (layout.corollary74MergerBoundaryWire hleft) .phase]) *
          FusionCircuit.eval
            (SymbolicCircuit.erase corollary74FactorValuation
              [relativeToffoliEndSymbolic
                (layout.corollary74MergerBoundaryWire hleft)]) := by
    rw [show InwardLadderLayout.corollary74MergerRelativePhaseAdjacentInput
          (layout.corollary74MergerBoundaryWire hleft) =
        [relativeToffoliEndSymbolic (layout.corollary74MergerBoundaryWire hleft)] ++
          [SymbolicPrimitive.atom
            (layout.corollary74MergerBoundaryWire hleft) .phase] by rfl]
    rw [corollary74MergerEraseAppend, FusionCircuit.eval_append]
  simp only [corollary74MergerCompleteExactPairRegroupedSymbolicCircuit,
    corollary74MergerCompleteRegroupedSymbolicCircuit,
    corollary74MergerFinalCancellationMiddle,
    InwardLadderLayout.corollary74MergerRelativePhaseAcrossSmaller,
    InwardLadderLayout.corollary74MergerRelativePhaseAdjacent,
    corollary74MergerEraseAppend, FusionCircuit.eval_append]
  rw [SymbolicCircuit.eval_erase_normalizeAtWire]
  rw [SymbolicCircuit.eval_erase_normalizeAtWire]
  rw [hadjacent]
  simp only [InwardLadderLayout.corollary74MergerRelativePhaseAcrossSmallerInput,
    corollary74MergerBoundaryWire, corollary74MergerEraseAppend, FusionCircuit.eval_append, mul_assoc]

/-- The four selective blocks have the same exact evaluator as the coherent
unmerged symbolic chronology. -/
theorem corollary74MergerEvalEraseSelectedFourBlock_eq_mixedExpanded
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2) :
    FusionCircuit.eval
        (SymbolicCircuit.erase corollary74FactorValuation
          (layout.corollary74MergerSelectedFourBlockSymbolicCircuit hleft hright)) =
      (layout.mixedExpandedRelativeCorollary74FusionCircuit
        hleft hright).eval := by
  simp only [corollary74MergerSelectedFourBlockSymbolicCircuit,
    mixedExpandedRelativeCorollary74FusionCircuit,
    mixedExpandedRelativeCorollary74SymbolicCircuit,
    corollary74MergerEraseAppend, FusionCircuit.eval_append]
  rw [eval_erase_selectiveMergedRelativeInwardSymbolicCircuit,
    eval_erase_selectiveMergedMixedHybridSymbolicCircuit,
    SymbolicCircuit.eval_erase_adjoint,
    eval_erase_selectiveMergedRelativeInwardSymbolicCircuit]
  rw [InwardLadderLayout.erase_relativeInwardLadderSymbolicCircuit,
    InwardLadderLayout.erase_mixedHybridInwardLadderSymbolicCircuit,
    SymbolicCircuit.erase_adjoint,
    FusionCircuit.eval_adjoint,
    InwardLadderLayout.erase_relativeInwardLadderSymbolicCircuit]

/-- Exact valued semantics of the selective complete `A;B;A†;B` merger. -/
@[simp]
theorem eval_completeMergedRelativeCorollary74SymbolicCircuit_eq_raw
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2)
    (htargetFree : leftTail ≤ rightTail + 1) :
    FusionCircuit.eval
        (SymbolicCircuit.erase corollary74FactorValuation
          (layout.completeMergedRelativeCorollary74SymbolicCircuit hleft hright)) =
      (layout.mixedExpandedRelativeCorollary74FusionCircuit
        hleft hright).eval := by
  rw [layout.corollary74MergerEvalEraseCompleteMerged_eq_exactPair
      hleft hright htargetFree,
    layout.corollary74MergerEvalEraseExactPair_eq_completeRegrouped hleft hright,
    layout.corollary74MergerCompleteRegrouped_eq_selected hleft hright,
    layout.corollary74MergerEvalEraseSelectedFourBlock_eq_mixedExpanded hleft hright]

/-- Consequently the selective 66-one-qubit/68-CNOT construction implements
the intended multiply controlled Pauli-X exactly on the full register. -/
@[simp]
theorem eval_completeMergedRelativeCorollary74SymbolicCircuit
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2)
    (htargetFree : leftTail ≤ rightTail + 1) :
    FusionCircuit.eval
        (SymbolicCircuit.erase corollary74FactorValuation
          (layout.completeMergedRelativeCorollary74SymbolicCircuit hleft hright)) =
      positiveControlledUnitary layout.targetWire
        layout.dataLayout.controlSet pauliX := by
  rw [layout.eval_completeMergedRelativeCorollary74SymbolicCircuit_eq_raw
      hleft hright htargetFree,
    layout.eval_mixedExpandedRelativeCorollary74FusionCircuit
      hleft hright htargetFree]

/-- The cross-block rewrites preserve every ordered CNOT endpoint exactly. -/
theorem cnotTrace_completeMergedRelativeCorollary74SymbolicCircuit_eq_regrouped
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2) :
    SymbolicCircuit.cnotTrace
        (layout.completeMergedRelativeCorollary74SymbolicCircuit hleft hright) =
      SymbolicCircuit.cnotTrace
        (layout.corollary74MergerCompleteRegroupedSymbolicCircuit
          hleft hright) := by
  simp [completeMergedRelativeCorollary74SymbolicCircuit,
    corollary74MergerCompleteRegroupedSymbolicCircuit,
    corollary74MergerFinalCancellationMiddle,
    corollary74MergerRelativePhaseAcrossSmaller,
    corollary74MergerRelativePhaseAcrossSmallerInput,
    corollary74MergerRelativePhaseAdjacent,
    corollary74MergerRelativePhaseAdjacentInput,
    corollary74MergerBoundaryWire,
    relativeToffoliEndSymbolic, relativeToffoliStartSymbolic,
    SymbolicPrimitive.atom, SymbolicPrimitive.inverseAtom]

/--
The final emitted list has the complete ordered CNOT trace of the four
selectively merged `A;B;A†;B` components.
-/
theorem cnotTrace_completeMergedRelativeCorollary74SymbolicCircuit_eq_selected
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2) :
    SymbolicCircuit.cnotTrace
        (layout.completeMergedRelativeCorollary74SymbolicCircuit hleft hright) =
      SymbolicCircuit.cnotTrace
        (layout.corollary74MergerSelectedFourBlockSymbolicCircuit
          hleft hright) := by
  rw [cnotTrace_completeMergedRelativeCorollary74SymbolicCircuit_eq_regrouped,
    layout.corollary74MergerCompleteRegrouped_eq_selected hleft hright]

end FourBlockLayout

end

end Barenco.MultiControl
