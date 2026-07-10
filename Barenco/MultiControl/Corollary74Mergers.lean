import Barenco.MultiControl.Corollary74Fusion
import Barenco.Optimization.SymbolicAdjoint
import Barenco.Optimization.SymbolicExpose

/-!
# Exact symbolic mergers for corrected Corollary 7.4

The raw transparent construction still contains many inverse one-qubit factors
separated only by gates on other wires.  This module assigns all relative and
exact-Toffoli payloads one coherent free-group provenance, applies the verified
target-directed symbolic normalizer at the recursive boundaries, and emits a
literal one-qubit/CNOT circuit.

All equalities are exact on the complete ambient register.  In particular, the
relative-phase ingredients are never substituted using a phase quotient: their
signed contextual correctness enters only through the already proved exact
`A;B;A†;B` evaluator.
-/

namespace Barenco.MultiControl

open Barenco.OneQubit
open Barenco.ControlledCircuit
open Barenco.Optimization
open Barenco.ThreeQubit

noncomputable section

/-! ## One coherent symbolic payload package -/

/-- Provenance atoms shared by every relative and exact occurrence. -/
inductive Corollary74FactorAtom where
  | relative
  | phase
  | A
  | B
  | C
  deriving DecidableEq

/-- Interpret all exact factors from one selected square-root package for X. -/
def corollary74FactorValuation : Corollary74FactorAtom → QubitUnitary :=
  let V := unitarySquareRoot pauliX
  let factors := selectedColumnABCFactors (specialUnitaryPart V)
  fun atom ↦ match atom with
    | .relative => ryUnitary (Real.pi / 4)
    | .phase => controlPhaseUnitary (determinantPhaseAngle V)
    | .A => specialUnitaryAsUnitary factors.A
    | .B => specialUnitaryAsUnitary factors.B
    | .C => specialUnitaryAsUnitary factors.C

private theorem erase_append
    (first second : SymbolicCircuit Corollary74FactorAtom n) :
    SymbolicCircuit.erase corollary74FactorValuation (first ++ second) =
      FusionCircuit.append
        (SymbolicCircuit.erase corollary74FactorValuation first)
        (SymbolicCircuit.erase corollary74FactorValuation second) := by
  simp [SymbolicCircuit.erase, FusionCircuit.append]

/-- The certified Y-rotation inverse carries the negated angle exactly. -/
private theorem ryUnitary_inv (theta : ℝ) :
    (ryUnitary theta)⁻¹ = ryUnitary (-theta) := by
  apply inv_eq_iff_mul_eq_one.mpr
  apply Subtype.ext
  change ry theta * ry (-theta) = (1 : QubitMatrix)
  rw [ry_mul]
  rw [add_neg_cancel]
  exact ry_zero

/-! ## Relative occurrence syntax -/

/-- One seven-node relative-phase Toffoli with formal endpoint provenance. -/
def relativeToffoliSymbolicCircuit {n : ℕ}
    (first second target : Fin n)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target) :
    SymbolicCircuit Corollary74FactorAtom n :=
  [SymbolicPrimitive.atom target .relative,
    .cnot second target hsecondTarget,
    SymbolicPrimitive.atom target .relative,
    .cnot first target hfirstTarget,
    SymbolicPrimitive.inverseAtom target .relative,
    .cnot second target hsecondTarget,
    SymbolicPrimitive.inverseAtom target .relative]

@[simp]
theorem erase_relativeToffoliSymbolicCircuit {n : ℕ}
    (first second target : Fin n)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target) :
    SymbolicCircuit.erase corollary74FactorValuation
        (relativeToffoliSymbolicCircuit first second target
          hfirstTarget hsecondTarget) =
      relativePhaseToffoliAFusionCircuit first second target
        hfirstTarget hsecondTarget := by
  simp [relativeToffoliSymbolicCircuit, corollary74FactorValuation,
    relativePhaseToffoliAFusionCircuit, SymbolicPrimitive.atom,
    SymbolicPrimitive.inverseAtom, ryUnitary_inv]

/-! ## Explicit oriented exact-Toffoli syntax -/

/--
The transparent sixteen-node expansion for one ordered choice of the two
Toffoli controls.  Every occurrence uses the same valuation; only wire roles
change.
-/
def exactToffoliForwardSymbolicCircuit {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target) :
    SymbolicCircuit Corollary74FactorAtom n :=
  [SymbolicPrimitive.atom second .phase,
    SymbolicPrimitive.atom target .A,
    .cnot second target hsecondTarget,
    SymbolicPrimitive.atom target .B,
    .cnot second target hsecondTarget,
    .cnot first second hfirstSecond,
    .cnot second target hsecondTarget,
    SymbolicPrimitive.inverseAtom target .B,
    .cnot second target hsecondTarget,
    SymbolicPrimitive.inverseAtom second .phase,
    .cnot first second hfirstSecond,
    SymbolicPrimitive.atom first .phase,
    .cnot first target hfirstTarget,
    SymbolicPrimitive.atom target .B,
    .cnot first target hfirstTarget,
    SymbolicPrimitive.atom target .C]

@[simp]
theorem erase_exactToffoliForwardSymbolicCircuit {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target) :
    SymbolicCircuit.erase corollary74FactorValuation
        (exactToffoliForwardSymbolicCircuit first second target
          hfirstSecond hfirstTarget hsecondTarget) =
      selectedDoubleControlledExpansion16FusionCircuit
        first second target hfirstSecond hfirstTarget hsecondTarget pauliX := by
  simp [exactToffoliForwardSymbolicCircuit,
    selectedDoubleControlledExpansion16FusionCircuit,
    corollary74FactorValuation, SymbolicPrimitive.atom,
    SymbolicPrimitive.inverseAtom, FusionPrimitive.adjoint]

/-- Literal reverse/inverse of one oriented exact expansion. -/
def exactToffoliAdjointSymbolicCircuit {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target) :
    SymbolicCircuit Corollary74FactorAtom n :=
  (exactToffoliForwardSymbolicCircuit first second target hfirstSecond
    hfirstTarget hsecondTarget).adjoint

@[simp]
theorem erase_exactToffoliAdjointSymbolicCircuit {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target) :
    SymbolicCircuit.erase corollary74FactorValuation
        (exactToffoliAdjointSymbolicCircuit first second target
          hfirstSecond hfirstTarget hsecondTarget) =
      (selectedDoubleControlledExpansion16FusionCircuit
        first second target hfirstSecond hfirstTarget hsecondTarget
          pauliX).adjoint := by
  simp [exactToffoliAdjointSymbolicCircuit]

/-! ## Raw symbolic relative ladders -/

namespace InwardLadderLayout

/-- Symbolic base occurrence. -/
def relativeBaseSymbolicCircuit {n : ℕ}
    (layout : InwardLadderLayout 0 n) :
    SymbolicCircuit Corollary74FactorAtom n :=
  relativeToffoliSymbolicCircuit
    (layout.controlWire 0) (layout.controlWire 1) layout.targetWire
    (layout.controlWire_ne_targetWire 0)
    (layout.controlWire_ne_targetWire 1)

/-- Symbolic recursive outer occurrence. -/
def relativeOuterSymbolicCircuit {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    SymbolicCircuit Corollary74FactorAtom n :=
  relativeToffoliSymbolicCircuit
    (layout.controlWire (Fin.last (b + 2)))
    (layout.borrowedWire (Fin.last b)) layout.targetWire
    (layout.controlWire_ne_targetWire _)
    (layout.borrowedWire_ne_targetWire _)

/-- Complete raw symbolic half ladder. -/
def relativeHalfLadderSymbolicCircuit {n : ℕ} :
    (b : ℕ) → InwardLadderLayout b n →
      SymbolicCircuit Corollary74FactorAtom n
  | 0, layout => layout.relativeBaseSymbolicCircuit
  | b + 1, layout =>
      layout.relativeOuterSymbolicCircuit ++
        relativeHalfLadderSymbolicCircuit b layout.smaller ++
          layout.relativeOuterSymbolicCircuit

/-- Complete raw symbolic all-relative inward ladder. -/
def relativeInwardLadderSymbolicCircuit {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    SymbolicCircuit Corollary74FactorAtom n :=
  relativeHalfLadderSymbolicCircuit (b + 1) layout ++
    relativeHalfLadderSymbolicCircuit b layout.smaller

@[simp]
theorem erase_relativeBaseSymbolicCircuit {n : ℕ}
    (layout : InwardLadderLayout 0 n) :
    SymbolicCircuit.erase corollary74FactorValuation
        layout.relativeBaseSymbolicCircuit =
      layout.relativeBaseFusionCircuit := by
  simp [relativeBaseSymbolicCircuit, relativeBaseFusionCircuit]

@[simp]
theorem erase_relativeOuterSymbolicCircuit {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    SymbolicCircuit.erase corollary74FactorValuation
        layout.relativeOuterSymbolicCircuit =
      layout.relativeOuterFusionCircuit := by
  simp [relativeOuterSymbolicCircuit, relativeOuterFusionCircuit]

@[simp]
theorem erase_relativeHalfLadderSymbolicCircuit {b n : ℕ}
    (layout : InwardLadderLayout b n) :
    SymbolicCircuit.erase corollary74FactorValuation
        (relativeHalfLadderSymbolicCircuit b layout) =
      relativeHalfLadderFusionCircuit b layout := by
  induction b with
  | zero =>
      rw [relativeHalfLadderSymbolicCircuit,
        relativeHalfLadderFusionCircuit,
        erase_relativeBaseSymbolicCircuit]
  | succ b ih =>
      rw [relativeHalfLadderSymbolicCircuit,
        relativeHalfLadderFusionCircuit]
      simp only [SymbolicCircuit.erase, List.map_append,
        FusionCircuit.append]
      rw [show List.map (SymbolicPrimitive.erase corollary74FactorValuation)
            layout.relativeOuterSymbolicCircuit =
          layout.relativeOuterFusionCircuit from
        erase_relativeOuterSymbolicCircuit layout]
      rw [show List.map (SymbolicPrimitive.erase corollary74FactorValuation)
            (relativeHalfLadderSymbolicCircuit b layout.smaller) =
          relativeHalfLadderFusionCircuit b layout.smaller from
        ih layout.smaller]
      simp only [List.append_assoc]

@[simp]
theorem erase_relativeInwardLadderSymbolicCircuit {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    SymbolicCircuit.erase corollary74FactorValuation
        layout.relativeInwardLadderSymbolicCircuit =
      layout.relativeInwardLadderFusionCircuit := by
  rw [relativeInwardLadderSymbolicCircuit,
    relativeInwardLadderFusionCircuit]
  simp only [SymbolicCircuit.erase, List.map_append,
    FusionCircuit.append]
  rw [show List.map (SymbolicPrimitive.erase corollary74FactorValuation)
          (relativeHalfLadderSymbolicCircuit (b + 1) layout) =
        relativeHalfLadderFusionCircuit (b + 1) layout from
      erase_relativeHalfLadderSymbolicCircuit layout]
  rw [show List.map (SymbolicPrimitive.erase corollary74FactorValuation)
          (relativeHalfLadderSymbolicCircuit b layout.smaller) =
        relativeHalfLadderFusionCircuit b layout.smaller from
      erase_relativeHalfLadderSymbolicCircuit layout.smaller]

/-! ## Coherent mixed orientations for the two exact outer occurrences -/

private theorem twoControlSet_swap {n : ℕ}
    (first second target : Fin n)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target) :
    twoControlSet second first target hsecondTarget hfirstTarget =
      twoControlSet first second target hfirstTarget hsecondTarget := by
  simp [twoControlSet, Finset.pair_comm]

/--
Forward exact outer expansion with the borrowed wire first and the new control
second.  Its first symbolic node is therefore the phase atom on the new control.
-/
def swappedForwardOuterSymbolicCircuit {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    SymbolicCircuit Corollary74FactorAtom n :=
  exactToffoliForwardSymbolicCircuit
    (layout.borrowedWire (Fin.last b))
    (layout.controlWire (Fin.last (b + 2))) layout.targetWire
    (layout.controlWire_ne_borrowedWire _ _).symm
    (layout.borrowedWire_ne_targetWire _)
    (layout.controlWire_ne_targetWire _)

/-- Visible fusion erasure of the swapped forward orientation. -/
def swappedForwardOuterFusionCircuit {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) : FusionCircuit n :=
  selectedDoubleControlledExpansion16FusionCircuit
    (layout.borrowedWire (Fin.last b))
    (layout.controlWire (Fin.last (b + 2))) layout.targetWire
    (layout.controlWire_ne_borrowedWire _ _).symm
    (layout.borrowedWire_ne_targetWire _)
    (layout.controlWire_ne_targetWire _) pauliX

@[simp]
theorem erase_swappedForwardOuterSymbolicCircuit {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    SymbolicCircuit.erase corollary74FactorValuation
        layout.swappedForwardOuterSymbolicCircuit =
      layout.swappedForwardOuterFusionCircuit := by
  simp [swappedForwardOuterSymbolicCircuit,
    swappedForwardOuterFusionCircuit]

@[simp]
theorem eval_swappedForwardOuterFusionCircuit {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    layout.swappedForwardOuterFusionCircuit.eval =
      layout.outerToffoli.denotation := by
  rw [swappedForwardOuterFusionCircuit,
    eval_selectedDoubleControlledExpansion16FusionCircuit,
    twoControlSet_swap]
  rw [outerToffoli, Primitive.toffoli_denotation, twoControlSet]

private theorem outerToffoli_denotation_mul_self {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    layout.outerToffoli.denotation * layout.outerToffoli.denotation = 1 := by
  apply Subtype.ext
  rw [matrix_eq_iff_mulVec_basisKet_eq]
  intro input
  rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
    outerToffoli_denotation_mulVec_basisKet,
    outerToffoli_denotation_mulVec_basisKet,
    outerUpdate_involutive]
  simp

private theorem outerToffoli_denotation_inv {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    layout.outerToffoli.denotation⁻¹ = layout.outerToffoli.denotation := by
  let T := layout.outerToffoli.denotation
  have hsquare : T * T = 1 := outerToffoli_denotation_mul_self layout
  calc
    T⁻¹ = T⁻¹ * 1 := (mul_one T⁻¹).symm
    _ = T⁻¹ * (T * T) := by rw [hsquare]
    _ = (T⁻¹ * T) * T := by rw [mul_assoc]
    _ = T := by simp

/-- Literal adjoint of the standard-role exact outer symbolic expansion. -/
def standardAdjointOuterSymbolicCircuit {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    SymbolicCircuit Corollary74FactorAtom n :=
  exactToffoliAdjointSymbolicCircuit
    (layout.controlWire (Fin.last (b + 2)))
    (layout.borrowedWire (Fin.last b)) layout.targetWire
    (layout.controlWire_ne_borrowedWire _ _)
    (layout.controlWire_ne_targetWire _)
    (layout.borrowedWire_ne_targetWire _)

/-- Visible literal adjoint of the standard-role exact outer expansion. -/
def standardAdjointOuterFusionCircuit {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) : FusionCircuit n :=
  layout.expandedOuterFusionCircuit.adjoint

@[simp]
theorem erase_standardAdjointOuterSymbolicCircuit {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    SymbolicCircuit.erase corollary74FactorValuation
        layout.standardAdjointOuterSymbolicCircuit =
      layout.standardAdjointOuterFusionCircuit := by
  simp [standardAdjointOuterSymbolicCircuit,
    standardAdjointOuterFusionCircuit, expandedOuterFusionCircuit]

@[simp]
theorem eval_standardAdjointOuterFusionCircuit {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    layout.standardAdjointOuterFusionCircuit.eval =
      layout.outerToffoli.denotation := by
  rw [standardAdjointOuterFusionCircuit, FusionCircuit.eval_adjoint,
    eval_expandedOuterFusionCircuit, outerToffoli_denotation_inv]

/-- Mixed exact/relative B chronology `F_D; H; D_w; H`. -/
def mixedHybridInwardLadderSymbolicCircuit {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    SymbolicCircuit Corollary74FactorAtom n :=
  layout.swappedForwardOuterSymbolicCircuit ++
    relativeHalfLadderSymbolicCircuit b layout.smaller ++
      layout.standardAdjointOuterSymbolicCircuit ++
        relativeHalfLadderSymbolicCircuit b layout.smaller

/-- Visible erasure of the coherent mixed B chronology. -/
def mixedHybridInwardLadderFusionCircuit {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) : FusionCircuit n :=
  FusionCircuit.append layout.swappedForwardOuterFusionCircuit
    (FusionCircuit.append
      (relativeHalfLadderFusionCircuit b layout.smaller)
      (FusionCircuit.append layout.standardAdjointOuterFusionCircuit
        (relativeHalfLadderFusionCircuit b layout.smaller)))

@[simp]
theorem erase_mixedHybridInwardLadderSymbolicCircuit {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    SymbolicCircuit.erase corollary74FactorValuation
        layout.mixedHybridInwardLadderSymbolicCircuit =
      layout.mixedHybridInwardLadderFusionCircuit := by
  rw [mixedHybridInwardLadderSymbolicCircuit,
    mixedHybridInwardLadderFusionCircuit]
  repeat' rw [erase_append]
  rw [erase_swappedForwardOuterSymbolicCircuit,
    erase_relativeHalfLadderSymbolicCircuit,
    erase_standardAdjointOuterSymbolicCircuit]
  simp only [FusionCircuit.append, List.append_assoc]

@[simp]
theorem eval_mixedHybridInwardLadderFusionCircuit {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    layout.mixedHybridInwardLadderFusionCircuit.eval =
      Circuit.eval (hybridInwardLadderCircuit layout) := by
  simp [mixedHybridInwardLadderFusionCircuit, hybridInwardLadderCircuit,
    FusionCircuit.eval_append, Circuit.eval_append]

end InwardLadderLayout

namespace FourBlockLayout

/-! ## Complete coherent raw Corollary chronology -/

/-- Corrected `A;B;A†;B` chronology with the mixed exact B orientations. -/
def mixedExpandedRelativeCorollary74SymbolicCircuit
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2) :
    SymbolicCircuit Corollary74FactorAtom n :=
  let a := InwardLadderLayout.relativeInwardLadderSymbolicCircuit
    (layout.corollary74ALayout hleft)
  let b := InwardLadderLayout.mixedHybridInwardLadderSymbolicCircuit
    (layout.corollary74BLayout hright)
  a ++ b ++ a.adjoint ++ b

/-- Visible circuit obtained by valuing the complete coherent symbolic input. -/
def mixedExpandedRelativeCorollary74FusionCircuit
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2) : FusionCircuit n :=
  SymbolicCircuit.erase corollary74FactorValuation
    (layout.mixedExpandedRelativeCorollary74SymbolicCircuit hleft hright)

@[simp]
theorem eval_mixedExpandedRelativeCorollary74FusionCircuit_eq_relative
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2) :
    (layout.mixedExpandedRelativeCorollary74FusionCircuit hleft hright).eval =
      Circuit.eval (layout.relativeCorollary74Circuit hleft hright) := by
  rw [mixedExpandedRelativeCorollary74FusionCircuit,
    mixedExpandedRelativeCorollary74SymbolicCircuit]
  repeat' rw [erase_append]
  repeat' rw [FusionCircuit.eval_append]
  rw [InwardLadderLayout.erase_relativeInwardLadderSymbolicCircuit,
    InwardLadderLayout.erase_mixedHybridInwardLadderSymbolicCircuit,
    SymbolicCircuit.erase_adjoint,
    FusionCircuit.eval_adjoint,
    InwardLadderLayout.eval_relativeInwardLadderFusionCircuit,
    InwardLadderLayout.eval_mixedHybridInwardLadderFusionCircuit]
  simp [relativeCorollary74Circuit, relativeCorollary74AImplementation,
    hybridCorollary74BImplementation, Circuit.eval_append]
  simp only [mul_assoc]

@[simp]
theorem eval_mixedExpandedRelativeCorollary74FusionCircuit
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2)
    (htargetFree : leftTail ≤ rightTail + 1) :
    (layout.mixedExpandedRelativeCorollary74FusionCircuit hleft hright).eval =
      positiveControlledUnitary layout.targetWire layout.dataLayout.controlSet
        pauliX := by
  rw [eval_mixedExpandedRelativeCorollary74FusionCircuit_eq_relative]
  exact eval_relativeCorollary74Circuit layout hleft hright htargetFree

end FourBlockLayout

end

end Barenco.MultiControl
