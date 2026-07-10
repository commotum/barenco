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

/-- The certified Y-rotation inverse carries the negated angle exactly. -/
private theorem ryUnitary_inv (theta : ℝ) :
    (ryUnitary theta)⁻¹ = ryUnitary (-theta) := by
  apply inv_eq_iff_mul_eq_one.mpr
  apply Subtype.ext
  change ry theta * ry (-theta) = (1 : QubitMatrix)
  rw [ry_mul]
  simpa using ry_zero

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
    SymbolicPrimitive.atom, SymbolicPrimitive.inverseAtom, ryUnitary_inv]

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
  | zero => simp [relativeHalfLadderSymbolicCircuit]
  | succ b ih =>
      simp [relativeHalfLadderSymbolicCircuit,
        relativeHalfLadderFusionCircuit, ih,
        SymbolicCircuit.erase, FusionCircuit.append]

@[simp]
theorem erase_relativeInwardLadderSymbolicCircuit {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    SymbolicCircuit.erase corollary74FactorValuation
        layout.relativeInwardLadderSymbolicCircuit =
      layout.relativeInwardLadderFusionCircuit := by
  simp [relativeInwardLadderSymbolicCircuit,
    relativeInwardLadderFusionCircuit, SymbolicCircuit.erase,
    FusionCircuit.append]

end InwardLadderLayout

end

end Barenco.MultiControl
