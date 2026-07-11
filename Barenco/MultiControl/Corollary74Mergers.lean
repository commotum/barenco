import Barenco.MultiControl.Corollary74Fusion
import Barenco.Optimization.SymbolicAdjoint
import Barenco.Optimization.SymbolicAvoids
import Barenco.Optimization.SymbolicSweep

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

/-! ## Exact recursive merger for relative half ladders -/

/-- First endpoint of every relative-phase Toffoli occurrence. -/
def relativeToffoliStartSymbolic {n : ℕ} (target : Fin n) :
    SymbolicPrimitive Corollary74FactorAtom n :=
  SymbolicPrimitive.atom target .relative

/-- Five-node interior after removing both relative-Toffoli endpoints. -/
def relativeToffoliCoreSymbolicCircuit {n : ℕ}
    (first second target : Fin n)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    SymbolicCircuit Corollary74FactorAtom n :=
  [.cnot second target hsecondTarget,
    SymbolicPrimitive.atom target .relative,
    .cnot first target hfirstTarget,
    SymbolicPrimitive.inverseAtom target .relative,
    .cnot second target hsecondTarget]

/-- Last endpoint of every relative-phase Toffoli occurrence. -/
def relativeToffoliEndSymbolic {n : ℕ} (target : Fin n) :
    SymbolicPrimitive Corollary74FactorAtom n :=
  SymbolicPrimitive.inverseAtom target .relative

def relativeToffoliPrefixSymbolicCircuit {n : ℕ}
    (first second target : Fin n)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    SymbolicCircuit Corollary74FactorAtom n :=
  [relativeToffoliStartSymbolic target] ++
    relativeToffoliCoreSymbolicCircuit first second target
      hfirstTarget hsecondTarget

def relativeToffoliTailSymbolicCircuit {n : ℕ}
    (first second target : Fin n)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    SymbolicCircuit Corollary74FactorAtom n :=
  relativeToffoliCoreSymbolicCircuit first second target
      hfirstTarget hsecondTarget ++
    [relativeToffoliEndSymbolic target]

@[simp]
theorem relativeToffoliSymbolicCircuit_eq_prefix_end {n : ℕ}
    (first second target : Fin n)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    relativeToffoliSymbolicCircuit first second target
        hfirstTarget hsecondTarget =
      relativeToffoliPrefixSymbolicCircuit first second target
          hfirstTarget hsecondTarget ++
        [relativeToffoliEndSymbolic target] := by
  rfl

@[simp]
theorem relativeToffoliSymbolicCircuit_eq_start_tail {n : ℕ}
    (first second target : Fin n)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    relativeToffoliSymbolicCircuit first second target
        hfirstTarget hsecondTarget =
      [relativeToffoliStartSymbolic target] ++
        relativeToffoliTailSymbolicCircuit first second target
          hfirstTarget hsecondTarget := by
  rfl

def relativeBaseCoreSymbolicCircuit {n : ℕ}
    (layout : InwardLadderLayout 0 n) :
    SymbolicCircuit Corollary74FactorAtom n :=
  relativeToffoliCoreSymbolicCircuit
    (layout.controlWire 0) (layout.controlWire 1) layout.targetWire
    (layout.controlWire_ne_targetWire 0)
    (layout.controlWire_ne_targetWire 1)

def relativeOuterCoreSymbolicCircuit {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    SymbolicCircuit Corollary74FactorAtom n :=
  relativeToffoliCoreSymbolicCircuit
    (layout.controlWire (Fin.last (b + 2)))
    (layout.borrowedWire (Fin.last b)) layout.targetWire
    (layout.controlWire_ne_targetWire _)
    (layout.borrowedWire_ne_targetWire _)

def relativeOuterPrefixSymbolicCircuit {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    SymbolicCircuit Corollary74FactorAtom n :=
  [relativeToffoliStartSymbolic layout.targetWire] ++
    layout.relativeOuterCoreSymbolicCircuit

@[simp]
theorem relativeBaseSymbolicCircuit_eq_start_core_end {n : ℕ}
    (layout : InwardLadderLayout 0 n) :
    layout.relativeBaseSymbolicCircuit =
      [relativeToffoliStartSymbolic layout.targetWire] ++
        layout.relativeBaseCoreSymbolicCircuit ++
          [relativeToffoliEndSymbolic layout.targetWire] := by
  rfl

@[simp]
theorem relativeOuterSymbolicCircuit_eq_prefix_end {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    layout.relativeOuterSymbolicCircuit =
      layout.relativeOuterPrefixSymbolicCircuit ++
        [relativeToffoliEndSymbolic layout.targetWire] := by
  rfl

/--
Explicit normal form after cancelling the two outer endpoints across the entire
smaller half, whose gates avoid the outer target.
-/
def selectiveRelativeHalfNormalForm {n : ℕ} :
    (b : ℕ) → InwardLadderLayout b n →
      SymbolicCircuit Corollary74FactorAtom n
  | 0, layout => layout.relativeBaseSymbolicCircuit
  | b + 1, layout =>
      layout.relativeOuterPrefixSymbolicCircuit ++
        selectiveRelativeHalfNormalForm b layout.smaller ++
          relativeToffoliTailSymbolicCircuit
            (layout.controlWire (Fin.last (b + 2)))
            (layout.borrowedWire (Fin.last b)) layout.targetWire
            (layout.controlWire_ne_targetWire _)
            (layout.borrowedWire_ne_targetWire _)

/-- Actual executable `normalizeAtWire` pass at every recursive level. -/
def selectiveMergedRelativeHalfSymbolicCircuit {n : ℕ} :
    (b : ℕ) → InwardLadderLayout b n →
      SymbolicCircuit Corollary74FactorAtom n
  | 0, layout => layout.relativeBaseSymbolicCircuit
  | b + 1, layout =>
      layout.relativeOuterPrefixSymbolicCircuit ++
        SymbolicCircuit.normalizeAtWire layout.targetWire
          ([relativeToffoliEndSymbolic layout.targetWire] ++
            selectiveMergedRelativeHalfSymbolicCircuit b layout.smaller ++
              [relativeToffoliStartSymbolic layout.targetWire]) ++
        relativeToffoliTailSymbolicCircuit
          (layout.controlWire (Fin.last (b + 2)))
          (layout.borrowedWire (Fin.last b)) layout.targetWire
          (layout.controlWire_ne_targetWire _)
          (layout.borrowedWire_ne_targetWire _)

private theorem relativeToffoliSymbolicCircuit_all_avoids {n : ℕ}
    (wire first second target : Fin n)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target)
    (hwireFirst : wire ≠ first) (hwireSecond : wire ≠ second)
    (hwireTarget : wire ≠ target) :
    ∀ gate ∈ relativeToffoliSymbolicCircuit first second target
        hfirstTarget hsecondTarget,
      SymbolicPrimitive.AvoidsWire wire gate := by
  intro gate hgate
  simp only [relativeToffoliSymbolicCircuit, List.mem_cons,
    List.not_mem_nil, or_false] at hgate
  have htargetWire : target ≠ wire := hwireTarget.symm
  rcases hgate with hgate | hgate | hgate | hgate | hgate | hgate | hgate
  all_goals subst gate
  all_goals simp [SymbolicPrimitive.atom,
    SymbolicPrimitive.inverseAtom, SymbolicPrimitive.AvoidsWire,
    hwireFirst, hwireSecond, hwireTarget, htargetWire]

private theorem relativeOuterPrefix_all_avoids {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) (wire : Fin n)
    (hcontrol : ∀ control, wire ≠ layout.controlWire control)
    (hwork : ∀ work, wire ≠ layout.workWire work) :
    ∀ gate ∈ layout.relativeOuterPrefixSymbolicCircuit,
      SymbolicPrimitive.AvoidsWire wire gate := by
  intro gate hgate
  have hall := relativeToffoliSymbolicCircuit_all_avoids wire
    (layout.controlWire (Fin.last (b + 2)))
    (layout.borrowedWire (Fin.last b)) layout.targetWire
    (layout.controlWire_ne_targetWire _)
    (layout.borrowedWire_ne_targetWire _)
    (hcontrol _) (hwork _) (hwork _)
  apply hall gate
  simp [relativeOuterPrefixSymbolicCircuit,
    relativeOuterCoreSymbolicCircuit,
    relativeToffoliCoreSymbolicCircuit,
    relativeToffoliSymbolicCircuit,
    relativeToffoliStartSymbolic] at hgate ⊢
  tauto

private theorem relativeOuterTail_all_avoids {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) (wire : Fin n)
    (hcontrol : ∀ control, wire ≠ layout.controlWire control)
    (hwork : ∀ work, wire ≠ layout.workWire work) :
    ∀ gate ∈ relativeToffoliTailSymbolicCircuit
        (layout.controlWire (Fin.last (b + 2)))
        (layout.borrowedWire (Fin.last b)) layout.targetWire
        (layout.controlWire_ne_targetWire _)
        (layout.borrowedWire_ne_targetWire _),
      SymbolicPrimitive.AvoidsWire wire gate := by
  intro gate hgate
  have hall := relativeToffoliSymbolicCircuit_all_avoids wire
    (layout.controlWire (Fin.last (b + 2)))
    (layout.borrowedWire (Fin.last b)) layout.targetWire
    (layout.controlWire_ne_targetWire _)
    (layout.borrowedWire_ne_targetWire _)
    (hcontrol _) (hwork _) (hwork _)
  apply hall gate
  simp [relativeToffoliTailSymbolicCircuit,
    relativeToffoliCoreSymbolicCircuit,
    relativeToffoliSymbolicCircuit,
    relativeToffoliEndSymbolic] at hgate ⊢
  tauto

theorem selectiveRelativeHalfNormalForm_all_avoids {b n : ℕ}
    (layout : InwardLadderLayout b n) (wire : Fin n)
    (hcontrol : ∀ control, wire ≠ layout.controlWire control)
    (hwork : ∀ work, wire ≠ layout.workWire work) :
    ∀ gate ∈ selectiveRelativeHalfNormalForm b layout,
      SymbolicPrimitive.AvoidsWire wire gate := by
  induction b with
  | zero =>
      exact relativeToffoliSymbolicCircuit_all_avoids wire
        (layout.controlWire 0) (layout.controlWire 1) layout.targetWire
        (layout.controlWire_ne_targetWire 0)
        (layout.controlWire_ne_targetWire 1)
        (hcontrol 0) (hcontrol 1) (hwork (Fin.last 0))
  | succ b ih =>
      intro gate hgate
      simp only [selectiveRelativeHalfNormalForm, List.mem_append] at hgate
      rcases hgate with (hprefix | hsmaller) | htail
      · exact relativeOuterPrefix_all_avoids layout wire hcontrol hwork gate hprefix
      · have hcsmall : ∀ control,
            wire ≠ layout.smaller.controlWire control := by
          intro control
          simpa using hcontrol control.castSucc
        have hwsmall : ∀ work,
            wire ≠ layout.smaller.workWire work := by
          intro work
          simpa using hwork work.castSucc
        exact ih layout.smaller hcsmall hwsmall gate hsmaller
      · exact relativeOuterTail_all_avoids layout wire hcontrol hwork gate htail

theorem selectiveRelativeHalfNormalForm_smaller_avoids_target {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    ∀ gate ∈ selectiveRelativeHalfNormalForm b layout.smaller,
      SymbolicPrimitive.AvoidsWire layout.targetWire gate := by
  apply selectiveRelativeHalfNormalForm_all_avoids
  · exact layout.targetWire_ne_smaller_controlWire
  · exact layout.targetWire_ne_smaller_workWire

theorem selectiveRelativeHalfNormalForm_start {b n : ℕ}
    (layout : InwardLadderLayout b n) :
    ∃ tail, selectiveRelativeHalfNormalForm b layout =
      relativeToffoliStartSymbolic layout.targetWire :: tail := by
  cases b with
  | zero =>
      refine ⟨_, rfl⟩
  | succ b =>
      refine ⟨layout.relativeOuterCoreSymbolicCircuit ++
        selectiveRelativeHalfNormalForm b layout.smaller ++
        relativeToffoliTailSymbolicCircuit
          (layout.controlWire (Fin.last (b + 2)))
          (layout.borrowedWire (Fin.last b)) layout.targetWire
          (layout.controlWire_ne_targetWire _)
          (layout.borrowedWire_ne_targetWire _), ?_⟩
      simp [selectiveRelativeHalfNormalForm,
        relativeOuterPrefixSymbolicCircuit, List.append_assoc]

theorem selectiveRelativeHalfNormalForm_end {b n : ℕ}
    (layout : InwardLadderLayout b n) :
    ∃ initial, selectiveRelativeHalfNormalForm b layout =
      initial ++ [relativeToffoliEndSymbolic layout.targetWire] := by
  cases b with
  | zero =>
      refine ⟨[relativeToffoliStartSymbolic layout.targetWire] ++
        layout.relativeBaseCoreSymbolicCircuit, ?_⟩
      rfl
  | succ b =>
      refine ⟨layout.relativeOuterPrefixSymbolicCircuit ++
        selectiveRelativeHalfNormalForm b layout.smaller ++
        relativeToffoliCoreSymbolicCircuit
          (layout.controlWire (Fin.last (b + 2)))
          (layout.borrowedWire (Fin.last b)) layout.targetWire
          (layout.controlWire_ne_targetWire _)
          (layout.borrowedWire_ne_targetWire _), ?_⟩
      simp [selectiveRelativeHalfNormalForm,
        relativeToffoliTailSymbolicCircuit, List.append_assoc]

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

/-! ## Executable all-wire symbolic merger -/

/--
Run the certified ascending/descending target-directed sweep on the complete
coherent raw chronology.
-/
def mergedRelativeCorollary74SymbolicCircuit
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2) :
    SymbolicCircuit Corollary74FactorAtom n :=
  SymbolicCircuit.sweepBoth
    (layout.mixedExpandedRelativeCorollary74SymbolicCircuit hleft hright)

/-- Visible valued syntax emitted by the real symbolic sweep. -/
def mergedRelativeCorollary74FusionCircuit
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2) : FusionCircuit n :=
  SymbolicCircuit.erase corollary74FactorValuation
    (layout.mergedRelativeCorollary74SymbolicCircuit hleft hright)

/-- Trusted public circuit syntax emitted after valuation and lowering. -/
def mergedRelativeCorollary74Circuit
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2) : Circuit n :=
  (layout.mergedRelativeCorollary74FusionCircuit hleft hright).lower

/-- The executable symbolic merger preserves exact full-register evaluation. -/
@[simp]
theorem eval_mergedRelativeCorollary74FusionCircuit_eq_raw
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2) :
    (layout.mergedRelativeCorollary74FusionCircuit hleft hright).eval =
      (layout.mixedExpandedRelativeCorollary74FusionCircuit hleft hright).eval := by
  rw [mergedRelativeCorollary74FusionCircuit,
    mergedRelativeCorollary74SymbolicCircuit,
    SymbolicCircuit.eval_erase_sweepBoth]
  rfl

@[simp]
theorem eval_mergedRelativeCorollary74Circuit
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2)
    (htargetFree : leftTail ≤ rightTail + 1) :
    Circuit.eval (layout.mergedRelativeCorollary74Circuit hleft hright) =
      positiveControlledUnitary layout.targetWire layout.dataLayout.controlSet
        pauliX := by
  rw [mergedRelativeCorollary74Circuit, FusionCircuit.eval_lower,
    eval_mergedRelativeCorollary74FusionCircuit_eq_raw,
    eval_mixedExpandedRelativeCorollary74FusionCircuit
      layout hleft hright htargetFree]

/-- The complete ordered CNOT trace is unchanged by the merger. -/
@[simp]
theorem cnotTrace_mergedRelativeCorollary74SymbolicCircuit_eq_raw
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2) :
    SymbolicCircuit.cnotTrace
        (layout.mergedRelativeCorollary74SymbolicCircuit hleft hright) =
      SymbolicCircuit.cnotTrace
        (layout.mixedExpandedRelativeCorollary74SymbolicCircuit
          hleft hright) := by
  simp [mergedRelativeCorollary74SymbolicCircuit]

/-! ## Balanced source-width wrapper -/

def balancedMergedRelativeCorollary74Circuit (sourceWidth : ℕ)
    (hwidth : 7 ≤ sourceWidth) : Circuit sourceWidth :=
  (balancedLayout sourceWidth hwidth).mergedRelativeCorollary74Circuit
    (balancedLeftCapacity hwidth) (balancedRightCapacity hwidth)

@[simp]
theorem eval_balancedMergedRelativeCorollary74Circuit
    (sourceWidth : ℕ) (hwidth : 7 ≤ sourceWidth) :
    Circuit.eval (balancedMergedRelativeCorollary74Circuit sourceWidth hwidth) =
      positiveControlledUnitary
        (balancedLayout sourceWidth hwidth).targetWire
        (balancedLayout sourceWidth hwidth).dataLayout.controlSet pauliX := by
  apply eval_mergedRelativeCorollary74Circuit
  exact balancedLeftTail_le_right_add_one hwidth

end FourBlockLayout

end

end Barenco.MultiControl
