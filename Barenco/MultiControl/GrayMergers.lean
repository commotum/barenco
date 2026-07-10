import Barenco.MultiControl.GrayFusion
import Barenco.Optimization.SymbolicExpose

/-!
# Coherent exact mergers for the general Gray construction

The raw Gray expansion in `GrayFusion` independently chooses factors for every
signed root.  This file instead chooses one `phase/A/B/C` package for `V`, uses a
boundary-oriented positive controlled-`V` block, and represents every negative
block by the literal formal adjoint of that same package.  Free-group provenance
therefore records the inverse endpoint pair at each Gray boundary.

The positive block is

`A(target); phase(control); CNOT; B(target); CNOT; C(target)`.

Its negative block is the literal reverse inverse

`C⁻¹(target); CNOT; B⁻¹(target); CNOT; phase⁻¹(control); A⁻¹(target)`.

The initial `A/phase` swap is exact because those gates act on distinct wires.
Consecutive Gray masks have opposite cardinality parity, so consecutive blocks
have opposite signs.  Target-directed symbolic exposure and cancellation are
used below without matrix equality tests or phase relaxation.
-/

namespace Barenco.MultiControl

open Barenco.OneQubit
open Barenco.ControlledCircuit
open Barenco.Optimization
open scoped symmDiff

noncomputable section

/-! ## Gray-cardinality sign lemmas -/

/-- Adjacent Gray masks differ by inserting or deleting exactly one member. -/
theorem GrayAdjacent.card_succ_or_succ_card {width : ℕ}
    {first second : GrayMask width} (h : GrayAdjacent first second) :
    second.card + 1 = first.card ∨ first.card + 1 = second.card := by
  obtain ⟨changed, hchange⟩ := h.exists_unique_changed
  have hchanged : changed ∈ (first ∆ second) := by
    rw [hchange]
    simp
  rw [Finset.mem_symmDiff] at hchanged
  rcases hchanged with hremove | hadd
  · left
    have hsecond : second = first.erase changed := by
      ext wire
      by_cases hwire : wire = changed
      · subst wire
        simp [hremove.2]
      · have hnotdiff : wire ∉ (first ∆ second) := by
          rw [hchange]
          simpa using hwire
        rw [Finset.mem_symmDiff] at hnotdiff
        simp only [Finset.mem_erase]
        tauto
    rw [hsecond]
    exact Finset.card_erase_add_one hremove.1
  · right
    have hsecond : second = insert changed first := by
      ext wire
      by_cases hwire : wire = changed
      · subst wire
        simp [hadd.1]
      · have hnotdiff : wire ∉ (first ∆ second) := by
          rw [hchange]
          simpa using hwire
        rw [Finset.mem_symmDiff] at hnotdiff
        simp only [Finset.mem_insert, hwire, false_or]
        tauto
    rw [hsecond, Finset.card_insert_of_notMem hadd.2]

/-- Gray adjacency flips cardinality parity. -/
theorem GrayAdjacent.odd_card_iff_even_card {width : ℕ}
    {first second : GrayMask width} (h : GrayAdjacent first second) :
    Odd first.card ↔ Even second.card := by
  rw [Nat.odd_iff, Nat.even_iff]
  rcases h.card_succ_or_succ_card with hcard | hcard <;> omega

/-- Symmetrically, an even mask is followed by an odd mask. -/
theorem GrayAdjacent.even_card_iff_odd_card {width : ℕ}
    {first second : GrayMask width} (h : GrayAdjacent first second) :
    Even first.card ↔ Odd second.card := by
  rw [Nat.even_iff, Nat.odd_iff]
  rcases h.card_succ_or_succ_card with hcard | hcard <;> omega

/-- Odd-cardinality masks use the positive selected root. -/
theorem signedGrayRoot_eq_of_odd {width : ℕ} (mask : GrayMask width)
    (V : QubitUnitary) (hodd : Odd mask.card) :
    signedGrayRoot mask V = V := by
  have hevenPred : Even (mask.card - 1) := by
    rw [Nat.odd_iff] at hodd
    rw [Nat.even_iff]
    omega
  rw [signedGrayRoot, hevenPred.neg_one_pow]
  exact zpow_one V

/-- Every nonempty even-cardinality mask uses the inverse selected root. -/
theorem signedGrayRoot_eq_inv_of_even {width : ℕ} (mask : GrayMask width)
    (V : QubitUnitary) (hne : mask.Nonempty) (heven : Even mask.card) :
    signedGrayRoot mask V = V⁻¹ := by
  have hoddPred : Odd (mask.card - 1) := by
    rw [Nat.even_iff] at heven
    rw [Nat.odd_iff]
    have hpos : 0 < mask.card := Finset.card_pos.mpr hne
    omega
  rw [signedGrayRoot, hoddPred.neg_one_pow]
  exact zpow_neg_one V

/-! ## One factor choice and symbolic inverse provenance -/

/-- Decidable provenance atoms for the one selected controlled-`V` package. -/
inductive GrayFactorAtom where
  | phase
  | A
  | B
  | C
  deriving DecidableEq

/-- Interpret every atom using one selected factor package for `V`. -/
def grayFactorValuation (V : QubitUnitary) : GrayFactorAtom → QubitUnitary :=
  let factors := selectedColumnABCFactors (specialUnitaryPart V)
  fun atom ↦ match atom with
    | .phase => controlPhaseUnitary (determinantPhaseAngle V)
    | .A => specialUnitaryAsUnitary factors.A
    | .B => specialUnitaryAsUnitary factors.B
    | .C => specialUnitaryAsUnitary factors.C

/--
Boundary-oriented positive controlled-`V` syntax.  Moving `A` before the control
phase exposes one inverse target pair at both signs of a later Gray boundary.
-/
def grayPositiveRootFusionCircuit {n : ℕ} (control target : Fin n)
    (h : control ≠ target) (V : QubitUnitary) : FusionCircuit n :=
  let factors := selectedColumnABCFactors (specialUnitaryPart V)
  [.oneQubit target (specialUnitaryAsUnitary factors.A),
    .oneQubit control (controlPhaseUnitary (determinantPhaseAngle V)),
    .cnot control target h,
    .oneQubit target (specialUnitaryAsUnitary factors.B),
    .cnot control target h,
    .oneQubit target (specialUnitaryAsUnitary factors.C)]

/-- Symbolic form of the same boundary-oriented positive block. -/
def grayPositiveRootSymbolicCircuit {n : ℕ} (control target : Fin n)
    (h : control ≠ target) : SymbolicCircuit GrayFactorAtom n :=
  [SymbolicPrimitive.atom target .A,
    SymbolicPrimitive.atom control .phase,
    .cnot control target h,
    SymbolicPrimitive.atom target .B,
    .cnot control target h,
    SymbolicPrimitive.atom target .C]

/-- Literal reverse/inverse symbolic block; no factors for `V⁻¹` are reselected. -/
def grayNegativeRootSymbolicCircuit {n : ℕ} (control target : Fin n)
    (h : control ≠ target) : SymbolicCircuit GrayFactorAtom n :=
  [SymbolicPrimitive.inverseAtom target .C,
    .cnot control target h,
    SymbolicPrimitive.inverseAtom target .B,
    .cnot control target h,
    SymbolicPrimitive.inverseAtom control .phase,
    SymbolicPrimitive.inverseAtom target .A]

/-- Odd masks use the positive block and even masks its literal formal adjoint. -/
def coherentGrayRootSymbolicCircuit {width n : ℕ} (mask : GrayMask width)
    (control target : Fin n) (h : control ≠ target) :
    SymbolicCircuit GrayFactorAtom n :=
  if Odd mask.card then
    grayPositiveRootSymbolicCircuit control target h
  else
    grayNegativeRootSymbolicCircuit control target h

/-- First target endpoint of one coherent signed block. -/
def grayRootStartSymbolic {width n : ℕ} (mask : GrayMask width)
    (target : Fin n) : SymbolicPrimitive GrayFactorAtom n :=
  if Odd mask.card then
    SymbolicPrimitive.atom target .A
  else
    SymbolicPrimitive.inverseAtom target .C

/-- Four-node middle of a coherent signed block after removing both endpoints. -/
def grayRootCoreSymbolicCircuit {width n : ℕ} (mask : GrayMask width)
    (control target : Fin n) (h : control ≠ target) :
    SymbolicCircuit GrayFactorAtom n :=
  if Odd mask.card then
    [SymbolicPrimitive.atom control .phase,
      .cnot control target h,
      SymbolicPrimitive.atom target .B,
      .cnot control target h]
  else
    [.cnot control target h,
      SymbolicPrimitive.inverseAtom target .B,
      .cnot control target h,
      SymbolicPrimitive.inverseAtom control .phase]

/-- Final target endpoint of one coherent signed block. -/
def grayRootEndSymbolic {width n : ℕ} (mask : GrayMask width)
    (target : Fin n) : SymbolicPrimitive GrayFactorAtom n :=
  if Odd mask.card then
    SymbolicPrimitive.atom target .C
  else
    SymbolicPrimitive.inverseAtom target .A

/-- Every coherent block is its start endpoint, four-node core, and end endpoint. -/
theorem coherentGrayRootSymbolicCircuit_eq_start_core_end {width n : ℕ}
    (mask : GrayMask width) (control target : Fin n)
    (h : control ≠ target) :
    coherentGrayRootSymbolicCircuit mask control target h =
      [grayRootStartSymbolic mask target] ++
        grayRootCoreSymbolicCircuit mask control target h ++
          [grayRootEndSymbolic mask target] := by
  rcases Nat.even_or_odd mask.card with heven | hodd
  · have hnotOdd : ¬Odd mask.card := Nat.not_odd_iff_even.mpr heven
    simp [coherentGrayRootSymbolicCircuit, grayRootStartSymbolic,
      grayRootCoreSymbolicCircuit, grayRootEndSymbolic, hnotOdd,
      grayNegativeRootSymbolicCircuit, SymbolicPrimitive.inverseAtom]
  · simp [coherentGrayRootSymbolicCircuit, grayRootStartSymbolic,
      grayRootCoreSymbolicCircuit, grayRootEndSymbolic, hodd,
      grayPositiveRootSymbolicCircuit, SymbolicPrimitive.atom]

/--
At one Gray boundary, target exposure and free-group normalization commute the
outgoing endpoint across the control-only CNOT and delete the inverse pair.
-/
theorem normalizeAtWire_grayBoundary {width n : ℕ}
    {first second : GrayMask width} (hadjacent : GrayAdjacent first second)
    (edgeControl edgeTarget target : Fin n)
    (hedge : edgeControl ≠ edgeTarget)
    (htargetControl : target ≠ edgeControl)
    (htargetTarget : target ≠ edgeTarget) :
    SymbolicCircuit.normalizeAtWire target
        [grayRootEndSymbolic first target,
          .cnot edgeControl edgeTarget hedge,
          grayRootStartSymbolic second target] =
      [.cnot edgeControl edgeTarget hedge] := by
  rcases Nat.even_or_odd first.card with heven | hodd
  · have hsecondOdd : Odd second.card :=
      hadjacent.even_card_iff_odd_card.mp heven
    have hfirstNotOdd : ¬Odd first.card :=
      Nat.not_odd_iff_even.mpr heven
    simp [SymbolicCircuit.normalizeAtWire, SymbolicCircuit.exposeWire,
      SymbolicCircuit.exposeWireInsert, SymbolicCircuit.normalize,
      NormalizeCore.normalize, NormalizeCore.insert,
      SymbolicPrimitive.isIdentity, SymbolicPrimitive.combine,
      grayRootEndSymbolic, grayRootStartSymbolic, hfirstNotOdd,
      hsecondOdd, htargetControl, htargetTarget,
      SymbolicPrimitive.atom, SymbolicPrimitive.inverseAtom]
  · have hsecondEven : Even second.card :=
      hadjacent.odd_card_iff_even_card.mp hodd
    have hsecondNotOdd : ¬Odd second.card :=
      Nat.not_odd_iff_even.mpr hsecondEven
    simp [SymbolicCircuit.normalizeAtWire, SymbolicCircuit.exposeWire,
      SymbolicCircuit.exposeWireInsert, SymbolicCircuit.normalize,
      NormalizeCore.normalize, NormalizeCore.insert,
      SymbolicPrimitive.isIdentity, SymbolicPrimitive.combine,
      grayRootEndSymbolic, grayRootStartSymbolic, hodd, hsecondNotOdd,
      htargetControl, htargetTarget,
      SymbolicPrimitive.atom, SymbolicPrimitive.inverseAtom]

@[simp]
theorem erase_grayPositiveRootSymbolicCircuit {n : ℕ}
    (control target : Fin n) (h : control ≠ target) (V : QubitUnitary) :
    SymbolicCircuit.erase (grayFactorValuation V)
        (grayPositiveRootSymbolicCircuit control target h) =
      grayPositiveRootFusionCircuit control target h V := by
  simp [grayPositiveRootSymbolicCircuit, grayPositiveRootFusionCircuit,
    grayFactorValuation, SymbolicPrimitive.atom]

@[simp]
theorem erase_grayNegativeRootSymbolicCircuit {n : ℕ}
    (control target : Fin n) (h : control ≠ target) (V : QubitUnitary) :
    SymbolicCircuit.erase (grayFactorValuation V)
        (grayNegativeRootSymbolicCircuit control target h) =
      (grayPositiveRootFusionCircuit control target h V).adjoint := by
  simp [grayNegativeRootSymbolicCircuit, grayPositiveRootFusionCircuit,
    grayFactorValuation, SymbolicPrimitive.inverseAtom,
    FusionCircuit.adjoint, FusionPrimitive.adjoint]

/-- The initial distinct-wire swap preserves the canonical selected evaluator. -/
theorem eval_grayPositiveRootFusionCircuit {n : ℕ}
    (control target : Fin n) (h : control ≠ target) (V : QubitUnitary) :
    FusionCircuit.eval (grayPositiveRootFusionCircuit control target h V) =
      positiveControlledUnitary target
        ({⟨control, h⟩} : ControlSet target) V := by
  let factors := selectedColumnABCFactors (specialUnitaryPart V)
  have hcommute := oneQubit_denotationsCommute_of_ne
    control target h
    (controlPhaseUnitary (determinantPhaseAngle V))
    (specialUnitaryAsUnitary factors.A)
  have hswap := eval_swap_head
    (.oneQubit control (controlPhaseUnitary (determinantPhaseAngle V)))
    (.oneQubit target (specialUnitaryAsUnitary factors.A))
    ([.cnot control target h,
      .oneQubit target (specialUnitaryAsUnitary factors.B),
      .cnot control target h,
      .oneQubit target (specialUnitaryAsUnitary factors.C)] : FusionCircuit n)
    hcommute
  calc
    FusionCircuit.eval (grayPositiveRootFusionCircuit control target h V) =
        FusionCircuit.eval
          (canonicalSelectedControlledU2FusionCircuit control target h V) := by
      simpa [grayPositiveRootFusionCircuit,
        canonicalSelectedControlledU2FusionCircuit, factors] using hswap.symm
    _ = positiveControlledUnitary target
          ({⟨control, h⟩} : ControlSet target) V :=
      eval_canonicalSelectedControlledU2FusionCircuit control target h V

private theorem singletonPositiveControlled_one {n : ℕ}
    (control target : Fin n) (h : control ≠ target) :
    positiveControlledUnitary target
      ({⟨control, h⟩} : ControlSet target) (1 : QubitUnitary) = 1 := by
  apply Subtype.ext
  rw [coe_positiveControlledUnitary,
    positiveControlledRaw_singleton_eq_targetBlockRaw]
  simp

/-- Inversion passes through one positive control exactly. -/
theorem singletonPositiveControlled_inv {n : ℕ}
    (control target : Fin n) (h : control ≠ target) (V : QubitUnitary) :
    (positiveControlledUnitary target
      ({⟨control, h⟩} : ControlSet target) V)⁻¹ =
      positiveControlledUnitary target
        ({⟨control, h⟩} : ControlSet target) V⁻¹ := by
  apply inv_eq_iff_mul_eq_one.mpr
  rw [singleControlledUnitary_mul, mul_inv_cancel,
    singletonPositiveControlled_one]

/-- Exact evaluator of the literal negative adjoint block. -/
theorem eval_erase_grayNegativeRootSymbolicCircuit {n : ℕ}
    (control target : Fin n) (h : control ≠ target) (V : QubitUnitary) :
    FusionCircuit.eval
        (SymbolicCircuit.erase (grayFactorValuation V)
          (grayNegativeRootSymbolicCircuit control target h)) =
      positiveControlledUnitary target
        ({⟨control, h⟩} : ControlSet target) V⁻¹ := by
  rw [erase_grayNegativeRootSymbolicCircuit, FusionCircuit.eval_adjoint,
    eval_grayPositiveRootFusionCircuit, singletonPositiveControlled_inv]

/-- Each coherent signed block has exactly the paper's signed-root semantics. -/
theorem eval_erase_coherentGrayRootSymbolicCircuit {width n : ℕ}
    (mask : GrayMask width) (hne : mask.Nonempty)
    (control target : Fin n) (h : control ≠ target) (V : QubitUnitary) :
    FusionCircuit.eval
        (SymbolicCircuit.erase (grayFactorValuation V)
          (coherentGrayRootSymbolicCircuit mask control target h)) =
      positiveControlledUnitary target
        ({⟨control, h⟩} : ControlSet target) (signedGrayRoot mask V) := by
  rcases Nat.even_or_odd mask.card with heven | hodd
  · have hnotOdd : ¬Odd mask.card := Nat.not_odd_iff_even.mpr heven
    rw [coherentGrayRootSymbolicCircuit, if_neg hnotOdd,
      eval_erase_grayNegativeRootSymbolicCircuit,
      signedGrayRoot_eq_inv_of_even mask V hne heven]
  · rw [coherentGrayRootSymbolicCircuit, if_pos hodd,
      erase_grayPositiveRootSymbolicCircuit,
      eval_grayPositiveRootFusionCircuit,
      signedGrayRoot_eq_of_odd mask V hodd]

/-! ## Complete coherent Gray schedule -/

namespace OrderedControlLayout

private theorem erase_append (valuation : GrayFactorAtom → QubitUnitary)
    {n : ℕ} (first second : SymbolicCircuit GrayFactorAtom n) :
    SymbolicCircuit.erase valuation (first ++ second) =
      FusionCircuit.append (SymbolicCircuit.erase valuation first)
        (SymbolicCircuit.erase valuation second) := by
  simp [SymbolicCircuit.erase, FusionCircuit.append]

private theorem coherentGrayPivot_index_lt_of_mask {controlCount index : ℕ}
    (hindex : index < (grayCode controlCount).length) :
    index < (grayPivots controlCount).length := by
  rw [length_grayPivots_eq_grayCode]
  exact hindex

private theorem coherentGrayMask_index_lt_of_edge {controlCount index : ℕ}
    (hindex : index < (grayCNOTEdges controlCount).length) :
    index < (grayCode controlCount).length := by
  rw [length_grayCNOTEdges] at hindex
  rw [length_grayCode]
  omega

private theorem coherentGrayNextMask_index_lt_of_edge {controlCount index : ℕ}
    (hindex : index < (grayCNOTEdges controlCount).length) :
    index + 1 < (grayCode controlCount).length := by
  rw [length_grayCNOTEdges] at hindex
  rw [length_grayCode]
  omega

private theorem coherentGrayMask_index_lt_of_prefix {controlCount count : ℕ}
    (hpositive : 0 < controlCount)
    (hcount : count ≤ (grayCNOTEdges controlCount).length) :
    count < (grayCode controlCount).length := by
  rw [length_grayCNOTEdges] at hcount
  rw [length_grayCode]
  cases controlCount with
  | zero => omega
  | succ width =>
      simp only [pow_succ]
      have hpow : 0 < 2 ^ width := pow_pos (by omega) width
      omega

private theorem coherentGrayInitialMask_index_lt (tail : ℕ) :
    0 < (grayCode (tail + 1)).length := by
  rw [length_grayCode]
  simp only [pow_succ]
  have hpow : 0 < 2 ^ tail := pow_pos (by omega) tail
  omega

private theorem coherentGrayFinalMask_index_lt (tail : ℕ) :
    (grayCNOTEdges (tail + 1)).length <
      (grayCode (tail + 1)).length := by
  rw [length_grayCNOTEdges, length_grayCode]
  have hpow : 0 < 2 ^ (tail + 1) := pow_pos (by omega) _
  omega

/-- One indexed coherent signed-root block. -/
def coherentGrayRootCircuitAt {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (_V : QubitUnitary) (index : ℕ)
    (hindex : index < (grayCode controlCount).length) :
    SymbolicCircuit GrayFactorAtom ambientWidth :=
  let mask := (grayCode controlCount)[index]'hindex
  let pivot := (grayPivots controlCount)[index]'
    (coherentGrayPivot_index_lt_of_mask hindex)
  coherentGrayRootSymbolicCircuit mask (layout.controlWire pivot)
    layout.targetWire (layout.control_ne_target pivot)

/-- Initial target endpoint of one indexed coherent root block. -/
def coherentGrayRootStartAt {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (index : ℕ) (hindex : index < (grayCode controlCount).length) :
    SymbolicPrimitive GrayFactorAtom ambientWidth :=
  grayRootStartSymbolic ((grayCode controlCount)[index]'hindex)
    layout.targetWire

/-- Four-node middle of one indexed coherent root block. -/
def coherentGrayRootCoreAt {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (index : ℕ) (hindex : index < (grayCode controlCount).length) :
    SymbolicCircuit GrayFactorAtom ambientWidth :=
  let mask := (grayCode controlCount)[index]'hindex
  let pivot := (grayPivots controlCount)[index]'
    (coherentGrayPivot_index_lt_of_mask hindex)
  grayRootCoreSymbolicCircuit mask (layout.controlWire pivot)
    layout.targetWire (layout.control_ne_target pivot)

/-- Final target endpoint of one indexed coherent root block. -/
def coherentGrayRootEndAt {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (index : ℕ) (hindex : index < (grayCode controlCount).length) :
    SymbolicPrimitive GrayFactorAtom ambientWidth :=
  grayRootEndSymbolic ((grayCode controlCount)[index]'hindex)
    layout.targetWire

/-- Indexed coherent roots decompose into their explicit endpoints and core. -/
theorem coherentGrayRootCircuitAt_eq_start_core_end
    {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (V : QubitUnitary) (index : ℕ)
    (hindex : index < (grayCode controlCount).length) :
    coherentGrayRootCircuitAt layout V index hindex =
      [coherentGrayRootStartAt layout index hindex] ++
        coherentGrayRootCoreAt layout index hindex ++
          [coherentGrayRootEndAt layout index hindex] := by
  simpa [coherentGrayRootCircuitAt, coherentGrayRootStartAt,
    coherentGrayRootCoreAt, coherentGrayRootEndAt] using
      coherentGrayRootSymbolicCircuit_eq_start_core_end
        ((grayCode controlCount)[index]'hindex)
        (layout.controlWire
          ((grayPivots controlCount)[index]'
            (coherentGrayPivot_index_lt_of_mask hindex)))
        layout.targetWire
        (layout.control_ne_target
          ((grayPivots controlCount)[index]'
            (coherentGrayPivot_index_lt_of_mask hindex)))

/-! ## Executable normalization at every Gray boundary -/

/-- The literal outgoing-endpoint/Gray-CNOT/incoming-endpoint boundary. -/
def coherentGrayBoundaryAt {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (index : ℕ) (hindex : index < (grayCNOTEdges controlCount).length) :
    SymbolicCircuit GrayFactorAtom ambientWidth :=
  let edge := (grayCNOTEdges controlCount)[index]'hindex
  [coherentGrayRootEndAt layout index
      (coherentGrayMask_index_lt_of_edge hindex),
    .cnot (layout.controlWire edge.1) (layout.controlWire edge.2)
      (layout.controlWire_ne (grayCNOTEdges_getElem_ne hindex)),
    coherentGrayRootStartAt layout (index + 1)
      (coherentGrayNextMask_index_lt_of_edge hindex)]

/-- Actual target-exposure/free-group normalization of one generated boundary. -/
def coherentGrayNormalizedBoundaryAt {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (index : ℕ) (hindex : index < (grayCNOTEdges controlCount).length) :
    SymbolicCircuit GrayFactorAtom ambientWidth :=
  SymbolicCircuit.normalizeAtWire layout.targetWire
    (coherentGrayBoundaryAt layout index hindex)

/-- Every generated boundary normalizes to its unchanged literal Gray CNOT. -/
@[simp]
theorem coherentGrayNormalizedBoundaryAt_eq_singleton
    {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (index : ℕ) (hindex : index < (grayCNOTEdges controlCount).length) :
    coherentGrayNormalizedBoundaryAt layout index hindex =
      let edge := (grayCNOTEdges controlCount)[index]'hindex
      [.cnot (layout.controlWire edge.1) (layout.controlWire edge.2)
        (layout.controlWire_ne (grayCNOTEdges_getElem_ne hindex))] := by
  have hadjacent :
      GrayAdjacent
        ((grayCode controlCount)[index]'
          (coherentGrayMask_index_lt_of_edge hindex))
        ((grayCode controlCount)[index + 1]'
          (coherentGrayNextMask_index_lt_of_edge hindex)) :=
    (grayCode_isChain controlCount).getElem index
      (coherentGrayNextMask_index_lt_of_edge hindex)
  let edge := (grayCNOTEdges controlCount)[index]'hindex
  simpa [coherentGrayNormalizedBoundaryAt, coherentGrayBoundaryAt,
    coherentGrayRootEndAt, coherentGrayRootStartAt, edge] using
    normalizeAtWire_grayBoundary hadjacent
      (layout.controlWire edge.1) (layout.controlWire edge.2)
      layout.targetWire
      (layout.controlWire_ne (grayCNOTEdges_getElem_ne hindex))
      (layout.control_ne_target edge.1).symm
      (layout.control_ne_target edge.2).symm

/-- One unmerged core followed by its literal boundary triple. -/
def coherentGrayUnmergedBoundarySegment {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (index : ℕ) (hindex : index < (grayCNOTEdges controlCount).length) :
    SymbolicCircuit GrayFactorAtom ambientWidth :=
  coherentGrayRootCoreAt layout index
      (coherentGrayMask_index_lt_of_edge hindex) ++
    coherentGrayBoundaryAt layout index hindex

/-- One core followed by the executable normalized form of its boundary. -/
def coherentGrayMergedBoundarySegment {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (index : ℕ) (hindex : index < (grayCNOTEdges controlCount).length) :
    SymbolicCircuit GrayFactorAtom ambientWidth :=
  coherentGrayRootCoreAt layout index
      (coherentGrayMask_index_lt_of_edge hindex) ++
    coherentGrayNormalizedBoundaryAt layout index hindex

/-- First `count` unmerged core/boundary segments. -/
def coherentGrayUnmergedBoundaryPrefixCircuit
    {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth) :
    (count : ℕ) → count ≤ (grayCNOTEdges controlCount).length →
      SymbolicCircuit GrayFactorAtom ambientWidth
  | 0, _ => []
  | count + 1, hcount =>
      coherentGrayUnmergedBoundaryPrefixCircuit layout count (by omega) ++
        coherentGrayUnmergedBoundarySegment layout count (by omega)

/--
Streaming merger over the first `count` Gray boundaries.  Every step invokes
the actual target-exposure/free-group normalizer on that boundary triple.
-/
def coherentGrayMergedBoundaryPrefixCircuit
    {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth) :
    (count : ℕ) → count ≤ (grayCNOTEdges controlCount).length →
      SymbolicCircuit GrayFactorAtom ambientWidth
  | 0, _ => []
  | count + 1, hcount =>
      coherentGrayMergedBoundaryPrefixCircuit layout count (by omega) ++
        coherentGrayMergedBoundarySegment layout count (by omega)

/-- Literal regrouping of the coherent raw schedule around all boundaries. -/
def coherentGrayRegroupedViaRootCircuit {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth) :
    SymbolicCircuit GrayFactorAtom ambientWidth :=
  let edgeCount := (grayCNOTEdges (tail + 1)).length
  [coherentGrayRootStartAt layout 0 (coherentGrayInitialMask_index_lt tail)] ++
    coherentGrayUnmergedBoundaryPrefixCircuit layout edgeCount le_rfl ++
      coherentGrayRootCoreAt layout edgeCount
          (coherentGrayFinalMask_index_lt tail) ++
        [coherentGrayRootEndAt layout edgeCount
          (coherentGrayFinalMask_index_lt tail)]

/--
The general post-merger Gray syntax.  It is built by applying the executable
normalizer independently at every certified Gray boundary, then concatenating
the untouched root cores and the two outer endpoints.
-/
def mergedGrayControlledViaRootSymbolicCircuit {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth) :
    SymbolicCircuit GrayFactorAtom ambientWidth :=
  let edgeCount := (grayCNOTEdges (tail + 1)).length
  [coherentGrayRootStartAt layout 0 (coherentGrayInitialMask_index_lt tail)] ++
    coherentGrayMergedBoundaryPrefixCircuit layout edgeCount le_rfl ++
      coherentGrayRootCoreAt layout edgeCount
          (coherentGrayFinalMask_index_lt tail) ++
        [coherentGrayRootEndAt layout edgeCount
          (coherentGrayFinalMask_index_lt tail)]

/-- Explicit emitted normal form of one merged core/boundary segment. -/
def coherentGrayMergedBoundaryNormalForm
    {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (index : ℕ) (hindex : index < (grayCNOTEdges controlCount).length) :
    SymbolicCircuit GrayFactorAtom ambientWidth :=
  let edge := (grayCNOTEdges controlCount)[index]'hindex
  coherentGrayRootCoreAt layout index
      (coherentGrayMask_index_lt_of_edge hindex) ++
    [.cnot (layout.controlWire edge.1) (layout.controlWire edge.2)
      (layout.controlWire_ne (grayCNOTEdges_getElem_ne hindex))]

/-- First `count` explicit emitted core/CNOT normal-form segments. -/
def coherentGrayMergedBoundaryNormalFormPrefixCircuit
    {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth) :
    (count : ℕ) → count ≤ (grayCNOTEdges controlCount).length →
      SymbolicCircuit GrayFactorAtom ambientWidth
  | 0, _ => []
  | count + 1, hcount =>
      coherentGrayMergedBoundaryNormalFormPrefixCircuit layout count (by omega) ++
        coherentGrayMergedBoundaryNormalForm layout count (by omega)

/--
The explicit normal form emitted by all boundary normalizations: two outer
target endpoints, every four-node root core, and every unchanged Gray CNOT.
-/
def mergedGrayControlledViaRootNormalForm {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth) :
    SymbolicCircuit GrayFactorAtom ambientWidth :=
  let edgeCount := (grayCNOTEdges (tail + 1)).length
  [coherentGrayRootStartAt layout 0 (coherentGrayInitialMask_index_lt tail)] ++
    coherentGrayMergedBoundaryNormalFormPrefixCircuit layout edgeCount le_rfl ++
      coherentGrayRootCoreAt layout edgeCount
          (coherentGrayFinalMask_index_lt tail) ++
        [coherentGrayRootEndAt layout edgeCount
          (coherentGrayFinalMask_index_lt tail)]

/-- Payload-visible erased form of the general merged root schedule. -/
def mergedGrayControlledViaRootFusionCircuit {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth)
    (V : QubitUnitary) : FusionCircuit ambientWidth :=
  SymbolicCircuit.erase (grayFactorValuation V)
    (mergedGrayControlledViaRootSymbolicCircuit layout)

/-- Trusted public circuit syntax for the general merged root schedule. -/
def mergedGrayControlledViaRootCircuit {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth)
    (V : QubitUnitary) : Circuit ambientWidth :=
  (mergedGrayControlledViaRootFusionCircuit layout V).lower

/-- Payload-visible selected-root circuit for an arbitrary controlled `U`. -/
def mergedGrayControlledFusionCircuit {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth)
    (U : QubitUnitary) : FusionCircuit ambientWidth :=
  mergedGrayControlledViaRootFusionCircuit layout (graySelectedRoot tail U)

/-- Trusted selected-root circuit for an arbitrary fully controlled `U`. -/
def mergedGrayControlledCircuit {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth)
    (U : QubitUnitary) : Circuit ambientWidth :=
  (mergedGrayControlledFusionCircuit layout U).lower

/-- One coherent signed root followed by its generated Gray CNOT. -/
def coherentGrayTransitionPair {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (V : QubitUnitary) (index : ℕ)
    (hindex : index < (grayCNOTEdges controlCount).length) :
    SymbolicCircuit GrayFactorAtom ambientWidth :=
  let edge := (grayCNOTEdges controlCount)[index]'hindex
  coherentGrayRootCircuitAt layout V index
      (coherentGrayMask_index_lt_of_edge hindex) ++
    [.cnot (layout.controlWire edge.1) (layout.controlWire edge.2)
      (layout.controlWire_ne (grayCNOTEdges_getElem_ne hindex))]

/-- First `count` coherent root/Gray-CNOT pairs. -/
def coherentGrayTransitionPrefixCircuit {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (V : QubitUnitary) :
    (count : ℕ) → count ≤ (grayCNOTEdges controlCount).length →
      SymbolicCircuit GrayFactorAtom ambientWidth
  | 0, _ => []
  | count + 1, hcount =>
      coherentGrayTransitionPrefixCircuit layout V count (by omega) ++
        coherentGrayTransitionPair layout V count (by omega)

/-- Full coherent raw schedule for `tail+1` positive controls. -/
def coherentGrayControlledViaRootCircuit {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth)
    (V : QubitUnitary) : SymbolicCircuit GrayFactorAtom ambientWidth :=
  coherentGrayTransitionPrefixCircuit layout V
      (grayCNOTEdges (tail + 1)).length le_rfl ++
    coherentGrayRootCircuitAt layout V
      (grayCNOTEdges (tail + 1)).length
      (coherentGrayFinalMask_index_lt tail)

/-- Selected exact-root wrapper for an arbitrary fully controlled `U`. -/
def coherentGrayControlledCircuit {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth)
    (U : QubitUnitary) : SymbolicCircuit GrayFactorAtom ambientWidth :=
  coherentGrayControlledViaRootCircuit layout (graySelectedRoot tail U)

private theorem coherentGrayUnmergedPrefix_eq_rawPrefix_start
    {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth)
    (V : QubitUnitary) :
    ∀ count (hcount : count ≤ (grayCNOTEdges (tail + 1)).length),
      [coherentGrayRootStartAt layout 0
          (coherentGrayInitialMask_index_lt tail)] ++
          coherentGrayUnmergedBoundaryPrefixCircuit layout count hcount =
        coherentGrayTransitionPrefixCircuit layout V count hcount ++
          [coherentGrayRootStartAt layout count
            (coherentGrayMask_index_lt_of_prefix (by omega) hcount)] := by
  intro count hcount
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [coherentGrayUnmergedBoundaryPrefixCircuit,
        coherentGrayTransitionPrefixCircuit]
      rw [← List.append_assoc, ih (by omega)]
      simp [coherentGrayUnmergedBoundarySegment,
        coherentGrayBoundaryAt, coherentGrayTransitionPair,
        coherentGrayRootCircuitAt_eq_start_core_end,
        List.append_assoc]

/-- The boundary-oriented unmerged syntax is only a literal regrouping. -/
theorem coherentGrayRegroupedViaRootCircuit_eq_raw
    {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth)
    (V : QubitUnitary) :
    coherentGrayRegroupedViaRootCircuit layout =
      coherentGrayControlledViaRootCircuit layout V := by
  rw [coherentGrayRegroupedViaRootCircuit,
    coherentGrayControlledViaRootCircuit]
  rw [coherentGrayUnmergedPrefix_eq_rawPrefix_start layout V]
  rw [coherentGrayRootCircuitAt_eq_start_core_end]
  simp [List.append_assoc]

/-- One executable merger step emits its explicit core/CNOT normal form. -/
@[simp]
theorem coherentGrayMergedBoundarySegment_eq_normalForm
    {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (index : ℕ) (hindex : index < (grayCNOTEdges controlCount).length) :
    coherentGrayMergedBoundarySegment layout index hindex =
      coherentGrayMergedBoundaryNormalForm layout index hindex := by
  rw [coherentGrayMergedBoundarySegment,
    coherentGrayMergedBoundaryNormalForm,
    coherentGrayNormalizedBoundaryAt_eq_singleton]

/-- Every streaming prefix emits exactly the direct core/CNOT prefix. -/
theorem coherentGrayMergedBoundaryPrefixCircuit_eq_normalForm
    {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth) :
    ∀ count (hcount : count ≤ (grayCNOTEdges controlCount).length),
      coherentGrayMergedBoundaryPrefixCircuit layout count hcount =
        coherentGrayMergedBoundaryNormalFormPrefixCircuit layout count hcount := by
  intro count hcount
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [coherentGrayMergedBoundaryPrefixCircuit,
        coherentGrayMergedBoundaryNormalFormPrefixCircuit,
        ih, coherentGrayMergedBoundarySegment_eq_normalForm]

/-- The executable boundarywise merger emits the named explicit normal form. -/
theorem mergedGrayControlledViaRootSymbolicCircuit_eq_normalForm
    {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth) :
    mergedGrayControlledViaRootSymbolicCircuit layout =
      mergedGrayControlledViaRootNormalForm layout := by
  rw [mergedGrayControlledViaRootSymbolicCircuit,
    mergedGrayControlledViaRootNormalForm,
    coherentGrayMergedBoundaryPrefixCircuit_eq_normalForm]

/-- Normalizing an indexed boundary preserves its exact erased evaluator. -/
@[simp]
theorem eval_erase_coherentGrayNormalizedBoundaryAt
    {controlCount ambientWidth : ℕ}
    (valuation : GrayFactorAtom → QubitUnitary)
    (layout : OrderedControlLayout controlCount ambientWidth)
    (index : ℕ) (hindex : index < (grayCNOTEdges controlCount).length) :
    FusionCircuit.eval
        (SymbolicCircuit.erase valuation
          (coherentGrayNormalizedBoundaryAt layout index hindex)) =
      FusionCircuit.eval
        (SymbolicCircuit.erase valuation
          (coherentGrayBoundaryAt layout index hindex)) := by
  simp [coherentGrayNormalizedBoundaryAt]

/-- One executable merged segment has the exact evaluator of its raw segment. -/
@[simp]
theorem eval_erase_coherentGrayMergedBoundarySegment
    {controlCount ambientWidth : ℕ}
    (valuation : GrayFactorAtom → QubitUnitary)
    (layout : OrderedControlLayout controlCount ambientWidth)
    (index : ℕ) (hindex : index < (grayCNOTEdges controlCount).length) :
    FusionCircuit.eval
        (SymbolicCircuit.erase valuation
          (coherentGrayMergedBoundarySegment layout index hindex)) =
      FusionCircuit.eval
        (SymbolicCircuit.erase valuation
          (coherentGrayUnmergedBoundarySegment layout index hindex)) := by
  rw [coherentGrayMergedBoundarySegment,
    coherentGrayUnmergedBoundarySegment]
  rw [erase_append, erase_append, FusionCircuit.eval_append,
    FusionCircuit.eval_append, eval_erase_coherentGrayNormalizedBoundaryAt]

/-- Exact evaluator preservation for every streaming merger prefix. -/
theorem eval_erase_coherentGrayMergedBoundaryPrefixCircuit
    {controlCount ambientWidth : ℕ}
    (valuation : GrayFactorAtom → QubitUnitary)
    (layout : OrderedControlLayout controlCount ambientWidth) :
    ∀ count (hcount : count ≤ (grayCNOTEdges controlCount).length),
      FusionCircuit.eval
          (SymbolicCircuit.erase valuation
            (coherentGrayMergedBoundaryPrefixCircuit layout count hcount)) =
        FusionCircuit.eval
          (SymbolicCircuit.erase valuation
            (coherentGrayUnmergedBoundaryPrefixCircuit layout count hcount)) := by
  intro count hcount
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [coherentGrayMergedBoundaryPrefixCircuit,
        coherentGrayUnmergedBoundaryPrefixCircuit]
      rw [erase_append, erase_append, FusionCircuit.eval_append,
        FusionCircuit.eval_append,
        eval_erase_coherentGrayMergedBoundarySegment, ih]

/-- Applying every certified boundary merger preserves the complete evaluator. -/
theorem eval_erase_mergedGrayControlledViaRootSymbolicCircuit_eq_regrouped
    {tail ambientWidth : ℕ}
    (valuation : GrayFactorAtom → QubitUnitary)
    (layout : OrderedControlLayout (tail + 1) ambientWidth) :
    FusionCircuit.eval
        (SymbolicCircuit.erase valuation
          (mergedGrayControlledViaRootSymbolicCircuit layout)) =
      FusionCircuit.eval
        (SymbolicCircuit.erase valuation
          (coherentGrayRegroupedViaRootCircuit layout)) := by
  simp only [mergedGrayControlledViaRootSymbolicCircuit,
    coherentGrayRegroupedViaRootCircuit]
  repeat' rw [erase_append, FusionCircuit.eval_append]
  rw [eval_erase_coherentGrayMergedBoundaryPrefixCircuit]

/-! ## Exact ordered CNOT chronology -/

@[simp]
theorem cnotTrace_coherentGrayNormalizedBoundaryAt
    {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (index : ℕ) (hindex : index < (grayCNOTEdges controlCount).length) :
    SymbolicCircuit.cnotTrace
        (coherentGrayNormalizedBoundaryAt layout index hindex) =
      SymbolicCircuit.cnotTrace (coherentGrayBoundaryAt layout index hindex) := by
  simp [coherentGrayNormalizedBoundaryAt]

@[simp]
theorem cnotTrace_coherentGrayMergedBoundarySegment
    {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (index : ℕ) (hindex : index < (grayCNOTEdges controlCount).length) :
    SymbolicCircuit.cnotTrace
        (coherentGrayMergedBoundarySegment layout index hindex) =
      SymbolicCircuit.cnotTrace
        (coherentGrayUnmergedBoundarySegment layout index hindex) := by
  rw [coherentGrayMergedBoundarySegment,
    coherentGrayUnmergedBoundarySegment,
    SymbolicCircuit.cnotTrace_append, SymbolicCircuit.cnotTrace_append,
    cnotTrace_coherentGrayNormalizedBoundaryAt]

theorem cnotTrace_coherentGrayMergedBoundaryPrefixCircuit
    {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth) :
    ∀ count (hcount : count ≤ (grayCNOTEdges controlCount).length),
      SymbolicCircuit.cnotTrace
          (coherentGrayMergedBoundaryPrefixCircuit layout count hcount) =
        SymbolicCircuit.cnotTrace
          (coherentGrayUnmergedBoundaryPrefixCircuit layout count hcount) := by
  intro count hcount
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [coherentGrayMergedBoundaryPrefixCircuit,
        coherentGrayUnmergedBoundaryPrefixCircuit,
        SymbolicCircuit.cnotTrace_append, SymbolicCircuit.cnotTrace_append,
        ih, cnotTrace_coherentGrayMergedBoundarySegment]

/-- Every literal CNOT and its orientation remain in the original exact order. -/
theorem cnotTrace_mergedGrayControlledViaRootSymbolicCircuit_eq_raw
    {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth)
    (V : QubitUnitary) :
    SymbolicCircuit.cnotTrace
        (mergedGrayControlledViaRootSymbolicCircuit layout) =
      SymbolicCircuit.cnotTrace
        (coherentGrayControlledViaRootCircuit layout V) := by
  rw [mergedGrayControlledViaRootSymbolicCircuit,
    ← coherentGrayRegroupedViaRootCircuit_eq_raw layout V,
    coherentGrayRegroupedViaRootCircuit]
  simp only [SymbolicCircuit.cnotTrace_append]
  rw [cnotTrace_coherentGrayMergedBoundaryPrefixCircuit]

/-! ## Syntax-derived post-merger resources -/

@[simp]
theorem coherentGrayRootStartAt_counts {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (index : ℕ) (hindex : index < (grayCode controlCount).length) :
    SymbolicCircuit.oneQubitCount
        [coherentGrayRootStartAt layout index hindex] = 1 ∧
      SymbolicCircuit.cnotCount
        [coherentGrayRootStartAt layout index hindex] = 0 ∧
      SymbolicCircuit.gateCount
        [coherentGrayRootStartAt layout index hindex] = 1 := by
  by_cases hodd : Odd ((grayCode controlCount)[index]'hindex).card <;>
    simp [coherentGrayRootStartAt, grayRootStartSymbolic, hodd,
      SymbolicPrimitive.atom, SymbolicPrimitive.inverseAtom,
      SymbolicCircuit.oneQubitCount, SymbolicCircuit.oneQubitWeight,
      SymbolicCircuit.cnotCount, SymbolicCircuit.cnotWeight,
      SymbolicCircuit.gateCount]

@[simp]
theorem coherentGrayRootEndAt_counts {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (index : ℕ) (hindex : index < (grayCode controlCount).length) :
    SymbolicCircuit.oneQubitCount
        [coherentGrayRootEndAt layout index hindex] = 1 ∧
      SymbolicCircuit.cnotCount
        [coherentGrayRootEndAt layout index hindex] = 0 ∧
      SymbolicCircuit.gateCount
        [coherentGrayRootEndAt layout index hindex] = 1 := by
  by_cases hodd : Odd ((grayCode controlCount)[index]'hindex).card <;>
    simp [coherentGrayRootEndAt, grayRootEndSymbolic, hodd,
      SymbolicPrimitive.atom, SymbolicPrimitive.inverseAtom,
      SymbolicCircuit.oneQubitCount, SymbolicCircuit.oneQubitWeight,
      SymbolicCircuit.cnotCount, SymbolicCircuit.cnotWeight,
      SymbolicCircuit.gateCount]

@[simp]
theorem coherentGrayRootCoreAt_counts {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (index : ℕ) (hindex : index < (grayCode controlCount).length) :
    SymbolicCircuit.oneQubitCount
        (coherentGrayRootCoreAt layout index hindex) = 2 ∧
      SymbolicCircuit.cnotCount
        (coherentGrayRootCoreAt layout index hindex) = 2 ∧
      SymbolicCircuit.gateCount
        (coherentGrayRootCoreAt layout index hindex) = 4 := by
  by_cases hodd : Odd ((grayCode controlCount)[index]'hindex).card <;>
    simp [coherentGrayRootCoreAt, grayRootCoreSymbolicCircuit, hodd,
      SymbolicPrimitive.atom, SymbolicPrimitive.inverseAtom,
      SymbolicCircuit.oneQubitCount, SymbolicCircuit.oneQubitWeight,
      SymbolicCircuit.cnotCount, SymbolicCircuit.cnotWeight,
      SymbolicCircuit.gateCount]

@[simp]
theorem coherentGrayMergedBoundaryNormalForm_counts
    {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (index : ℕ) (hindex : index < (grayCNOTEdges controlCount).length) :
    SymbolicCircuit.oneQubitCount
        (coherentGrayMergedBoundaryNormalForm layout index hindex) = 2 ∧
      SymbolicCircuit.cnotCount
        (coherentGrayMergedBoundaryNormalForm layout index hindex) = 3 ∧
      SymbolicCircuit.gateCount
        (coherentGrayMergedBoundaryNormalForm layout index hindex) = 5 := by
  have hmask := coherentGrayMask_index_lt_of_edge hindex
  by_cases hodd : Odd ((grayCode controlCount)[index]'hmask).card <;>
    simp [coherentGrayMergedBoundaryNormalForm, coherentGrayRootCoreAt,
      grayRootCoreSymbolicCircuit, hodd,
      SymbolicPrimitive.atom, SymbolicPrimitive.inverseAtom,
      SymbolicCircuit.oneQubitCount, SymbolicCircuit.oneQubitWeight,
      SymbolicCircuit.cnotCount, SymbolicCircuit.cnotWeight,
      SymbolicCircuit.gateCount]

/-- Every emitted core/CNOT prefix has its exact constructor-folded profile. -/
theorem coherentGrayMergedBoundaryNormalFormPrefixCircuit_counts
    {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth) :
    ∀ count (hcount : count ≤ (grayCNOTEdges controlCount).length),
      SymbolicCircuit.oneQubitCount
          (coherentGrayMergedBoundaryNormalFormPrefixCircuit
            layout count hcount) = 2 * count ∧
        SymbolicCircuit.cnotCount
          (coherentGrayMergedBoundaryNormalFormPrefixCircuit
            layout count hcount) = 3 * count ∧
        SymbolicCircuit.gateCount
          (coherentGrayMergedBoundaryNormalFormPrefixCircuit
            layout count hcount) = 5 * count := by
  intro count hcount
  induction count with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ count ih =>
      rw [coherentGrayMergedBoundaryNormalFormPrefixCircuit]
      rcases ih (by omega) with ⟨hone, hcnot, hgate⟩
      rw [SymbolicCircuit.oneQubitCount_append,
        SymbolicCircuit.cnotCount_append,
        SymbolicCircuit.gateCount_append,
        hone, hcnot, hgate]
      simp only [coherentGrayMergedBoundaryNormalForm_counts]
      omega

@[simp]
theorem mergedGrayControlledViaRootNormalForm_oneQubitCount
    {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth) :
    SymbolicCircuit.oneQubitCount
        (mergedGrayControlledViaRootNormalForm layout) =
      2 * 2 ^ (tail + 1) := by
  rw [mergedGrayControlledViaRootNormalForm]
  simp only [SymbolicCircuit.oneQubitCount_append]
  rcases coherentGrayMergedBoundaryNormalFormPrefixCircuit_counts layout
      (grayCNOTEdges (tail + 1)).length le_rfl with ⟨hone, _, _⟩
  rcases coherentGrayRootStartAt_counts layout 0
      (coherentGrayInitialMask_index_lt tail) with ⟨hstart, _, _⟩
  rcases coherentGrayRootCoreAt_counts layout
      (grayCNOTEdges (tail + 1)).length
      (coherentGrayFinalMask_index_lt tail) with ⟨hcore, _, _⟩
  rcases coherentGrayRootEndAt_counts layout
      (grayCNOTEdges (tail + 1)).length
      (coherentGrayFinalMask_index_lt tail) with ⟨hend, _, _⟩
  rw [hstart, hone, hcore, hend, length_grayCNOTEdges]
  have hpow : 0 < 2 ^ tail := pow_pos (by omega) tail
  simp only [pow_succ]
  omega

@[simp]
theorem mergedGrayControlledViaRootNormalForm_cnotCount
    {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth) :
    SymbolicCircuit.cnotCount
        (mergedGrayControlledViaRootNormalForm layout) =
      3 * 2 ^ (tail + 1) - 4 := by
  rw [mergedGrayControlledViaRootNormalForm]
  simp only [SymbolicCircuit.cnotCount_append]
  rcases coherentGrayMergedBoundaryNormalFormPrefixCircuit_counts layout
      (grayCNOTEdges (tail + 1)).length le_rfl with ⟨_, hcnot, _⟩
  rcases coherentGrayRootStartAt_counts layout 0
      (coherentGrayInitialMask_index_lt tail) with ⟨_, hstart, _⟩
  rcases coherentGrayRootCoreAt_counts layout
      (grayCNOTEdges (tail + 1)).length
      (coherentGrayFinalMask_index_lt tail) with ⟨_, hcore, _⟩
  rcases coherentGrayRootEndAt_counts layout
      (grayCNOTEdges (tail + 1)).length
      (coherentGrayFinalMask_index_lt tail) with ⟨_, hend, _⟩
  rw [hstart, hcnot, hcore, hend, length_grayCNOTEdges]
  have hpow : 0 < 2 ^ tail := pow_pos (by omega) tail
  simp only [pow_succ]
  omega

@[simp]
theorem mergedGrayControlledViaRootNormalForm_gateCount
    {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth) :
    SymbolicCircuit.gateCount
        (mergedGrayControlledViaRootNormalForm layout) =
      5 * 2 ^ (tail + 1) - 4 := by
  rw [SymbolicCircuit.gateCount_eq_componentCounts,
    mergedGrayControlledViaRootNormalForm_oneQubitCount,
    mergedGrayControlledViaRootNormalForm_cnotCount]
  have hpow : 0 < 2 ^ tail := pow_pos (by omega) tail
  simp only [pow_succ]
  omega

@[simp]
theorem mergedGrayControlledViaRootSymbolicCircuit_oneQubitCount
    {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth) :
    SymbolicCircuit.oneQubitCount
        (mergedGrayControlledViaRootSymbolicCircuit layout) =
      2 * 2 ^ (tail + 1) := by
  rw [mergedGrayControlledViaRootSymbolicCircuit_eq_normalForm,
    mergedGrayControlledViaRootNormalForm_oneQubitCount]

@[simp]
theorem mergedGrayControlledViaRootSymbolicCircuit_cnotCount
    {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth) :
    SymbolicCircuit.cnotCount
        (mergedGrayControlledViaRootSymbolicCircuit layout) =
      3 * 2 ^ (tail + 1) - 4 := by
  rw [mergedGrayControlledViaRootSymbolicCircuit_eq_normalForm,
    mergedGrayControlledViaRootNormalForm_cnotCount]

@[simp]
theorem mergedGrayControlledViaRootSymbolicCircuit_gateCount
    {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth) :
    SymbolicCircuit.gateCount
        (mergedGrayControlledViaRootSymbolicCircuit layout) =
      5 * 2 ^ (tail + 1) - 4 := by
  rw [mergedGrayControlledViaRootSymbolicCircuit_eq_normalForm,
    mergedGrayControlledViaRootNormalForm_gateCount]

@[simp]
theorem mergedGrayControlledViaRootFusionCircuit_oneQubitCount
    {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth)
    (V : QubitUnitary) :
    FusionCircuit.oneQubitCount
        (mergedGrayControlledViaRootFusionCircuit layout V) =
      2 * 2 ^ (tail + 1) := by
  rw [mergedGrayControlledViaRootFusionCircuit,
    SymbolicCircuit.erase_oneQubitCount,
    mergedGrayControlledViaRootSymbolicCircuit_oneQubitCount]

@[simp]
theorem mergedGrayControlledViaRootFusionCircuit_cnotCount
    {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth)
    (V : QubitUnitary) :
    FusionCircuit.cnotCount
        (mergedGrayControlledViaRootFusionCircuit layout V) =
      3 * 2 ^ (tail + 1) - 4 := by
  rw [mergedGrayControlledViaRootFusionCircuit,
    SymbolicCircuit.erase_cnotCount,
    mergedGrayControlledViaRootSymbolicCircuit_cnotCount]

@[simp]
theorem mergedGrayControlledViaRootFusionCircuit_twoQubitCount
    {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth)
    (V : QubitUnitary) :
    FusionCircuit.twoQubitCount
        (mergedGrayControlledViaRootFusionCircuit layout V) = 0 := by
  simp [mergedGrayControlledViaRootFusionCircuit]

@[simp]
theorem mergedGrayControlledViaRootFusionCircuit_gateCount
    {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth)
    (V : QubitUnitary) :
    FusionCircuit.gateCount
        (mergedGrayControlledViaRootFusionCircuit layout V) =
      5 * 2 ^ (tail + 1) - 4 := by
  rw [mergedGrayControlledViaRootFusionCircuit,
    SymbolicCircuit.erase_gateCount,
    mergedGrayControlledViaRootSymbolicCircuit_gateCount]

@[simp]
theorem mergedGrayControlledViaRootFusionCircuit_oneQubitCNOTCost
    {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth)
    (V : QubitUnitary) :
    FusionCircuit.cost CostModel.oneQubitCNOT
        (mergedGrayControlledViaRootFusionCircuit layout V) =
      some (5 * 2 ^ (tail + 1) - 4) := by
  rw [mergedGrayControlledViaRootFusionCircuit,
    SymbolicCircuit.erase_oneQubitCNOTCost,
    mergedGrayControlledViaRootSymbolicCircuit_gateCount]

@[simp]
theorem mergedGrayControlledViaRootFusionCircuit_arbitraryTwoQubitCost
    {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth)
    (V : QubitUnitary) :
    FusionCircuit.cost CostModel.arbitraryTwoQubit
        (mergedGrayControlledViaRootFusionCircuit layout V) =
      some (5 * 2 ^ (tail + 1) - 4) := by
  rw [FusionCircuit.arbitraryTwoQubit_cost_eq_gateCount,
    mergedGrayControlledViaRootFusionCircuit_gateCount]

@[simp]
theorem mergedGrayControlledViaRootCircuit_oneQubitCount
    {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth)
    (V : QubitUnitary) :
    Circuit.kindCount .oneQubit
        (mergedGrayControlledViaRootCircuit layout V) =
      2 * 2 ^ (tail + 1) := by
  rw [mergedGrayControlledViaRootCircuit,
    FusionCircuit.oneQubitCount_lower,
    mergedGrayControlledViaRootFusionCircuit_oneQubitCount]

@[simp]
theorem mergedGrayControlledViaRootCircuit_cnotCount
    {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth)
    (V : QubitUnitary) :
    Circuit.kindCount .cnot
        (mergedGrayControlledViaRootCircuit layout V) =
      3 * 2 ^ (tail + 1) - 4 := by
  rw [mergedGrayControlledViaRootCircuit,
    FusionCircuit.cnotCount_lower,
    mergedGrayControlledViaRootFusionCircuit_cnotCount]

@[simp]
theorem mergedGrayControlledViaRootCircuit_twoQubitCount
    {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth)
    (V : QubitUnitary) :
    Circuit.kindCount .arbitraryTwoQubit
        (mergedGrayControlledViaRootCircuit layout V) = 0 := by
  rw [mergedGrayControlledViaRootCircuit,
    FusionCircuit.twoQubitCount_lower,
    mergedGrayControlledViaRootFusionCircuit_twoQubitCount]

@[simp]
theorem mergedGrayControlledViaRootCircuit_gateCount
    {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth)
    (V : QubitUnitary) :
    Circuit.gateCount (mergedGrayControlledViaRootCircuit layout V) =
      5 * 2 ^ (tail + 1) - 4 := by
  rw [mergedGrayControlledViaRootCircuit,
    FusionCircuit.gateCount_lower,
    mergedGrayControlledViaRootFusionCircuit_gateCount]

@[simp]
theorem mergedGrayControlledViaRootCircuit_oneQubitCNOTCost
    {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth)
    (V : QubitUnitary) :
    Circuit.cost CostModel.oneQubitCNOT
        (mergedGrayControlledViaRootCircuit layout V) =
      some (5 * 2 ^ (tail + 1) - 4) := by
  rw [mergedGrayControlledViaRootCircuit,
    FusionCircuit.cost_lower,
    mergedGrayControlledViaRootFusionCircuit_oneQubitCNOTCost]

@[simp]
theorem mergedGrayControlledViaRootCircuit_arbitraryTwoQubitCost
    {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth)
    (V : QubitUnitary) :
    Circuit.cost CostModel.arbitraryTwoQubit
        (mergedGrayControlledViaRootCircuit layout V) =
      some (5 * 2 ^ (tail + 1) - 4) := by
  rw [mergedGrayControlledViaRootCircuit,
    FusionCircuit.cost_lower,
    mergedGrayControlledViaRootFusionCircuit_arbitraryTwoQubitCost]

/-- The selected-root fusion family has the complete checked merged profile. -/
theorem mergedGrayControlledFusionCircuit_profile
    {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth)
    (U : QubitUnitary) :
    FusionCircuit.oneQubitCount (mergedGrayControlledFusionCircuit layout U) =
        2 * 2 ^ (tail + 1) ∧
      FusionCircuit.cnotCount (mergedGrayControlledFusionCircuit layout U) =
        3 * 2 ^ (tail + 1) - 4 ∧
      FusionCircuit.twoQubitCount (mergedGrayControlledFusionCircuit layout U) = 0 ∧
      FusionCircuit.gateCount (mergedGrayControlledFusionCircuit layout U) =
        5 * 2 ^ (tail + 1) - 4 ∧
      FusionCircuit.cost CostModel.oneQubitCNOT
          (mergedGrayControlledFusionCircuit layout U) =
        some (5 * 2 ^ (tail + 1) - 4) := by
  simp only [mergedGrayControlledFusionCircuit]
  exact
    ⟨mergedGrayControlledViaRootFusionCircuit_oneQubitCount layout _,
      mergedGrayControlledViaRootFusionCircuit_cnotCount layout _,
      mergedGrayControlledViaRootFusionCircuit_twoQubitCount layout _,
      mergedGrayControlledViaRootFusionCircuit_gateCount layout _,
      mergedGrayControlledViaRootFusionCircuit_oneQubitCNOTCost layout _⟩

@[simp]
theorem eval_erase_coherentGrayRootCircuitAt
    {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (V : QubitUnitary) (index : ℕ)
    (hindex : index < (grayCode controlCount).length) :
    FusionCircuit.eval
        (SymbolicCircuit.erase (grayFactorValuation V)
          (coherentGrayRootCircuitAt layout V index hindex)) =
      (grayRootPrimitiveAt layout V index hindex).denotation := by
  have hmem : (grayCode controlCount)[index] ∈ grayCode controlCount :=
    List.getElem_mem _
  have hne : ((grayCode controlCount)[index]'hindex).Nonempty :=
    (mem_grayCode_iff _).mp hmem
  simp [coherentGrayRootCircuitAt, grayRootPrimitiveAt,
    controlledTargetPrimitive, controlComplement,
    eval_erase_coherentGrayRootSymbolicCircuit _ hne]

@[simp]
theorem eval_erase_coherentGrayTransitionPair
    {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (V : QubitUnitary) (index : ℕ)
    (hindex : index < (grayCNOTEdges controlCount).length) :
    FusionCircuit.eval
        (SymbolicCircuit.erase (grayFactorValuation V)
          (coherentGrayTransitionPair layout V index hindex)) =
      Circuit.eval (grayTransitionPair layout V index hindex) := by
  rw [coherentGrayTransitionPair, erase_append,
    FusionCircuit.eval_append, eval_erase_coherentGrayRootCircuitAt]
  simp [grayTransitionPair, FusionPrimitive.denotation, cnotPrimitive]

/-- Every coherent raw prefix exactly matches the established macro prefix. -/
theorem eval_erase_coherentGrayTransitionPrefixCircuit
    {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (V : QubitUnitary) :
    ∀ count (hcount : count ≤ (grayCNOTEdges controlCount).length),
      FusionCircuit.eval
          (SymbolicCircuit.erase (grayFactorValuation V)
            (coherentGrayTransitionPrefixCircuit layout V count hcount)) =
        Circuit.eval (grayTransitionPrefixCircuit layout V count hcount) := by
  intro count hcount
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [coherentGrayTransitionPrefixCircuit, grayTransitionPrefixCircuit]
      rw [erase_append, FusionCircuit.eval_append, Circuit.eval_append,
        eval_erase_coherentGrayTransitionPair, ih]

/-- Complete coherent raw syntax is exactly the checked Lemma 7.1 macro circuit. -/
theorem eval_erase_coherentGrayControlledViaRootCircuit_eq_macro
    {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth)
    (V : QubitUnitary) :
    FusionCircuit.eval
        (SymbolicCircuit.erase (grayFactorValuation V)
          (coherentGrayControlledViaRootCircuit layout V)) =
      Circuit.eval (grayControlledViaRootCircuit layout V) := by
  rw [coherentGrayControlledViaRootCircuit, grayControlledViaRootCircuit]
  rw [erase_append, FusionCircuit.eval_append, Circuit.eval_append,
    eval_erase_coherentGrayTransitionPrefixCircuit,
    eval_erase_coherentGrayRootCircuitAt]
  rw [Circuit.eval_singleton]

/-- The complete streaming merger is exactly evaluator-preserving. -/
theorem eval_erase_mergedGrayControlledViaRootSymbolicCircuit_eq_raw
    {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth)
    (V : QubitUnitary) :
    FusionCircuit.eval
        (SymbolicCircuit.erase (grayFactorValuation V)
          (mergedGrayControlledViaRootSymbolicCircuit layout)) =
      FusionCircuit.eval
        (SymbolicCircuit.erase (grayFactorValuation V)
          (coherentGrayControlledViaRootCircuit layout V)) := by
  rw [eval_erase_mergedGrayControlledViaRootSymbolicCircuit_eq_regrouped,
    coherentGrayRegroupedViaRootCircuit_eq_raw layout V]

/-- The erased merged circuit has the established Lemma 7.1 macro evaluator. -/
theorem eval_mergedGrayControlledViaRootFusionCircuit_eq_macro
    {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth)
    (V : QubitUnitary) :
    FusionCircuit.eval (mergedGrayControlledViaRootFusionCircuit layout V) =
      Circuit.eval (grayControlledViaRootCircuit layout V) := by
  rw [mergedGrayControlledViaRootFusionCircuit,
    eval_erase_mergedGrayControlledViaRootSymbolicCircuit_eq_raw,
    eval_erase_coherentGrayControlledViaRootCircuit_eq_macro]

/-- The trusted lowered merged circuit preserves the same exact macro evaluator. -/
theorem eval_mergedGrayControlledViaRootCircuit_eq_macro
    {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth)
    (V : QubitUnitary) :
    Circuit.eval (mergedGrayControlledViaRootCircuit layout V) =
      Circuit.eval (grayControlledViaRootCircuit layout V) := by
  rw [mergedGrayControlledViaRootCircuit, FusionCircuit.eval_lower,
    eval_mergedGrayControlledViaRootFusionCircuit_eq_macro]

/-- Exact arbitrary-register semantics of the selected-root merged fusion circuit. -/
@[simp]
theorem eval_mergedGrayControlledFusionCircuit {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth)
    (U : QubitUnitary) :
    FusionCircuit.eval (mergedGrayControlledFusionCircuit layout U) =
      positiveControlledUnitary layout.targetWire layout.controlSet U := by
  rw [mergedGrayControlledFusionCircuit,
    eval_mergedGrayControlledViaRootFusionCircuit_eq_macro]
  simpa [grayControlledCircuit] using eval_grayControlledCircuit layout U

/-- Exact arbitrary-register semantics of the trusted merged circuit. -/
@[simp]
theorem eval_mergedGrayControlledCircuit {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth)
    (U : QubitUnitary) :
    Circuit.eval (mergedGrayControlledCircuit layout U) =
      positiveControlledUnitary layout.targetWire layout.controlSet U := by
  rw [mergedGrayControlledCircuit, FusionCircuit.eval_lower,
    eval_mergedGrayControlledFusionCircuit]

/-- Exact arbitrary-register semantics of the selected-root coherent raw syntax. -/
@[simp]
theorem eval_erase_coherentGrayControlledCircuit {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth)
    (U : QubitUnitary) :
    FusionCircuit.eval
        (SymbolicCircuit.erase (grayFactorValuation (graySelectedRoot tail U))
          (coherentGrayControlledCircuit layout U)) =
      positiveControlledUnitary layout.targetWire layout.controlSet U := by
  rw [coherentGrayControlledCircuit,
    eval_erase_coherentGrayControlledViaRootCircuit_eq_macro]
  simpa [grayControlledCircuit] using eval_grayControlledCircuit layout U

end OrderedControlLayout

end


end Barenco.MultiControl
