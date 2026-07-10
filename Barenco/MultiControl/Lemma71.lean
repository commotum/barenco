import Barenco.MultiControl.GrayAccumulator
import Barenco.MultiControl.Layout
import Barenco.OneQubit.Roots
import Barenco.ThreeQubit.Lemma61

/-!
# Gray-code circuit semantics for Lemma 7.1

This file begins the semantic bridge from the pure Boolean Gray accumulator to
certified arbitrary-width quantum circuits.  The first layer identifies the
ambient basis update of an embedded logical CNOT and proves that restricting it
back to the ordered controls is exactly `xorWireUpdate`.

The full interleaved controlled-root circuit and its evaluator are added only
after the generated Gray edge schedule has a general validity/restoration proof.
-/

namespace Barenco.MultiControl

open Barenco.ControlledCircuit
open scoped BigOperators Matrix

/-! ## Signed target product, independent of the CNOT realization -/

/-- The Gray traversal enumerates exactly the nonempty subsets of all control positions. -/
theorem grayCode_toFinset (controlCount : ℕ) :
    (grayCode controlCount).toFinset =
      nonemptySubsets (Finset.univ : Finset (Fin controlCount)) := by
  ext mask
  simp [mem_grayCode_iff]

/-- Alternating signed exponent accumulated over the Gray masks for one input. -/
def grayExponentSum (controlCount : ℕ) (bits : Fin controlCount → Bool) : ℤ :=
  ((grayCode controlCount).map
    (fun mask => signedParityContribution mask bits)).sum

/-- Gray order changes execution locality but not the inclusion-exclusion sum. -/
theorem grayExponentSum_eq_parityInclusionExclusionSum (controlCount : ℕ)
    (bits : Fin controlCount → Bool) :
    grayExponentSum controlCount bits =
      parityInclusionExclusionSum (Finset.univ : Finset (Fin controlCount)) bits := by
  rw [grayExponentSum, ← List.sum_toFinset _ (nodup_grayCode controlCount),
    grayCode_toFinset]
  rfl

/-- Closed exponent formula for a positive number of controls. -/
theorem grayExponentSum_succ_formula (controlCount : ℕ)
    (bits : Fin (controlCount + 1) → Bool) :
    grayExponentSum (controlCount + 1) bits =
      if (∀ control, bits control = true) then (2 : ℤ) ^ controlCount else 0 := by
  rw [grayExponentSum_eq_parityInclusionExclusionSum]
  simpa using parityInclusionExclusionSum_univ bits

private theorem prod_zpow_eq_zpow_sum (V : QubitUnitary) :
    ∀ exponents : List ℤ,
      (exponents.map (fun exponent => V ^ exponent)).prod = V ^ exponents.sum := by
  intro exponents
  induction exponents with
  | nil => simp
  | cons exponent exponents ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons, ih]
      rw [zpow_add]

/-- Root or inverse-root chosen by the alternating cardinality sign of one mask. -/
def signedGrayRoot {controlCount : ℕ} (mask : GrayMask controlCount)
    (V : QubitUnitary) : QubitUnitary :=
  V ^ ((-1 : ℤ) ^ (mask.card - 1))

/-- A controlled signed root contributes its signed power exactly when parity is true. -/
theorem signedGrayRoot_factor {controlCount : ℕ} (mask : GrayMask controlCount)
    (V : QubitUnitary) (bits : Fin controlCount → Bool) :
    (if xorParity mask bits then signedGrayRoot mask V else 1) =
      V ^ signedParityContribution mask bits := by
  cases hparity : xorParity mask bits <;>
    simp [signedGrayRoot, signedParityContribution, xorParityInt, boolInt, hparity]

/-- Product of the controlled-root factors selected by all Gray parities. -/
def grayRootProduct (controlCount : ℕ) (V : QubitUnitary)
    (bits : Fin controlCount → Bool) : QubitUnitary :=
  ((grayCode controlCount).map
    (fun mask => V ^ signedParityContribution mask bits)).prod

/-- The target product is the selected root raised to the signed Gray exponent. -/
theorem grayRootProduct_eq_zpow (controlCount : ℕ) (V : QubitUnitary)
    (bits : Fin controlCount → Bool) :
    grayRootProduct controlCount V bits = V ^ grayExponentSum controlCount bits := by
  rw [grayRootProduct, grayExponentSum]
  simpa [List.map_map, Function.comp_def] using
    prod_zpow_eq_zpow_sum V
      ((grayCode controlCount).map
        (fun mask => signedParityContribution mask bits))

/-- The Gray target product is a large positive power only on the all-true branch. -/
theorem grayRootProduct_succ_formula (controlCount : ℕ) (V : QubitUnitary)
    (bits : Fin (controlCount + 1) → Bool) :
    grayRootProduct (controlCount + 1) V bits =
      if (∀ control, bits control = true) then V ^ ((2 : ℤ) ^ controlCount) else 1 := by
  rw [grayRootProduct_eq_zpow, grayExponentSum_succ_formula]
  by_cases hall : ∀ control, bits control = true <;> simp [hall]

/-- Selected exact root for a register with `controlCount + 1` controls. -/
noncomputable def graySelectedRoot (controlCount : ℕ) (U : QubitUnitary) : QubitUnitary :=
  OneQubit.unitaryRoot (2 ^ controlCount) U

/-- The selected root's complete Gray product is exactly controlled-`U` branchwise. -/
theorem grayRootProduct_selectedRoot_formula (controlCount : ℕ) (U : QubitUnitary)
    (bits : Fin (controlCount + 1) → Bool) :
    grayRootProduct (controlCount + 1) (graySelectedRoot controlCount U) bits =
      if (∀ control, bits control = true) then U else 1 := by
  rw [grayRootProduct_succ_formula]
  by_cases hall : ∀ control, bits control = true
  · rw [if_pos hall, if_pos hall]
    have hcast : (2 : ℤ) ^ controlCount = ((2 ^ controlCount : ℕ) : ℤ) := by
      norm_cast
    rw [hcast, zpow_natCast]
    exact
      OneQubit.unitaryRoot_pow (2 ^ controlCount)
        (pow_pos (by omega) controlCount) U
  · rw [if_neg hall, if_neg hall]

/-- Ambient computational-basis update of one logical-control CNOT. -/
def embeddedCNOTUpdate {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (control target : Fin controlCount) (input : Basis ambientWidth) :
    Basis ambientWidth :=
  if input (layout.controlWire control) then
    setTarget (layout.controlWire target) input (!input (layout.controlWire target))
  else input

/-- The certified embedded CNOT has exactly the stated ambient basis action. -/
theorem cnotPrimitive_mulVec_basisKet {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (control target : Fin controlCount) (h : control ≠ target)
    (input : Basis ambientWidth) :
    ((layout.cnotPrimitive control target h).denotation : Gate ambientWidth) *ᵥ
        basisKet input =
      basisKet (embeddedCNOTUpdate layout control target input) := by
  rw [OrderedControlLayout.cnotPrimitive, Primitive.cnot_denotation_val]
  simpa [embeddedCNOTUpdate] using
    cnotRaw_mulVec_basisKet (layout.controlWire control)
      (layout.controlWire target) (layout.controlWire_ne h) input

/--
A singly controlled target gate acts on a target-local state by left-multiplying
the target matrix exactly when its control wire is true.
-/
theorem controlledTargetPrimitive_mulVec_localRaw_basisKet
    {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (control : Fin controlCount) (U : QubitUnitary) (A : QubitMatrix)
    (input : Basis ambientWidth) :
    ((layout.controlledTargetPrimitive control U).denotation : Gate ambientWidth) *ᵥ
        (localRaw layout.targetWire A *ᵥ basisKet input) =
      localRaw layout.targetWire
          ((if input (layout.controlWire control) then (U : QubitMatrix) else 1) * A) *ᵥ
        basisKet input := by
  rw [Matrix.mulVec_mulVec]
  rw [OrderedControlLayout.controlledTargetPrimitive,
    Primitive.positiveControlled_denotation_val,
    positiveControlledRaw_singleton_eq_targetBlockRaw,
    localRaw_eq_targetBlockRaw, targetBlockRaw_mul,
    targetBlockRaw_mulVec_basisKet]
  simp [OrderedControlLayout.controlComplement, splitTarget_snd_apply]

/--
A logical control-to-control CNOT commutes past target-local state evolution and
performs only its certified ambient basis update.
-/
theorem cnotPrimitive_mulVec_localRaw_basisKet
    {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (control target : Fin controlCount) (h : control ≠ target)
    (A : QubitMatrix) (input : Basis ambientWidth) :
    ((layout.cnotPrimitive control target h).denotation : Gate ambientWidth) *ᵥ
        (localRaw layout.targetWire A *ᵥ basisKet input) =
      localRaw layout.targetWire A *ᵥ
        basisKet (embeddedCNOTUpdate layout control target input) := by
  rw [Matrix.mulVec_mulVec]
  rw [OrderedControlLayout.cnotPrimitive, Primitive.cnot_denotation_val,
    Barenco.ThreeQubit.cnotRaw_commute_localRaw
      (layout.controlWire control) (layout.controlWire target) layout.targetWire
      (layout.controlWire_ne h) (layout.control_ne_target control)
      (layout.control_ne_target target) A,
    ← Matrix.mulVec_mulVec, cnotRaw_mulVec_basisKet]
  rfl

/-- Restricting an embedded logical CNOT is exactly the pure Boolean XOR update. -/
theorem restrictControls_embeddedCNOTUpdate {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (control target : Fin controlCount)
    (input : Basis ambientWidth) :
    layout.restrictControls (embeddedCNOTUpdate layout control target input) =
      xorWireUpdate control target (layout.restrictControls input) := by
  funext wire
  by_cases hwire : wire = target
  · subst wire
    cases hcontrol : input (layout.controlWire control) <;>
      cases htarget : input (layout.controlWire target) <;>
      simp [embeddedCNOTUpdate, OrderedControlLayout.restrictControls,
        xorWireUpdate, hcontrol, htarget] <;>
      decide
  · have hambient : layout.controlWire wire ≠ layout.controlWire target :=
      layout.controlWire_ne hwire
    cases hcontrol : input (layout.controlWire control) <;>
      simp [embeddedCNOTUpdate, OrderedControlLayout.restrictControls,
        xorWireUpdate, hcontrol, hwire, hambient]

/-- An embedded logical CNOT preserves every ambient wire other than its target. -/
theorem embeddedCNOTUpdate_apply_of_ne {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (control target : Fin controlCount) (input : Basis ambientWidth)
    (wire : Fin ambientWidth) (hwire : wire ≠ layout.controlWire target) :
    embeddedCNOTUpdate layout control target input wire = input wire := by
  cases hcontrol : input (layout.controlWire control) <;>
    simp [embeddedCNOTUpdate, hcontrol, hwire]

/-- In particular, an embedded control-to-control CNOT preserves the quantum target. -/
@[simp]
theorem embeddedCNOTUpdate_apply_targetWire {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (control target : Fin controlCount) (input : Basis ambientWidth) :
    embeddedCNOTUpdate layout control target input layout.targetWire =
      input layout.targetWire := by
  apply embeddedCNOTUpdate_apply_of_ne
  exact Ne.symm (layout.control_ne_target target)

/-- Execute a list of logical-control CNOT edges inside the ambient register. -/
def runEmbeddedCNOTUpdates {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (edges : List (Fin controlCount × Fin controlCount))
    (input : Basis ambientWidth) : Basis ambientWidth :=
  edges.foldl
    (fun current edge => embeddedCNOTUpdate layout edge.1 edge.2 current) input

@[simp]
theorem runEmbeddedCNOTUpdates_nil {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (input : Basis ambientWidth) :
    runEmbeddedCNOTUpdates layout [] input = input := rfl

/-- Restriction commutes exactly with executing any ordered logical CNOT edge list. -/
theorem restrictControls_runEmbeddedCNOTUpdates {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (edges : List (Fin controlCount × Fin controlCount))
    (input : Basis ambientWidth) :
    layout.restrictControls (runEmbeddedCNOTUpdates layout edges input) =
      runXorEdges edges (layout.restrictControls input) := by
  induction edges generalizing input with
  | nil => rfl
  | cons edge edges ih =>
      change layout.restrictControls
          (runEmbeddedCNOTUpdates layout edges
            (embeddedCNOTUpdate layout edge.1 edge.2 input)) =
        runXorEdges edges
          (xorWireUpdate edge.1 edge.2 (layout.restrictControls input))
      rw [ih, restrictControls_embeddedCNOTUpdate]

/-- Every control-to-control edge schedule preserves the separate quantum target wire. -/
@[simp]
theorem runEmbeddedCNOTUpdates_apply_targetWire {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (edges : List (Fin controlCount × Fin controlCount))
    (input : Basis ambientWidth) :
    runEmbeddedCNOTUpdates layout edges input layout.targetWire =
      input layout.targetWire := by
  induction edges generalizing input with
  | nil => rfl
  | cons edge edges ih =>
      change runEmbeddedCNOTUpdates layout edges
          (embeddedCNOTUpdate layout edge.1 edge.2 input) layout.targetWire = _
      rw [ih, embeddedCNOTUpdate_apply_targetWire]

/-- A wire outside the ordered control image is untouched by every logical edge. -/
theorem runEmbeddedCNOTUpdates_apply_of_not_control {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (edges : List (Fin controlCount × Fin controlCount))
    (input : Basis ambientWidth) (wire : Fin ambientWidth)
    (hwire : ∀ control, wire ≠ layout.controlWire control) :
    runEmbeddedCNOTUpdates layout edges input wire = input wire := by
  induction edges generalizing input with
  | nil => rfl
  | cons edge edges ih =>
      change runEmbeddedCNOTUpdates layout edges
          (embeddedCNOTUpdate layout edge.1 edge.2 input) wire = _
      rw [ih]
      exact embeddedCNOTUpdate_apply_of_ne layout edge.1 edge.2 input wire
        (hwire edge.2)

/-- Chronological circuit obtained from an ordered list of proved-valid logical edges. -/
def cnotEdgeCircuit {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (edges : List (ControlEdge controlCount)) : Circuit ambientWidth :=
  edges.map layout.cnotEdgePrimitive

/-- Forget proof fields from an ordered valid-edge list. -/
def controlEdgePairs {controlCount : ℕ} (edges : List (ControlEdge controlCount)) :
    List (Fin controlCount × Fin controlCount) :=
  edges.map ControlEdge.toPair

@[simp]
theorem length_cnotEdgeCircuit {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (edges : List (ControlEdge controlCount)) :
    (cnotEdgeCircuit layout edges).length = edges.length := by
  simp [cnotEdgeCircuit]

/-- Exact arbitrary-width basis action of any proved-valid logical CNOT edge circuit. -/
theorem eval_cnotEdgeCircuit_mulVec_basisKet {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (edges : List (ControlEdge controlCount)) (input : Basis ambientWidth) :
    (Circuit.eval (cnotEdgeCircuit layout edges) : Gate ambientWidth) *ᵥ
        basisKet input =
      basisKet
        (runEmbeddedCNOTUpdates layout (controlEdgePairs edges) input) := by
  induction edges generalizing input with
  | nil =>
      simp [cnotEdgeCircuit, controlEdgePairs]
  | cons edge edges ih =>
      simp only [cnotEdgeCircuit, controlEdgePairs, List.map_cons,
        Circuit.eval_cons, Submonoid.coe_mul]
      rw [← Matrix.mulVec_mulVec, OrderedControlLayout.cnotEdgePrimitive,
        cnotPrimitive_mulVec_basisKet layout edge.control edge.target edge.ne input]
      simpa only [cnotEdgeCircuit, controlEdgePairs, runEmbeddedCNOTUpdates,
        List.foldl_cons, ControlEdge.toPair_fst, ControlEdge.toPair_snd] using
        ih (embeddedCNOTUpdate layout edge.control edge.target input)

/-! ## The proved-valid generated CNOT circuit -/

/-- Attach the generated distinctness theorem to every raw Gray CNOT edge. -/
def certifiedGrayCNOTEdges (controlCount : ℕ) : List (ControlEdge controlCount) :=
  (grayCNOTEdges controlCount).attach.map fun edge =>
    { control := edge.1.1
      target := edge.1.2
      ne := grayCNOTEdges_wires_ne edge.2 }

@[simp]
theorem length_certifiedGrayCNOTEdges (controlCount : ℕ) :
    (certifiedGrayCNOTEdges controlCount).length = 2 ^ controlCount - 2 := by
  simp [certifiedGrayCNOTEdges]

/-- Forgetting proof fields recovers the exact generated edge schedule. -/
theorem controlEdgePairs_certifiedGrayCNOTEdges (controlCount : ℕ) :
    controlEdgePairs (certifiedGrayCNOTEdges controlCount) =
      grayCNOTEdges controlCount := by
  simpa [certifiedGrayCNOTEdges, controlEdgePairs, ControlEdge.toPair,
    List.map_map, Function.comp_def] using
    (List.attach_map_subtype_val (grayCNOTEdges controlCount))

/-- The CNOT-only syntax underlying the interleaved Gray construction. -/
def grayCNOTCircuit {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth) : Circuit ambientWidth :=
  cnotEdgeCircuit layout (certifiedGrayCNOTEdges controlCount)

@[simp]
theorem length_grayCNOTCircuit {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth) :
    (grayCNOTCircuit layout).length = 2 ^ controlCount - 2 := by
  simp [grayCNOTCircuit]

/-- The complete generated logical CNOT update restores the full ambient basis assignment. -/
theorem runEmbedded_grayCNOTEdges_eq_self {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (input : Basis ambientWidth) :
    runEmbeddedCNOTUpdates layout (grayCNOTEdges controlCount) input = input := by
  funext wire
  by_cases hcontrol : ∃ control, layout.controlWire control = wire
  · rcases hcontrol with ⟨control, rfl⟩
    have hrestricted := congrFun
      (restrictControls_runEmbeddedCNOTUpdates layout
        (grayCNOTEdges controlCount) input) control
    rw [runXorEdges_grayCNOTEdges] at hrestricted
    exact hrestricted
  · apply runEmbeddedCNOTUpdates_apply_of_not_control
    intro control heq
    exact hcontrol ⟨control, heq.symm⟩

/-- Exact arbitrary-width restoration action of the generated CNOT-only circuit. -/
theorem eval_grayCNOTCircuit_mulVec_basisKet {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (input : Basis ambientWidth) :
    (Circuit.eval (grayCNOTCircuit layout) : Gate ambientWidth) *ᵥ basisKet input =
      basisKet input := by
  rw [grayCNOTCircuit, eval_cnotEdgeCircuit_mulVec_basisKet,
    controlEdgePairs_certifiedGrayCNOTEdges, runEmbedded_grayCNOTEdges_eq_self]

end Barenco.MultiControl
