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

/-- Embedded logical CNOT updates execute sequentially across list concatenation. -/
theorem runEmbeddedCNOTUpdates_append {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (first second : List (Fin controlCount × Fin controlCount))
    (input : Basis ambientWidth) :
    runEmbeddedCNOTUpdates layout (first ++ second) input =
      runEmbeddedCNOTUpdates layout second
        (runEmbeddedCNOTUpdates layout first input) := by
  simp [runEmbeddedCNOTUpdates, List.foldl_append]

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

/-! ## The interleaved controlled-root circuit -/

/-- Signed exponent contributed by the first `count` Gray masks. -/
def grayExponentPrefix (controlCount count : ℕ) (bits : Fin controlCount → Bool) : ℤ :=
  (((grayCode controlCount).take count).map
    (fun mask => signedParityContribution mask bits)).sum

@[simp]
theorem grayExponentPrefix_zero (controlCount : ℕ) (bits : Fin controlCount → Bool) :
    grayExponentPrefix controlCount 0 bits = 0 := by
  simp [grayExponentPrefix]

/-- Appending one indexed mask adds exactly its signed parity contribution. -/
theorem grayExponentPrefix_succ {controlCount index : ℕ}
    (hindex : index < (grayCode controlCount).length)
    (bits : Fin controlCount → Bool) :
    grayExponentPrefix controlCount (index + 1) bits =
      grayExponentPrefix controlCount index bits +
        signedParityContribution ((grayCode controlCount)[index]'hindex) bits := by
  unfold grayExponentPrefix
  rw [List.take_succ_eq_append_getElem hindex]
  simp only [List.map_append, List.map_singleton, List.sum_append,
    List.sum_singleton]

/-- Taking every Gray mask recovers the previously defined total exponent. -/
theorem grayExponentPrefix_length (controlCount : ℕ)
    (bits : Fin controlCount → Bool) :
    grayExponentPrefix controlCount (grayCode controlCount).length bits =
      grayExponentSum controlCount bits := by
  unfold grayExponentPrefix grayExponentSum
  rw [List.take_length]

private theorem grayPivot_index_lt_of_mask {controlCount index : ℕ}
    (hindex : index < (grayCode controlCount).length) :
    index < (grayPivots controlCount).length := by
  rw [length_grayPivots_eq_grayCode]
  exact hindex

/-- The controlled signed-root node associated to one indexed Gray mask. -/
def grayRootPrimitiveAt {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth) (V : QubitUnitary)
    (index : ℕ) (hindex : index < (grayCode controlCount).length) :
    Primitive ambientWidth :=
  layout.controlledTargetPrimitive
    ((grayPivots controlCount)[index]'(grayPivot_index_lt_of_mask hindex))
    (signedGrayRoot ((grayCode controlCount)[index]'hindex) V)

private theorem grayMask_index_lt_of_edge {controlCount index : ℕ}
    (hindex : index < (grayCNOTEdges controlCount).length) :
    index < (grayCode controlCount).length := by
  rw [length_grayCNOTEdges] at hindex
  rw [length_grayCode]
  omega

/--
One chronological root/CNOT pair: apply the root for mask `index`, then advance
the parity accumulator to the next mask.
-/
def grayTransitionPair {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth) (V : QubitUnitary)
    (index : ℕ) (hindex : index < (grayCNOTEdges controlCount).length) :
    Circuit ambientWidth :=
  let edge := (grayCNOTEdges controlCount)[index]'hindex
  [grayRootPrimitiveAt layout V index (grayMask_index_lt_of_edge hindex),
    layout.cnotPrimitive edge.1 edge.2 (grayCNOTEdges_getElem_ne hindex)]

/--
The first `count` root/CNOT pairs, with the bound carried in the constructor so
every indexed primitive is certified by construction.
-/
def grayTransitionPrefixCircuit {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth) (V : QubitUnitary) :
    (count : ℕ) → count ≤ (grayCNOTEdges controlCount).length → Circuit ambientWidth
  | 0, _ => []
  | count + 1, hcount =>
      Circuit.append
        (grayTransitionPrefixCircuit layout V count (by omega))
        (grayTransitionPair layout V count (by omega))

private theorem grayFinalMask_index_lt (tail : ℕ) :
    (grayCNOTEdges (tail + 1)).length < (grayCode (tail + 1)).length := by
  rw [length_grayCNOTEdges, length_grayCode]
  have hpow : 0 < 2 ^ (tail + 1) := pow_pos (by omega) _
  omega

/--
The complete chronological Gray construction for `tail + 1` controls: every
nonfinal root is followed by its generated CNOT, and the last root stands alone.

The positive-control indexing makes the useful boundary explicit. `tail = 0`
is the ordinary one-control construction; the zero-control local-gate case is a
different base circuit.
-/
def grayControlledViaRootCircuit {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth) (V : QubitUnitary) :
    Circuit ambientWidth :=
  Circuit.append
    (grayTransitionPrefixCircuit layout V
      (grayCNOTEdges (tail + 1)).length le_rfl)
    [grayRootPrimitiveAt layout V (grayCNOTEdges (tail + 1)).length
      (grayFinalMask_index_lt tail)]

/-- Ambient basis assignment after the first `count` generated Gray CNOTs. -/
def embeddedGrayPrefixState {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (count : ℕ) (input : Basis ambientWidth) : Basis ambientWidth :=
  runEmbeddedCNOTUpdates layout ((grayCNOTEdges controlCount).take count) input

/--
Before root node `index`, its pivot control wire contains exactly the XOR parity
of the indexed Gray mask in the original control assignment.
-/
theorem embeddedGrayPrefixState_apply_pivot {tail ambientWidth index : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth)
    (input : Basis ambientWidth)
    (hindex : index < (grayCode (tail + 1)).length) :
    embeddedGrayPrefixState layout index input
        (layout.controlWire
          ((grayPivots (tail + 1))[index]'
            (grayPivot_index_lt_of_mask hindex))) =
      xorParity ((grayCode (tail + 1))[index]'hindex)
        (layout.restrictControls input) := by
  let pivot :=
    (grayPivots (tail + 1))[index]'(grayPivot_index_lt_of_mask hindex)
  have hrestrict := congrFun
    (restrictControls_runEmbeddedCNOTUpdates layout
      ((grayCNOTEdges (tail + 1)).take index) input) pivot
  have hinvariant := runXorEdges_take_grayCNOTEdges
    (width := tail + 1) (count := index) (by omega) hindex
    (layout.restrictControls input)
  rw [hinvariant] at hrestrict
  simpa [embeddedGrayPrefixState, pivot] using hrestrict

/--
One indexed controlled root left-multiplies the accumulated target power by its
signed parity contribution. The hypothesis exposes exactly the classical
control fact supplied by the Gray prefix invariant.
-/
theorem grayRootPrimitiveAt_mulVec_zpow_basisKet
    {controlCount ambientWidth index : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth) (V : QubitUnitary)
    (hindex : index < (grayCode controlCount).length)
    (bits : Fin controlCount → Bool) (exponent : ℤ)
    (input : Basis ambientWidth)
    (hcontrol :
      input
          (layout.controlWire
            ((grayPivots controlCount)[index]'
              (grayPivot_index_lt_of_mask hindex))) =
        xorParity ((grayCode controlCount)[index]'hindex) bits) :
    ((grayRootPrimitiveAt layout V index hindex).denotation : Gate ambientWidth) *ᵥ
        (localRaw layout.targetWire
            ((V ^ exponent : QubitUnitary) : QubitMatrix) *ᵥ basisKet input) =
      localRaw layout.targetWire
          (((V ^
              (signedParityContribution
                ((grayCode controlCount)[index]'hindex) bits + exponent) :
              QubitUnitary) : QubitMatrix)) *ᵥ basisKet input := by
  rw [grayRootPrimitiveAt,
    controlledTargetPrimitive_mulVec_localRaw_basisKet, hcontrol]
  let mask := (grayCode controlCount)[index]'hindex
  let contribution := signedParityContribution mask bits
  have hfactor :
      (if xorParity mask bits then
          (signedGrayRoot mask V : QubitMatrix) else 1) =
        ((V ^ contribution : QubitUnitary) : QubitMatrix) := by
    simpa [mask, contribution] using congrArg
      (fun W : QubitUnitary => (W : QubitMatrix))
      (signedGrayRoot_factor mask V bits)
  have hpowers :
      ((V ^ contribution : QubitUnitary) : QubitMatrix) *
          ((V ^ exponent : QubitUnitary) : QubitMatrix) =
        ((V ^ (contribution + exponent) : QubitUnitary) : QubitMatrix) := by
    exact congrArg Subtype.val (zpow_add V contribution exponent).symm
  rw [hfactor, hpowers]

/-- One more generated edge advances the ambient prefix state definitionally. -/
theorem embeddedGrayPrefixState_succ {controlCount ambientWidth index : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (input : Basis ambientWidth)
    (hindex : index < (grayCNOTEdges controlCount).length) :
    embeddedGrayPrefixState layout (index + 1) input =
      embeddedCNOTUpdate layout
        ((grayCNOTEdges controlCount)[index]'hindex).1
        ((grayCNOTEdges controlCount)[index]'hindex).2
        (embeddedGrayPrefixState layout index input) := by
  rw [embeddedGrayPrefixState, embeddedGrayPrefixState,
    List.take_succ_eq_append_getElem hindex,
    runEmbeddedCNOTUpdates_append]
  rfl

end Barenco.MultiControl
