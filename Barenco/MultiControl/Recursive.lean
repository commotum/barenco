import Barenco.MultiControl.Layout
import Barenco.ControlledCircuit.Block
import Barenco.OneQubit.Roots
import Barenco.Cost

/-!
# Barenco Lemma 7.5: one recursive multi-control step

This module reconstructs the five-macro circuit from Lemma 7.5 on an ordered
family of controls embedded in an arbitrary ambient register.  For `prefix + 1`
controls, write `c` for the final ordered control.  The chronological circuit is

`C(c,V,target); MCX(prefix,c); C(c,V⁻¹,target); MCX(prefix,c);`
`MC-V(prefix,target)`.

The theorem is uniform at `prefix = 0`: the two empty-controlled X macros are
local X gates on `c`, and the final empty-controlled `V` macro is local on the
target.  A genuinely zero-control target gate is exposed separately as a local
base circuit.

All five nodes are retained as macros.  Consequently their structural count is
exact, but neither paper cost model accepts the unexpanded circuit.
-/

namespace Barenco.MultiControl

open Barenco.OneQubit
open Barenco.ControlledCircuit
open scoped Matrix

noncomputable section

attribute [local instance] Classical.propDecidable

namespace OrderedControlLayout

/-! ## Prefix and final-control projections -/

/-- The final ordered control wire in a nonempty control layout. -/
def lastControlWire {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth) : Fin ambientWidth :=
  layout.controlWire (Fin.last p)

/-- The first `prefix` controls, retaining the original target wire. -/
def prefixTargetLayout {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth) :
    OrderedControlLayout p ambientWidth where
  controlWire := Fin.castSuccEmb.trans layout.controlWire
  targetWire := layout.targetWire
  control_ne_target := fun control => layout.control_ne_target control.castSucc

/-- The first `prefix` controls, now targeting the final ordered control wire. -/
def prefixToLastLayout {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth) :
    OrderedControlLayout p ambientWidth where
  controlWire := Fin.castSuccEmb.trans layout.controlWire
  targetWire := layout.lastControlWire
  control_ne_target := fun control =>
    layout.controlWire_ne (Fin.castSucc_ne_last control)

@[simp]
theorem prefixTargetLayout_controlWire {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (control : Fin p) :
    layout.prefixTargetLayout.controlWire control =
      layout.controlWire control.castSucc := rfl

@[simp]
theorem prefixTargetLayout_targetWire {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth) :
    layout.prefixTargetLayout.targetWire = layout.targetWire := rfl

@[simp]
theorem prefixToLastLayout_controlWire {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (control : Fin p) :
    layout.prefixToLastLayout.controlWire control =
      layout.controlWire control.castSucc := rfl

@[simp]
theorem prefixToLastLayout_targetWire {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth) :
    layout.prefixToLastLayout.targetWire = layout.lastControlWire := rfl

@[simp]
theorem lastControlWire_ne_targetWire {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth) :
    layout.lastControlWire ≠ layout.targetWire :=
  layout.control_ne_target (Fin.last p)

/-! ## The five chronological macros -/

/-- A target gate controlled only by the final ordered control. -/
def lastControlledTarget {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (V : QubitUnitary) : Primitive ambientWidth :=
  Primitive.positiveControlled layout.targetWire
    ({⟨layout.lastControlWire, layout.lastControlWire_ne_targetWire⟩} :
      ControlSet layout.targetWire) V

/-- A prefix-controlled X whose target is the final ordered control. -/
def prefixControlledX {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth) :
    Primitive ambientWidth :=
  Primitive.positiveControlled layout.prefixToLastLayout.targetWire
    layout.prefixToLastLayout.controlSet pauliX

/-- A target gate controlled by all controls except the final ordered one. -/
def prefixControlledTarget {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (V : QubitUnitary) : Primitive ambientWidth :=
  Primitive.positiveControlled layout.targetWire
    layout.prefixTargetLayout.controlSet V

/-- The exact five-macro chronology of Barenco Lemma 7.5. -/
def recursiveViaSquareCircuit {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (V : QubitUnitary) : Circuit ambientWidth :=
  [layout.lastControlledTarget V,
    layout.prefixControlledX,
    layout.lastControlledTarget V⁻¹,
    layout.prefixControlledX,
    layout.prefixControlledTarget V]

/-- Lemma 7.5 specialized to the selected exact square root of `U`. -/
def recursiveRootCircuit {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (U : QubitUnitary) : Circuit ambientWidth :=
  layout.recursiveViaSquareCircuit (unitarySquareRoot U)

/-! ## Separate zero-control base -/

/-- A genuinely zero-control target gate is one local one-qubit primitive. -/
def zeroControlCircuit {ambientWidth : ℕ} (target : Fin ambientWidth)
    (U : QubitUnitary) : Circuit ambientWidth :=
  [Primitive.oneQubit target U]

@[simp]
theorem eval_zeroControlCircuit {ambientWidth : ℕ} (target : Fin ambientWidth)
    (U : QubitUnitary) :
    Circuit.eval (zeroControlCircuit target U) = localUnitary target U := by
  simp [zeroControlCircuit, Circuit.eval]

/-! ## Boolean action of the prefix-controlled X -/

/-- Every prefix control is true on a computational-basis assignment. -/
def prefixEnabled {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (input : Basis ambientWidth) : Prop :=
  ∀ control : Fin p, input (layout.controlWire control.castSucc) = true

/-- Toggle the final control exactly when all prefix controls are true. -/
def prefixXUpdate {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (input : Basis ambientWidth) : Basis ambientWidth :=
  if layout.prefixEnabled input then
    setTarget layout.lastControlWire input (!input layout.lastControlWire)
  else input

theorem prefixEnabled_iff_controlSet {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (input : Basis ambientWidth) :
    layout.prefixEnabled input ↔
      ∀ wire ∈ layout.prefixToLastLayout.controlSet, input wire = true := by
  rw [layout.prefixToLastLayout.all_controls_iff]
  rfl

@[simp]
theorem prefixXUpdate_apply_lastControlWire {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (input : Basis ambientWidth) :
    layout.prefixXUpdate input layout.lastControlWire =
      if layout.prefixEnabled input then !input layout.lastControlWire
      else input layout.lastControlWire := by
  by_cases henabled : layout.prefixEnabled input <;>
    simp [prefixXUpdate, henabled]

@[simp]
theorem prefixXUpdate_apply_of_ne {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (input : Basis ambientWidth) (wire : Fin ambientWidth)
    (hwire : wire ≠ layout.lastControlWire) :
    layout.prefixXUpdate input wire = input wire := by
  by_cases henabled : layout.prefixEnabled input <;>
    simp [prefixXUpdate, henabled, setTarget_apply_of_ne, hwire]

@[simp]
theorem prefixXUpdate_apply_targetWire {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (input : Basis ambientWidth) :
    layout.prefixXUpdate input layout.targetWire = input layout.targetWire := by
  exact layout.prefixXUpdate_apply_of_ne input layout.targetWire
    layout.lastControlWire_ne_targetWire.symm

@[simp]
theorem prefixEnabled_prefixXUpdate {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (input : Basis ambientWidth) :
    layout.prefixEnabled (layout.prefixXUpdate input) ↔
      layout.prefixEnabled input := by
  constructor
  · intro h control
    have hcontrol := h control
    rw [layout.prefixXUpdate_apply_of_ne] at hcontrol
    · exact hcontrol
    · exact layout.controlWire_ne (Fin.castSucc_ne_last control)
  · intro h control
    rw [layout.prefixXUpdate_apply_of_ne]
    · exact h control
    · exact layout.controlWire_ne (Fin.castSucc_ne_last control)

@[simp]
theorem prefixXUpdate_involutive {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (input : Basis ambientWidth) :
    layout.prefixXUpdate (layout.prefixXUpdate input) = input := by
  by_cases henabled : layout.prefixEnabled input
  · have henabled' : layout.prefixEnabled (layout.prefixXUpdate input) :=
      (layout.prefixEnabled_prefixXUpdate input).2 henabled
    rw [prefixXUpdate, if_pos henabled', prefixXUpdate, if_pos henabled]
    funext wire
    by_cases hwire : wire = layout.lastControlWire
    · subst wire
      simp
    · simp [setTarget_apply_of_ne, hwire]
  · have henabled' : ¬layout.prefixEnabled (layout.prefixXUpdate input) := by
      exact fun h => henabled ((layout.prefixEnabled_prefixXUpdate input).1 h)
    rw [prefixXUpdate, if_neg henabled', prefixXUpdate, if_neg henabled]

/-- Exact full-register basis action of the prefix-controlled X macro. -/
@[simp]
theorem prefixControlledX_denotation_mulVec_basisKet {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (input : Basis ambientWidth) :
    (layout.prefixControlledX.denotation : Gate ambientWidth) *ᵥ basisKet input =
      basisKet (layout.prefixXUpdate input) := by
  rw [prefixControlledX, Primitive.positiveControlled_denotation_val,
    positiveControlledRaw_truthTable]
  have hall := layout.prefixToLastLayout.all_controls_iff input
  by_cases henabled : layout.prefixEnabled input
  · have hcontrols : ∀ control,
        layout.prefixToLastLayout.restrictControls input control = true :=
      henabled
    rw [if_pos (hall.mpr hcontrols)]
    simpa [prefixXUpdate, henabled, xRaw] using
      xRaw_mulVec_basisKet layout.lastControlWire input
  · have hcontrols : ¬∀ control,
        layout.prefixToLastLayout.restrictControls input control = true :=
      henabled
    rw [if_neg (fun h => hcontrols (hall.mp h))]
    simp [prefixXUpdate, henabled]

/-! ## Target-local state transport -/

/-- Expand one target-local basis column over its two possible target bits. -/
private theorem localRaw_mulVec_basisKet_eq_sum {ambientWidth : ℕ}
    (target : Fin ambientWidth) (A : QubitMatrix) (input : Basis ambientWidth) :
    localRaw target A *ᵥ basisKet input =
      ∑ bit : Bool,
        A bit (input target) • basisKet (setTarget target input bit) := by
  rw [localRaw_mulVec_basisKet]
  funext row
  by_cases hagree : AgreeOff target row input
  · rw [if_pos hagree]
    have heq : ∀ bit : Bool,
        row = setTarget target input bit ↔ row target = bit := by
      intro bit
      exact (eq_setTarget_iff target input row bit).trans (and_iff_right hagree)
    cases hrow : row target <;>
      simp [basisKet_apply, heq, hrow]
  · rw [if_neg hagree]
    have hne : ∀ bit : Bool, row ≠ setTarget target input bit := by
      intro bit hrow
      apply hagree
      rw [hrow]
      intro wire hwire
      exact setTarget_apply_of_ne target input bit wire hwire
    simp [basisKet_apply, hne]

private theorem prefixEnabled_setTarget_targetWire {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (input : Basis ambientWidth) (bit : Bool) :
    layout.prefixEnabled (setTarget layout.targetWire input bit) ↔
      layout.prefixEnabled input := by
  constructor
  · intro h control
    simpa [prefixEnabled, layout.control_ne_target control.castSucc] using h control
  · intro h control
    simpa [prefixEnabled, layout.control_ne_target control.castSucc] using h control

private theorem prefixXUpdate_setTarget_targetWire {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (input : Basis ambientWidth) (bit : Bool) :
    layout.prefixXUpdate (setTarget layout.targetWire input bit) =
      setTarget layout.targetWire (layout.prefixXUpdate input) bit := by
  funext wire
  by_cases henabled : layout.prefixEnabled input
  · have henabled' :
        layout.prefixEnabled (setTarget layout.targetWire input bit) :=
      (prefixEnabled_setTarget_targetWire layout input bit).2 henabled
    by_cases hlast : wire = layout.lastControlWire
    · subst wire
      simp [prefixXUpdate, henabled, henabled',
        layout.lastControlWire_ne_targetWire]
    · by_cases htarget : wire = layout.targetWire
      · subst wire
        simp
      · simp [prefixXUpdate, henabled, henabled', hlast, htarget]
  · have henabled' :
        ¬layout.prefixEnabled (setTarget layout.targetWire input bit) :=
      fun h => henabled ((prefixEnabled_setTarget_targetWire layout input bit).1 h)
    rw [prefixXUpdate, if_neg henabled', prefixXUpdate, if_neg henabled]

/-- Prefix-controlled X commutes with arbitrary state evolution on the final target. -/
theorem prefixControlledX_denotation_mulVec_localRaw_basisKet
    {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (A : QubitMatrix) (input : Basis ambientWidth) :
    (layout.prefixControlledX.denotation : Gate ambientWidth) *ᵥ
        (localRaw layout.targetWire A *ᵥ basisKet input) =
      localRaw layout.targetWire A *ᵥ
        basisKet (layout.prefixXUpdate input) := by
  rw [localRaw_mulVec_basisKet_eq_sum, Matrix.mulVec_sum]
  simp_rw [Matrix.mulVec_smul,
    layout.prefixControlledX_denotation_mulVec_basisKet]
  rw [localRaw_mulVec_basisKet_eq_sum]
  simp only [prefixXUpdate_apply_targetWire]
  apply Finset.sum_congr rfl
  intro bit _
  rw [prefixXUpdate_setTarget_targetWire]

/-- A final-control target macro left-multiplies the current target-local state. -/
theorem lastControlledTarget_denotation_mulVec_localRaw_basisKet
    {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (U : QubitUnitary) (A : QubitMatrix) (input : Basis ambientWidth) :
    (layout.lastControlledTarget U).denotation *ᵥ
        (localRaw layout.targetWire A *ᵥ basisKet input) =
      localRaw layout.targetWire
          ((if input layout.lastControlWire then (U : QubitMatrix) else 1) * A) *ᵥ
        basisKet input := by
  rw [Matrix.mulVec_mulVec, lastControlledTarget,
    Primitive.positiveControlled_denotation_val,
    positiveControlledRaw_singleton_eq_targetBlockRaw,
    localRaw_eq_targetBlockRaw, targetBlockRaw_mul,
    targetBlockRaw_mulVec_basisKet]
  rfl

/-- The prefix-controlled target macro left-multiplies the current local state. -/
theorem prefixControlledTarget_denotation_mulVec_localRaw_basisKet
    {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (U : QubitUnitary) (A : QubitMatrix) (input : Basis ambientWidth) :
    (layout.prefixControlledTarget U).denotation *ᵥ
        (localRaw layout.targetWire A *ᵥ basisKet input) =
      localRaw layout.targetWire
          ((if layout.prefixEnabled input then (U : QubitMatrix) else 1) * A) *ᵥ
        basisKet input := by
  rw [Matrix.mulVec_mulVec, prefixControlledTarget,
    Primitive.positiveControlled_denotation_val,
    positiveControlledRaw, controlledRaw_eq_targetBlockRaw,
    localRaw_eq_targetBlockRaw]
  change ((targetBlockRaw layout.targetWire (fun rest =>
      if positiveControlsEnabled layout.prefixTargetLayout.controlSet rest
      then (U : QubitMatrix) else 1) *
      targetBlockRaw layout.targetWire (fun _ => A)) *ᵥ basisKet input) = _
  rw [targetBlockRaw_mul, targetBlockRaw_mulVec_basisKet]
  congr 2
  congr 1
  have hall := layout.prefixTargetLayout.all_controls_iff input
  by_cases henabled : layout.prefixEnabled input
  · rw [if_pos henabled]
    have hcontrols : ∀ control,
        layout.prefixTargetLayout.restrictControls input control = true :=
      henabled
    rw [show positiveControlsEnabled layout.prefixTargetLayout.controlSet
        (splitTarget layout.targetWire input).2 = true from
      (positiveControlsEnabled_splitTarget_eq_true_iff _ _).2
        (hall.mpr hcontrols)]
    rfl
  · rw [if_neg henabled]
    have hcontrols : ¬∀ control,
        layout.prefixTargetLayout.restrictControls input control = true :=
      henabled
    have hnot : positiveControlsEnabled layout.prefixTargetLayout.controlSet
        (splitTarget layout.targetWire input).2 = false := by
      cases hvalue : positiveControlsEnabled layout.prefixTargetLayout.controlSet
          (splitTarget layout.targetWire input).2
      · rfl
      · exact (hcontrols (hall.mp
          ((positiveControlsEnabled_splitTarget_eq_true_iff _ _).1 hvalue))).elim
    rw [hnot]
    simp

/-! ## Exact five-block evaluator -/

/-- The target-qubit product selected on one ambient basis assignment. -/
def recursiveTargetProduct {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (V : QubitUnitary) (input : Basis ambientWidth) : QubitMatrix :=
  (if layout.prefixEnabled input then (V : QubitMatrix) else 1) *
    ((if layout.prefixXUpdate input layout.lastControlWire then
        ((V⁻¹ : QubitUnitary) : QubitMatrix) else 1) *
      (if input layout.lastControlWire then (V : QubitMatrix) else 1))

/-- The five selected target factors collapse to `V²` exactly when all controls hold. -/
theorem recursiveTargetProduct_eq {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (V : QubitUnitary) (input : Basis ambientWidth) :
    layout.recursiveTargetProduct V input =
      if layout.prefixEnabled input ∧ input layout.lastControlWire = true then
        (V ^ 2 : QubitUnitary)
      else 1 := by
  have hstar_mul : star (V : QubitMatrix) * (V : QubitMatrix) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp V.prop
  have hmul_star : (V : QubitMatrix) * star (V : QubitMatrix) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp V.prop
  by_cases henabled : layout.prefixEnabled input <;>
    cases hlast : input layout.lastControlWire <;>
      simp [recursiveTargetProduct, henabled, hlast, pow_two,
        hstar_mul, hmul_star]

/-- The original ordered control set is the prefix condition plus the final bit. -/
theorem all_controls_iff_prefixEnabled_and_last {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (input : Basis ambientWidth) :
    (∀ wire ∈ layout.controlSet, input wire = true) ↔
      layout.prefixEnabled input ∧ input layout.lastControlWire = true := by
  rw [layout.all_controls_iff]
  change (∀ control : Fin (p + 1),
      input (layout.controlWire control) = true) ↔ _
  rw [Fin.forall_fin_succ']
  rfl

/-- Full-register raw product of the five chronological macro nodes. -/
theorem eval_recursiveViaSquareCircuit_raw {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (V : QubitUnitary) :
    (Circuit.eval (layout.recursiveViaSquareCircuit V) : Gate ambientWidth) =
      (layout.prefixControlledTarget V).denotation *
        layout.prefixControlledX.denotation *
        (layout.lastControlledTarget V⁻¹).denotation *
        layout.prefixControlledX.denotation *
        (layout.lastControlledTarget V).denotation := by
  simp [recursiveViaSquareCircuit, Circuit.eval]

private theorem localRaw_one {ambientWidth : ℕ} (target : Fin ambientWidth) :
    localRaw target (1 : QubitMatrix) = 1 := by
  rw [localRaw_eq_targetBlockRaw, targetBlockRaw_one]

private theorem lastControlledTarget_denotation_mulVec_basisKet
    {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (U : QubitUnitary) (input : Basis ambientWidth) :
    (layout.lastControlledTarget U).denotation *ᵥ basisKet input =
      localRaw layout.targetWire
          (if input layout.lastControlWire then (U : QubitMatrix) else 1) *ᵥ
        basisKet input := by
  simpa [localRaw_one] using
    layout.lastControlledTarget_denotation_mulVec_localRaw_basisKet
      U (1 : QubitMatrix) input

/-- Exact basis-column action of the five chronological macro nodes. -/
theorem eval_recursiveViaSquareCircuit_mulVec_basisKet {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (V : QubitUnitary) (input : Basis ambientWidth) :
    (Circuit.eval (layout.recursiveViaSquareCircuit V) : Gate ambientWidth) *ᵥ
        basisKet input =
      localRaw layout.targetWire (layout.recursiveTargetProduct V input) *ᵥ
        basisKet input := by
  rw [eval_recursiveViaSquareCircuit_raw]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [layout.lastControlledTarget_denotation_mulVec_basisKet]
  rw [layout.prefixControlledX_denotation_mulVec_localRaw_basisKet]
  rw [layout.lastControlledTarget_denotation_mulVec_localRaw_basisKet]
  rw [layout.prefixControlledX_denotation_mulVec_localRaw_basisKet]
  rw [layout.prefixXUpdate_involutive]
  rw [layout.prefixControlledTarget_denotation_mulVec_localRaw_basisKet]
  rfl

/-- Lemma 7.5: the five-macro step implements full positive control of `V²`. -/
theorem eval_recursiveViaSquareCircuit_pow_two {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (V : QubitUnitary) :
    Circuit.eval (layout.recursiveViaSquareCircuit V) =
      positiveControlledUnitary layout.targetWire layout.controlSet (V ^ 2) := by
  apply Subtype.ext
  rw [matrix_eq_iff_mulVec_basisKet_eq]
  intro input
  rw [eval_recursiveViaSquareCircuit_mulVec_basisKet,
    recursiveTargetProduct_eq, coe_positiveControlledUnitary,
    positiveControlledRaw_truthTable]
  by_cases hall : ∀ wire ∈ layout.controlSet, input wire = true
  · have henabledLast :
        layout.prefixEnabled input ∧ input layout.lastControlWire = true :=
      (layout.all_controls_iff_prefixEnabled_and_last input).1 hall
    rw [if_pos hall, if_pos henabledLast]
  · have hnotEnabledLast :
        ¬(layout.prefixEnabled input ∧ input layout.lastControlWire = true) :=
      fun h => hall ((layout.all_controls_iff_prefixEnabled_and_last input).2 h)
    rw [if_neg hall, if_neg hnotEnabledLast, localRaw_one, Matrix.one_mulVec]

/-- Parameterized Lemma 7.5 for any explicitly supplied square witness. -/
theorem eval_recursiveViaSquareCircuit_of_sq_eq {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (U V : QubitUnitary) (hV : V ^ 2 = U) :
    Circuit.eval (layout.recursiveViaSquareCircuit V) =
      positiveControlledUnitary layout.targetWire layout.controlSet U := by
  rw [eval_recursiveViaSquareCircuit_pow_two, hV]

/-- Lemma 7.5 using the library's selected exact unitary square root. -/
@[simp]
theorem eval_recursiveRootCircuit {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (U : QubitUnitary) :
    Circuit.eval (layout.recursiveRootCircuit U) =
      positiveControlledUnitary layout.targetWire layout.controlSet U := by
  rw [recursiveRootCircuit, eval_recursiveViaSquareCircuit_pow_two,
    unitarySquareRoot_pow_two]

/-! ## Structural macro resources -/

@[simp]
theorem recursiveViaSquareCircuit_gateCount {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (V : QubitUnitary) :
    Circuit.gateCount (layout.recursiveViaSquareCircuit V) = 5 := by
  rfl

/--
Exact kind accounting without pretending the arities `1` and `p` are distinct.
At `p = 1` the two summands deliberately combine to five occurrences.
-/
theorem recursiveViaSquareCircuit_kindCount {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (V : QubitUnitary) (kind : PrimitiveKind) :
    Circuit.kindCount kind (layout.recursiveViaSquareCircuit V) =
      (if kind = .controlledOneQubit 1 then 2 else 0) +
        (if kind = .controlledOneQubit p then 3 else 0) := by
  simp [recursiveViaSquareCircuit, lastControlledTarget, prefixControlledX,
    prefixControlledTarget, Circuit.kindCount]

/-- The Section 3–7 model rejects the five unexpanded controlled macros. -/
@[simp]
theorem recursiveViaSquareCircuit_oneQubitCNOTCost {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (V : QubitUnitary) :
    Circuit.cost CostModel.oneQubitCNOT
      (layout.recursiveViaSquareCircuit V) = none := by
  simp [recursiveViaSquareCircuit, lastControlledTarget, prefixControlledX,
    prefixControlledTarget, Circuit.cost, Circuit.addCost]

/-- The later at-most-two-qubit model also rejects these unexpanded macros. -/
@[simp]
theorem recursiveViaSquareCircuit_arbitraryTwoQubitCost {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (V : QubitUnitary) :
    Circuit.cost CostModel.arbitraryTwoQubit
      (layout.recursiveViaSquareCircuit V) = none := by
  simp [recursiveViaSquareCircuit, lastControlledTarget, prefixControlledX,
    prefixControlledTarget, Circuit.cost, Circuit.addCost]

@[simp]
theorem zeroControlCircuit_gateCount {ambientWidth : ℕ}
    (target : Fin ambientWidth) (U : QubitUnitary) :
    Circuit.gateCount (zeroControlCircuit target U) = 1 := by
  rfl

@[simp]
theorem zeroControlCircuit_oneQubitCNOTCost {ambientWidth : ℕ}
    (target : Fin ambientWidth) (U : QubitUnitary) :
    Circuit.cost CostModel.oneQubitCNOT (zeroControlCircuit target U) = some 1 := by
  simp [zeroControlCircuit, Circuit.cost, Circuit.addCost]

/-! ## Five-way substitution for later recursive expansion -/

/--
Substitute five independently selected implementations into the Lemma 7.5
chronology.  The parameters remain distinct so later expansion may coordinate
or optimize each occurrence separately.
-/
def recursiveSubstitutionCircuit {ambientWidth : ℕ}
    (firstTarget firstPrefixX inverseTarget secondPrefixX residualTarget :
      Circuit ambientWidth) : Circuit ambientWidth :=
  firstTarget ++ firstPrefixX ++ inverseTarget ++ secondPrefixX ++ residualTarget

/-- The evaluator of a five-way substitution is the expected reverse product. -/
theorem eval_recursiveSubstitutionCircuit {ambientWidth : ℕ}
    (firstTarget firstPrefixX inverseTarget secondPrefixX residualTarget :
      Circuit ambientWidth) :
    Circuit.eval (recursiveSubstitutionCircuit firstTarget firstPrefixX
      inverseTarget secondPrefixX residualTarget) =
      Circuit.eval residualTarget * Circuit.eval secondPrefixX *
        Circuit.eval inverseTarget * Circuit.eval firstPrefixX *
          Circuit.eval firstTarget := by
  simp [recursiveSubstitutionCircuit, Circuit.eval_append, mul_assoc]

/-- Checked five-way substitution preserves the five-macro evaluator exactly. -/
theorem eval_recursiveSubstitutionCircuit_of_eq {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (V : QubitUnitary)
    (firstTarget firstPrefixX inverseTarget secondPrefixX residualTarget :
      Circuit ambientWidth)
    (hfirstTarget : Circuit.eval firstTarget =
      (layout.lastControlledTarget V).denotation)
    (hfirstPrefixX : Circuit.eval firstPrefixX =
      layout.prefixControlledX.denotation)
    (hinverseTarget : Circuit.eval inverseTarget =
      (layout.lastControlledTarget V⁻¹).denotation)
    (hsecondPrefixX : Circuit.eval secondPrefixX =
      layout.prefixControlledX.denotation)
    (hresidualTarget : Circuit.eval residualTarget =
      (layout.prefixControlledTarget V).denotation) :
    Circuit.eval (recursiveSubstitutionCircuit firstTarget firstPrefixX
      inverseTarget secondPrefixX residualTarget) =
      Circuit.eval (layout.recursiveViaSquareCircuit V) := by
  rw [eval_recursiveSubstitutionCircuit, hfirstTarget, hfirstPrefixX,
    hinverseTarget, hsecondPrefixX, hresidualTarget]
  apply Subtype.ext
  exact (eval_recursiveViaSquareCircuit_raw layout V).symm

/-- A checked five-way substitution therefore implements full control of `V²`. -/
theorem eval_recursiveSubstitutionCircuit_pow_two {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (V : QubitUnitary)
    (firstTarget firstPrefixX inverseTarget secondPrefixX residualTarget :
      Circuit ambientWidth)
    (hfirstTarget : Circuit.eval firstTarget =
      (layout.lastControlledTarget V).denotation)
    (hfirstPrefixX : Circuit.eval firstPrefixX =
      layout.prefixControlledX.denotation)
    (hinverseTarget : Circuit.eval inverseTarget =
      (layout.lastControlledTarget V⁻¹).denotation)
    (hsecondPrefixX : Circuit.eval secondPrefixX =
      layout.prefixControlledX.denotation)
    (hresidualTarget : Circuit.eval residualTarget =
      (layout.prefixControlledTarget V).denotation) :
    Circuit.eval (recursiveSubstitutionCircuit firstTarget firstPrefixX
      inverseTarget secondPrefixX residualTarget) =
      positiveControlledUnitary layout.targetWire layout.controlSet (V ^ 2) := by
  rw [eval_recursiveSubstitutionCircuit_of_eq layout V firstTarget firstPrefixX
    inverseTarget secondPrefixX residualTarget hfirstTarget hfirstPrefixX
    hinverseTarget hsecondPrefixX hresidualTarget,
    eval_recursiveViaSquareCircuit_pow_two]

theorem recursiveSubstitutionCircuit_gateCount {ambientWidth : ℕ}
    (firstTarget firstPrefixX inverseTarget secondPrefixX residualTarget :
      Circuit ambientWidth) :
    Circuit.gateCount (recursiveSubstitutionCircuit firstTarget firstPrefixX
      inverseTarget secondPrefixX residualTarget) =
      Circuit.gateCount firstTarget + Circuit.gateCount firstPrefixX +
        Circuit.gateCount inverseTarget + Circuit.gateCount secondPrefixX +
          Circuit.gateCount residualTarget := by
  simp [recursiveSubstitutionCircuit, Circuit.gateCount_append]

theorem recursiveSubstitutionCircuit_kindCount {ambientWidth : ℕ}
    (kind : PrimitiveKind)
    (firstTarget firstPrefixX inverseTarget secondPrefixX residualTarget :
      Circuit ambientWidth) :
    Circuit.kindCount kind (recursiveSubstitutionCircuit firstTarget firstPrefixX
      inverseTarget secondPrefixX residualTarget) =
      Circuit.kindCount kind firstTarget + Circuit.kindCount kind firstPrefixX +
        Circuit.kindCount kind inverseTarget +
          Circuit.kindCount kind secondPrefixX +
            Circuit.kindCount kind residualTarget := by
  simp [recursiveSubstitutionCircuit, Circuit.kindCount_append]

/-- Exact partial-cost composition, retaining unsupported components as `none`. -/
theorem recursiveSubstitutionCircuit_cost {ambientWidth : ℕ}
    (model : CostModel)
    (firstTarget firstPrefixX inverseTarget secondPrefixX residualTarget :
      Circuit ambientWidth) :
    Circuit.cost model (recursiveSubstitutionCircuit firstTarget firstPrefixX
      inverseTarget secondPrefixX residualTarget) =
      Circuit.addCost
        (Circuit.addCost
          (Circuit.addCost
            (Circuit.addCost (Circuit.cost model firstTarget)
              (Circuit.cost model firstPrefixX))
            (Circuit.cost model inverseTarget))
          (Circuit.cost model secondPrefixX))
        (Circuit.cost model residualTarget) := by
  simp [recursiveSubstitutionCircuit, Circuit.cost_append,
    Circuit.addCost_assoc]

/-- Additive accepted cost when all five supplied implementations are priced. -/
theorem recursiveSubstitutionCircuit_cost_of_eq {ambientWidth : ℕ}
    (model : CostModel)
    (firstTarget firstPrefixX inverseTarget secondPrefixX residualTarget :
      Circuit ambientWidth)
    (firstCost firstXCost inverseCost secondXCost residualCost : ℕ)
    (hfirst : Circuit.cost model firstTarget = some firstCost)
    (hfirstX : Circuit.cost model firstPrefixX = some firstXCost)
    (hinverse : Circuit.cost model inverseTarget = some inverseCost)
    (hsecondX : Circuit.cost model secondPrefixX = some secondXCost)
    (hresidual : Circuit.cost model residualTarget = some residualCost) :
    Circuit.cost model (recursiveSubstitutionCircuit firstTarget firstPrefixX
      inverseTarget secondPrefixX residualTarget) =
      some (firstCost + firstXCost + inverseCost + secondXCost + residualCost) := by
  rw [recursiveSubstitutionCircuit_cost, hfirst, hfirstX, hinverse, hsecondX,
    hresidual]
  rfl

end OrderedControlLayout

end

end Barenco.MultiControl
