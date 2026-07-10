import Barenco.MultiControl.Recursive
import Barenco.State.CleanWire
import Barenco.Cost

/-!
# Barenco Lemma 7.11: one clean auxiliary wire

An `OrderedControlLayout (p + 1) ambientWidth` is interpreted here with the first
`p` controls as data controls, the final ordered control as the auxiliary, and
the ordinary layout target as the unitary target.  The exact chronology is

`MCX(data,aux); C(aux,U,target); MCX(data,aux)`.

The circuit restores either classical value of the auxiliary, but its target
gate fires according to the intermediate value
`aux xor conjunction(data)`.  Consequently the desired controlled-`U` semantics
is proved on the literal clean-zero subspace, not as equality of full-register
unitaries.  The state theorem quantifies arbitrary data and spectator amplitudes
and concludes exact output factorization through `cleanZeroLinearEquiv`.
-/

namespace Barenco.MultiControl

open Barenco.ControlledCircuit
open scoped Matrix

noncomputable section

attribute [local instance] Classical.propDecidable

namespace OrderedControlLayout

/-- The final ordered control, interpreted as the clean auxiliary wire. -/
abbrev cleanAncillaWire {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth) : Fin ambientWidth :=
  layout.lastControlWire

/-- The first `p` ordered controls acting on the original target. -/
abbrev cleanDataLayout {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth) :
    OrderedControlLayout p ambientWidth :=
  layout.prefixTargetLayout

/-- Exact three-macro chronology of Lemma 7.11. -/
def cleanAncillaCircuit {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (U : QubitUnitary) : Circuit ambientWidth :=
  [layout.prefixControlledX,
    layout.lastControlledTarget U,
    layout.prefixControlledX]

/-- The target block selected after the first compute-MCX. -/
def cleanAncillaTargetProduct {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (U : QubitUnitary) (input : Basis ambientWidth) : QubitMatrix :=
  if layout.prefixXUpdate input layout.cleanAncillaWire then
    (U : QubitMatrix)
  else 1

/-- Direct full-register product of the three chronological macro nodes. -/
theorem eval_cleanAncillaCircuit_raw {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (U : QubitUnitary) :
    (Circuit.eval (layout.cleanAncillaCircuit U) : Gate ambientWidth) =
      layout.prefixControlledX.denotation *
        (layout.lastControlledTarget U).denotation *
          layout.prefixControlledX.denotation := by
  simp [cleanAncillaCircuit, Circuit.eval]

private theorem localRaw_one {ambientWidth : ℕ} (target : Fin ambientWidth) :
    localRaw target (1 : QubitMatrix) = 1 := by
  rw [localRaw_eq_targetBlockRaw, targetBlockRaw_one]

private theorem lastControlledTarget_denotation_mulVec_basisKet
    {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (U : QubitUnitary) (input : Basis ambientWidth) :
    (layout.lastControlledTarget U).denotation *ᵥ basisKet input =
      localRaw layout.targetWire
          (if input layout.cleanAncillaWire then (U : QubitMatrix) else 1) *ᵥ
        basisKet input := by
  simpa [localRaw_one] using
    layout.lastControlledTarget_denotation_mulVec_localRaw_basisKet
      U (1 : QubitMatrix) input

/--
Exact arbitrary-basis action: the target condition uses the computed auxiliary,
while the second MCX restores the original complete basis assignment.
-/
theorem eval_cleanAncillaCircuit_mulVec_basisKet {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (U : QubitUnitary) (input : Basis ambientWidth) :
    (Circuit.eval (layout.cleanAncillaCircuit U) : Gate ambientWidth) *ᵥ
        basisKet input =
      localRaw layout.targetWire (layout.cleanAncillaTargetProduct U input) *ᵥ
        basisKet input := by
  rw [eval_cleanAncillaCircuit_raw]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [layout.prefixControlledX_denotation_mulVec_basisKet]
  rw [layout.lastControlledTarget_denotation_mulVec_basisKet]
  rw [layout.prefixControlledX_denotation_mulVec_localRaw_basisKet]
  rw [layout.prefixXUpdate_involutive]
  rfl

/-- With a clean-zero auxiliary, the intermediate bit is the data conjunction. -/
theorem cleanAncillaTargetProduct_eq_of_aux_false {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (U : QubitUnitary) (input : Basis ambientWidth)
    (haux : input layout.cleanAncillaWire = false) :
    layout.cleanAncillaTargetProduct U input =
      if layout.prefixEnabled input then (U : QubitMatrix) else 1 := by
  by_cases hprefix : layout.prefixEnabled input <;>
    simp [cleanAncillaTargetProduct, prefixXUpdate, hprefix, haux]

/-- With auxiliary one, the circuit has the complementary, undesired condition. -/
theorem cleanAncillaTargetProduct_eq_of_aux_true {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (U : QubitUnitary) (input : Basis ambientWidth)
    (haux : input layout.cleanAncillaWire = true) :
    layout.cleanAncillaTargetProduct U input =
      if layout.prefixEnabled input then 1 else (U : QubitMatrix) := by
  by_cases hprefix : layout.prefixEnabled input <;>
    simp [cleanAncillaTargetProduct, prefixXUpdate, hprefix, haux]

private theorem prefixControlledTarget_denotation_mulVec_basisKet
    {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (U : QubitUnitary) (input : Basis ambientWidth) :
    (layout.prefixControlledTarget U).denotation *ᵥ basisKet input =
      localRaw layout.targetWire
          (if layout.prefixEnabled input then (U : QubitMatrix) else 1) *ᵥ
        basisKet input := by
  simpa [localRaw_one] using
    layout.prefixControlledTarget_denotation_mulVec_localRaw_basisKet
      U (1 : QubitMatrix) input

/-- Exact desired basis-column equality on clean-zero inputs. -/
theorem eval_cleanAncillaCircuit_mulVec_basisKet_of_aux_false
    {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (U : QubitUnitary) (input : Basis ambientWidth)
    (haux : input layout.cleanAncillaWire = false) :
    (Circuit.eval (layout.cleanAncillaCircuit U) : Gate ambientWidth) *ᵥ
        basisKet input =
      (layout.prefixControlledTarget U).denotation *ᵥ basisKet input := by
  rw [eval_cleanAncillaCircuit_mulVec_basisKet,
    cleanAncillaTargetProduct_eq_of_aux_false layout U input haux,
    layout.prefixControlledTarget_denotation_mulVec_basisKet]

/-! ## Arbitrary clean-zero state semantics and restoration -/

/--
Lemma 7.11 on the entire clean-zero input subspace, including arbitrary data and
spectator superpositions.
-/
theorem eval_cleanAncillaCircuit_mulVec_of_mem_cleanZero
    {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (U : QubitUnitary) (state : State ambientWidth)
    (hstate : state ∈ cleanZeroSubspace layout.cleanAncillaWire) :
    (Circuit.eval (layout.cleanAncillaCircuit U) : Gate ambientWidth) *ᵥ state =
      (layout.prefixControlledTarget U).denotation *ᵥ state := by
  apply mulVec_eq_of_basisKet_eq_on_support _ _ state
    (fun input => input layout.cleanAncillaWire = false)
  · intro input hinput
    exact (mem_fixedWireSubspace_iff
      layout.cleanAncillaWire false state).mp hstate input hinput
  · intro input hinput
    exact layout.eval_cleanAncillaCircuit_mulVec_basisKet_of_aux_false
      U input hinput

/-- The clean auxiliary is returned exactly to the clean-zero subspace. -/
theorem eval_cleanAncillaCircuit_mulVec_mem_cleanZero
    {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (U : QubitUnitary) (state : State ambientWidth)
    (hstate : state ∈ cleanZeroSubspace layout.cleanAncillaWire) :
    (Circuit.eval (layout.cleanAncillaCircuit U) : Gate ambientWidth) *ᵥ state ∈
      cleanZeroSubspace layout.cleanAncillaWire := by
  rw [layout.eval_cleanAncillaCircuit_mulVec_of_mem_cleanZero U state hstate]
  exact positiveControlledUnitary_mulVec_mem_cleanZeroSubspace
    layout.cleanAncillaWire layout.targetWire
    layout.lastControlWire_ne_targetWire layout.prefixTargetLayout.controlSet U
    state hstate

/--
Explicit no-residual-entanglement witness: the output is exactly `|0⟩` on the
auxiliary tensored, via `splitTarget`, with one complementary-register state.
-/
theorem eval_cleanAncillaCircuit_factorization
    {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (U : QubitUnitary) (state : State ambientWidth)
    (hstate : state ∈ cleanZeroSubspace layout.cleanAncillaWire) :
    ∃ rest : ComplementBasis layout.cleanAncillaWire → ℂ,
      (Circuit.eval (layout.cleanAncillaCircuit U) : Gate ambientWidth) *ᵥ state =
        fixedWireEmbed layout.cleanAncillaWire false rest := by
  let output :=
    (Circuit.eval (layout.cleanAncillaCircuit U) : Gate ambientWidth) *ᵥ state
  have houtput : output ∈ cleanZeroSubspace layout.cleanAncillaWire :=
    layout.eval_cleanAncillaCircuit_mulVec_mem_cleanZero U state hstate
  refine ⟨fixedWireRestrict layout.cleanAncillaWire false output, ?_⟩
  exact (fixedWireEmbed_restrict layout.cleanAncillaWire false output houtput).symm

/-! ## Macro resources -/

@[simp]
theorem cleanAncillaCircuit_gateCount {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (U : QubitUnitary) :
    Circuit.gateCount (layout.cleanAncillaCircuit U) = 3 := by
  rfl

/-- Collision-safe kind accounting at `p=1`. -/
theorem cleanAncillaCircuit_kindCount {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (U : QubitUnitary) (kind : PrimitiveKind) :
    Circuit.kindCount kind (layout.cleanAncillaCircuit U) =
      (if .controlledOneQubit p = kind then 2 else 0) +
        (if .controlledOneQubit 1 = kind then 1 else 0) := by
  by_cases hp : .controlledOneQubit p = kind <;>
    by_cases hone : .controlledOneQubit 1 = kind <;>
      simp [cleanAncillaCircuit, Circuit.kindCount, hp, hone]

@[simp]
theorem cleanAncillaCircuit_oneQubitCNOTCost {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (U : QubitUnitary) :
    Circuit.cost CostModel.oneQubitCNOT (layout.cleanAncillaCircuit U) = none := by
  simp [cleanAncillaCircuit, prefixControlledX, lastControlledTarget,
    Circuit.cost, Circuit.addCost]

end OrderedControlLayout

end

end Barenco.MultiControl
