import Barenco.MultiControl.CleanAncillaExpansion
import Barenco.MultiControl.LinearSpecialUnitaryExpansion

/-!
# Diagnostics for the linear and one-clean-ancilla constructions

This root-excluded leaf specializes Barenco Lemmas 7.9 and 7.11 to canonical
consecutive registers.  It pins both component profiles at the first supported
logical width and the next width, exhibits the exact failure of Lemma 7.11 on a
dirty-one auxiliary using Pauli X, and checks clean-wire factorization for an
arbitrary complementary-register state.

The dirty-auxiliary diagnostic is a vector-level statement: the expanded
circuit and the intended controlled-X operation send the same basis ket to
provably different basis kets.  It is therefore not merely a classical truth
table observation.
-/

namespace Barenco.MultiControl.AncillaExamples

open Barenco
open Barenco.ControlledCircuit
open OrderedControlLayout
open scoped Matrix

noncomputable section

/-! ## Canonical consecutive layouts -/

/-- Consecutive controls `0,…,k-1` followed by target wire `k`. -/
def consecutiveLayout (controlCount : ℕ) :
    OrderedControlLayout controlCount (controlCount + 1) where
  controlWire := Fin.castSuccEmb
  targetWire := Fin.last controlCount
  control_ne_target := Fin.castSucc_ne_last

/-- Five data controls, clean auxiliary wire `5`, and target wire `6`. -/
def widthSevenLayout : OrderedControlLayout 6 7 := consecutiveLayout 6

/-- Six data controls, clean auxiliary wire `6`, and target wire `7`. -/
def widthEightLayout : OrderedControlLayout 7 8 := consecutiveLayout 7

/-- The canonical width-seven clean-ancilla roles are exactly wires `0,…,4;5;6`. -/
theorem widthSeven_wireRoles :
    widthSevenLayout.cleanAncillaWire = (5 : Fin 7) ∧
      widthSevenLayout.targetWire = (6 : Fin 7) ∧
      widthSevenLayout.cleanDataLayout.controlSet.card = 5 := by
  decide

/-- The next canonical clean-ancilla layout uses auxiliary `6` and target `7`. -/
theorem widthEight_wireRoles :
    widthEightLayout.cleanAncillaWire = (6 : Fin 8) ∧
      widthEightLayout.targetWire = (7 : Fin 8) ∧
      widthEightLayout.cleanDataLayout.controlSet.card = 6 := by
  decide

/-! ## Exact Stage 8 component profiles -/

/-- Lemma 7.9 has exact profile `(169,142,311)` at logical width seven. -/
theorem widthSeven_linearSU2_resources (W : QubitSpecialUnitary) :
    Circuit.kindCount .oneQubit
        (widthSevenLayout.expandedLinearSU2Circuit (p := 5) (by omega) W) = 169 ∧
      Circuit.kindCount .cnot
          (widthSevenLayout.expandedLinearSU2Circuit (p := 5) (by omega) W) = 142 ∧
      Circuit.gateCount
          (widthSevenLayout.expandedLinearSU2Circuit (p := 5) (by omega) W) = 311 ∧
      Circuit.cost CostModel.oneQubitCNOT
          (widthSevenLayout.expandedLinearSU2Circuit (p := 5) (by omega) W) =
        some 311 := by
  exact expandedLinearSU2Circuit_seven_resources widthSevenLayout W

/-- Lemma 7.11 uses exactly one clean wire and profile `(164,138,302)` at width seven. -/
theorem widthSeven_cleanAncilla_resources (U : QubitUnitary) :
    widthSevenLayout.expandedCleanAncillaRequiredCleanWires.card = 1 ∧
      Circuit.kindCount .oneQubit
          (widthSevenLayout.expandedCleanAncillaCircuit (p := 5) (by omega) U) = 164 ∧
      Circuit.kindCount .cnot
          (widthSevenLayout.expandedCleanAncillaCircuit (p := 5) (by omega) U) = 138 ∧
      Circuit.gateCount
          (widthSevenLayout.expandedCleanAncillaCircuit (p := 5) (by omega) U) = 302 ∧
      Circuit.cost CostModel.oneQubitCNOT
          (widthSevenLayout.expandedCleanAncillaCircuit (p := 5) (by omega) U) =
        some 302 := by
  exact expandedCleanAncillaCircuit_seven_resources widthSevenLayout U

/-- The next Lemma 7.9 instance has profile `(233,190,423)`. -/
theorem widthEight_linearSU2_resources (W : QubitSpecialUnitary) :
    Circuit.kindCount .oneQubit
        (widthEightLayout.expandedLinearSU2Circuit (p := 6) (by omega) W) = 233 ∧
      Circuit.kindCount .cnot
          (widthEightLayout.expandedLinearSU2Circuit (p := 6) (by omega) W) = 190 ∧
      Circuit.gateCount
          (widthEightLayout.expandedLinearSU2Circuit (p := 6) (by omega) W) = 423 ∧
      Circuit.cost CostModel.oneQubitCNOT
          (widthEightLayout.expandedLinearSU2Circuit (p := 6) (by omega) W) =
        some 423 := by
  norm_num

/-- The next one-clean-ancilla instance has profile `(228,186,414)`. -/
theorem widthEight_cleanAncilla_resources (U : QubitUnitary) :
    widthEightLayout.expandedCleanAncillaRequiredCleanWires.card = 1 ∧
      Circuit.kindCount .oneQubit
          (widthEightLayout.expandedCleanAncillaCircuit (p := 6) (by omega) U) = 228 ∧
      Circuit.kindCount .cnot
          (widthEightLayout.expandedCleanAncillaCircuit (p := 6) (by omega) U) = 186 ∧
      Circuit.gateCount
          (widthEightLayout.expandedCleanAncillaCircuit (p := 6) (by omega) U) = 414 ∧
      Circuit.cost CostModel.oneQubitCNOT
          (widthEightLayout.expandedCleanAncillaCircuit (p := 6) (by omega) U) =
        some 414 := by
  norm_num

/-! ## Dirty-one auxiliary counterexample -/

/-- Only the auxiliary wire is one; every data control and the target are zero. -/
def dirtyAuxInput : Basis 7 := fun wire =>
  decide (wire = widthSevenLayout.cleanAncillaWire)

/-- The erroneous dirty-auxiliary execution additionally flips the target. -/
def dirtyAuxOutput : Basis 7 :=
  setTarget widthSevenLayout.targetWire dirtyAuxInput true

@[simp]
theorem dirtyAuxInput_auxiliary :
    dirtyAuxInput widthSevenLayout.cleanAncillaWire = true := by
  simp [dirtyAuxInput]

@[simp]
theorem dirtyAuxInput_target :
    dirtyAuxInput widthSevenLayout.targetWire = false := by
  simp [dirtyAuxInput, widthSevenLayout, consecutiveLayout, cleanAncillaWire,
    lastControlWire]

/-- The data conjunction is false on the chosen dirty-auxiliary input. -/
theorem dirtyAuxInput_prefixDisabled :
    ¬widthSevenLayout.prefixEnabled dirtyAuxInput := by
  intro h
  have hzero := h (0 : Fin 5)
  norm_num [dirtyAuxInput, widthSevenLayout, consecutiveLayout, cleanAncillaWire,
    lastControlWire] at hzero
  exact (by decide : (0 : Fin 7) ≠ (Fin.last 5).castSucc) hzero

/-- The primitive Lemma 7.11 circuit fires Pauli X on this dirty-one input. -/
theorem dirtyAux_expanded_action :
    (Circuit.eval
        (widthSevenLayout.expandedCleanAncillaCircuit (p := 5) (by omega) pauliX) :
      Gate 7) *ᵥ basisKet dirtyAuxInput = basisKet dirtyAuxOutput := by
  rw [widthSevenLayout.eval_expandedCleanAncillaCircuit_mulVec_basisKet]
  rw [widthSevenLayout.cleanAncillaTargetProduct_eq_of_aux_true pauliX
    dirtyAuxInput dirtyAuxInput_auxiliary]
  rw [if_neg dirtyAuxInput_prefixDisabled]
  change xRaw widthSevenLayout.targetWire *ᵥ basisKet dirtyAuxInput = _
  rw [xRaw_mulVec_basisKet]
  congr 1

/-- The intended data-controlled Pauli X is inactive on the same basis ket. -/
theorem dirtyAux_intended_action :
    (widthSevenLayout.prefixControlledTarget pauliX).denotation *ᵥ
        basisKet dirtyAuxInput = basisKet dirtyAuxInput := by
  have hone : localRaw widthSevenLayout.targetWire (1 : QubitMatrix) = 1 := by
    rw [localRaw_eq_targetBlockRaw, targetBlockRaw_one]
  simpa [dirtyAuxInput_prefixDisabled, hone, Matrix.one_mulVec] using
    widthSevenLayout.prefixControlledTarget_denotation_mulVec_localRaw_basisKet
      pauliX (1 : QubitMatrix) dirtyAuxInput

/-- The actual and intended output assignments differ at the target wire. -/
theorem dirtyAuxOutput_ne_input : dirtyAuxOutput ≠ dirtyAuxInput := by
  intro heq
  have htarget := congrFun heq widthSevenLayout.targetWire
  simp [dirtyAuxOutput, dirtyAuxInput_target] at htarget

/-- Distinct assignments give distinct basis kets in this concrete diagnostic. -/
theorem dirtyAuxOutputKet_ne_inputKet :
    basisKet dirtyAuxOutput ≠ basisKet dirtyAuxInput := by
  intro heq
  have happ := congrFun heq dirtyAuxOutput
  simp [basisKet_apply, dirtyAuxOutput_ne_input] at happ

/--
The expanded Lemma 7.11 circuit is not the intended controlled-X operator when
the declared auxiliary is initialized to one.
-/
theorem dirtyAux_expanded_ne_intended :
    (Circuit.eval
        (widthSevenLayout.expandedCleanAncillaCircuit (p := 5) (by omega) pauliX) :
      Gate 7) *ᵥ basisKet dirtyAuxInput ≠
      (widthSevenLayout.prefixControlledTarget pauliX).denotation *ᵥ
        basisKet dirtyAuxInput := by
  rw [dirtyAux_expanded_action, dirtyAux_intended_action]
  exact dirtyAuxOutputKet_ne_inputKet

/-! ## Arbitrary-state fixed-wire factorization -/

/--
For an arbitrary state on the six complementary wires, the width-seven
primitive circuit returns an output that still factors with the auxiliary
literally fixed to zero.
-/
theorem widthSeven_fixedWire_factorization (U : QubitUnitary)
    (rest : ComplementBasis widthSevenLayout.cleanAncillaWire → ℂ) :
    ∃ outputRest : ComplementBasis widthSevenLayout.cleanAncillaWire → ℂ,
      (Circuit.eval
          (widthSevenLayout.expandedCleanAncillaCircuit (p := 5) (by omega) U) :
        Gate 7) *ᵥ
          fixedWireEmbed widthSevenLayout.cleanAncillaWire false rest =
        fixedWireEmbed widthSevenLayout.cleanAncillaWire false outputRest := by
  apply widthSevenLayout.eval_expandedCleanAncillaCircuit_factorization
  exact fixedWireEmbed_mem widthSevenLayout.cleanAncillaWire false rest

end

end Barenco.MultiControl.AncillaExamples
