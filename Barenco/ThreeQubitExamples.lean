import Barenco.ThreeQubit.Expansion
import Barenco.ThreeQubit.RelativePhase

/-!
# Diagnostic checks for Section 6 three-qubit constructions

This module instantiates the arbitrary-width public theorems at concrete wire
layouts. It is diagnostic and intentionally excluded from the public root.
-/

namespace Barenco.ThreeQubitExamples

open Barenco
open Barenco.OneQubit
open Barenco.ThreeQubit
open scoped Matrix

noncomputable section

private theorem fin3_zero_ne_one : (0 : Fin 3) ≠ 1 := by decide
private theorem fin3_zero_ne_two : (0 : Fin 3) ≠ 2 := by decide
private theorem fin3_one_ne_two : (1 : Fin 3) ≠ 2 := by decide

private def threeBit (first second target : Bool) : Basis 3 := fun i =>
  if i = 0 then first else if i = 1 then second else target

private theorem setTarget_threeBit_two (first second target output : Bool) :
    setTarget (2 : Fin 3) (threeBit first second target) output =
      threeBit first second output := by
  funext i
  fin_cases i <;> simp [threeBit]

/-- The selected-root Lemma 6.1 circuit specializes directly to three wires. -/
example (U : QubitUnitary) :
    Circuit.eval
        (doubleControlledRootCircuit (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)
          fin3_zero_ne_one fin3_zero_ne_two fin3_one_ne_two U) =
      positiveControlledUnitary (2 : Fin 3)
        (twoControlSet (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)
          fin3_zero_ne_two fin3_one_ne_two) U := by
  exact eval_doubleControlledRootCircuit (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)
    fin3_zero_ne_one fin3_zero_ne_two fin3_one_ne_two U

/-- The unexpanded source diagram is five macros but is not early-basic syntax. -/
example (V : QubitUnitary) :
    Circuit.gateCount
        (doubleControlledViaSquareCircuit (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)
          fin3_zero_ne_one fin3_zero_ne_two fin3_one_ne_two V) = 5 ∧
      Circuit.cost CostModel.oneQubitCNOT
        (doubleControlledViaSquareCircuit (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)
          fin3_zero_ne_one fin3_zero_ne_two fin3_one_ne_two V) = none := by
  simp

/-- Corollary 6.2 supplies an exact sixteen-basic-gate circuit for every target. -/
example (U : QubitUnitary) :
    ∃ circuit : Circuit 3,
      Circuit.eval circuit = positiveControlledUnitary (2 : Fin 3)
        (twoControlSet (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)
          fin3_zero_ne_two fin3_one_ne_two) U ∧
      Circuit.gateCount circuit = 16 ∧
      Circuit.kindCount .oneQubit circuit = 8 ∧
      Circuit.kindCount .cnot circuit = 8 ∧
      Circuit.cost CostModel.oneQubitCNOT circuit = some 16 := by
  exact doubleControlledUnitary_has_sixteenPrimitiveCircuit
    (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)
    fin3_zero_ne_one fin3_zero_ne_two fin3_one_ne_two U

private theorem fin5_four_ne_zero : (4 : Fin 5) ≠ 0 := by decide
private theorem fin5_four_ne_two : (4 : Fin 5) ≠ 2 := by decide
private theorem fin5_zero_ne_two : (0 : Fin 5) ≠ 2 := by decide

/--
The exact theorem is not tied to adjacent wires: controls `4` and `0` may target
wire `2`, with wires `1` and `3` included as untouched spectators.
-/
example (U : QubitUnitary) :
    Circuit.eval
        (doubleControlledRootCircuit (4 : Fin 5) (0 : Fin 5) (2 : Fin 5)
          fin5_four_ne_zero fin5_four_ne_two fin5_zero_ne_two U) =
      positiveControlledUnitary (2 : Fin 5)
        (twoControlSet (4 : Fin 5) (0 : Fin 5) (2 : Fin 5)
          fin5_four_ne_two fin5_zero_ne_two) U := by
  exact eval_doubleControlledRootCircuit (4 : Fin 5) (0 : Fin 5) (2 : Fin 5)
    fin5_four_ne_zero fin5_four_ne_two fin5_zero_ne_two U

/-! ## Complete three-bit relative-phase sign tables -/

/--
One quantified theorem exhausts all eight inputs of the A/CNOT diagram: Toffoli
flips the target only on controls `11`, and the sole negative input is `101`.
-/
theorem relativePhaseToffoliA_threeBit_truthTable
    (first second target : Bool) :
    (Circuit.eval
        (relativePhaseToffoliACircuit (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)
          fin3_zero_ne_two fin3_one_ne_two) : Gate 3) *ᵥ
        basisKet (threeBit first second target) =
      (if first = true ∧ second = false ∧ target = true then (-1 : ℂ) else 1) •
        basisKet (threeBit first second
          (if first = true ∧ second = true then !target else target)) := by
  rw [relativePhaseToffoliACircuit_mulVec_basisKet (0 : Fin 3) (1 : Fin 3)
    (2 : Fin 3) fin3_zero_ne_one fin3_zero_ne_two fin3_one_ne_two]
  rw [relativeToffoliPhase_input]
  cases first <;> cases second <;> cases target <;>
    simp [threeBit, toffoliOutput, setTarget_threeBit_two]

/-- The B/controlled-Z diagram has exactly the same complete eight-input table. -/
theorem relativePhaseToffoliB_threeBit_truthTable
    (first second target : Bool) :
    (Circuit.eval
        (relativePhaseToffoliBCircuit (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)
          fin3_zero_ne_two fin3_one_ne_two) : Gate 3) *ᵥ
        basisKet (threeBit first second target) =
      (if first = true ∧ second = false ∧ target = true then (-1 : ℂ) else 1) •
        basisKet (threeBit first second
          (if first = true ∧ second = true then !target else target)) := by
  rw [relativePhaseToffoliBCircuit_mulVec_basisKet (0 : Fin 3) (1 : Fin 3)
    (2 : Fin 3) fin3_zero_ne_one fin3_zero_ne_two fin3_one_ne_two]
  rw [relativeToffoliPhase_input]
  cases first <;> cases second <;> cases target <;>
    simp [threeBit, toffoliOutput, setTarget_threeBit_two]

/-- Controlled paper `W` has the same permutation but its sole minus is `111`. -/
theorem controlledW_threeBit_truthTable (first second target : Bool) :
    (controlledWUnitary (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)
        fin3_zero_ne_two fin3_one_ne_two : Gate 3) *ᵥ
        basisKet (threeBit first second target) =
      (if first = true ∧ second = true ∧ target = true then (-1 : ℂ) else 1) •
        basisKet (threeBit first second
          (if first = true ∧ second = true then !target else target)) := by
  rw [controlledWUnitary_mulVec_basisKet (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)
    fin3_zero_ne_one fin3_zero_ne_two fin3_one_ne_two]
  rw [controlledWPhase_input]
  cases first <;> cases second <;> cases target <;>
    simp [threeBit, toffoliOutput, setTarget_threeBit_two]

/-- The A diagram's seven syntax nodes are exactly four one-qubit plus three CNOT. -/
example :
    Circuit.gateCount
        (relativePhaseToffoliACircuit (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)
          fin3_zero_ne_two fin3_one_ne_two) = 7 ∧
      Circuit.cost CostModel.oneQubitCNOT
        (relativePhaseToffoliACircuit (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)
          fin3_zero_ne_two fin3_one_ne_two) = some 7 := by
  simp

/-- The B diagram retains controlled-Z macros, so the early basic model rejects it. -/
example :
    Circuit.gateCount
        (relativePhaseToffoliBCircuit (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)
          fin3_zero_ne_two fin3_one_ne_two) = 7 ∧
      Circuit.cost CostModel.oneQubitCNOT
        (relativePhaseToffoliBCircuit (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)
          fin3_zero_ne_two fin3_one_ne_two) = none := by
  simp

end

end Barenco.ThreeQubitExamples
