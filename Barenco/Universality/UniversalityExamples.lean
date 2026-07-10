import Barenco.Universality.ExactSynthesis
import Barenco.Universality.WidthOne

/-!
# Low-dimensional exact-synthesis diagnostics

This root-excluded leaf instantiates the Stage 11 APIs at widths one and two.
The checks use ordinary kernel proofs only.  Resource conclusions come from the
literal circuit syntax under `CostModel.oneQubitCNOT`, not from semantic matrix
equalities.
-/

namespace Barenco.Universality.UniversalityExamples

open Matrix

noncomputable section

/-! ## Width one: the direct one-gate boundary -/

/-- The trusted local Pauli-X semantic gate on the unique wire. -/
def widthOneX : UnitaryGate 1 :=
  xUnitary (0 : Fin 1)

/-- Direct width-one synthesis is exact and costs one accepted primitive. -/
theorem widthOneX_direct_exact_and_cost :
    Circuit.eval (widthOneCircuit widthOneX) = widthOneX ∧
      Circuit.cost CostModel.oneQubitCNOT (widthOneCircuit widthOneX) = some 1 := by
  constructor <;> simp

/-! ## Width two: a nonadjacent ordered basis pair -/

/-- The concrete endpoint `|00⟩`. -/
def widthTwoZero : Basis 2 :=
  twoBit false false

/-- The concrete endpoint `|11⟩`. -/
def widthTwoOne : Basis 2 :=
  twoBit true true

theorem widthTwoZero_ne_widthTwoOne : widthTwoZero ≠ widthTwoOne := by
  intro h
  have hwire := congrFun h (0 : Fin 2)
  simp [widthTwoZero, widthTwoOne, twoBit] at hwire

/-- Exact affine implementation of Pauli-X on the ordered pair `|00⟩,|11⟩`. -/
def widthTwoNonadjacentX : Circuit 2 :=
  twoLevelCircuit 1 widthTwoZero widthTwoOne widthTwoZero_ne_widthTwoOne pauliX

/-- The concrete two-level circuit has the requested full-register evaluator. -/
theorem widthTwoNonadjacentX_eval :
    Circuit.eval widthTwoNonadjacentX =
      twoLevelUnitary widthTwoZero widthTwoOne
        widthTwoZero_ne_widthTwoOne pauliX := by
  exact eval_twoLevelCircuit 1 widthTwoZero widthTwoOne
    widthTwoZero_ne_widthTwoOne pauliX

/-- On the named first endpoint, the concrete block maps `|00⟩` to `|11⟩`. -/
theorem widthTwoNonadjacentX_moves_zero_to_one :
    (Circuit.eval widthTwoNonadjacentX : Gate 2) *ᵥ basisKet widthTwoZero =
      basisKet widthTwoOne := by
  rw [widthTwoNonadjacentX_eval,
    twoLevelUnitary_mulVec_basisKet_first]
  simp [pauliX_apply]

/-- The nonadjacent implementation has its exact accepted syntax cost. -/
theorem widthTwoNonadjacentX_cost :
    Circuit.cost CostModel.oneQubitCNOT widthTwoNonadjacentX =
      some (twoLevelCircuitCost 1 widthTwoZero widthTwoOne
        widthTwoZero_ne_widthTwoOne) := by
  exact twoLevelCircuit_oneQubitCNOTCost 1 widthTwoZero widthTwoOne
    widthTwoZero_ne_widthTwoOne pauliX

/-! ## Width two: complete synthesis instantiated on CNOT -/

/-- The trusted two-wire CNOT with wire zero controlling wire one. -/
def widthTwoCNOT : UnitaryGate 2 :=
  cnotUnitary (0 : Fin 2) (1 : Fin 2) (by decide)

/-- The complete finite-elimination pipeline instantiated on the trusted CNOT. -/
def widthTwoCNOTExactCircuit : Circuit 2 :=
  exactSynthesisCircuit 1 widthTwoCNOT

/-- Complete synthesis realizes CNOT exactly and exposes an accepted exact cost. -/
theorem widthTwoCNOT_exact_and_cost :
    Circuit.eval widthTwoCNOTExactCircuit = widthTwoCNOT ∧
      Circuit.cost CostModel.oneQubitCNOT widthTwoCNOTExactCircuit =
        some (exactSynthesisCost 1 widthTwoCNOT) := by
  constructor <;> simp [widthTwoCNOTExactCircuit]

end


end Barenco.Universality.UniversalityExamples
