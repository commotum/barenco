import Barenco.Universality.CircuitProduct
import Barenco.Universality.DiagonalCircuit
import Barenco.Universality.TwoLevelCircuit

/-!
# Exact positive-width synthesis

This module assembles the finite-dimensional elimination into a literal circuit
over arbitrary one-qubit gates and CNOTs.  Algebraic factors are listed in
conventional matrix-product order, with the diagonal residual last.
`orderedCircuitProduct` executes that list from right to left, so the resulting
chronology applies the diagonal first and has evaluator

`factor₁ * ⋯ * factorₘ * diagonal`.

All equality is exact, including every diagonal and global phase.  The cost
theorem is an exact finite sum obtained from the literal component circuits; no
asymptotic claim is made here.
-/

namespace Barenco.Universality

noncomputable section

/-- Literal circuits for a conventional list of algebraic two-level factors. -/
def finiteFactorCircuits (controlCount : ℕ)
    (factors : List (FiniteTwoLevelFactor (Basis (controlCount + 1)))) :
    List (Circuit (controlCount + 1)) :=
  factors.map fun factor => factor.circuit controlCount

@[simp]
theorem finiteFactorCircuits_nil (controlCount : ℕ) :
    finiteFactorCircuits controlCount [] = [] := rfl

@[simp]
theorem finiteFactorCircuits_cons (controlCount : ℕ)
    (factor : FiniteTwoLevelFactor (Basis (controlCount + 1)))
    (factors : List (FiniteTwoLevelFactor (Basis (controlCount + 1)))) :
    finiteFactorCircuits controlCount (factor :: factors) =
      factor.circuit controlCount :: finiteFactorCircuits controlCount factors := rfl

/-- Exact finite sum of the accepted costs of a factor list. -/
def finiteFactorCircuitsCost (controlCount : ℕ)
    (factors : List (FiniteTwoLevelFactor (Basis (controlCount + 1)))) : ℕ :=
  (factors.map fun factor => factor.circuitCost controlCount).sum

@[simp]
theorem finiteFactorCircuitsCost_nil (controlCount : ℕ) :
    finiteFactorCircuitsCost controlCount [] = 0 := rfl

@[simp]
theorem finiteFactorCircuitsCost_cons (controlCount : ℕ)
    (factor : FiniteTwoLevelFactor (Basis (controlCount + 1)))
    (factors : List (FiniteTwoLevelFactor (Basis (controlCount + 1)))) :
    finiteFactorCircuitsCost controlCount (factor :: factors) =
      factor.circuitCost controlCount + finiteFactorCircuitsCost controlCount factors := rfl

@[simp]
theorem eval_finiteFactorCircuits_product (controlCount : ℕ)
    (factors : List (FiniteTwoLevelFactor (Basis (controlCount + 1)))) :
    ((finiteFactorCircuits controlCount factors).map Circuit.eval).prod =
      finiteFactorProduct factors := by
  induction factors with
  | nil => simp [finiteFactorProduct]
  | cons factor factors ih =>
      rw [finiteFactorCircuits_cons, List.map_cons, List.prod_cons,
        FiniteTwoLevelFactor.eval_circuit, finiteFactorProduct_cons, ih]

/--
Conventional component list: all two-level factors followed by the exact
diagonal residual.
-/
def exactSynthesisComponents (controlCount : ℕ)
    (U : UnitaryGate (controlCount + 1)) :
    List (Circuit (controlCount + 1)) :=
  let decomposition := decomposeFiniteUnitary U
  finiteFactorCircuits controlCount decomposition.factors ++
    [diagonalCircuit controlCount (Fin.last controlCount)
      decomposition.residual decomposition.residual_diagonal]

/-- Exact accepted cost attached to `exactSynthesisComponents`. -/
def exactSynthesisCost (controlCount : ℕ)
    (U : UnitaryGate (controlCount + 1)) : ℕ :=
  let decomposition := decomposeFiniteUnitary U
  finiteFactorCircuitsCost controlCount decomposition.factors +
    diagonalPatternCircuitsCost (Fin.last controlCount)
      (allComplementPatterns (Fin.last controlCount))

/--
The final literal circuit.  Its component input is in conventional product
order; `orderedCircuitProduct` supplies the required reverse chronology.
-/
def exactSynthesisCircuit (controlCount : ℕ)
    (U : UnitaryGate (controlCount + 1)) : Circuit (controlCount + 1) :=
  orderedCircuitProduct (exactSynthesisComponents controlCount U)

/-- Exact evaluator of the assembled positive-width circuit. -/
@[simp]
theorem eval_exactSynthesisCircuit (controlCount : ℕ)
    (U : UnitaryGate (controlCount + 1)) :
    Circuit.eval (exactSynthesisCircuit controlCount U) = U := by
  let decomposition := decomposeFiniteUnitary U
  change Circuit.eval (orderedCircuitProduct
    (finiteFactorCircuits controlCount decomposition.factors ++
      [diagonalCircuit controlCount (Fin.last controlCount)
        decomposition.residual decomposition.residual_diagonal])) = U
  rw [eval_orderedCircuitProduct, List.map_append, List.prod_append,
    eval_finiteFactorCircuits_product]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, eval_diagonalCircuit]
  exact decomposition.product_eq.symm

/--
Exact accepted cost for a factor list followed by one diagonal circuit.

The proof is structural in the actual syntax and does not infer a cost from the
evaluator equality.
-/
theorem orderedFactorCircuits_diagonal_oneQubitCNOTCost (controlCount : ℕ)
    (factors : List (FiniteTwoLevelFactor (Basis (controlCount + 1))))
    (D : UnitaryGate (controlCount + 1)) (hD : IsDiagonalUnitary D) :
    Circuit.cost CostModel.oneQubitCNOT
        (orderedCircuitProduct
          (finiteFactorCircuits controlCount factors ++
            [diagonalCircuit controlCount (Fin.last controlCount) D hD])) =
      some (finiteFactorCircuitsCost controlCount factors +
        diagonalPatternCircuitsCost (Fin.last controlCount)
          (allComplementPatterns (Fin.last controlCount))) := by
  induction factors with
  | nil =>
      simp [orderedCircuitProduct]
  | cons factor factors ih =>
      rw [finiteFactorCircuits_cons, List.cons_append,
        orderedCircuitProduct_cons, Circuit.cost_append, ih,
        FiniteTwoLevelFactor.circuit_oneQubitCNOTCost,
        finiteFactorCircuitsCost_cons]
      simp [Circuit.addCost, Nat.add_assoc, Nat.add_comm]

/-- Exact finite accepted one-qubit/CNOT cost of the assembled circuit. -/
@[simp]
theorem exactSynthesisCircuit_oneQubitCNOTCost (controlCount : ℕ)
    (U : UnitaryGate (controlCount + 1)) :
    Circuit.cost CostModel.oneQubitCNOT (exactSynthesisCircuit controlCount U) =
      some (exactSynthesisCost controlCount U) := by
  let decomposition := decomposeFiniteUnitary U
  exact orderedFactorCircuits_diagonal_oneQubitCNOTCost controlCount
    decomposition.factors decomposition.residual decomposition.residual_diagonal

/--
Positive-width exact universality using only syntax accepted by the
one-qubit/CNOT cost model.
-/
theorem exact_oneQubitCNOT_universality (controlCount : ℕ)
    (U : UnitaryGate (controlCount + 1)) :
    ∃ circuit : Circuit (controlCount + 1), ∃ cost : ℕ,
      Circuit.eval circuit = U ∧
        Circuit.cost CostModel.oneQubitCNOT circuit = some cost := by
  exact ⟨exactSynthesisCircuit controlCount U, exactSynthesisCost controlCount U,
    eval_exactSynthesisCircuit controlCount U,
    exactSynthesisCircuit_oneQubitCNOTCost controlCount U⟩

end


end Barenco.Universality
