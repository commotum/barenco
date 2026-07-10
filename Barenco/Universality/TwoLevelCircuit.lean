import Barenco.Universality.AffinePair
import Barenco.Universality.AdjacentTwoLevel
import Barenco.Universality.TwoLevelTransport
import Barenco.Universality.FiniteBridge

/-!
# Exact literal circuits for arbitrary computational-basis two-level unitaries

For distinct basis assignments `first` and `second`, `affinePairCircuit` sends
the ordered pair to `allZeroBasis` and the singleton assignment at a canonical
differing pivot.  Those canonical endpoints are adjacent.  We apply the desired
ordered block there and execute the adjoint affine circuit afterwards.

Chronologically the construction is `P; Q; P†`, so its evaluator is
`P⁻¹ * Q * P`.  `unitary_conjugate_twoLevelUnitary` proves that this is exactly
the requested full-register two-level unitary.  The syntax contains only
arbitrary one-qubit gates and CNOTs, and the accepted cost below is derived from
that syntax.
-/

namespace Barenco.Universality

noncomputable section

/-! ## The canonical adjacent pair -/

/-- The all-zero assignment and a singleton differ exactly at its support. -/
theorem allZeroBasis_singletonBasis_stepAt {n : ℕ} (pivot : Fin n) :
    BasisStepAt pivot (allZeroBasis : Basis n) (singletonBasis pivot) := by
  constructor
  · simp
  · intro other hother
    simp [singletonBasis, hother]

/-- Literal mixed-polarity implementation on the canonical adjacent pair. -/
def canonicalAdjacentTwoLevelCircuit (controlCount : ℕ)
    (pivot : Fin (controlCount + 1)) (U : QubitUnitary) :
    Circuit (controlCount + 1) :=
  adjacentTwoLevelCircuit controlCount pivot allZeroBasis (singletonBasis pivot)
    (allZeroBasis_singletonBasis_stepAt pivot) U

@[simp]
theorem eval_canonicalAdjacentTwoLevelCircuit (controlCount : ℕ)
    (pivot : Fin (controlCount + 1)) (U : QubitUnitary) :
    Circuit.eval (canonicalAdjacentTwoLevelCircuit controlCount pivot U) =
      twoLevelUnitary allZeroBasis (singletonBasis pivot)
        (allZeroBasis_ne_singletonBasis pivot) U := by
  exact eval_adjacentTwoLevelCircuit controlCount pivot allZeroBasis
    (singletonBasis pivot) (allZeroBasis_singletonBasis_stepAt pivot) U

/-- Exact accepted cost of the canonical adjacent block. -/
def canonicalAdjacentTwoLevelCircuitCost (controlCount : ℕ)
    (pivot : Fin (controlCount + 1)) : ℕ :=
  2 * patternFlipCount
      ((splitTarget pivot (allZeroBasis : Basis (controlCount + 1))).2) +
    fullControlCircuitCost controlCount

@[simp]
theorem canonicalAdjacentTwoLevelCircuit_oneQubitCNOTCost
    (controlCount : ℕ) (pivot : Fin (controlCount + 1))
    (U : QubitUnitary) :
    Circuit.cost CostModel.oneQubitCNOT
        (canonicalAdjacentTwoLevelCircuit controlCount pivot U) =
      some (canonicalAdjacentTwoLevelCircuitCost controlCount pivot) := by
  exact adjacentTwoLevelCircuit_oneQubitCNOTCost controlCount pivot allZeroBasis
    (singletonBasis pivot) (allZeroBasis_singletonBasis_stepAt pivot) U

/-! ## Arbitrary ordered pairs -/

/--
Literal `P; Q; P†` implementation of an arbitrary ordered two-level block.
-/
def twoLevelCircuit (controlCount : ℕ)
    (first second : Basis (controlCount + 1))
    (hfirstSecond : first ≠ second) (U : QubitUnitary) :
    Circuit (controlCount + 1) :=
  let transport := affinePairCircuit first second hfirstSecond
  let pivot := differingPivot first second hfirstSecond
  Circuit.append transport
    (Circuit.append
      (canonicalAdjacentTwoLevelCircuit controlCount pivot U)
      (Circuit.adjoint transport))

/-- Exact full-register evaluator of the arbitrary-pair construction. -/
@[simp]
theorem eval_twoLevelCircuit (controlCount : ℕ)
    (first second : Basis (controlCount + 1))
    (hfirstSecond : first ≠ second) (U : QubitUnitary) :
    Circuit.eval (twoLevelCircuit controlCount first second hfirstSecond U) =
      twoLevelUnitary first second hfirstSecond U := by
  rw [twoLevelCircuit, Circuit.eval_append, Circuit.eval_append,
    Circuit.eval_adjoint, eval_canonicalAdjacentTwoLevelCircuit]
  exact unitary_conjugate_twoLevelUnitary
    (Circuit.eval (affinePairCircuit first second hfirstSecond))
    first second allZeroBasis
    (singletonBasis (differingPivot first second hfirstSecond))
    hfirstSecond
    (allZeroBasis_ne_singletonBasis
      (differingPivot first second hfirstSecond))
    (eval_affinePairCircuit_first first second hfirstSecond)
    (eval_affinePairCircuit_second first second hfirstSecond) U

/-- Exact accepted cost of the affine conjugation construction. -/
def twoLevelCircuitCost (controlCount : ℕ)
    (first second : Basis (controlCount + 1))
    (hfirstSecond : first ≠ second) : ℕ :=
  2 * affinePairGateCount first second hfirstSecond +
    canonicalAdjacentTwoLevelCircuitCost controlCount
      (differingPivot first second hfirstSecond)

@[simp]
theorem twoLevelCircuit_oneQubitCNOTCost (controlCount : ℕ)
    (first second : Basis (controlCount + 1))
    (hfirstSecond : first ≠ second) (U : QubitUnitary) :
    Circuit.cost CostModel.oneQubitCNOT
        (twoLevelCircuit controlCount first second hfirstSecond U) =
      some (twoLevelCircuitCost controlCount first second hfirstSecond) := by
  rw [twoLevelCircuit, Circuit.cost_append, Circuit.cost_append,
    Circuit.cost_adjoint,
    affinePairCircuit_oneQubitCNOTCost,
    canonicalAdjacentTwoLevelCircuit_oneQubitCNOTCost]
  simp [Circuit.addCost, twoLevelCircuitCost]
  omega

/-! ## Generic finite-factor bridge specialized to qubit bases -/

namespace FiniteTwoLevelFactor

/-- Literal circuit denotation of a factor returned by finite elimination. -/
def circuit (controlCount : ℕ)
    (factor : FiniteTwoLevelFactor (Basis (controlCount + 1))) :
    Circuit (controlCount + 1) :=
  twoLevelCircuit controlCount factor.first factor.second factor.distinct
    factor.block

/-- Exact evaluator of a synthesized finite two-level factor. -/
@[simp]
theorem eval_circuit (controlCount : ℕ)
    (factor : FiniteTwoLevelFactor (Basis (controlCount + 1))) :
    Circuit.eval (factor.circuit controlCount) = factor.eval := by
  exact eval_twoLevelCircuit controlCount factor.first factor.second
    factor.distinct factor.block

/-- Exact accepted cost attached to a synthesized finite factor. -/
def circuitCost (controlCount : ℕ)
    (factor : FiniteTwoLevelFactor (Basis (controlCount + 1))) : ℕ :=
  twoLevelCircuitCost controlCount factor.first factor.second factor.distinct

@[simp]
theorem circuit_oneQubitCNOTCost (controlCount : ℕ)
    (factor : FiniteTwoLevelFactor (Basis (controlCount + 1))) :
    Circuit.cost CostModel.oneQubitCNOT (factor.circuit controlCount) =
      some (factor.circuitCost controlCount) := by
  exact twoLevelCircuit_oneQubitCNOTCost controlCount factor.first factor.second
    factor.distinct factor.block

end FiniteTwoLevelFactor

end


end Barenco.Universality
