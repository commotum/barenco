import Barenco.Universality.FullControl
import Barenco.Universality.PatternFlip

/-!
# Literal mixed-polarity fully controlled gates

For a positive-width register, `patternControlledCircuit` implements a one-qubit
unitary on `target` exactly when every complementary wire equals a prescribed
Boolean pattern. False controls are converted to positive controls by the literal
Pauli-X prefix from `PatternFlip`, the all-positive operation is supplied by
`FullControl`, and the prefix is undone by its adjoint.

Correctness is exact matrix equality on the complete register. In particular,
the proof includes inactive basis states, restoration of every flipped wire, and
commutation with the target-local active block.
-/

namespace Barenco.Universality

open scoped Matrix

noncomputable section

/-- Boolean predicate selecting one exact complementary basis pattern. -/
def exactPatternEnabled {n : ℕ} {target : Fin n}
    (pattern : ComplementBasis target) (rest : ComplementBasis target) : Bool :=
  decide (rest = pattern)

@[simp]
theorem exactPatternEnabled_eq_true_iff {n : ℕ} {target : Fin n}
    (pattern rest : ComplementBasis target) :
    exactPatternEnabled pattern rest = true ↔ rest = pattern := by
  simp [exactPatternEnabled]

@[simp]
theorem exactPatternEnabled_eq_false_iff {n : ℕ} {target : Fin n}
    (pattern rest : ComplementBasis target) :
    exactPatternEnabled pattern rest = false ↔ rest ≠ pattern := by
  simp [exactPatternEnabled]

/-- Certified semantic gate active on exactly one complementary bit pattern. -/
def patternControlledUnitary {n : ℕ} (target : Fin n)
    (pattern : ComplementBasis target) (U : QubitUnitary) : UnitaryGate n :=
  controlledUnitary target (exactPatternEnabled pattern) U

@[simp]
theorem coe_patternControlledUnitary {n : ℕ} (target : Fin n)
    (pattern : ComplementBasis target) (U : QubitUnitary) :
    (patternControlledUnitary target pattern U : Gate n) =
      controlledRaw target (exactPatternEnabled pattern) U := by
  simp [patternControlledUnitary]

/--
Literal mixed-polarity implementation on `controlCount + 1` wires.

Chronology is: flip false controls, run the all-positive fully controlled gate,
then undo the flips.
-/
def patternControlledCircuit (controlCount : ℕ)
    (target : Fin (controlCount + 1)) (pattern : ComplementBasis target)
    (U : QubitUnitary) : Circuit (controlCount + 1) :=
  let flips := patternFlipCircuit target pattern
  Circuit.append flips
    (Circuit.append (fullControlCircuit controlCount target U)
      (Circuit.adjoint flips))

theorem all_true_patternFlipBasis_iff (controlCount : ℕ)
    (target : Fin (controlCount + 1)) (pattern : ComplementBasis target)
    (input : Basis (controlCount + 1)) :
    (∀ wire ∈ (Finset.univ : ControlSet target),
        patternFlipBasis target pattern input wire = true) ↔
      (splitTarget target input).2 = pattern := by
  simpa using patternFlipBasis_all_true_iff target pattern input

/-- The positive backend's action after the pattern-flip prefix. -/
theorem eval_fullControlCircuit_patternFlipBasis (controlCount : ℕ)
    (target : Fin (controlCount + 1)) (pattern : ComplementBasis target)
    (U : QubitUnitary) (input : Basis (controlCount + 1)) :
    (Circuit.eval (fullControlCircuit controlCount target U) :
        Gate (controlCount + 1)) *ᵥ
        basisKet (patternFlipBasis target pattern input) =
      if (splitTarget target input).2 = pattern then
        localRaw target U *ᵥ basisKet (patternFlipBasis target pattern input)
      else basisKet (patternFlipBasis target pattern input) := by
  rw [eval_fullControlCircuit]
  rw [coe_positiveControlledUnitary, positiveControlledRaw_truthTable]
  have hiff : (∀ wire ∈ (Finset.univ : ControlSet target),
      patternFlipBasis target pattern input wire = true) ↔
      (splitTarget target input).2 = pattern :=
    all_true_patternFlipBasis_iff controlCount target pattern input
  by_cases hmatch : (splitTarget target input).2 = pattern
  · rw [if_pos hmatch, if_pos (hiff.mpr hmatch)]
  · rw [if_neg hmatch, if_neg (fun hall => hmatch (hiff.mp hall))]

/-- Exact evaluator of the mixed-polarity flip/apply/unflip construction. -/
@[simp]
theorem eval_patternControlledCircuit (controlCount : ℕ)
    (target : Fin (controlCount + 1)) (pattern : ComplementBasis target)
    (U : QubitUnitary) :
    Circuit.eval (patternControlledCircuit controlCount target pattern U) =
      patternControlledUnitary target pattern U := by
  let flips := patternFlipCircuit target pattern
  let P : UnitaryGate (controlCount + 1) := Circuit.eval flips
  let L : UnitaryGate (controlCount + 1) := localUnitary target U
  have hcomm : Commute P L := by
    exact eval_patternFlipCircuit_commute_localUnitary target pattern U
  have hactive : P⁻¹ * L * P = L := by
    calc
      P⁻¹ * L * P = P⁻¹ * (L * P) := by rw [mul_assoc]
      _ = P⁻¹ * (P * L) := by rw [← hcomm.eq]
      _ = L := by simp
  apply Subtype.ext
  rw [matrix_eq_iff_mulVec_basisKet_eq]
  intro input
  rw [patternControlledCircuit, Circuit.eval_append, Circuit.eval_append,
    Circuit.eval_adjoint]
  change ((((P⁻¹ * Circuit.eval (fullControlCircuit controlCount target U)) * P :
      UnitaryGate (controlCount + 1)) : Gate (controlCount + 1)) *ᵥ
        basisKet input) = _
  rw [coe_patternControlledUnitary, controlledRaw_truthTable]
  simp only [exactPatternEnabled, decide_eq_true_eq]
  change (((P⁻¹ : Gate (controlCount + 1)) *
      (Circuit.eval (fullControlCircuit controlCount target U) :
        Gate (controlCount + 1)) * (P : Gate (controlCount + 1))) *ᵥ
      basisKet input) = _
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    eval_patternFlipCircuit_mulVec_basisKet,
    eval_fullControlCircuit_patternFlipBasis]
  by_cases hmatch : (splitTarget target input).2 = pattern
  · rw [if_pos hmatch, if_pos hmatch]
    change ((P⁻¹ : Gate (controlCount + 1)) *ᵥ
        (L : Gate (controlCount + 1)) *ᵥ
          basisKet (patternFlipBasis target pattern input)) =
      (L : Gate (controlCount + 1)) *ᵥ basisKet input
    rw [← eval_patternFlipCircuit_mulVec_basisKet target pattern input]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    change ((P⁻¹ * L * P : UnitaryGate (controlCount + 1)) :
        Gate (controlCount + 1)) *ᵥ basisKet input = _
    rw [hactive]
  · rw [if_neg hmatch, if_neg hmatch]
    rw [← eval_patternFlipCircuit_mulVec_basisKet target pattern input]
    rw [Matrix.mulVec_mulVec]
    change (((P⁻¹ * P : UnitaryGate (controlCount + 1)) :
      Gate (controlCount + 1)) *ᵥ basisKet input) = basisKet input
    simp

/-! ## Literal syntax accounting -/

/-- Number of local-X nodes in the negative-control prefix. -/
def patternFlipCount {n : ℕ} {target : Fin n}
    (pattern : ComplementBasis target) : ℕ :=
  (falsePatternWires pattern).length

@[simp]
theorem patternFlipCircuit_gateCount {n : ℕ} (target : Fin n)
    (pattern : ComplementBasis target) :
    Circuit.gateCount (patternFlipCircuit target pattern) =
      patternFlipCount pattern := by
  simp [patternFlipCircuit, xCircuit, patternFlipCount, Circuit.gateCount]

@[simp]
theorem patternFlipCircuit_oneQubitCNOTCost {n : ℕ} (target : Fin n)
    (pattern : ComplementBasis target) :
    Circuit.cost CostModel.oneQubitCNOT (patternFlipCircuit target pattern) =
      some (patternFlipCount pattern) := by
  have hx : ∀ wires : List (Fin n),
      Circuit.cost CostModel.oneQubitCNOT (xCircuit wires) =
        some wires.length := by
    intro wires
    induction wires with
    | nil => rfl
    | cons wire wires ih =>
        rw [xCircuit_cons, Circuit.cost_cons, Primitive.oneQubit_kind,
          CostModel.oneQubitCNOT_oneQubit, ih]
        simp [Circuit.addCost]
        omega
  exact hx (falsePatternWires pattern)

/-- Exact accepted cost of the mixed-polarity implementation. -/
@[simp]
theorem patternControlledCircuit_oneQubitCNOTCost (controlCount : ℕ)
    (target : Fin (controlCount + 1)) (pattern : ComplementBasis target)
    (U : QubitUnitary) :
    Circuit.cost CostModel.oneQubitCNOT
        (patternControlledCircuit controlCount target pattern U) =
      some (2 * patternFlipCount pattern + fullControlCircuitCost controlCount) := by
  rw [patternControlledCircuit, Circuit.cost_append, Circuit.cost_append,
    Circuit.cost_adjoint, patternFlipCircuit_oneQubitCNOTCost,
    fullControlCircuit_oneQubitCNOTCost]
  simp only [Circuit.addCost_some, Option.some.injEq]
  omega

end

end Barenco.Universality
