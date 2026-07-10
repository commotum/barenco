import Barenco.Universality.AdjacentTwoLevel
import Barenco.Universality.EliminationCore

/-!
# Exact literal circuits for diagonal unitaries

On a register of positive width `controlCount + 1`, fix a target wire.  Every
assignment of the complementary wires names exactly two basis states, according
to whether the target bit is `false` or `true`.  A diagonal unitary therefore
restricts on that pair to a diagonal one-qubit unitary.  This module constructs
that certified block for every complementary pattern and concatenates the exact
mixed-polarity implementation supplied by `PatternControl`.

No diagonal phase is discarded.  The final theorem is exact matrix equality,
including the one-qubit and zero-control boundary.
-/

namespace Barenco.Universality

open Matrix
open Barenco.OneQubit
open scoped Matrix

noncomputable section

/-! ## Diagonal entries and certified two-entry blocks -/

/-- A diagonal unitary's individual diagonal entries have squared norm one. -/
theorem diagonalUnitary_entry_star_mul {n : ℕ} (D : UnitaryGate n)
    (hD : IsDiagonalUnitary D) (index : Basis n) :
    star (D index index) * D index index = 1 := by
  have hunitary : star (D : Gate n) * (D : Gate n) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp D.property
  have hentry := congrFun (congrFun hunitary index) index
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply,
    if_pos] at hentry
  rw [Finset.sum_eq_single index] at hentry
  · exact hentry
  · intro other _ hother
    rw [hD other index hother]
    simp
  · simp

/-- A certified diagonal one-qubit unitary from two unit-modulus scalars. -/
def diagonalQubitUnitary (zFalse zTrue : ℂ)
    (hFalse : star zFalse * zFalse = 1)
    (hTrue : star zTrue * zTrue = 1) : QubitUnitary := by
  refine ⟨matrix2 zFalse 0 0 zTrue, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff', star_matrix2, matrix2_mul]
  apply Matrix.ext
  intro row col
  cases row <;> cases col <;> simp [hFalse, hTrue]

@[simp]
theorem diagonalQubitUnitary_false_false (zFalse zTrue : ℂ)
    (hFalse : star zFalse * zFalse = 1)
    (hTrue : star zTrue * zTrue = 1) :
    diagonalQubitUnitary zFalse zTrue hFalse hTrue false false = zFalse := rfl

@[simp]
theorem diagonalQubitUnitary_false_true (zFalse zTrue : ℂ)
    (hFalse : star zFalse * zFalse = 1)
    (hTrue : star zTrue * zTrue = 1) :
    diagonalQubitUnitary zFalse zTrue hFalse hTrue false true = 0 := rfl

@[simp]
theorem diagonalQubitUnitary_true_false (zFalse zTrue : ℂ)
    (hFalse : star zFalse * zFalse = 1)
    (hTrue : star zTrue * zTrue = 1) :
    diagonalQubitUnitary zFalse zTrue hFalse hTrue true false = 0 := rfl

@[simp]
theorem diagonalQubitUnitary_true_true (zFalse zTrue : ℂ)
    (hFalse : star zFalse * zFalse = 1)
    (hTrue : star zTrue * zTrue = 1) :
    diagonalQubitUnitary zFalse zTrue hFalse hTrue true true = zTrue := rfl

/-- Reassemble a basis assignment from its target bit and complementary pattern. -/
def targetPatternBasis {n : ℕ} (target : Fin n)
    (pattern : ComplementBasis target) (bit : Bool) : Basis n :=
  (splitTarget target).symm (bit, pattern)

@[simp]
theorem splitTarget_targetPatternBasis {n : ℕ} (target : Fin n)
    (pattern : ComplementBasis target) (bit : Bool) :
    splitTarget target (targetPatternBasis target pattern bit) = (bit, pattern) := by
  simp [targetPatternBasis]

@[simp]
theorem targetPatternBasis_target {n : ℕ} (target : Fin n)
    (pattern : ComplementBasis target) (bit : Bool) :
    targetPatternBasis target pattern bit target = bit := by
  change (splitTarget target (targetPatternBasis target pattern bit)).1 = bit
  simp

@[simp]
theorem targetPatternBasis_complement {n : ℕ} (target : Fin n)
    (pattern : ComplementBasis target) (bit : Bool) :
    (splitTarget target (targetPatternBasis target pattern bit)).2 = pattern := by
  simp

@[simp]
theorem setTarget_targetPatternBasis {n : ℕ} (target : Fin n)
    (pattern : ComplementBasis target) (first second : Bool) :
    setTarget target (targetPatternBasis target pattern first) second =
      targetPatternBasis target pattern second := by
  apply (splitTarget target).injective
  simp

/-- The exact two diagonal entries of `D` over one complementary pattern. -/
def diagonalPatternBlock {controlCount : ℕ}
    (target : Fin (controlCount + 1)) (D : UnitaryGate (controlCount + 1))
    (hD : IsDiagonalUnitary D) (pattern : ComplementBasis target) :
    QubitUnitary :=
  let falseState := targetPatternBasis target pattern false
  let trueState := targetPatternBasis target pattern true
  diagonalQubitUnitary (D falseState falseState) (D trueState trueState)
    (diagonalUnitary_entry_star_mul D hD falseState)
    (diagonalUnitary_entry_star_mul D hD trueState)

@[simp]
theorem diagonalPatternBlock_apply_same {controlCount : ℕ}
    (target : Fin (controlCount + 1)) (D : UnitaryGate (controlCount + 1))
    (hD : IsDiagonalUnitary D) (pattern : ComplementBasis target) (bit : Bool) :
    diagonalPatternBlock target D hD pattern bit bit =
      D (targetPatternBasis target pattern bit)
        (targetPatternBasis target pattern bit) := by
  cases bit <;> rfl

@[simp]
theorem diagonalPatternBlock_apply_ne {controlCount : ℕ}
    (target : Fin (controlCount + 1)) (D : UnitaryGate (controlCount + 1))
    (hD : IsDiagonalUnitary D) (pattern : ComplementBasis target)
    {row col : Bool} (hrowCol : row ≠ col) :
    diagonalPatternBlock target D hD pattern row col = 0 := by
  cases row <;> cases col <;> simp_all [diagonalPatternBlock]

/-- Exact local action of one selected diagonal block. -/
theorem local_diagonalPatternBlock_mulVec_basisKet {controlCount : ℕ}
    (target : Fin (controlCount + 1)) (D : UnitaryGate (controlCount + 1))
    (hD : IsDiagonalUnitary D) (pattern : ComplementBasis target) (bit : Bool) :
    localRaw target (diagonalPatternBlock target D hD pattern) *ᵥ
        basisKet (targetPatternBasis target pattern bit) =
      D (targetPatternBasis target pattern bit)
          (targetPatternBasis target pattern bit) •
        basisKet (targetPatternBasis target pattern bit) := by
  rw [localRaw_mulVec_basisKet_eq_pair]
  cases bit <;> simp

/-! ## Pattern list and literal circuit -/

/-- Every complementary pattern, exactly once, in `Finset.toList` order. -/
def allComplementPatterns {controlCount : ℕ}
    (target : Fin (controlCount + 1)) : List (ComplementBasis target) :=
  (Finset.univ : Finset (ComplementBasis target)).toList

@[simp]
theorem mem_allComplementPatterns {controlCount : ℕ}
    (target : Fin (controlCount + 1)) (pattern : ComplementBasis target) :
    pattern ∈ allComplementPatterns target := by
  simp [allComplementPatterns]

theorem nodup_allComplementPatterns {controlCount : ℕ}
    (target : Fin (controlCount + 1)) :
    (allComplementPatterns target).Nodup := by
  exact Finset.nodup_toList _

/-- Literal implementation associated with one complementary pattern. -/
def diagonalPatternCircuit {controlCount : ℕ}
    (target : Fin (controlCount + 1)) (D : UnitaryGate (controlCount + 1))
    (hD : IsDiagonalUnitary D) (pattern : ComplementBasis target) :
    Circuit (controlCount + 1) :=
  patternControlledCircuit controlCount target pattern
    (diagonalPatternBlock target D hD pattern)

/-- Concatenate the pattern circuits in the supplied chronological order. -/
def diagonalPatternCircuits {controlCount : ℕ}
    (target : Fin (controlCount + 1)) (D : UnitaryGate (controlCount + 1))
    (hD : IsDiagonalUnitary D) (patterns : List (ComplementBasis target)) :
    Circuit (controlCount + 1) :=
  patterns.flatMap (diagonalPatternCircuit target D hD)

@[simp]
theorem diagonalPatternCircuits_nil {controlCount : ℕ}
    (target : Fin (controlCount + 1)) (D : UnitaryGate (controlCount + 1))
    (hD : IsDiagonalUnitary D) :
    diagonalPatternCircuits target D hD [] = [] := rfl

@[simp]
theorem diagonalPatternCircuits_cons {controlCount : ℕ}
    (target : Fin (controlCount + 1)) (D : UnitaryGate (controlCount + 1))
    (hD : IsDiagonalUnitary D) (pattern : ComplementBasis target)
    (patterns : List (ComplementBasis target)) :
    diagonalPatternCircuits target D hD (pattern :: patterns) =
      Circuit.append (diagonalPatternCircuit target D hD pattern)
        (diagonalPatternCircuits target D hD patterns) := rfl

/-- One literal mixed-polarity block for every complementary pattern. -/
def diagonalCircuit (controlCount : ℕ)
    (target : Fin (controlCount + 1)) (D : UnitaryGate (controlCount + 1))
    (hD : IsDiagonalUnitary D) : Circuit (controlCount + 1) :=
  diagonalPatternCircuits target D hD (allComplementPatterns target)

/-! ## Exact semantics -/

/-- Basis action of one pattern circuit, including its inactive branch. -/
theorem eval_diagonalPatternCircuit_mulVec_basisKet {controlCount : ℕ}
    (target : Fin (controlCount + 1)) (D : UnitaryGate (controlCount + 1))
    (hD : IsDiagonalUnitary D) (pattern : ComplementBasis target)
    (input : Basis (controlCount + 1)) :
    (Circuit.eval (diagonalPatternCircuit target D hD pattern) :
        Gate (controlCount + 1)) *ᵥ basisKet input =
      if (splitTarget target input).2 = pattern then
        D input input • basisKet input
      else basisKet input := by
  rw [diagonalPatternCircuit, eval_patternControlledCircuit,
    coe_patternControlledUnitary, controlledRaw_truthTable]
  simp only [exactPatternEnabled, decide_eq_true_eq]
  by_cases hpattern : (splitTarget target input).2 = pattern
  · rw [if_pos hpattern]
    have hinput : input = targetPatternBasis target pattern (input target) := by
      apply (splitTarget target).injective
      apply Prod.ext
      · rfl
      · exact hpattern
    subst input
    exact local_diagonalPatternBlock_mulVec_basisKet target D hD pattern _
  · rw [if_neg hpattern]

/--
Action of an arbitrary duplicate-free pattern schedule. Exactly the matching
pattern contributes its phase; if no pattern matches, the input is fixed.
-/
theorem eval_diagonalPatternCircuits_mulVec_basisKet {controlCount : ℕ}
    (target : Fin (controlCount + 1)) (D : UnitaryGate (controlCount + 1))
    (hD : IsDiagonalUnitary D) :
    ∀ (patterns : List (ComplementBasis target)), patterns.Nodup →
      ∀ input : Basis (controlCount + 1),
      (Circuit.eval (diagonalPatternCircuits target D hD patterns) :
          Gate (controlCount + 1)) *ᵥ basisKet input =
        if (splitTarget target input).2 ∈ patterns then
          D input input • basisKet input
        else basisKet input
  | [], _hnodup, input => by simp
  | pattern :: patterns, hnodup, input => by
      rw [diagonalPatternCircuits_cons, Circuit.eval_append]
      change (((Circuit.eval (diagonalPatternCircuits target D hD patterns) :
          UnitaryGate (controlCount + 1)) : Gate (controlCount + 1)) *
          ((Circuit.eval (diagonalPatternCircuit target D hD pattern) :
            UnitaryGate (controlCount + 1)) : Gate (controlCount + 1))) *ᵥ
        basisKet input = _
      rw [← Matrix.mulVec_mulVec,
        eval_diagonalPatternCircuit_mulVec_basisKet]
      have hpatternNotMem : pattern ∉ patterns := (List.nodup_cons.mp hnodup).1
      have htailNodup : patterns.Nodup := (List.nodup_cons.mp hnodup).2
      by_cases hmatch : (splitTarget target input).2 = pattern
      · rw [if_pos hmatch, Matrix.mulVec_smul,
          eval_diagonalPatternCircuits_mulVec_basisKet target D hD patterns
            htailNodup input]
        have hnotTail : (splitTarget target input).2 ∉ patterns := by
          simpa [hmatch] using hpatternNotMem
        rw [if_neg hnotTail]
        simp [hmatch]
      · rw [if_neg hmatch,
          eval_diagonalPatternCircuits_mulVec_basisKet target D hD patterns
            htailNodup input]
        simp [hmatch]

/-- A diagonal unitary acts on each basis ket by its exact diagonal phase. -/
theorem diagonalUnitary_mulVec_basisKet {n : ℕ} (D : UnitaryGate n)
    (hD : IsDiagonalUnitary D) (input : Basis n) :
    (D : Gate n) *ᵥ basisKet input = D input input • basisKet input := by
  funext row
  rw [mulVec_basisKet_apply]
  by_cases hrow : row = input
  · subst row
    simp
  · rw [hD row input hrow]
    simp [basisKet_apply, hrow]

/-- Exact evaluator of the complete diagonal circuit; all phases are retained. -/
@[simp]
theorem eval_diagonalCircuit (controlCount : ℕ)
    (target : Fin (controlCount + 1)) (D : UnitaryGate (controlCount + 1))
    (hD : IsDiagonalUnitary D) :
    Circuit.eval (diagonalCircuit controlCount target D hD) = D := by
  apply Subtype.ext
  rw [matrix_eq_iff_mulVec_basisKet_eq]
  intro input
  rw [diagonalCircuit,
    eval_diagonalPatternCircuits_mulVec_basisKet target D hD
      (allComplementPatterns target) (nodup_allComplementPatterns target) input,
    if_pos (mem_allComplementPatterns target (splitTarget target input).2),
    diagonalUnitary_mulVec_basisKet]

/-! ## Literal accepted cost -/

/-- Sum of the exact accepted costs of the selected pattern circuits. -/
def diagonalPatternCircuitsCost {controlCount : ℕ}
    (target : Fin (controlCount + 1))
    (patterns : List (ComplementBasis target)) : ℕ :=
  (patterns.map fun pattern =>
    2 * patternFlipCount pattern + fullControlCircuitCost controlCount).sum

/-- Exact accepted cost of any finite pattern schedule. -/
theorem diagonalPatternCircuits_oneQubitCNOTCost {controlCount : ℕ}
    (target : Fin (controlCount + 1)) (D : UnitaryGate (controlCount + 1))
    (hD : IsDiagonalUnitary D) :
    ∀ patterns : List (ComplementBasis target),
      Circuit.cost CostModel.oneQubitCNOT
          (diagonalPatternCircuits target D hD patterns) =
        some (diagonalPatternCircuitsCost target patterns)
  | [] => by simp [diagonalPatternCircuitsCost]
  | pattern :: patterns => by
      rw [diagonalPatternCircuits_cons, Circuit.cost_append,
        diagonalPatternCircuits_oneQubitCNOTCost target D hD patterns]
      simp [diagonalPatternCircuit, diagonalPatternCircuitsCost]

/-- Exact finite-sum cost of the complete diagonal circuit. -/
@[simp]
theorem diagonalCircuit_oneQubitCNOTCost (controlCount : ℕ)
    (target : Fin (controlCount + 1)) (D : UnitaryGate (controlCount + 1))
    (hD : IsDiagonalUnitary D) :
    Circuit.cost CostModel.oneQubitCNOT
        (diagonalCircuit controlCount target D hD) =
      some (diagonalPatternCircuitsCost target (allComplementPatterns target)) := by
  exact diagonalPatternCircuits_oneQubitCNOTCost target D hD _

/-- Existential accepted-cost form for callers that do not inspect the sum. -/
theorem exists_diagonalCircuit_oneQubitCNOTCost (controlCount : ℕ)
    (target : Fin (controlCount + 1)) (D : UnitaryGate (controlCount + 1))
    (hD : IsDiagonalUnitary D) :
    ∃ cost, Circuit.cost CostModel.oneQubitCNOT
      (diagonalCircuit controlCount target D hD) = some cost :=
  ⟨diagonalPatternCircuitsCost target (allComplementPatterns target),
    diagonalCircuit_oneQubitCNOTCost controlCount target D hD⟩

end

end Barenco.Universality
