import Barenco.ThreeQubit.Lemma61

/-!
# Barenco Corollary 6.2: sixteen one-qubit/CNOT primitives

This file expands the three controlled-one-qubit macros in Lemma 6.1 using one
shared Corollary 5.3 decomposition.  The direct expansion has twenty primitives:
twelve one-qubit gates and eight CNOTs.  The middle implementation is the exact
adjoint of the first, so two inverse pairs can be commuted across operations on
disjoint wires and cancelled.  The resulting named syntax has exactly sixteen
primitives: eight one-qubit gates and eight CNOTs.

The source calls the cancelled gates adjacent. In chronological list syntax they
are not literally adjacent; their separation by control-only operations is why
the disjoint-wire commutation theorems from `Lemma61` are required.
-/

namespace Barenco.ThreeQubit

open Barenco.OneQubit
open Barenco.ControlledCircuit

noncomputable section

/--
The unmerged twenty-node expansion
`S(second); K; S(second)†; K; S(first)`.

Here `S(control)` is the six-node Corollary 5.3 circuit and `K` is CNOT from the
first control to the second. The same parameters are deliberately reused at both
controls, and the middle circuit is their exact syntactic adjoint.
-/
def doubleControlledExpansion20Circuit {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (delta : ℝ) (A B C : QubitUnitary) : Circuit n :=
  Circuit.append
    (controlledU2Circuit second target hsecondTarget delta A B C)
    (Circuit.append [Primitive.cnot first second hfirstSecond]
      (Circuit.append
        (Circuit.adjoint
          (controlledU2Circuit second target hsecondTarget delta A B C))
        (Circuit.append [Primitive.cnot first second hfirstSecond]
          (controlledU2Circuit first target hfirstTarget delta A B C))))

/--
The explicit sixteen-node circuit after the paper's two inverse-pair
cancellations.
-/
def doubleControlledExpansion16Circuit {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (delta : ℝ) (A B C : QubitUnitary) : Circuit n :=
  [Primitive.oneQubit second (controlPhaseUnitary delta),
    Primitive.oneQubit target A,
    Primitive.cnot second target hsecondTarget,
    Primitive.oneQubit target B,
    Primitive.cnot second target hsecondTarget,
    Primitive.cnot first second hfirstSecond,
    (Primitive.cnot second target hsecondTarget).adjoint,
    (Primitive.oneQubit target B).adjoint,
    (Primitive.cnot second target hsecondTarget).adjoint,
    (Primitive.oneQubit second (controlPhaseUnitary delta)).adjoint,
    Primitive.cnot first second hfirstSecond,
    Primitive.oneQubit first (controlPhaseUnitary delta),
    Primitive.cnot first target hfirstTarget,
    Primitive.oneQubit target B,
    Primitive.cnot first target hfirstTarget,
    Primitive.oneQubit target C]

/-! ## Exact cancellation semantics -/

private theorem eval_local_cnot_localAdjoint {n : ℕ}
    (control cnotTarget localTarget : Fin n)
    (hct : control ≠ cnotTarget) (hcl : control ≠ localTarget)
    (htl : cnotTarget ≠ localTarget) (U : QubitUnitary) :
    Circuit.eval
        [Primitive.oneQubit localTarget U,
          Primitive.cnot control cnotTarget hct,
          (Primitive.oneQubit localTarget U).adjoint] =
      Circuit.eval [Primitive.cnot control cnotTarget hct] := by
  simp only [Circuit.eval_cons, Circuit.eval_nil, one_mul,
    Primitive.adjoint_denotation, Primitive.oneQubit_denotation,
    Primitive.cnot_denotation]
  rw [mul_assoc,
    cnotUnitary_commute_localUnitary control cnotTarget localTarget
      hct hcl htl]
  simp

private theorem eval_A_controlOnly_A_cancel {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (delta : ℝ) (A : QubitUnitary) :
    Circuit.eval
        [(Primitive.oneQubit target A).adjoint,
          (Primitive.oneQubit second (controlPhaseUnitary delta)).adjoint,
          Primitive.cnot first second hfirstSecond,
          Primitive.oneQubit first (controlPhaseUnitary delta),
          Primitive.oneQubit target A] =
      Circuit.eval
        [(Primitive.oneQubit second (controlPhaseUnitary delta)).adjoint,
          Primitive.cnot first second hfirstSecond,
          Primitive.oneQubit first (controlPhaseUnitary delta)] := by
  let LA : UnitaryGate n := localUnitary target A
  let E1 : UnitaryGate n := localUnitary first (controlPhaseUnitary delta)
  let E2 : UnitaryGate n := localUnitary second (controlPhaseUnitary delta)
  let K : UnitaryGate n := cnotUnitary first second hfirstSecond
  simp only [Circuit.eval_cons, Circuit.eval_nil, one_mul,
    Primitive.adjoint_denotation, Primitive.oneQubit_denotation,
    Primitive.cnot_denotation]
  change LA * E1 * K * E2⁻¹ * LA⁻¹ = E1 * K * E2⁻¹
  have hAE1 : Commute LA E1 := by
    exact localUnitary_commute_of_ne target first hfirstTarget.symm A
      (controlPhaseUnitary delta)
  have hAK : Commute LA K := by
    exact (cnotUnitary_commute_localUnitary first second target
      hfirstSecond hfirstTarget hsecondTarget A).symm
  have hAE2 : Commute LA E2 := by
    exact localUnitary_commute_of_ne target second hsecondTarget.symm A
      (controlPhaseUnitary delta)
  calc
    LA * E1 * K * E2⁻¹ * LA⁻¹ =
        E1 * LA * K * E2⁻¹ * LA⁻¹ := by rw [hAE1.eq]
    _ = E1 * K * LA * E2⁻¹ * LA⁻¹ := by
      rw [mul_assoc E1 LA K, hAK.eq, ← mul_assoc E1 K LA]
    _ = E1 * K * E2⁻¹ * LA * LA⁻¹ := by
      rw [mul_assoc (E1 * K) LA E2⁻¹, (hAE2.inv_right).eq,
        ← mul_assoc (E1 * K) E2⁻¹ LA]
    _ = E1 * K * E2⁻¹ := by simp

/--
The paper's two implicit disjoint-wire commutations and inverse-pair
cancellations turn the twenty-node expansion into the explicit sixteen-node
circuit without changing its full-register evaluator.
-/
theorem eval_doubleControlledExpansion20Circuit_eq_16 {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (delta : ℝ) (A B C : QubitUnitary) :
    Circuit.eval
        (doubleControlledExpansion20Circuit first second target hfirstSecond
          hfirstTarget hsecondTarget delta A B C) =
      Circuit.eval
        (doubleControlledExpansion16Circuit first second target hfirstSecond
          hfirstTarget hsecondTarget delta A B C) := by
  change Circuit.eval (Circuit.append
      [Primitive.oneQubit second (controlPhaseUnitary delta),
        Primitive.oneQubit target A,
        Primitive.cnot second target hsecondTarget,
        Primitive.oneQubit target B,
        Primitive.cnot second target hsecondTarget]
      (Circuit.append
        [Primitive.oneQubit target C,
          Primitive.cnot first second hfirstSecond,
          (Primitive.oneQubit target C).adjoint]
        (Circuit.append
          [(Primitive.cnot second target hsecondTarget).adjoint,
            (Primitive.oneQubit target B).adjoint,
            (Primitive.cnot second target hsecondTarget).adjoint]
          (Circuit.append
            [(Primitive.oneQubit target A).adjoint,
              (Primitive.oneQubit second (controlPhaseUnitary delta)).adjoint,
              Primitive.cnot first second hfirstSecond,
              Primitive.oneQubit first (controlPhaseUnitary delta),
              Primitive.oneQubit target A]
            [Primitive.cnot first target hfirstTarget,
              Primitive.oneQubit target B,
              Primitive.cnot first target hfirstTarget,
              Primitive.oneQubit target C])))) =
    Circuit.eval (Circuit.append
      [Primitive.oneQubit second (controlPhaseUnitary delta),
        Primitive.oneQubit target A,
        Primitive.cnot second target hsecondTarget,
        Primitive.oneQubit target B,
        Primitive.cnot second target hsecondTarget]
      (Circuit.append
        [Primitive.cnot first second hfirstSecond]
        (Circuit.append
          [(Primitive.cnot second target hsecondTarget).adjoint,
            (Primitive.oneQubit target B).adjoint,
            (Primitive.cnot second target hsecondTarget).adjoint]
          (Circuit.append
            [(Primitive.oneQubit second (controlPhaseUnitary delta)).adjoint,
              Primitive.cnot first second hfirstSecond,
              Primitive.oneQubit first (controlPhaseUnitary delta)]
            [Primitive.cnot first target hfirstTarget,
              Primitive.oneQubit target B,
              Primitive.cnot first target hfirstTarget,
              Primitive.oneQubit target C]))))
  simp only [Circuit.eval_append]
  rw [eval_local_cnot_localAdjoint first second target hfirstSecond
      hfirstTarget hsecondTarget C,
    eval_A_controlOnly_A_cancel first second target hfirstSecond
      hfirstTarget hsecondTarget delta A]

/-! ## Structural resources -/

@[simp]
theorem doubleControlledExpansion20Circuit_gateCount {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (delta : ℝ) (A B C : QubitUnitary) :
  Circuit.gateCount
      (doubleControlledExpansion20Circuit first second target hfirstSecond
        hfirstTarget hsecondTarget delta A B C) = 20 := by
  rfl

@[simp]
theorem doubleControlledExpansion20Circuit_kindCounts {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (delta : ℝ) (A B C : QubitUnitary) :
    Circuit.kindCount .oneQubit
        (doubleControlledExpansion20Circuit first second target hfirstSecond
          hfirstTarget hsecondTarget delta A B C) = 12 ∧
      Circuit.kindCount .cnot
        (doubleControlledExpansion20Circuit first second target hfirstSecond
          hfirstTarget hsecondTarget delta A B C) = 8 := by
  constructor <;> rfl

@[simp]
theorem doubleControlledExpansion20Circuit_oneQubitCNOTCost {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (delta : ℝ) (A B C : QubitUnitary) :
    Circuit.cost CostModel.oneQubitCNOT
      (doubleControlledExpansion20Circuit first second target hfirstSecond
        hfirstTarget hsecondTarget delta A B C) = some 20 := by
  simp [doubleControlledExpansion20Circuit, Circuit.cost_append,
    Circuit.cost, Circuit.addCost]

@[simp]
theorem doubleControlledExpansion16Circuit_gateCount {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (delta : ℝ) (A B C : QubitUnitary) :
    Circuit.gateCount
      (doubleControlledExpansion16Circuit first second target hfirstSecond
        hfirstTarget hsecondTarget delta A B C) = 16 := by
  rfl

@[simp]
theorem doubleControlledExpansion16Circuit_kindCounts {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (delta : ℝ) (A B C : QubitUnitary) :
    Circuit.kindCount .oneQubit
        (doubleControlledExpansion16Circuit first second target hfirstSecond
          hfirstTarget hsecondTarget delta A B C) = 8 ∧
      Circuit.kindCount .cnot
        (doubleControlledExpansion16Circuit first second target hfirstSecond
          hfirstTarget hsecondTarget delta A B C) = 8 := by
  simp [doubleControlledExpansion16Circuit, Circuit.kindCount]

@[simp]
theorem doubleControlledExpansion16Circuit_oneQubitCNOTCost {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (delta : ℝ) (A B C : QubitUnitary) :
    Circuit.cost CostModel.oneQubitCNOT
      (doubleControlledExpansion16Circuit first second target hfirstSecond
        hfirstTarget hsecondTarget delta A B C) = some 16 := by
  simp [doubleControlledExpansion16Circuit, Circuit.cost, Circuit.addCost]

/-! ## Semantic bridge and Corollary 6.2 -/

/-- A singleton-controlled identity is the full-register identity. -/
@[simp]
theorem singleControlledUnitary_one {n : ℕ}
    (control target : Fin n) (h : control ≠ target) :
    positiveControlledUnitary target ({⟨control, h⟩} : ControlSet target)
        (1 : QubitUnitary) = 1 := by
  apply Subtype.ext
  rw [coe_positiveControlledUnitary,
    positiveControlledRaw_singleton_eq_targetBlockRaw]
  simp

/-- Inversion passes through a singleton positive control exactly. -/
@[simp]
theorem singleControlledUnitary_inv {n : ℕ}
    (control target : Fin n) (h : control ≠ target) (V : QubitUnitary) :
    (positiveControlledUnitary target
      ({⟨control, h⟩} : ControlSet target) V)⁻¹ =
      positiveControlledUnitary target
        ({⟨control, h⟩} : ControlSet target) V⁻¹ := by
  apply inv_eq_iff_mul_eq_one.mpr
  rw [singleControlledUnitary_mul, mul_inv_cancel, singleControlledUnitary_one]

/-- The twenty-node expansion is exactly the Lemma 6.1 macro evaluator. -/
theorem eval_doubleControlledExpansion20Circuit_eq_macro {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (delta : ℝ) (A B C V : QubitUnitary)
    (hsecond : Circuit.eval
        (controlledU2Circuit second target hsecondTarget delta A B C) =
      positiveControlledUnitary target
        ({⟨second, hsecondTarget⟩} : ControlSet target) V)
    (hfirst : Circuit.eval
        (controlledU2Circuit first target hfirstTarget delta A B C) =
      positiveControlledUnitary target
        ({⟨first, hfirstTarget⟩} : ControlSet target) V) :
    Circuit.eval (doubleControlledExpansion20Circuit first second target
        hfirstSecond hfirstTarget hsecondTarget delta A B C) =
      Circuit.eval (doubleControlledViaSquareCircuit first second target
        hfirstSecond hfirstTarget hsecondTarget V) := by
  rw [doubleControlledExpansion20Circuit, Circuit.eval_append,
    Circuit.eval_append, Circuit.eval_append, Circuit.eval_append,
    Circuit.eval_adjoint, hsecond, hfirst, singleControlledUnitary_inv]
  simp [doubleControlledViaSquareCircuit, Circuit.eval]

/-- The sixteen-node syntax is correct from one shared Section 5 factorization. -/
theorem eval_doubleControlledExpansion16Circuit_of_products {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (delta : ℝ) (A B C W V U : QubitUnitary)
    (hinactive : (C : QubitMatrix) * (B : QubitMatrix) * (A : QubitMatrix) = 1)
    (hactive : (C : QubitMatrix) * sigmaX * (B : QubitMatrix) * sigmaX *
      (A : QubitMatrix) = (W : QubitMatrix))
    (hV : (V : QubitMatrix) = phaseShift delta * (W : QubitMatrix))
    (hSq : V ^ 2 = U) :
    Circuit.eval (doubleControlledExpansion16Circuit first second target
        hfirstSecond hfirstTarget hsecondTarget delta A B C) =
      positiveControlledUnitary target
        (twoControlSet first second target hfirstTarget hsecondTarget) U := by
  have hsecond := eval_controlledU2Circuit_of_products second target hsecondTarget
    delta A B C W V hinactive hactive hV
  have hfirst := eval_controlledU2Circuit_of_products first target hfirstTarget
    delta A B C W V hinactive hactive hV
  calc
    Circuit.eval (doubleControlledExpansion16Circuit first second target
        hfirstSecond hfirstTarget hsecondTarget delta A B C) =
        Circuit.eval (doubleControlledExpansion20Circuit first second target
          hfirstSecond hfirstTarget hsecondTarget delta A B C) :=
      (eval_doubleControlledExpansion20Circuit_eq_16 first second target
        hfirstSecond hfirstTarget hsecondTarget delta A B C).symm
    _ = Circuit.eval (doubleControlledViaSquareCircuit first second target
          hfirstSecond hfirstTarget hsecondTarget V) :=
      eval_doubleControlledExpansion20Circuit_eq_macro first second target
        hfirstSecond hfirstTarget hsecondTarget delta A B C V hsecond hfirst
    _ = positiveControlledUnitary target
          (twoControlSet first second target hfirstTarget hsecondTarget) U :=
      eval_doubleControlledViaSquareCircuit_of_sq_eq first second target
        hfirstSecond hfirstTarget hsecondTarget U V hSq

/-- Selected-root witnesses choose the Section 5 factorization only once. -/
theorem doubleControlledExpansion16Circuit_exists {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (U : QubitUnitary) :
    ∃ A B C : QubitSpecialUnitary,
      Circuit.eval (doubleControlledExpansion16Circuit first second target
        hfirstSecond hfirstTarget hsecondTarget
        (determinantPhaseAngle (unitarySquareRoot U))
        (specialUnitaryAsUnitary A) (specialUnitaryAsUnitary B)
        (specialUnitaryAsUnitary C)) =
      positiveControlledUnitary target
        (twoControlSet first second target hfirstTarget hsecondTarget) U := by
  let V := unitarySquareRoot U
  obtain ⟨A, B, C, hinactive, hactive⟩ :=
    specialUnitary_exists_columnChronologicalABC (specialUnitaryPart V)
  refine ⟨A, B, C, ?_⟩
  apply eval_doubleControlledExpansion16Circuit_of_products first second target
    hfirstSecond hfirstTarget hsecondTarget (determinantPhaseAngle V)
    (specialUnitaryAsUnitary A) (specialUnitaryAsUnitary B)
    (specialUnitaryAsUnitary C)
    (specialUnitaryAsUnitary (specialUnitaryPart V)) V U
  · exact hinactive
  · exact hactive
  · exact (phaseShift_mul_specialUnitaryPart V).symm
  · exact unitarySquareRoot_pow_two U

/-- Corollary 6.2 as an exact existence-and-resource theorem. -/
theorem doubleControlledUnitary_has_sixteenPrimitiveCircuit {n : ℕ}
    (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target)
    (U : QubitUnitary) :
    ∃ circuit : Circuit n,
      Circuit.eval circuit = positiveControlledUnitary target
        (twoControlSet first second target hfirstTarget hsecondTarget) U ∧
      Circuit.gateCount circuit = 16 ∧
      Circuit.kindCount .oneQubit circuit = 8 ∧
      Circuit.kindCount .cnot circuit = 8 ∧
      Circuit.cost CostModel.oneQubitCNOT circuit = some 16 := by
  obtain ⟨A, B, C, heval⟩ := doubleControlledExpansion16Circuit_exists
    first second target hfirstSecond hfirstTarget hsecondTarget U
  let circuit := doubleControlledExpansion16Circuit first second target
    hfirstSecond hfirstTarget hsecondTarget
    (determinantPhaseAngle (unitarySquareRoot U))
    (specialUnitaryAsUnitary A) (specialUnitaryAsUnitary B)
    (specialUnitaryAsUnitary C)
  refine ⟨circuit, heval, ?_, ?_, ?_, ?_⟩ <;> simp [circuit]

end

end Barenco.ThreeQubit
