import Barenco.Basic

/-!
# Chronological circuit syntax

This module separates countable circuit syntax from matrix semantics. A circuit is
a list in execution order: its head runs first. Consequently, later primitive
denotations multiply on the left during evaluation.

Primitive kinds and supports are structural metadata. They are deliberately kept
independent of the certified unitary denotation so later cost models can inspect
syntax without attempting to recover a circuit from its matrix.
-/

namespace Barenco

open scoped Matrix

/-- Stable structural classes used by later resource-cost models. -/
inductive PrimitiveKind where
  /-- An arbitrary gate acting locally on one qubit. -/
  | oneQubit
  /-- A controlled-NOT gate. -/
  | cnot
  /-- A three-qubit Toffoli gate. -/
  | toffoli
  /-- A multiply controlled one-qubit gate retained before primitive expansion. -/
  | controlledOneQubit (controls : ℕ)
  /-- An arbitrary two-qubit unitary, as used by the paper's Section 8 cost model. -/
  | arbitraryTwoQubit
  /-- An explicitly tagged structural class for later extensions. -/
  | other (tag : String)
  deriving DecidableEq, Repr

/--
A syntactic primitive on an `n`-qubit register.

`kind` and `support` are retained for structural accounting. `denotation` is a
certified unitary, so every circuit made from primitives evaluates to a unitary
without a separate post-hoc proof.
-/
structure Primitive (n : ℕ) where
  kind : PrimitiveKind
  support : Finset (Fin n)
  denotation : UnitaryGate n

namespace Primitive

/-- The adjoint primitive preserves its structural class and wire support. -/
def adjoint {n : ℕ} (p : Primitive n) : Primitive n where
  kind := p.kind
  support := p.support
  denotation := p.denotation⁻¹

@[simp]
theorem adjoint_kind {n : ℕ} (p : Primitive n) : p.adjoint.kind = p.kind := rfl

@[simp]
theorem adjoint_support {n : ℕ} (p : Primitive n) : p.adjoint.support = p.support := rfl

@[simp]
theorem adjoint_denotation {n : ℕ} (p : Primitive n) :
    p.adjoint.denotation = p.denotation⁻¹ := rfl

/-- At the matrix level, inverse in the unitary group is conjugate transpose. -/
@[simp]
theorem adjoint_denotation_val {n : ℕ} (p : Primitive n) :
    (p.adjoint.denotation : Gate n) = star (p.denotation : Gate n) := rfl

@[simp]
theorem adjoint_adjoint {n : ℕ} (p : Primitive n) : p.adjoint.adjoint = p := by
  cases p
  simp [adjoint]

end Primitive

/-- A circuit is a chronological list of primitives; the head executes first. -/
abbrev Circuit (n : ℕ) := List (Primitive n)

namespace Circuit

/-- The empty chronological circuit. -/
def identity (n : ℕ) : Circuit n := []

/-- Sequential composition: execute `first`, then execute `second`. -/
def append {n : ℕ} (first second : Circuit n) : Circuit n := first ++ second

@[simp]
theorem identity_append {n : ℕ} (circuit : Circuit n) :
    append (identity n) circuit = circuit := rfl

@[simp]
theorem append_identity {n : ℕ} (circuit : Circuit n) :
    append circuit (identity n) = circuit := by
  exact List.append_nil circuit

theorem append_assoc {n : ℕ} (first second third : Circuit n) :
    append (append first second) third = append first (append second third) := by
  exact List.append_assoc first second third

/--
Certified evaluation of a chronological circuit. The head executes first, so its
denotation is the rightmost factor in the resulting product.
-/
def eval {n : ℕ} : Circuit n → UnitaryGate n
  | [] => 1
  | primitive :: circuit => eval circuit * primitive.denotation

@[simp]
theorem eval_nil {n : ℕ} : eval ([] : Circuit n) = 1 := rfl

@[simp]
theorem eval_identity (n : ℕ) : eval (identity n) = 1 := rfl

@[simp]
theorem eval_cons {n : ℕ} (primitive : Primitive n) (circuit : Circuit n) :
    eval (primitive :: circuit) = eval circuit * primitive.denotation := rfl

@[simp]
theorem eval_singleton {n : ℕ} (primitive : Primitive n) :
    eval [primitive] = primitive.denotation := by
  simp [eval]

/-- Generic order check: `first` runs before `second`. -/
@[simp]
theorem eval_pair {n : ℕ} (first second : Primitive n) :
    eval [first, second] = second.denotation * first.denotation := by
  simp [eval]

/--
Chronological concatenation evaluates with the later circuit on the left.
-/
theorem eval_append {n : ℕ} (first second : Circuit n) :
    eval (append first second) = eval second * eval first := by
  induction first with
  | nil => simp [append]
  | cons primitive first ih =>
      have ih' : eval (first ++ second) = eval second * eval first := by
        simpa [append] using ih
      simp only [append, List.cons_append, eval_cons]
      rw [ih']
      rw [mul_assoc]

/-- Certified evaluation agrees with the raw chronological evaluator in `Basic`. -/
@[simp]
theorem eval_val {n : ℕ} (circuit : Circuit n) :
    (eval circuit : Gate n) =
      evalGates (circuit.map fun primitive => (primitive.denotation : Gate n)) := by
  induction circuit with
  | nil => simp [eval]
  | cons primitive circuit ih => simp [eval, ih]

/--
The adjoint circuit reverses execution order and adjoints every primitive.
-/
def adjoint {n : ℕ} (circuit : Circuit n) : Circuit n :=
  circuit.reverse.map Primitive.adjoint

@[simp]
theorem adjoint_nil {n : ℕ} : adjoint ([] : Circuit n) = [] := rfl

@[simp]
theorem adjoint_identity (n : ℕ) : adjoint (identity n) = identity n := rfl

@[simp]
theorem adjoint_singleton {n : ℕ} (primitive : Primitive n) :
    adjoint [primitive] = [primitive.adjoint] := by
  simp [adjoint]

@[simp]
theorem adjoint_cons {n : ℕ} (primitive : Primitive n) (circuit : Circuit n) :
    adjoint (primitive :: circuit) = append (adjoint circuit) [primitive.adjoint] := by
  simp [adjoint, append]

@[simp]
theorem adjoint_append {n : ℕ} (first second : Circuit n) :
    adjoint (append first second) = append (adjoint second) (adjoint first) := by
  simp [adjoint, append, List.map_reverse]

@[simp]
theorem adjoint_adjoint {n : ℕ} (circuit : Circuit n) :
    adjoint (adjoint circuit) = circuit := by
  simp [adjoint, List.map_reverse, List.map_map, Function.comp_def]

/-- Evaluating the adjoint circuit gives the inverse certified unitary. -/
@[simp]
theorem eval_adjoint {n : ℕ} (circuit : Circuit n) :
    eval (adjoint circuit) = (eval circuit)⁻¹ := by
  induction circuit with
  | nil => simp
  | cons primitive circuit ih =>
      rw [adjoint_cons, eval_append]
      simp [ih]

/-- Executing a circuit followed by its adjoint evaluates to identity. -/
@[simp]
theorem eval_append_adjoint {n : ℕ} (circuit : Circuit n) :
    eval (append circuit (adjoint circuit)) = 1 := by
  rw [eval_append, eval_adjoint, inv_mul_cancel]

/-- Executing an adjoint circuit followed by the original also evaluates to identity. -/
@[simp]
theorem eval_adjoint_append {n : ℕ} (circuit : Circuit n) :
    eval (append (adjoint circuit) circuit) = 1 := by
  rw [eval_append, eval_adjoint, mul_inv_cancel]

/--
State-action order sanity check: on a two-primitive circuit, `first` acts on the
input state before `second`.
-/
theorem eval_pair_mulVec {n : ℕ} (first second : Primitive n) (state : State n) :
    (eval [first, second] : Gate n) *ᵥ state =
      (second.denotation : Gate n) *ᵥ ((first.denotation : Gate n) *ᵥ state) := by
  rw [eval_pair]
  exact
    (Matrix.mulVec_mulVec state (second.denotation : Gate n)
      (first.denotation : Gate n)).symm

end Circuit

end Barenco
