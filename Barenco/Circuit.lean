import Barenco.Controlled

/-!
# Chronological circuit syntax

This module separates countable circuit syntax from matrix semantics. A circuit is
a list in execution order: its head runs first. Consequently, later primitive
denotations multiply on the left during evaluation.

Primitive kinds and supports are structural metadata. They are deliberately kept
independent of the certified unitary denotation so later cost models can inspect
syntax without attempting to recover a circuit from its matrix. The raw primitive
constructor is private: otherwise an arbitrary global unitary could be mislabeled
as one CNOT and make a later resource theorem meaningless. This module exposes a
conservative unclassified constructor and trusted smart constructors built from
the certified local and controlled semantics.
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
  private mk ::
  kind : PrimitiveKind
  support : Finset (Fin n)
  denotation : UnitaryGate n

namespace Primitive

/--
Conservatively wrap an arbitrary certified unitary as an unclassified primitive.

Its support is the full register and its `other` kind is intentionally outside the
paper's basic-gate classes. A resource model must reject or explicitly price such
tags rather than treating them as one-qubit, CNOT, Toffoli, or arbitrary two-qubit
gates.
-/
def unclassified {n : ℕ} (tag : String) (denotation : UnitaryGate n) : Primitive n where
  kind := .other tag
  support := Finset.univ
  denotation := denotation

@[simp]
theorem unclassified_kind {n : ℕ} (tag : String) (denotation : UnitaryGate n) :
    (unclassified tag denotation).kind = .other tag := rfl

@[simp]
theorem unclassified_support {n : ℕ} (tag : String) (denotation : UnitaryGate n) :
    (unclassified tag denotation).support = Finset.univ := rfl

@[simp]
theorem unclassified_denotation {n : ℕ} (tag : String) (denotation : UnitaryGate n) :
    (unclassified tag denotation).denotation = denotation := rfl

/-! ## Correctness-by-construction standard primitives -/

/-- Package a certified one-qubit unitary acting at exactly `target`. -/
def oneQubit {n : ℕ} (target : Fin n) (U : QubitUnitary) : Primitive n where
  kind := .oneQubit
  support := {target}
  denotation := localUnitary target U

@[simp]
theorem oneQubit_kind {n : ℕ} (target : Fin n) (U : QubitUnitary) :
    (oneQubit target U).kind = .oneQubit := rfl

@[simp]
theorem oneQubit_support {n : ℕ} (target : Fin n) (U : QubitUnitary) :
    (oneQubit target U).support = {target} := rfl

@[simp]
theorem oneQubit_support_card {n : ℕ} (target : Fin n) (U : QubitUnitary) :
    (oneQubit target U).support.card = 1 := by
  simp

@[simp]
theorem oneQubit_denotation {n : ℕ} (target : Fin n) (U : QubitUnitary) :
    (oneQubit target U).denotation = localUnitary target U := rfl

@[simp]
theorem oneQubit_denotation_val {n : ℕ} (target : Fin n) (U : QubitUnitary) :
    ((oneQubit target U).denotation : Gate n) = localRaw target U := rfl

/-- The target together with the underlying register values of all controls. -/
def positiveControlledSupport {n : ℕ} (target : Fin n) (controls : ControlSet target) :
    Finset (Fin n) :=
  insert target
    (controls.image fun control : TargetComplement target => (control : Fin n))

@[simp]
theorem mem_positiveControlledSupport {n : ℕ} (target wire : Fin n)
    (controls : ControlSet target) :
    wire ∈ positiveControlledSupport target controls ↔
      wire = target ∨ ∃ control ∈ controls, (control : Fin n) = wire := by
  simp [positiveControlledSupport]

@[simp]
theorem positiveControlledSupport_card {n : ℕ} (target : Fin n)
    (controls : ControlSet target) :
    (positiveControlledSupport target controls).card = controls.card + 1 := by
  have htarget : target ∉
      controls.image (fun control : TargetComplement target => (control : Fin n)) := by
    simp only [Finset.mem_image]
    rintro ⟨control, _, hcontrol⟩
    exact control.property hcontrol
  rw [positiveControlledSupport, Finset.card_insert_of_notMem htarget]
  rw [Finset.card_image_of_injective controls Subtype.val_injective]

/--
Package a certified positive multi-controlled one-qubit unitary. The support
contains exactly the target and the register values represented by `controls`.
-/
def positiveControlled {n : ℕ} (target : Fin n) (controls : ControlSet target)
    (U : QubitUnitary) : Primitive n where
  kind := .controlledOneQubit controls.card
  support := positiveControlledSupport target controls
  denotation := positiveControlledUnitary target controls U

@[simp]
theorem positiveControlled_kind {n : ℕ} (target : Fin n) (controls : ControlSet target)
    (U : QubitUnitary) :
    (positiveControlled target controls U).kind = .controlledOneQubit controls.card := rfl

@[simp]
theorem positiveControlled_support {n : ℕ} (target : Fin n)
    (controls : ControlSet target) (U : QubitUnitary) :
    (positiveControlled target controls U).support =
      positiveControlledSupport target controls := rfl

@[simp]
theorem positiveControlled_support_card {n : ℕ} (target : Fin n)
    (controls : ControlSet target) (U : QubitUnitary) :
    (positiveControlled target controls U).support.card = controls.card + 1 := by
  simp

@[simp]
theorem positiveControlled_denotation {n : ℕ} (target : Fin n)
    (controls : ControlSet target) (U : QubitUnitary) :
    (positiveControlled target controls U).denotation =
      positiveControlledUnitary target controls U := rfl

@[simp]
theorem positiveControlled_denotation_val {n : ℕ} (target : Fin n)
    (controls : ControlSet target) (U : QubitUnitary) :
    ((positiveControlled target controls U).denotation : Gate n) =
      positiveControlledRaw target controls U := by
  exact coe_positiveControlledUnitary target controls U

/-- Package the certified CNOT with its ordered control and target wires. -/
def cnot {n : ℕ} (control target : Fin n) (h : control ≠ target) : Primitive n where
  kind := .cnot
  support := {control, target}
  denotation := cnotUnitary control target h

@[simp]
theorem cnot_kind {n : ℕ} (control target : Fin n) (h : control ≠ target) :
    (cnot control target h).kind = .cnot := rfl

@[simp]
theorem cnot_support {n : ℕ} (control target : Fin n) (h : control ≠ target) :
    (cnot control target h).support = {control, target} := rfl

@[simp]
theorem cnot_support_card {n : ℕ} (control target : Fin n) (h : control ≠ target) :
    (cnot control target h).support.card = 2 := by
  simp [h]

@[simp]
theorem cnot_denotation {n : ℕ} (control target : Fin n) (h : control ≠ target) :
    (cnot control target h).denotation = cnotUnitary control target h := rfl

@[simp]
theorem cnot_denotation_val {n : ℕ} (control target : Fin n) (h : control ≠ target) :
    ((cnot control target h).denotation : Gate n) = cnotRaw control target h := by
  exact coe_cnotUnitary control target h

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
