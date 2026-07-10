import Barenco.Circuit

/-!
# Payload-preserving fusion syntax

This module reifies exactly the local data needed by circuit fusion.  A visible
node contains either a certified one-qubit payload, a CNOT with its ordered
distinct wires, or a certified arbitrary two-qubit payload on an ordered wire
pair.  Lowering uses only the trusted smart constructors from `Barenco.Circuit`.

An arbitrary existing `Primitive` cannot in general be reified: its structural
kind and support do not recover a local matrix.  `FusionStep` therefore keeps
such syntax in a separate explicit `barrier` alternative.  Barriers lower to the
original primitive unchanged and never inhabit `FusionPrimitive`.

Circuits and programs remain chronological lists.  Their heads execute first,
so appending `second` after `first` evaluates as `eval second * eval first`.
Every equality in this module is exact; no scalar phase is discarded.
-/

namespace Barenco.Optimization

open Barenco

/--
An optimizer-visible primitive whose complete one- or two-wire payload is
retained by syntax.
-/
inductive FusionPrimitive (n : ℕ) where
  /-- A certified one-qubit unitary on `target`. -/
  | oneQubit (target : Fin n) (U : QubitUnitary)
  /-- A CNOT with ordered, distinct control and target wires. -/
  | cnot (control target : Fin n) (hcontrolTarget : control ≠ target)
  /-- A certified arbitrary `U(4)` on an ordered pair of distinct wires. -/
  | twoQubit (pair : OrderedWirePair n) (U : TwoQubitUnitary)

namespace FusionPrimitive

/-- Lower a visible node through the corresponding trusted smart constructor. -/
def lower {n : ℕ} : FusionPrimitive n → Primitive n
  | .oneQubit target U => Primitive.oneQubit target U
  | .cnot control target h => Primitive.cnot control target h
  | .twoQubit pair U => Primitive.twoQubit pair U

/-- Certified full-register denotation retained by a visible node. -/
def denotation {n : ℕ} : FusionPrimitive n → UnitaryGate n
  | .oneQubit target U => localUnitary target U
  | .cnot control target h => cnotUnitary control target h
  | .twoQubit pair U => twoWireUnitary pair U

/-- Structural primitive class of a visible node. -/
def kind {n : ℕ} : FusionPrimitive n → PrimitiveKind
  | .oneQubit _ _ => .oneQubit
  | .cnot _ _ _ => .cnot
  | .twoQubit _ _ => .arbitraryTwoQubit

/-- Structural support retained by a visible node. -/
def support {n : ℕ} : FusionPrimitive n → Finset (Fin n)
  | .oneQubit target _ => {target}
  | .cnot control target _ => {control, target}
  | .twoQubit pair _ => {pair.first, pair.second}

/-- Lowering preserves the certified full-register denotation exactly. -/
@[simp]
theorem lower_denotation {n : ℕ} (primitive : FusionPrimitive n) :
    primitive.lower.denotation = primitive.denotation := by
  cases primitive <;> rfl

/-- Lowering preserves the structural primitive class exactly. -/
@[simp]
theorem lower_kind {n : ℕ} (primitive : FusionPrimitive n) :
    primitive.lower.kind = primitive.kind := by
  cases primitive <;> rfl

/-- Lowering preserves the declared structural wire support exactly. -/
@[simp]
theorem lower_support {n : ℕ} (primitive : FusionPrimitive n) :
    primitive.lower.support = primitive.support := by
  cases primitive <;> rfl

private theorem localUnitary_one (n : ℕ) (target : Fin n) :
    localUnitary target (1 : QubitUnitary) = 1 := by
  apply Subtype.ext
  change Matrix.reindexAlgEquiv ℂ ℂ (splitTarget target).symm
      (Matrix.blockDiagonal (1 : ComplementBasis target → QubitMatrix)) = 1
  rw [Matrix.blockDiagonal_one, map_one]

private theorem localUnitary_mul {n : ℕ} (target : Fin n)
    (U V : QubitUnitary) :
    localUnitary target (U * V) = localUnitary target U * localUnitary target V := by
  apply Subtype.ext
  change Matrix.reindexAlgEquiv ℂ ℂ (splitTarget target).symm
      (Matrix.blockDiagonal (fun _ : ComplementBasis target =>
        ((U : QubitMatrix) * (V : QubitMatrix)))) =
    Matrix.reindexAlgEquiv ℂ ℂ (splitTarget target).symm
        (Matrix.blockDiagonal (fun _ : ComplementBasis target => (U : QubitMatrix))) *
      Matrix.reindexAlgEquiv ℂ ℂ (splitTarget target).symm
        (Matrix.blockDiagonal (fun _ : ComplementBasis target => (V : QubitMatrix)))
  rw [← map_mul, ← Matrix.blockDiagonal_mul]

private def localEmbedding (n : ℕ) (target : Fin n) :
    QubitUnitary →* UnitaryGate n where
  toFun := localUnitary target
  map_one' := localUnitary_one n target
  map_mul' := localUnitary_mul target

private theorem localUnitary_inv {n : ℕ} (target : Fin n) (U : QubitUnitary) :
    localUnitary target U⁻¹ = (localUnitary target U)⁻¹ := by
  exact map_inv (localEmbedding n target) U

private theorem setTarget_setTarget {n : ℕ} (target : Fin n) (input : Basis n)
    (firstBit secondBit : Bool) :
    setTarget target (setTarget target input firstBit) secondBit =
      setTarget target input secondBit := by
  apply (splitTarget target).injective
  simp

private theorem cnotUnitary_mul_self {n : ℕ} (control target : Fin n)
    (h : control ≠ target) :
    cnotUnitary control target h * cnotUnitary control target h = 1 := by
  apply Subtype.ext
  rw [matrix_eq_iff_mulVec_basisKet_eq]
  intro input
  rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  simp only [coe_cnotUnitary, cnotRaw_mulVec_basisKet]
  cases hcontrol : input control
  · simp [hcontrol]
  · simp [hcontrol, setTarget_apply_of_ne target input (!input target) control h,
      setTarget_setTarget, setTarget_self]

private theorem cnotUnitary_inv {n : ℕ} (control target : Fin n)
    (h : control ≠ target) :
    (cnotUnitary control target h)⁻¹ = cnotUnitary control target h := by
  let C := cnotUnitary control target h
  have hsquare : C * C = 1 := cnotUnitary_mul_self control target h
  calc
    C⁻¹ = C⁻¹ * 1 := (mul_one C⁻¹).symm
    _ = C⁻¹ * (C * C) := by rw [hsquare]
    _ = (C⁻¹ * C) * C := by rw [mul_assoc]
    _ = C := by simp

/--
Payload-preserving adjoint of a visible node.  One- and two-qubit payloads are
inverted locally; CNOT remains an explicit CNOT because it is self-adjoint.
-/
def adjoint {n : ℕ} : FusionPrimitive n → FusionPrimitive n
  | .oneQubit target U => .oneQubit target U⁻¹
  | .cnot control target h => .cnot control target h
  | .twoQubit pair U => .twoQubit pair U⁻¹

/-- Adjointing a visible node twice recovers its complete payload. -/
@[simp]
theorem adjoint_adjoint {n : ℕ} (primitive : FusionPrimitive n) :
    primitive.adjoint.adjoint = primitive := by
  cases primitive <;> simp [adjoint]

/-- Adjointing preserves the node's structural kind. -/
@[simp]
theorem adjoint_kind {n : ℕ} (primitive : FusionPrimitive n) :
    primitive.adjoint.kind = primitive.kind := by
  cases primitive <;> rfl

/-- Adjointing preserves the node's structural support. -/
@[simp]
theorem adjoint_support {n : ℕ} (primitive : FusionPrimitive n) :
    primitive.adjoint.support = primitive.support := by
  cases primitive <;> rfl

/-- Visible adjoint commutes exactly with lowering to trusted primitive syntax. -/
@[simp]
theorem lower_adjoint {n : ℕ} (primitive : FusionPrimitive n) :
    primitive.adjoint.lower = primitive.lower.adjoint := by
  cases primitive with
  | oneQubit target U =>
      cases U
      simp [adjoint, lower, Primitive.adjoint, Primitive.oneQubit,
        localUnitary_inv]
  | cnot control target h =>
      simp [adjoint, lower, Primitive.adjoint, Primitive.cnot, cnotUnitary_inv]
  | twoQubit pair U =>
      simp [adjoint, lower, Primitive.adjoint, Primitive.twoQubit,
        twoWireUnitary_inv]

/-- The visible adjoint denotes the exact inverse full-register unitary. -/
@[simp]
theorem adjoint_denotation {n : ℕ} (primitive : FusionPrimitive n) :
    primitive.adjoint.denotation = primitive.denotation⁻¹ := by
  rw [← lower_denotation, lower_adjoint, Primitive.adjoint_denotation,
    lower_denotation]

end FusionPrimitive

/-- A chronological list of optimizer-visible primitives. -/
abbrev FusionCircuit (n : ℕ) := List (FusionPrimitive n)

namespace FusionCircuit

/-- Lower every visible node, retaining chronological list order. -/
def lower {n : ℕ} (circuit : FusionCircuit n) : Circuit n :=
  circuit.map FusionPrimitive.lower

@[simp]
theorem lower_nil (n : ℕ) :
    lower ([] : FusionCircuit n) = Circuit.identity n := rfl

@[simp]
theorem lower_cons {n : ℕ} (primitive : FusionPrimitive n)
    (circuit : FusionCircuit n) :
    lower (primitive :: circuit) = primitive.lower :: lower circuit := rfl

/-- Lowering preserves the complete chronological list of denotations. -/
@[simp]
theorem lower_denotations {n : ℕ} (circuit : FusionCircuit n) :
    circuit.lower.map Primitive.denotation =
      circuit.map FusionPrimitive.denotation := by
  simp [lower]

/-- Lowering preserves the complete chronological list of structural kinds. -/
@[simp]
theorem lower_kinds {n : ℕ} (circuit : FusionCircuit n) :
    circuit.lower.map Primitive.kind = circuit.map FusionPrimitive.kind := by
  simp [lower]

/-- Lowering preserves the complete chronological list of structural supports. -/
@[simp]
theorem lower_supports {n : ℕ} (circuit : FusionCircuit n) :
    circuit.lower.map Primitive.support = circuit.map FusionPrimitive.support := by
  simp [lower]

/-- Independent certified evaluator for visible chronological syntax. -/
def eval {n : ℕ} : FusionCircuit n → UnitaryGate n
  | [] => 1
  | primitive :: circuit => eval circuit * primitive.denotation

@[simp]
theorem eval_nil {n : ℕ} : eval ([] : FusionCircuit n) = 1 := rfl

@[simp]
theorem eval_cons {n : ℕ} (primitive : FusionPrimitive n)
    (circuit : FusionCircuit n) :
    eval (primitive :: circuit) = eval circuit * primitive.denotation := rfl

/-- Trusted lowering preserves the exact certified evaluator. -/
@[simp]
theorem eval_lower {n : ℕ} (circuit : FusionCircuit n) :
    Circuit.eval circuit.lower = circuit.eval := by
  induction circuit with
  | nil => rfl
  | cons primitive circuit ih => simp [ih]

/-- Chronological concatenation: run `first`, then run `second`. -/
def append {n : ℕ} (first second : FusionCircuit n) : FusionCircuit n :=
  first ++ second

/-- Lowering commutes exactly with chronological concatenation. -/
@[simp]
theorem lower_append {n : ℕ} (first second : FusionCircuit n) :
    lower (append first second) = Circuit.append first.lower second.lower := by
  simp [append, lower, Circuit.append]

/-- A concatenated visible circuit retains the library's head-first chronology. -/
@[simp]
theorem eval_append {n : ℕ} (first second : FusionCircuit n) :
    eval (append first second) = eval second * eval first := by
  rw [← eval_lower, lower_append, Circuit.eval_append, eval_lower, eval_lower]

/-- Structural union of every support declared by visible syntax. -/
def support {n : ℕ} : FusionCircuit n → Finset (Fin n)
  | [] => ∅
  | primitive :: circuit => primitive.support ∪ support circuit

@[simp]
theorem support_nil (n : ℕ) : support ([] : FusionCircuit n) = ∅ := rfl

@[simp]
theorem support_cons {n : ℕ} (primitive : FusionPrimitive n)
    (circuit : FusionCircuit n) :
    support (primitive :: circuit) = primitive.support ∪ support circuit := rfl

/-- Structural support distributes over chronological concatenation. -/
@[simp]
theorem support_append {n : ℕ} (first second : FusionCircuit n) :
    support (append first second) = support first ∪ support second := by
  induction first with
  | nil => simp [append]
  | cons primitive first ih =>
      have ih' : support (first ++ second) = support first ∪ support second := by
        simpa only [append] using ih
      change primitive.support ∪ support (first ++ second) =
        primitive.support ∪ support first ∪ support second
      rw [ih', Finset.union_assoc]

/-- Reverse chronology and adjoint every visible payload. -/
def adjoint {n : ℕ} (circuit : FusionCircuit n) : FusionCircuit n :=
  circuit.reverse.map FusionPrimitive.adjoint

/-- Visible circuit adjoint commutes exactly with lowering. -/
@[simp]
theorem lower_adjoint {n : ℕ} (circuit : FusionCircuit n) :
    lower circuit.adjoint = Circuit.adjoint circuit.lower := by
  simp [adjoint, lower, Circuit.adjoint, List.map_reverse, List.map_map,
    Function.comp_def]

/-- Evaluating the visible adjoint gives the exact inverse certified unitary. -/
@[simp]
theorem eval_adjoint {n : ℕ} (circuit : FusionCircuit n) :
    eval circuit.adjoint = (eval circuit)⁻¹ := by
  rw [← eval_lower, lower_adjoint, Circuit.eval_adjoint, eval_lower]

/-- Visible circuit adjoint is an involution. -/
@[simp]
theorem adjoint_adjoint {n : ℕ} (circuit : FusionCircuit n) :
    circuit.adjoint.adjoint = circuit := by
  simp [adjoint, List.map_reverse, List.map_map, Function.comp_def]

private theorem support_map_adjoint {n : ℕ} (circuit : FusionCircuit n) :
    support (circuit.map FusionPrimitive.adjoint) = support circuit := by
  induction circuit with
  | nil => rfl
  | cons primitive circuit ih => simp [ih]

private theorem support_reverse {n : ℕ} (circuit : FusionCircuit n) :
    support circuit.reverse = support circuit := by
  induction circuit with
  | nil => rfl
  | cons primitive circuit ih =>
      rw [List.reverse_cons, ← append, support_append, ih]
      simp [Finset.union_comm]

/-- Adjointing preserves the visible circuit's structural support. -/
@[simp]
theorem support_adjoint {n : ℕ} (circuit : FusionCircuit n) :
    support circuit.adjoint = support circuit := by
  rw [adjoint, support_map_adjoint, support_reverse]

end FusionCircuit

/-! ## Explicit barriers for non-reifiable existing syntax -/

/--
A mixed compiler step is either fully visible optimizer syntax or an exact opaque
barrier.  The latter stores an already trusted `Primitive` verbatim; it does not
claim that the primitive's local payload has been recovered.
-/
inductive FusionStep (n : ℕ) where
  | gate (primitive : FusionPrimitive n)
  | barrier (primitive : Primitive n)

namespace FusionStep

/-- Lower a visible gate or preserve an opaque barrier verbatim. -/
def lower {n : ℕ} : FusionStep n → Primitive n
  | .gate primitive => primitive.lower
  | .barrier primitive => primitive

/-- Exact full-register denotation of a mixed step. -/
def denotation {n : ℕ} (step : FusionStep n) : UnitaryGate n :=
  step.lower.denotation

/-- Exact structural kind of a mixed step. -/
def kind {n : ℕ} (step : FusionStep n) : PrimitiveKind :=
  step.lower.kind

/-- Exact structural support of a mixed step. -/
def support {n : ℕ} (step : FusionStep n) : Finset (Fin n) :=
  step.lower.support

@[simp]
theorem lower_denotation {n : ℕ} (step : FusionStep n) :
    step.lower.denotation = step.denotation := rfl

@[simp]
theorem lower_kind {n : ℕ} (step : FusionStep n) :
    step.lower.kind = step.kind := rfl

@[simp]
theorem lower_support {n : ℕ} (step : FusionStep n) :
    step.lower.support = step.support := rfl

/-- Adjoint visible payloads locally and opaque barriers through trusted syntax. -/
def adjoint {n : ℕ} : FusionStep n → FusionStep n
  | .gate primitive => .gate primitive.adjoint
  | .barrier primitive => .barrier primitive.adjoint

/-- Mixed-step adjoint commutes exactly with lowering. -/
@[simp]
theorem lower_adjoint {n : ℕ} (step : FusionStep n) :
    step.adjoint.lower = step.lower.adjoint := by
  cases step <;> simp [adjoint, lower]

@[simp]
theorem adjoint_adjoint {n : ℕ} (step : FusionStep n) :
    step.adjoint.adjoint = step := by
  cases step <;> simp [adjoint]

@[simp]
theorem adjoint_denotation {n : ℕ} (step : FusionStep n) :
    step.adjoint.denotation = step.denotation⁻¹ := by
  rw [← lower_denotation, lower_adjoint, Primitive.adjoint_denotation,
    lower_denotation]

@[simp]
theorem adjoint_kind {n : ℕ} (step : FusionStep n) :
    step.adjoint.kind = step.kind := by
  rw [← lower_kind, lower_adjoint, Primitive.adjoint_kind, lower_kind]

@[simp]
theorem adjoint_support {n : ℕ} (step : FusionStep n) :
    step.adjoint.support = step.support := by
  rw [← lower_support, lower_adjoint, Primitive.adjoint_support, lower_support]

end FusionStep

/-- A chronological list of visible gates separated by exact opaque barriers. -/
abbrev FusionProgram (n : ℕ) := List (FusionStep n)

namespace FusionProgram

/-- Lower a mixed program without changing its chronological order. -/
def lower {n : ℕ} (program : FusionProgram n) : Circuit n :=
  program.map FusionStep.lower

@[simp]
theorem lower_nil (n : ℕ) :
    lower ([] : FusionProgram n) = Circuit.identity n := rfl

@[simp]
theorem lower_cons {n : ℕ} (step : FusionStep n) (program : FusionProgram n) :
    lower (step :: program) = step.lower :: lower program := rfl

/-- Embed a fully visible circuit into the mixed layer without adding barriers. -/
def visible {n : ℕ} (circuit : FusionCircuit n) : FusionProgram n :=
  circuit.map FusionStep.gate

/-- Preserve an arbitrary existing circuit as a program consisting only of barriers. -/
def barriers {n : ℕ} (circuit : Circuit n) : FusionProgram n :=
  circuit.map FusionStep.barrier

/-- Fully visible embedding lowers to the original visible lowering exactly. -/
@[simp]
theorem lower_visible {n : ℕ} (circuit : FusionCircuit n) :
    lower (visible circuit) = FusionCircuit.lower circuit := by
  induction circuit with
  | nil => rfl
  | cons primitive circuit ih =>
      change primitive.lower :: lower (visible circuit) =
        primitive.lower :: FusionCircuit.lower circuit
      rw [ih]

/-- The all-barrier preservation path lowers to its original circuit exactly. -/
@[simp]
theorem lower_barriers {n : ℕ} (circuit : Circuit n) :
    lower (barriers circuit) = circuit := by
  induction circuit with
  | nil => rfl
  | cons primitive circuit ih =>
      change primitive :: lower (barriers circuit) = primitive :: circuit
      rw [ih]

/-- Independent certified evaluator for chronological mixed syntax. -/
def eval {n : ℕ} : FusionProgram n → UnitaryGate n
  | [] => 1
  | step :: program => eval program * step.denotation

@[simp]
theorem eval_nil {n : ℕ} : eval ([] : FusionProgram n) = 1 := rfl

@[simp]
theorem eval_cons {n : ℕ} (step : FusionStep n) (program : FusionProgram n) :
    eval (step :: program) = eval program * step.denotation := rfl

/-- Mixed lowering preserves the exact certified evaluator. -/
@[simp]
theorem eval_lower {n : ℕ} (program : FusionProgram n) :
    Circuit.eval program.lower = program.eval := by
  induction program with
  | nil => rfl
  | cons step program ih => simp [ih]

/-- Evaluating a fully visible mixed program agrees with the visible evaluator. -/
@[simp]
theorem eval_visible {n : ℕ} (circuit : FusionCircuit n) :
    eval (visible circuit) = circuit.eval := by
  rw [← eval_lower, lower_visible, FusionCircuit.eval_lower]

/-- Evaluating an all-barrier program agrees with the original circuit exactly. -/
@[simp]
theorem eval_barriers {n : ℕ} (circuit : Circuit n) :
    eval (barriers circuit) = Circuit.eval circuit := by
  rw [← eval_lower, lower_barriers]

/-- Chronological concatenation of mixed programs. -/
def append {n : ℕ} (first second : FusionProgram n) : FusionProgram n :=
  first ++ second

@[simp]
theorem lower_append {n : ℕ} (first second : FusionProgram n) :
    lower (append first second) = Circuit.append first.lower second.lower := by
  simp [append, lower, Circuit.append]

@[simp]
theorem eval_append {n : ℕ} (first second : FusionProgram n) :
    eval (append first second) = eval second * eval first := by
  rw [← eval_lower, lower_append, Circuit.eval_append, eval_lower, eval_lower]

/-- Structural union of support declared by both visible gates and exact barriers. -/
def support {n : ℕ} : FusionProgram n → Finset (Fin n)
  | [] => ∅
  | step :: program => step.support ∪ support program

@[simp]
theorem support_nil (n : ℕ) : support ([] : FusionProgram n) = ∅ := rfl

@[simp]
theorem support_cons {n : ℕ} (step : FusionStep n) (program : FusionProgram n) :
    support (step :: program) = step.support ∪ support program := rfl

@[simp]
theorem support_append {n : ℕ} (first second : FusionProgram n) :
    support (append first second) = support first ∪ support second := by
  induction first with
  | nil => simp [append]
  | cons step first ih =>
      have ih' : support (first ++ second) = support first ∪ support second := by
        simpa only [append] using ih
      change step.support ∪ support (first ++ second) =
        step.support ∪ support first ∪ support second
      rw [ih', Finset.union_assoc]

/-- Reverse chronology and adjoint every visible gate or exact barrier. -/
def adjoint {n : ℕ} (program : FusionProgram n) : FusionProgram n :=
  program.reverse.map FusionStep.adjoint

/-- Mixed-program adjoint commutes exactly with lowering. -/
@[simp]
theorem lower_adjoint {n : ℕ} (program : FusionProgram n) :
    lower program.adjoint = Circuit.adjoint program.lower := by
  simp [adjoint, lower, Circuit.adjoint, List.map_reverse, List.map_map,
    Function.comp_def]

@[simp]
theorem eval_adjoint {n : ℕ} (program : FusionProgram n) :
    eval program.adjoint = (eval program)⁻¹ := by
  rw [← eval_lower, lower_adjoint, Circuit.eval_adjoint, eval_lower]

@[simp]
theorem adjoint_adjoint {n : ℕ} (program : FusionProgram n) :
    program.adjoint.adjoint = program := by
  simp [adjoint, List.map_reverse, List.map_map, Function.comp_def]

private theorem support_map_adjoint {n : ℕ} (program : FusionProgram n) :
    support (program.map FusionStep.adjoint) = support program := by
  induction program with
  | nil => rfl
  | cons step program ih => simp [ih]

private theorem support_reverse {n : ℕ} (program : FusionProgram n) :
    support program.reverse = support program := by
  induction program with
  | nil => rfl
  | cons step program ih =>
      rw [List.reverse_cons, ← append, support_append, ih]
      simp [Finset.union_comm]

@[simp]
theorem support_adjoint {n : ℕ} (program : FusionProgram n) :
    support program.adjoint = support program := by
  rw [adjoint, support_map_adjoint, support_reverse]

/-- Adjointing the all-barrier lift agrees with lifting the circuit adjoint. -/
@[simp]
theorem adjoint_barriers {n : ℕ} (circuit : Circuit n) :
    adjoint (barriers circuit) = barriers (Circuit.adjoint circuit) := by
  simp [adjoint, barriers, Circuit.adjoint, List.map_reverse, List.map_map,
    Function.comp_def, FusionStep.adjoint]

end FusionProgram

end Barenco.Optimization
