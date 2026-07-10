import Barenco.Optimization.FusionCommutation
import Barenco.Optimization.NormalizeCore

/-!
# Exact early-model normalization

This module implements the normalization policy that retains literal CNOT syntax.
It has two deterministic phases:

1. `earlyExpose` moves an earlier one-qubit gate to the right across certified
   disjoint CNOTs and sorts mutually commuting one-qubit gates by wire.  Touching
   CNOTs and every generic `U(4)` node are hard stops.
2. `earlyAdjacentNormalize` fuses adjacent one-qubit gates on the same wire with
   chronological payload `second * first`.

The pass never compares unitary matrices, never deletes scalar phase, and never
turns a CNOT into a generic two-qubit node.  Its exact output guarantee is local
adjacent stability after the second phase; no global canonicality or idempotence
of the complete commute-then-fuse composition is claimed.
-/

namespace Barenco.Optimization

open Barenco
open NormalizeCore

/--
Insert an earlier visible gate before a tail while exposing safe one-qubit
mergers.  Distinct one-qubit wires are sorted by their `Fin` order.  An earlier
one-qubit gate always moves right across a CNOT disjoint from its wire.
-/
def earlyExposeInsert {n : ℕ} :
    FusionPrimitive n → FusionCircuit n → FusionCircuit n
  | gate@(.oneQubit _wire _), [] => [gate]
  | gate@(.oneQubit wire _), next@(.oneQubit nextWire _) :: rest =>
      if wire = nextWire then gate :: next :: rest
      else if wire ≤ nextWire then gate :: next :: rest
      else next :: earlyExposeInsert gate rest
  | gate@(.oneQubit wire _), next@(.cnot control target _) :: rest =>
      if wire = control ∨ wire = target then gate :: next :: rest
      else next :: earlyExposeInsert gate rest
  | gate@(.oneQubit _ _), next@(.twoQubit _ _) :: rest =>
      gate :: next :: rest
  | gate, circuit => gate :: circuit

/-- Tail-first deterministic exposure of same-wire one-qubit opportunities. -/
def earlyExpose {n : ℕ} : FusionCircuit n → FusionCircuit n
  | [] => []
  | gate :: circuit => earlyExposeInsert gate (earlyExpose circuit)

/-- Exposure insertion preserves exact head-first chronological semantics. -/
theorem eval_earlyExposeInsert {n : ℕ} (gate : FusionPrimitive n) :
    ∀ circuit : FusionCircuit n,
      FusionCircuit.eval (earlyExposeInsert gate circuit) =
        FusionCircuit.eval circuit * gate.denotation := by
  intro circuit
  induction circuit generalizing gate with
  | nil =>
      cases gate <;> rfl
  | cons next rest ih =>
      cases gate with
      | cnot => rfl
      | twoQubit => rfl
      | oneQubit wire payload =>
          cases next with
          | twoQubit => rfl
          | oneQubit nextWire nextPayload =>
              by_cases hsame : wire = nextWire
              · simp [earlyExposeInsert, hsame]
              · by_cases horder : wire ≤ nextWire
                · simp [earlyExposeInsert, hsame, horder]
                · simp only [earlyExposeInsert, hsame, horder, ↓reduceIte,
                    FusionCircuit.eval_cons]
                  rw [ih]
                  have hcommute := oneQubit_denotationsCommute_of_ne
                    wire nextWire hsame payload nextPayload
                  calc
                    (FusionCircuit.eval rest *
                          (FusionPrimitive.oneQubit wire payload).denotation) *
                        (FusionPrimitive.oneQubit nextWire nextPayload).denotation =
                      FusionCircuit.eval rest *
                        ((FusionPrimitive.oneQubit wire payload).denotation *
                          (FusionPrimitive.oneQubit nextWire nextPayload).denotation) :=
                        mul_assoc _ _ _
                    _ = FusionCircuit.eval rest *
                        ((FusionPrimitive.oneQubit nextWire nextPayload).denotation *
                          (FusionPrimitive.oneQubit wire payload).denotation) := by
                          rw [hcommute]
                    _ = (FusionCircuit.eval rest *
                          (FusionPrimitive.oneQubit nextWire nextPayload).denotation) *
                        (FusionPrimitive.oneQubit wire payload).denotation :=
                          (mul_assoc _ _ _).symm
          | cnot control target hcontrolTarget =>
              by_cases htouch : wire = control ∨ wire = target
              · simp [earlyExposeInsert, htouch]
              · rcases not_or.mp htouch with ⟨hwireControl, hwireTarget⟩
                simp only [earlyExposeInsert, htouch, ↓reduceIte,
                  FusionCircuit.eval_cons]
                rw [ih]
                have hcommute := oneQubit_cnot_denotationsCommute_of_disjoint
                  wire control target hcontrolTarget (Ne.symm hwireControl)
                    (Ne.symm hwireTarget) payload
                calc
                  (FusionCircuit.eval rest *
                        (FusionPrimitive.oneQubit wire payload).denotation) *
                      (FusionPrimitive.cnot control target hcontrolTarget).denotation =
                    FusionCircuit.eval rest *
                      ((FusionPrimitive.oneQubit wire payload).denotation *
                        (FusionPrimitive.cnot control target hcontrolTarget).denotation) :=
                      mul_assoc _ _ _
                  _ = FusionCircuit.eval rest *
                      ((FusionPrimitive.cnot control target hcontrolTarget).denotation *
                        (FusionPrimitive.oneQubit wire payload).denotation) := by
                        rw [hcommute]
                  _ = (FusionCircuit.eval rest *
                        (FusionPrimitive.cnot control target hcontrolTarget).denotation) *
                      (FusionPrimitive.oneQubit wire payload).denotation :=
                        (mul_assoc _ _ _).symm

/-- The complete exposure phase preserves exact visible evaluation. -/
@[simp]
theorem eval_earlyExpose {n : ℕ} (circuit : FusionCircuit n) :
    FusionCircuit.eval (earlyExpose circuit) = FusionCircuit.eval circuit := by
  induction circuit with
  | nil => rfl
  | cons gate circuit ih =>
      rw [earlyExpose, eval_earlyExposeInsert, ih]
      rfl

/-- Exposure insertion preserves literal length exactly. -/
@[simp]
theorem length_earlyExposeInsert {n : ℕ} (gate : FusionPrimitive n) :
    ∀ circuit : FusionCircuit n,
      (earlyExposeInsert gate circuit).length = circuit.length + 1 := by
  intro circuit
  induction circuit generalizing gate with
  | nil => cases gate <;> rfl
  | cons next rest ih =>
      cases gate with
      | cnot => rfl
      | twoQubit => rfl
      | oneQubit wire payload =>
          cases next with
          | twoQubit => rfl
          | oneQubit nextWire nextPayload =>
              by_cases hsame : wire = nextWire
              · simp [earlyExposeInsert, hsame]
              · by_cases horder : wire ≤ nextWire
                · simp [earlyExposeInsert, hsame, horder]
                · simp [earlyExposeInsert, hsame, horder, ih]
          | cnot control target hcontrolTarget =>
              by_cases htouch : wire = control ∨ wire = target
              · simp [earlyExposeInsert, htouch]
              · simp [earlyExposeInsert, htouch, ih]

/-- Exposure is a pure reordering and preserves literal length. -/
@[simp]
theorem length_earlyExpose {n : ℕ} (circuit : FusionCircuit n) :
    (earlyExpose circuit).length = circuit.length := by
  induction circuit with
  | nil => rfl
  | cons gate circuit ih =>
      rw [earlyExpose, length_earlyExposeInsert, ih]
      rfl

/-! ## Adjacent same-wire fusion -/

/-- No raw matrix identity test is available in the concrete-payload policy. -/
def earlyIsIdentity {n : ℕ} (_ : FusionPrimitive n) : Bool := false

/-- Fuse exactly adjacent one-qubit nodes on the same wire. -/
def earlyCombine {n : ℕ} :
    FusionPrimitive n → FusionPrimitive n → CombineResult (FusionPrimitive n)
  | .oneQubit firstWire first, .oneQubit secondWire second =>
      if firstWire = secondWire then
        .fused (.oneQubit firstWire (second * first))
      else .blocked
  | _, _ => .blocked

/-- The concrete early policy never claims a payload is syntactic identity. -/
theorem earlyIsIdentity_sound {n : ℕ} (gate : FusionPrimitive n)
    (hidentity : earlyIsIdentity gate = true) : gate.denotation = 1 := by
  simp [earlyIsIdentity] at hidentity

/-- Every adjacent early combination preserves exact chronological denotation. -/
theorem earlyCombine_sound {n : ℕ} (first second : FusionPrimitive n) :
    CombineResult.Sound FusionPrimitive.denotation first second
      (earlyCombine first second) := by
  cases first with
  | cnot => trivial
  | twoQubit => trivial
  | oneQubit firstWire firstPayload =>
      cases second with
      | cnot => trivial
      | twoQubit => trivial
      | oneQubit secondWire secondPayload =>
          by_cases hwire : firstWire = secondWire
          · subst secondWire
            simp [earlyCombine, CombineResult.Sound]
            exact oneQubit_chronological firstWire firstPayload secondPayload
          · simp [earlyCombine, hwire, CombineResult.Sound]

/-- Adjacent same-wire fusion after the exposure phase. -/
def earlyAdjacentNormalize {n : ℕ} (circuit : FusionCircuit n) : FusionCircuit n :=
  NormalizeCore.normalize earlyIsIdentity earlyCombine circuit

/-- Complete concrete early policy: expose, then fuse adjacent same-wire nodes. -/
def normalizeEarly {n : ℕ} (circuit : FusionCircuit n) : FusionCircuit n :=
  earlyAdjacentNormalize (earlyExpose circuit)

/-- The generic group evaluator specializes definitionally to fusion evaluation. -/
theorem evalChronological_eq_fusionEval {n : ℕ} (circuit : FusionCircuit n) :
    NormalizeCore.evalChronological FusionPrimitive.denotation circuit =
      FusionCircuit.eval circuit := by
  induction circuit with
  | nil => rfl
  | cons gate circuit ih =>
      simp [NormalizeCore.evalChronological, FusionCircuit.eval, ih]

/-- Adjacent concrete early fusion preserves exact visible evaluation. -/
@[simp]
theorem eval_earlyAdjacentNormalize {n : ℕ} (circuit : FusionCircuit n) :
    FusionCircuit.eval (earlyAdjacentNormalize circuit) =
      FusionCircuit.eval circuit := by
  rw [← evalChronological_eq_fusionEval, ← evalChronological_eq_fusionEval]
  exact NormalizeCore.evalChronological_normalize
    FusionPrimitive.denotation earlyIsIdentity earlyCombine
      earlyIsIdentity_sound earlyCombine_sound circuit

/-- The complete early policy preserves exact full-register evaluation. -/
@[simp]
theorem eval_normalizeEarly {n : ℕ} (circuit : FusionCircuit n) :
    FusionCircuit.eval (normalizeEarly circuit) = FusionCircuit.eval circuit := by
  rw [normalizeEarly, eval_earlyAdjacentNormalize, eval_earlyExpose]

/-- Exact soundness after lowering into established trusted circuit syntax. -/
theorem eval_lower_normalizeEarly {n : ℕ} (circuit : FusionCircuit n) :
    Circuit.eval (normalizeEarly circuit).lower = Circuit.eval circuit.lower := by
  simp

/-- Adjacent early fusion never increases literal syntax length. -/
theorem length_earlyAdjacentNormalize_le {n : ℕ} (circuit : FusionCircuit n) :
    (earlyAdjacentNormalize circuit).length ≤ circuit.length :=
  NormalizeCore.length_normalize_le earlyIsIdentity earlyCombine circuit

/-- The complete early policy never increases literal syntax length. -/
theorem length_normalizeEarly_le {n : ℕ} (circuit : FusionCircuit n) :
    (normalizeEarly circuit).length ≤ circuit.length := by
  calc
    (normalizeEarly circuit).length =
        (earlyAdjacentNormalize (earlyExpose circuit)).length := rfl
    _ ≤ (earlyExpose circuit).length :=
      length_earlyAdjacentNormalize_le (earlyExpose circuit)
    _ = circuit.length := length_earlyExpose circuit

/-- Every complete early output has no immediately fuseable same-wire pair. -/
theorem normalizeEarly_stable {n : ℕ} (circuit : FusionCircuit n) :
    NormalizeCore.Stable earlyIsIdentity earlyCombine (normalizeEarly circuit) :=
  NormalizeCore.normalize_stable earlyIsIdentity earlyCombine _

/-- The adjacent fusion subpass is an exact fixed point on its own output. -/
@[simp]
theorem earlyAdjacentNormalize_idempotent {n : ℕ} (circuit : FusionCircuit n) :
    earlyAdjacentNormalize (earlyAdjacentNormalize circuit) =
      earlyAdjacentNormalize circuit :=
  NormalizeCore.normalize_idempotent earlyIsIdentity earlyCombine circuit

end Barenco.Optimization
