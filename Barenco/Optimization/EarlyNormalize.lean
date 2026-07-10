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

/-! ## Exact literal CNOT order -/

/--
The ordered control/target sequence of literal CNOT nodes in visible syntax.
One-qubit and generic two-qubit payload nodes do not contribute entries.
-/
def earlyCNOTSequence {n : ℕ} :
    FusionCircuit n → List (OrderedWirePair n)
  | [] => []
  | .oneQubit _ _ :: circuit => earlyCNOTSequence circuit
  | .cnot control target h :: circuit =>
      ⟨control, target, h⟩ :: earlyCNOTSequence circuit
  | .twoQubit _ _ :: circuit => earlyCNOTSequence circuit

private theorem earlyCNOTSequence_earlyExposeInsert {n : ℕ}
    (gate : FusionPrimitive n) :
    ∀ circuit : FusionCircuit n,
      earlyCNOTSequence (earlyExposeInsert gate circuit) =
        earlyCNOTSequence (gate :: circuit) := by
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
              · simp [earlyExposeInsert, earlyCNOTSequence, hsame]
              · by_cases horder : wire ≤ nextWire
                · simp [earlyExposeInsert, earlyCNOTSequence, hsame, horder]
                · simp [earlyExposeInsert, earlyCNOTSequence, hsame, horder, ih]
          | cnot control target hcontrolTarget =>
              by_cases htouch : wire = control ∨ wire = target
              · simp [earlyExposeInsert, earlyCNOTSequence, htouch]
              · simp [earlyExposeInsert, earlyCNOTSequence, htouch, ih]

/-- Exposure preserves every literal CNOT and their exact chronological order. -/
@[simp]
theorem earlyCNOTSequence_earlyExpose {n : ℕ}
    (circuit : FusionCircuit n) :
    earlyCNOTSequence (earlyExpose circuit) =
      earlyCNOTSequence circuit := by
  induction circuit with
  | nil => rfl
  | cons gate circuit ih =>
      rw [earlyExpose, earlyCNOTSequence_earlyExposeInsert]
      cases gate <;> simp [earlyCNOTSequence, ih]

private theorem earlyCNOTSequence_normalizeInsert {n : ℕ}
    (gate : FusionPrimitive n) :
    ∀ circuit : FusionCircuit n,
      earlyCNOTSequence
          (NormalizeCore.insert earlyIsIdentity earlyCombine gate circuit) =
        earlyCNOTSequence (gate :: circuit) := by
  intro circuit
  induction circuit generalizing gate with
  | nil => cases gate <;> rfl
  | cons next rest ih =>
      cases gate with
      | cnot => rfl
      | twoQubit => rfl
      | oneQubit wire payload =>
          cases next with
          | cnot => rfl
          | twoQubit => rfl
          | oneQubit nextWire nextPayload =>
              by_cases hsame : wire = nextWire
              · simp [NormalizeCore.insert, earlyIsIdentity, earlyCombine,
                  earlyCNOTSequence, hsame, ih]
              · simp [NormalizeCore.insert, earlyIsIdentity, earlyCombine,
                  earlyCNOTSequence, hsame]

/-- Adjacent one-qubit fusion preserves literal CNOT syntax and order. -/
@[simp]
theorem earlyCNOTSequence_earlyAdjacentNormalize {n : ℕ}
    (circuit : FusionCircuit n) :
    earlyCNOTSequence (earlyAdjacentNormalize circuit) =
      earlyCNOTSequence circuit := by
  induction circuit with
  | nil => rfl
  | cons gate circuit ih =>
      have ih' :
          earlyCNOTSequence
              (NormalizeCore.normalize earlyIsIdentity earlyCombine circuit) =
            earlyCNOTSequence circuit := by
        simpa only [earlyAdjacentNormalize] using ih
      rw [earlyAdjacentNormalize, NormalizeCore.normalize,
        earlyCNOTSequence_normalizeInsert]
      cases gate <;> simp only [earlyCNOTSequence, ih']

/-- The complete early pass preserves every literal CNOT in exact order. -/
@[simp]
theorem earlyCNOTSequence_normalizeEarly {n : ℕ}
    (circuit : FusionCircuit n) :
    earlyCNOTSequence (normalizeEarly circuit) =
      earlyCNOTSequence circuit := by
  rw [normalizeEarly, earlyCNOTSequence_earlyAdjacentNormalize,
    earlyCNOTSequence_earlyExpose]

@[simp]
private theorem earlyCNOTSequence_append {n : ℕ}
    (first second : FusionCircuit n) :
    earlyCNOTSequence (FusionCircuit.append first second) =
      earlyCNOTSequence first ++ earlyCNOTSequence second := by
  induction first with
  | nil => rfl
  | cons gate first ih =>
      have ih' : earlyCNOTSequence (first ++ second) =
          earlyCNOTSequence first ++ earlyCNOTSequence second := by
        simpa only [FusionCircuit.append] using ih
      cases gate <;> simp only [FusionCircuit.append, List.cons_append,
        earlyCNOTSequence, ih']

/-! ## Barrier-preserving mixed programs -/

/--
Normalize a mixed program while carrying the visible run since the previous
barrier.  A barrier flushes that run, is copied verbatim, and restarts the
accumulator.  The final run is flushed at the end of the program.
-/
def earlyNormalizeProgramAux {n : ℕ} (visible : FusionCircuit n) :
    FusionProgram n → FusionProgram n
  | [] => FusionProgram.visible (normalizeEarly visible)
  | .gate gate :: program =>
      earlyNormalizeProgramAux (FusionCircuit.append visible [gate]) program
  | .barrier primitive :: program =>
      FusionProgram.append
        (FusionProgram.visible (normalizeEarly visible))
        (.barrier primitive :: earlyNormalizeProgramAux [] program)

/-- Normalize each maximal visible run independently across exact barriers. -/
def normalizeEarlyProgram {n : ℕ} (program : FusionProgram n) :
    FusionProgram n :=
  earlyNormalizeProgramAux [] program

private theorem earlyNormalizeProgramAux_visible {n : ℕ}
    (accumulated circuit : FusionCircuit n) :
    earlyNormalizeProgramAux accumulated (FusionProgram.visible circuit) =
      FusionProgram.visible
        (normalizeEarly (FusionCircuit.append accumulated circuit)) := by
  induction circuit generalizing accumulated with
  | nil =>
      simp [earlyNormalizeProgramAux, FusionProgram.visible,
        FusionCircuit.append]
  | cons gate circuit ih =>
      change earlyNormalizeProgramAux
          (FusionCircuit.append accumulated [gate])
          (FusionProgram.visible circuit) =
        FusionProgram.visible
          (normalizeEarly
            (FusionCircuit.append accumulated (gate :: circuit)))
      rw [ih]
      have happend :
          FusionCircuit.append
              (FusionCircuit.append accumulated [gate]) circuit =
            FusionCircuit.append accumulated (gate :: circuit) := by
        simp [FusionCircuit.append, List.append_assoc]
      rw [happend]

/-- A fully visible program is normalized by exactly the visible early pass. -/
@[simp]
theorem normalizeEarlyProgram_visible {n : ℕ}
    (circuit : FusionCircuit n) :
    normalizeEarlyProgram (FusionProgram.visible circuit) =
      FusionProgram.visible (normalizeEarly circuit) := by
  simpa only [normalizeEarlyProgram, FusionCircuit.append,
    List.nil_append] using
      earlyNormalizeProgramAux_visible ([] : FusionCircuit n) circuit

/-- A leading barrier is copied verbatim and starts a fresh visible run. -/
@[simp]
theorem normalizeEarlyProgram_barrier {n : ℕ}
    (primitive : Primitive n) (program : FusionProgram n) :
    normalizeEarlyProgram (.barrier primitive :: program) =
      .barrier primitive :: normalizeEarlyProgram program := by
  rfl

private theorem eval_earlyNormalizeProgramAux {n : ℕ}
    (visible : FusionCircuit n) (program : FusionProgram n) :
    FusionProgram.eval (earlyNormalizeProgramAux visible program) =
      FusionProgram.eval program * FusionCircuit.eval visible := by
  induction program generalizing visible with
  | nil => simp [earlyNormalizeProgramAux]
  | cons step program ih =>
      cases step with
      | gate gate =>
          rw [earlyNormalizeProgramAux, ih, FusionCircuit.eval_append]
          simp [FusionProgram.eval_cons, FusionStep.denotation,
            FusionStep.lower, mul_assoc]
      | barrier primitive =>
          rw [earlyNormalizeProgramAux, FusionProgram.eval_append]
          simp [ih, FusionProgram.eval_cons, mul_assoc]

/-- Mixed-program early normalization preserves exact full-register evaluation. -/
@[simp]
theorem eval_normalizeEarlyProgram {n : ℕ} (program : FusionProgram n) :
    FusionProgram.eval (normalizeEarlyProgram program) =
      FusionProgram.eval program := by
  rw [normalizeEarlyProgram, eval_earlyNormalizeProgramAux]
  simp

/-- Exact evaluation is also preserved after lowering to trusted circuit syntax. -/
@[simp]
theorem eval_lower_normalizeEarlyProgram {n : ℕ}
    (program : FusionProgram n) :
    Circuit.eval (normalizeEarlyProgram program).lower =
      Circuit.eval program.lower := by
  rw [FusionProgram.eval_lower, FusionProgram.eval_lower,
    eval_normalizeEarlyProgram]

/-- Ordered list of exact trusted primitives stored at early-program barriers. -/
def earlyBarrierSequence {n : ℕ} : FusionProgram n → List (Primitive n)
  | [] => []
  | .gate _ :: program => earlyBarrierSequence program
  | .barrier primitive :: program =>
      primitive :: earlyBarrierSequence program

@[simp]
private theorem earlyBarrierSequence_visible {n : ℕ}
    (circuit : FusionCircuit n) :
    earlyBarrierSequence (FusionProgram.visible circuit) = [] := by
  induction circuit with
  | nil => rfl
  | cons gate circuit ih =>
      change earlyBarrierSequence
          (.gate gate :: FusionProgram.visible circuit) = []
      simpa only [earlyBarrierSequence] using ih

@[simp]
private theorem earlyBarrierSequence_append {n : ℕ}
    (first second : FusionProgram n) :
    earlyBarrierSequence (FusionProgram.append first second) =
      earlyBarrierSequence first ++ earlyBarrierSequence second := by
  induction first with
  | nil => rfl
  | cons step first ih =>
      have ih' : earlyBarrierSequence (first ++ second) =
          earlyBarrierSequence first ++ earlyBarrierSequence second := by
        simpa only [FusionProgram.append] using ih
      cases step <;> simp only [FusionProgram.append, List.cons_append,
        earlyBarrierSequence, ih']

private theorem earlyBarrierSequence_earlyNormalizeProgramAux {n : ℕ}
    (visible : FusionCircuit n) (program : FusionProgram n) :
    earlyBarrierSequence (earlyNormalizeProgramAux visible program) =
      earlyBarrierSequence program := by
  induction program generalizing visible with
  | nil => simp [earlyNormalizeProgramAux, earlyBarrierSequence]
  | cons step program ih =>
      cases step with
      | gate gate =>
          rw [earlyNormalizeProgramAux, ih]
          rfl
      | barrier primitive =>
          rw [earlyNormalizeProgramAux, earlyBarrierSequence_append,
            earlyBarrierSequence_visible]
          simp only [List.nil_append, earlyBarrierSequence]
          rw [ih]

/-- Every barrier payload is retained verbatim and in exact chronological order. -/
@[simp]
theorem earlyBarrierSequence_normalizeEarlyProgram {n : ℕ}
    (program : FusionProgram n) :
    earlyBarrierSequence (normalizeEarlyProgram program) =
      earlyBarrierSequence program := by
  exact earlyBarrierSequence_earlyNormalizeProgramAux [] program

/-- Ordered literal-CNOT trace across the visible steps of a mixed program. -/
def earlyProgramCNOTSequence {n : ℕ} :
    FusionProgram n → List (OrderedWirePair n)
  | [] => []
  | .gate (.cnot control target h) :: program =>
      ⟨control, target, h⟩ :: earlyProgramCNOTSequence program
  | .gate _ :: program => earlyProgramCNOTSequence program
  | .barrier _ :: program => earlyProgramCNOTSequence program

@[simp]
private theorem earlyProgramCNOTSequence_visible {n : ℕ}
    (circuit : FusionCircuit n) :
    earlyProgramCNOTSequence (FusionProgram.visible circuit) =
      earlyCNOTSequence circuit := by
  induction circuit with
  | nil => rfl
  | cons gate circuit ih =>
      change earlyProgramCNOTSequence
          (.gate gate :: FusionProgram.visible circuit) =
        earlyCNOTSequence (gate :: circuit)
      cases gate <;> simp only [earlyProgramCNOTSequence,
        earlyCNOTSequence, ih]

@[simp]
private theorem earlyProgramCNOTSequence_append {n : ℕ}
    (first second : FusionProgram n) :
    earlyProgramCNOTSequence (FusionProgram.append first second) =
      earlyProgramCNOTSequence first ++ earlyProgramCNOTSequence second := by
  induction first with
  | nil => rfl
  | cons step first ih =>
      have ih' : earlyProgramCNOTSequence (first ++ second) =
          earlyProgramCNOTSequence first ++
            earlyProgramCNOTSequence second := by
        simpa only [FusionProgram.append] using ih
      cases step with
      | barrier primitive =>
          simpa only [FusionProgram.append, List.cons_append,
            earlyProgramCNOTSequence] using ih'
      | gate gate =>
          cases gate <;>
            simp only [FusionProgram.append, List.cons_append,
              earlyProgramCNOTSequence, ih']

private theorem earlyProgramCNOTSequence_earlyNormalizeProgramAux {n : ℕ}
    (visible : FusionCircuit n) (program : FusionProgram n) :
    earlyProgramCNOTSequence (earlyNormalizeProgramAux visible program) =
      earlyCNOTSequence visible ++ earlyProgramCNOTSequence program := by
  induction program generalizing visible with
  | nil =>
      rw [earlyNormalizeProgramAux, earlyProgramCNOTSequence_visible,
        earlyCNOTSequence_normalizeEarly]
      simp only [earlyProgramCNOTSequence, List.append_nil]
  | cons step program ih =>
      cases step with
      | barrier primitive =>
          rw [earlyNormalizeProgramAux, earlyProgramCNOTSequence_append,
            earlyProgramCNOTSequence_visible,
            earlyCNOTSequence_normalizeEarly]
          simp only [earlyProgramCNOTSequence]
          rw [ih ([] : FusionCircuit n)]
          simp only [earlyCNOTSequence, List.nil_append]
      | gate gate =>
          rw [earlyNormalizeProgramAux, ih,
            earlyCNOTSequence_append]
          cases gate with
          | oneQubit target payload =>
              simp only [earlyCNOTSequence, earlyProgramCNOTSequence,
                List.append_nil]
          | twoQubit pair payload =>
              simp only [earlyCNOTSequence, earlyProgramCNOTSequence,
                List.append_nil]
          | cnot control target hcontrolTarget =>
              simp only [earlyCNOTSequence, earlyProgramCNOTSequence]
              rw [List.append_assoc]
              rfl

/--
Mixed-program early normalization retains every visible literal CNOT, including
its control, target, multiplicity, and chronological order.
-/
@[simp]
theorem earlyProgramCNOTSequence_normalizeEarlyProgram {n : ℕ}
    (program : FusionProgram n) :
    earlyProgramCNOTSequence (normalizeEarlyProgram program) =
      earlyProgramCNOTSequence program := by
  simpa only [normalizeEarlyProgram, earlyCNOTSequence, List.nil_append] using
    earlyProgramCNOTSequence_earlyNormalizeProgramAux
      ([] : FusionCircuit n) program

/-- An all-barrier program is copied exactly, not merely semantically. -/
@[simp]
theorem normalizeEarlyProgram_barriers {n : ℕ} (circuit : Circuit n) :
    normalizeEarlyProgram (FusionProgram.barriers circuit) =
      FusionProgram.barriers circuit := by
  induction circuit with
  | nil => rfl
  | cons primitive circuit ih =>
      have ih' : earlyNormalizeProgramAux []
          (FusionProgram.barriers circuit) =
            FusionProgram.barriers circuit := by
        simpa only [normalizeEarlyProgram] using ih
      change earlyNormalizeProgramAux []
          (.barrier primitive :: FusionProgram.barriers circuit) =
        .barrier primitive :: FusionProgram.barriers circuit
      rw [earlyNormalizeProgramAux, ih']
      rfl

end Barenco.Optimization
