import Barenco.Optimization.FusionLaws
import Barenco.Optimization.FusionResources
import Barenco.Optimization.NormalizeCore

/-!
# Exact Section 8 fusion normalization

The Section 8 policy may treat every certified one- or two-qubit operation as
one basic node.  This module therefore promotes each visible CNOT to its trusted
ordered `U(4)` payload and greedily combines adjacent nodes whenever their
structural support fits one ordered pair.

The pass is total and deterministic.  It performs no semantic equality test:
the identity recognizer supplied to `NormalizeCore` is constantly false.
Consequently the pass fuses payloads but never guesses that an arbitrary complex
unitary is identity.  Chronology is exact: `first; second` receives payload
`second * first`.

Mixed programs are normalized one visible run at a time.  A barrier is copied
verbatim and stops every rewrite; neither its metadata nor its denotation is
inspected to recover a payload.
-/

namespace Barenco.Optimization

open Barenco
open NormalizeCore

/-! ## Executable adjacent policy -/

/-- This policy deliberately performs no semantic identity recognition. -/
def section8IsIdentity {n : ℕ} (_ : FusionPrimitive n) : Bool := false

@[simp]
theorem section8IsIdentity_eq_false {n : ℕ} (gate : FusionPrimitive n) :
    section8IsIdentity gate = false := rfl

/--
Deterministically combine two adjacent already-promoted nodes when possible.

The orientation of a newly created pair follows the first then second wire of
two distinct one-qubit nodes.  Existing two-qubit orientation is retained;
oppositely oriented pairs use the explicit local bit-swap reindexing.
-/
def section8Combine {n : ℕ} :
    FusionPrimitive n → FusionPrimitive n → CombineResult (FusionPrimitive n)
  | .oneQubit firstWire first, .oneQubit secondWire second =>
      if h : firstWire = secondWire then
        .fused (.oneQubit firstWire (second * first))
      else
        .fused (.twoQubit ⟨firstWire, secondWire, h⟩
          (localOnePayload second * localZeroPayload first))
  | .oneQubit wire first, .twoQubit pair second =>
      if _ : wire = pair.first then
        .fused (.twoQubit pair (second * localZeroPayload first))
      else if _ : wire = pair.second then
        .fused (.twoQubit pair (second * localOnePayload first))
      else .blocked
  | .twoQubit pair first, .oneQubit wire second =>
      if _ : wire = pair.first then
        .fused (.twoQubit pair (localZeroPayload second * first))
      else if _ : wire = pair.second then
        .fused (.twoQubit pair (localOnePayload second * first))
      else .blocked
  | .twoQubit firstPair first, .twoQubit secondPair second =>
      if _ : firstPair = secondPair then
        .fused (.twoQubit firstPair (second * first))
      else if _ : secondPair = firstPair.swap then
        .fused (.twoQubit firstPair
          (reindexUnitary reverseTwoQubitBasis second * first))
      else .blocked
  | _, _ => .blocked

/-- Every successful adjacent rewrite has the exact head-first denotation. -/
theorem section8Combine_sound {n : ℕ} (first second : FusionPrimitive n) :
    CombineResult.Sound FusionPrimitive.denotation first second
      (section8Combine first second) := by
  cases first with
  | cnot => cases second <;> trivial
  | oneQubit firstWire first =>
      cases second with
      | cnot => trivial
      | oneQubit secondWire second =>
          by_cases h : firstWire = secondWire
          · subst secondWire
            simpa [section8Combine, CombineResult.Sound] using
              oneQubit_chronological firstWire first second
          · simp only [section8Combine, h, ↓reduceDIte,
              CombineResult.Sound]
            change twoWireUnitary ⟨firstWire, secondWire, h⟩
                (localOnePayload second * localZeroPayload first) =
              localUnitary secondWire second * localUnitary firstWire first
            rw [twoWireUnitary_mul, twoWireUnitary_localOnePayload,
              twoWireUnitary_localZeroPayload]
      | twoQubit pair second =>
          by_cases hfirst : firstWire = pair.first
          · subst firstWire
            simpa [section8Combine, CombineResult.Sound] using
              oneQubit_first_then_twoQubit pair first second
          · by_cases hsecond : firstWire = pair.second
            · subst firstWire
              simpa [section8Combine, hfirst, CombineResult.Sound] using
                oneQubit_second_then_twoQubit pair first second
            · simp [section8Combine, hfirst, hsecond,
                CombineResult.Sound]
  | twoQubit firstPair first =>
      cases second with
      | cnot => trivial
      | oneQubit wire second =>
          by_cases hfirst : wire = firstPair.first
          · subst wire
            simpa [section8Combine, CombineResult.Sound] using
              twoQubit_then_oneQubit_first firstPair first second
          · by_cases hsecond : wire = firstPair.second
            · subst wire
              simpa [section8Combine, hfirst, CombineResult.Sound] using
                twoQubit_then_oneQubit_second firstPair first second
            · simp [section8Combine, hfirst, hsecond,
                CombineResult.Sound]
      | twoQubit secondPair second =>
          by_cases hsame : firstPair = secondPair
          · subst secondPair
            simpa [section8Combine, CombineResult.Sound] using
              twoQubit_chronological firstPair first second
          · by_cases hswap : secondPair = firstPair.swap
            · subst secondPair
              simpa [section8Combine, hsame, CombineResult.Sound] using
                twoQubit_then_swap_chronological firstPair first second
            · simp [section8Combine, hsame, hswap,
                CombineResult.Sound]

@[simp]
theorem section8IsIdentity_sound {n : ℕ} (gate : FusionPrimitive n)
    (hidentity : section8IsIdentity gate = true) :
    gate.denotation = 1 := by
  simp at hidentity

/-! ## Visible preprocessing and normalization -/

/-- Promote every CNOT in a visible chronological circuit. -/
def promoteCNOTCircuit {n : ℕ} (circuit : FusionCircuit n) : FusionCircuit n :=
  circuit.map promoteCNOT

@[simp]
theorem length_promoteCNOTCircuit {n : ℕ} (circuit : FusionCircuit n) :
    (promoteCNOTCircuit circuit).length = circuit.length := by
  simp [promoteCNOTCircuit]

@[simp]
theorem eval_promoteCNOTCircuit {n : ℕ} (circuit : FusionCircuit n) :
    FusionCircuit.eval (promoteCNOTCircuit circuit) =
      FusionCircuit.eval circuit := by
  induction circuit with
  | nil => rfl
  | cons gate circuit ih =>
      change FusionCircuit.eval
          (promoteCNOT gate :: promoteCNOTCircuit circuit) =
        FusionCircuit.eval (gate :: circuit)
      simp [ih]

/-- Exact deterministic Section 8 normalization of visible syntax. -/
def section8Normalize {n : ℕ} (circuit : FusionCircuit n) : FusionCircuit n :=
  NormalizeCore.normalize section8IsIdentity section8Combine
    (promoteCNOTCircuit circuit)

private theorem evalChronological_eq_fusionEval {n : ℕ}
    (circuit : FusionCircuit n) :
    evalChronological FusionPrimitive.denotation circuit =
      FusionCircuit.eval circuit := by
  induction circuit with
  | nil => rfl
  | cons gate circuit ih => simp [evalChronological, ih]

/-- The visible pass preserves the exact certified full-register evaluator. -/
@[simp]
theorem eval_section8Normalize {n : ℕ} (circuit : FusionCircuit n) :
    FusionCircuit.eval (section8Normalize circuit) =
      FusionCircuit.eval circuit := by
  rw [← evalChronological_eq_fusionEval, section8Normalize,
    evalChronological_normalize FusionPrimitive.denotation section8IsIdentity
      section8Combine section8IsIdentity_sound section8Combine_sound,
    evalChronological_eq_fusionEval, eval_promoteCNOTCircuit]

/-- Exact evaluator preservation after lowering to established trusted syntax. -/
@[simp]
theorem eval_lower_section8Normalize {n : ℕ} (circuit : FusionCircuit n) :
    Circuit.eval (section8Normalize circuit).lower =
      Circuit.eval circuit.lower := by
  rw [FusionCircuit.eval_lower, FusionCircuit.eval_lower,
    eval_section8Normalize]

/-! ## Structural output invariants -/

/-- A visible circuit contains no literal CNOT constructor. -/
def CNOTFree {n : ℕ} (circuit : FusionCircuit n) : Prop :=
  ∀ gate ∈ circuit, gate.kind ≠ .cnot

private theorem promoteCNOT_not_cnot {n : ℕ} (gate : FusionPrimitive n) :
    (promoteCNOT gate).kind ≠ .cnot := by
  cases gate <;> simp [promoteCNOT, cnotAsTwoQubit,
    FusionPrimitive.kind]

private theorem cnotFree_promoteCNOTCircuit {n : ℕ}
    (circuit : FusionCircuit n) :
    CNOTFree (promoteCNOTCircuit circuit) := by
  intro gate hgate
  rw [promoteCNOTCircuit, List.mem_map] at hgate
  rcases hgate with ⟨source, _, rfl⟩
  exact promoteCNOT_not_cnot source

private theorem section8Combine_fused_not_cnot {n : ℕ}
    (first second fused : FusionPrimitive n)
    (hfused : section8Combine first second = .fused fused) :
    fused.kind ≠ .cnot := by
  cases first with
  | cnot => cases second <;> simp [section8Combine] at hfused
  | oneQubit firstWire first =>
      cases second with
      | cnot => simp [section8Combine] at hfused
      | oneQubit secondWire second =>
          by_cases h : firstWire = secondWire <;>
            simp [section8Combine, h] at hfused <;>
            subst fused <;> simp [FusionPrimitive.kind]
      | twoQubit pair second =>
          by_cases hfirst : firstWire = pair.first
          · simp [section8Combine, hfirst] at hfused
            subst fused
            simp [FusionPrimitive.kind]
          · by_cases hsecond : firstWire = pair.second
            · subst firstWire
              have hne : pair.second ≠ pair.first := pair.ne.symm
              simp [section8Combine, hne] at hfused
              subst fused
              simp [FusionPrimitive.kind]
            · simp [section8Combine, hfirst, hsecond] at hfused
  | twoQubit firstPair first =>
      cases second with
      | cnot => simp [section8Combine] at hfused
      | oneQubit wire second =>
          by_cases hfirst : wire = firstPair.first
          · simp [section8Combine, hfirst] at hfused
            subst fused
            simp [FusionPrimitive.kind]
          · by_cases hsecond : wire = firstPair.second
            · subst wire
              have hne : firstPair.second ≠ firstPair.first := firstPair.ne.symm
              simp [section8Combine, hne] at hfused
              subst fused
              simp [FusionPrimitive.kind]
            · simp [section8Combine, hfirst, hsecond] at hfused
      | twoQubit secondPair second =>
          by_cases hsame : firstPair = secondPair
          · simp [section8Combine, hsame] at hfused
            subst fused
            simp [FusionPrimitive.kind]
          · by_cases hswap : secondPair = firstPair.swap
            · subst secondPair
              have hne : firstPair ≠ firstPair.swap := by
                intro heq
                exact firstPair.ne (congrArg OrderedWirePair.first heq)
              simp [section8Combine, hne] at hfused
              subst fused
              simp [FusionPrimitive.kind]
            · simp [section8Combine, hsame, hswap] at hfused

private theorem cnotFree_insert {n : ℕ} (gate : FusionPrimitive n)
    (hgate : gate.kind ≠ .cnot) :
    ∀ {circuit : FusionCircuit n}, CNOTFree circuit →
      CNOTFree
        (NormalizeCore.insert section8IsIdentity section8Combine gate circuit) := by
  intro circuit hcircuit
  induction circuit generalizing gate with
  | nil =>
      intro output houtput
      simp [NormalizeCore.insert, section8IsIdentity] at houtput
      rcases houtput with rfl
      exact hgate
  | cons next rest ih =>
      have hnext : next.kind ≠ .cnot := hcircuit next (by simp)
      have hrest : CNOTFree rest := by
        intro item hitem
        exact hcircuit item (by simp [hitem])
      simp only [NormalizeCore.insert, section8IsIdentity, Bool.false_eq_true,
        ↓reduceIte]
      generalize hresult : section8Combine gate next = result
      cases result with
      | blocked =>
          intro item hitem
          rcases List.mem_cons.mp hitem with rfl | hitem
          · exact hgate
          · exact hcircuit item hitem
      | deleted => exact hrest
      | fused fused =>
          exact ih fused (section8Combine_fused_not_cnot gate next fused hresult)
            hrest

private theorem cnotFree_normalize {n : ℕ} :
    ∀ {circuit : FusionCircuit n}, CNOTFree circuit →
      CNOTFree
        (NormalizeCore.normalize section8IsIdentity section8Combine circuit) := by
  intro circuit hcircuit
  induction circuit with
  | nil => simp [NormalizeCore.normalize, CNOTFree]
  | cons gate circuit ih =>
      rw [NormalizeCore.normalize]
      apply cnotFree_insert gate (hcircuit gate (by simp))
      apply ih
      intro item hitem
      exact hcircuit item (by simp [hitem])

/-- Section 8 normalization leaves no literal CNOT node in visible syntax. -/
theorem section8Normalize_cnotFree {n : ℕ} (circuit : FusionCircuit n) :
    CNOTFree (section8Normalize circuit) := by
  apply cnotFree_normalize
  exact cnotFree_promoteCNOTCircuit circuit

private theorem cnotCount_eq_zero_of_cnotFree {n : ℕ}
    {circuit : FusionCircuit n} (hfree : CNOTFree circuit) :
    FusionCircuit.cnotCount circuit = 0 := by
  induction circuit with
  | nil => rfl
  | cons gate circuit ih =>
      rw [FusionCircuit.cnotCount] at ih ⊢
      rw [FusionCircuit.kindCount_cons]
      have hgate := hfree gate (by simp)
      have htail : CNOTFree circuit := by
        intro item hitem
        exact hfree item (by simp [hitem])
      rw [ih htail]
      simp [hgate]

@[simp]
theorem section8Normalize_cnotCount {n : ℕ} (circuit : FusionCircuit n) :
    FusionCircuit.cnotCount (section8Normalize circuit) = 0 :=
  cnotCount_eq_zero_of_cnotFree (section8Normalize_cnotFree circuit)

/-- Normalization never increases literal visible list length. -/
theorem length_section8Normalize_le {n : ℕ} (circuit : FusionCircuit n) :
    (section8Normalize circuit).length ≤ circuit.length := by
  rw [section8Normalize]
  exact (length_normalize_le section8IsIdentity section8Combine
    (promoteCNOTCircuit circuit)).trans_eq (length_promoteCNOTCircuit circuit)

/-- Equivalent resource-facing form of literal length nonincrease. -/
theorem gateCount_section8Normalize_le {n : ℕ} (circuit : FusionCircuit n) :
    FusionCircuit.gateCount (section8Normalize circuit) ≤
      FusionCircuit.gateCount circuit := by
  exact length_section8Normalize_le circuit

/-- The output satisfies the generic engine's exact local fixed-point predicate. -/
theorem section8Normalize_stable {n : ℕ} (circuit : FusionCircuit n) :
    NormalizeCore.Stable section8IsIdentity section8Combine
      (section8Normalize circuit) := by
  exact normalize_stable section8IsIdentity section8Combine
    (promoteCNOTCircuit circuit)

private theorem promoteCNOT_eq_self_of_not_cnot {n : ℕ}
    (gate : FusionPrimitive n) (hgate : gate.kind ≠ .cnot) :
    promoteCNOT gate = gate := by
  cases gate <;> simp [promoteCNOT, FusionPrimitive.kind] at hgate ⊢

private theorem promoteCNOTCircuit_eq_self_of_cnotFree {n : ℕ}
    {circuit : FusionCircuit n} (hfree : CNOTFree circuit) :
    promoteCNOTCircuit circuit = circuit := by
  induction circuit with
  | nil => rfl
  | cons gate circuit ih =>
      have hgate : gate.kind ≠ .cnot := hfree gate (by simp)
      have htail : CNOTFree circuit := by
        intro item hitem
        exact hfree item (by simp [hitem])
      change promoteCNOT gate :: promoteCNOTCircuit circuit = gate :: circuit
      rw [promoteCNOT_eq_self_of_not_cnot gate hgate, ih htail]

/-- The complete promote-then-normalize pass is idempotent. -/
@[simp]
theorem section8Normalize_idempotent {n : ℕ} (circuit : FusionCircuit n) :
    section8Normalize (section8Normalize circuit) =
      section8Normalize circuit := by
  rw [section8Normalize,
    promoteCNOTCircuit_eq_self_of_cnotFree (section8Normalize_cnotFree circuit)]
  exact normalize_eq_self_of_stable section8IsIdentity section8Combine
    (section8Normalize_stable circuit)

/-! ## Barrier-preserving mixed programs -/

/-- Insert one promoted earlier gate into the visible run preceding a barrier. -/
def section8ProgramInsert {n : ℕ} (gate : FusionPrimitive n) :
    FusionProgram n → FusionProgram n
  | [] => [.gate gate]
  | .barrier primitive :: program =>
      .gate gate :: .barrier primitive :: program
  | .gate next :: program =>
      match section8Combine gate next with
      | .blocked => .gate gate :: .gate next :: program
      | .deleted => program
      | .fused fused => section8ProgramInsert fused program

/-- Normalize visible runs independently while copying every barrier verbatim. -/
def section8NormalizeProgram {n : ℕ} : FusionProgram n → FusionProgram n
  | [] => []
  | .barrier primitive :: program =>
      .barrier primitive :: section8NormalizeProgram program
  | .gate gate :: program =>
      section8ProgramInsert (promoteCNOT gate)
        (section8NormalizeProgram program)

private theorem section8ProgramInsert_visible {n : ℕ}
    (gate : FusionPrimitive n) (circuit : FusionCircuit n) :
    section8ProgramInsert gate (FusionProgram.visible circuit) =
      FusionProgram.visible
        (NormalizeCore.insert section8IsIdentity section8Combine gate circuit) := by
  induction circuit generalizing gate with
  | nil => rfl
  | cons next circuit ih =>
      change section8ProgramInsert gate
          (.gate next :: FusionProgram.visible circuit) =
        FusionProgram.visible
          (NormalizeCore.insert section8IsIdentity section8Combine gate
            (next :: circuit))
      rw [section8ProgramInsert, NormalizeCore.insert]
      generalize hresult : section8Combine gate next = result
      cases result with
      | blocked => rfl
      | deleted => rfl
      | fused fused => exact ih fused

/--
On a fully visible program, the mixed-program policy is exactly the visible
Section 8 normalizer followed by the visible embedding.
-/
@[simp]
theorem section8NormalizeProgram_visible {n : ℕ}
    (circuit : FusionCircuit n) :
    section8NormalizeProgram (FusionProgram.visible circuit) =
      FusionProgram.visible (section8Normalize circuit) := by
  induction circuit with
  | nil => rfl
  | cons gate circuit ih =>
      change section8NormalizeProgram
          (.gate gate :: FusionProgram.visible circuit) =
        FusionProgram.visible (section8Normalize (gate :: circuit))
      rw [section8NormalizeProgram, ih, section8ProgramInsert_visible]
      rfl

/-- A leading barrier is copied verbatim and blocks every Section 8 rewrite. -/
@[simp]
theorem section8NormalizeProgram_barrier {n : ℕ}
    (primitive : Primitive n) (program : FusionProgram n) :
    section8NormalizeProgram (.barrier primitive :: program) =
      .barrier primitive :: section8NormalizeProgram program := by
  rfl

/-- An all-barrier program is copied exactly, not merely semantically. -/
@[simp]
theorem section8NormalizeProgram_barriers {n : ℕ} (circuit : Circuit n) :
    section8NormalizeProgram (FusionProgram.barriers circuit) =
      FusionProgram.barriers circuit := by
  induction circuit with
  | nil => rfl
  | cons primitive circuit ih =>
      change section8NormalizeProgram
          (.barrier primitive :: FusionProgram.barriers circuit) =
        .barrier primitive :: FusionProgram.barriers circuit
      rw [section8NormalizeProgram, ih]

@[simp]
private theorem gateStep_denotation {n : ℕ} (gate : FusionPrimitive n) :
    (FusionStep.gate gate).denotation = gate.denotation := by
  change gate.lower.denotation = gate.denotation
  exact FusionPrimitive.lower_denotation gate

private theorem eval_section8ProgramInsert {n : ℕ}
    (gate : FusionPrimitive n) (program : FusionProgram n) :
    FusionProgram.eval (section8ProgramInsert gate program) =
      FusionProgram.eval program * gate.denotation := by
  induction program generalizing gate with
  | nil => simp [section8ProgramInsert]
  | cons step program ih =>
      cases step with
      | barrier primitive =>
          simp [section8ProgramInsert, FusionProgram.eval_cons]
      | gate next =>
          rw [section8ProgramInsert]
          generalize hresult : section8Combine gate next = result
          cases result with
          | blocked =>
              simp [FusionProgram.eval_cons, mul_assoc]
          | deleted =>
              have hsound := section8Combine_sound gate next
              rw [hresult] at hsound
              simp only [CombineResult.Sound] at hsound
              simp only [FusionProgram.eval_cons, FusionStep.denotation,
                FusionStep.lower, FusionPrimitive.lower_denotation]
              rw [mul_assoc, hsound, mul_one]
          | fused fused =>
              rw [ih]
              have hsound := section8Combine_sound gate next
              rw [hresult] at hsound
              simp only [CombineResult.Sound] at hsound
              simp only [FusionProgram.eval_cons, FusionStep.denotation,
                FusionStep.lower, FusionPrimitive.lower_denotation]
              rw [hsound, mul_assoc]

/-- Mixed-program normalization preserves the exact independent evaluator. -/
@[simp]
theorem eval_section8NormalizeProgram {n : ℕ} (program : FusionProgram n) :
    FusionProgram.eval (section8NormalizeProgram program) =
      FusionProgram.eval program := by
  induction program with
  | nil => rfl
  | cons step program ih =>
      cases step with
      | barrier primitive => simp [section8NormalizeProgram, ih]
      | gate gate =>
          rw [section8NormalizeProgram, eval_section8ProgramInsert, ih,
            promoteCNOT_denotation]
          simp [FusionProgram.eval_cons]

/-- Exact evaluator preservation after lowering a normalized mixed program. -/
@[simp]
theorem eval_lower_section8NormalizeProgram {n : ℕ}
    (program : FusionProgram n) :
    Circuit.eval (section8NormalizeProgram program).lower =
      Circuit.eval program.lower := by
  rw [FusionProgram.eval_lower, FusionProgram.eval_lower,
    eval_section8NormalizeProgram]

/-- Ordered list of the exact trusted primitives stored at barriers. -/
def barrierSequence {n : ℕ} : FusionProgram n → List (Primitive n)
  | [] => []
  | .gate _ :: program => barrierSequence program
  | .barrier primitive :: program => primitive :: barrierSequence program

private theorem barrierSequence_section8ProgramInsert {n : ℕ}
    (gate : FusionPrimitive n) (program : FusionProgram n) :
    barrierSequence (section8ProgramInsert gate program) =
      barrierSequence program := by
  induction program generalizing gate with
  | nil => rfl
  | cons step program ih =>
      cases step with
      | barrier primitive => rfl
      | gate next =>
          rw [section8ProgramInsert]
          generalize section8Combine gate next = result
          cases result with
          | blocked => rfl
          | deleted => rfl
          | fused fused => exact ih fused

/-- Every barrier is preserved exactly and in the same chronological order. -/
@[simp]
theorem barrierSequence_section8NormalizeProgram {n : ℕ}
    (program : FusionProgram n) :
    barrierSequence (section8NormalizeProgram program) =
      barrierSequence program := by
  induction program with
  | nil => rfl
  | cons step program ih =>
      cases step with
      | barrier primitive => simp [section8NormalizeProgram, barrierSequence, ih]
      | gate gate =>
          rw [section8NormalizeProgram,
            barrierSequence_section8ProgramInsert, ih]
          rfl

end Barenco.Optimization
