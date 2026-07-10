import Barenco.Optimization.EarlyNormalize
import Barenco.Optimization.Section8Normalize
import Barenco.Optimization.SymbolicCancellation
import Barenco.Optimization.FusionResources

/-!
# Syntax-derived resources for exact normalization

This module derives resource statements from the literal output syntax of the
normalizers.  Partial costs are compared only when the input is accepted.  In
particular, an unsupported input does not acquire a fabricated numerical cost,
and the Section 8 pass is not claimed to preserve acceptance in the stricter
one-qubit/CNOT model after it promotes CNOTs to generic two-qubit nodes.
-/

namespace Barenco.Optimization

open Barenco

/--
An honest nonincrease relation for partial costs: whenever the input has a
numerical cost, the output also has a numerical cost no larger than it.

No condition is imposed on an unsupported (`none`) input.
-/
def AcceptedCostNonincrease (input output : Option ℕ) : Prop :=
  ∀ inputCost, input = some inputCost →
    ∃ outputCost, output = some outputCost ∧ outputCost ≤ inputCost

namespace AcceptedCostNonincrease

/-- Exact equality of partial costs implies accepted-cost nonincrease. -/
theorem of_eq {input output : Option ℕ} (h : output = input) :
    AcceptedCostNonincrease input output := by
  intro inputCost hinput
  exact ⟨inputCost, h.trans hinput, Nat.le_refl inputCost⟩

/-- Accepted-cost nonincrease is reflexive. -/
theorem refl (cost : Option ℕ) : AcceptedCostNonincrease cost cost :=
  of_eq rfl

/-- Accepted-cost nonincrease composes. -/
theorem trans {first second third : Option ℕ}
    (hfirst : AcceptedCostNonincrease first second)
    (hsecond : AcceptedCostNonincrease second third) :
    AcceptedCostNonincrease first third := by
  intro firstCost hfirstCost
  rcases hfirst firstCost hfirstCost with ⟨secondCost, hsecondCost, hsecondLe⟩
  rcases hsecond secondCost hsecondCost with ⟨thirdCost, hthirdCost, hthirdLe⟩
  exact ⟨thirdCost, hthirdCost, hthirdLe.trans hsecondLe⟩

/-- Adding two independently nonincreasing accepted costs preserves the relation. -/
theorem addCost {firstInput firstOutput secondInput secondOutput : Option ℕ}
    (hfirst : AcceptedCostNonincrease firstInput firstOutput)
    (hsecond : AcceptedCostNonincrease secondInput secondOutput) :
    AcceptedCostNonincrease
      (Circuit.addCost firstInput secondInput)
      (Circuit.addCost firstOutput secondOutput) := by
  intro inputCost hinput
  cases hfirstInput : firstInput with
  | none => simp [Circuit.addCost, hfirstInput] at hinput
  | some firstCost =>
      cases hsecondInput : secondInput with
      | none => simp [Circuit.addCost, hfirstInput, hsecondInput] at hinput
      | some secondCost =>
          have hinputCost : inputCost = firstCost + secondCost := by
            simpa [Circuit.addCost, hfirstInput, hsecondInput] using hinput.symm
          rcases hfirst firstCost hfirstInput with
            ⟨firstOutputCost, hfirstOutput, hfirstLe⟩
          rcases hsecond secondCost hsecondInput with
            ⟨secondOutputCost, hsecondOutput, hsecondLe⟩
          refine ⟨firstOutputCost + secondOutputCost, ?_, ?_⟩
          · simp [Circuit.addCost, hfirstOutput, hsecondOutput]
          · rw [hinputCost]
            exact Nat.add_le_add hfirstLe hsecondLe

/-- Removing a nonnegative accepted prefix cost cannot increase the remainder. -/
theorem dropLeft (added : ℕ) (tail : Option ℕ) :
    AcceptedCostNonincrease (Circuit.addCost (some added) tail) tail := by
  intro inputCost hinput
  cases htail : tail with
  | none => simp [Circuit.addCost, htail] at hinput
  | some tailCost =>
      have hinputCost : inputCost = added + tailCost := by
        simpa [Circuit.addCost, htail] using hinput.symm
      exact ⟨tailCost, rfl, by omega⟩

end AcceptedCostNonincrease

private theorem addCost_zero_left (cost : Option ℕ) :
    Circuit.addCost (some 0) cost = cost := by
  cases cost <;> simp [Circuit.addCost]

private theorem addCost_zero_right (cost : Option ℕ) :
    Circuit.addCost cost (some 0) = cost := by
  cases cost <;> simp [Circuit.addCost]

private theorem addCost_eq_none_iff (first second : Option ℕ) :
    Circuit.addCost first second = none ↔ first = none ∨ second = none := by
  cases first <;> cases second <;> simp [Circuit.addCost]

/-! ## Concrete early-policy counts -/

private theorem kindCount_earlyExposeInsert {n : ℕ} (kind : PrimitiveKind)
    (gate : FusionPrimitive n) : ∀ circuit : FusionCircuit n,
    FusionCircuit.kindCount kind (earlyExposeInsert gate circuit) =
      FusionCircuit.kindCount kind (gate :: circuit) := by
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
                · simp only [earlyExposeInsert, hsame, horder, ↓reduceIte]
                  rw [FusionCircuit.kindCount_cons, ih]
                  simp only [FusionCircuit.kindCount_cons, FusionPrimitive.kind]
                  omega
          | cnot control target hcontrolTarget =>
              by_cases htouch : wire = control ∨ wire = target
              · simp [earlyExposeInsert, htouch]
              · simp only [earlyExposeInsert, htouch, ↓reduceIte]
                rw [FusionCircuit.kindCount_cons, ih]
                simp only [FusionCircuit.kindCount_cons, FusionPrimitive.kind]
                omega

private theorem kindCount_earlyExpose {n : ℕ} (kind : PrimitiveKind)
    (circuit : FusionCircuit n) :
    FusionCircuit.kindCount kind (earlyExpose circuit) =
      FusionCircuit.kindCount kind circuit := by
  induction circuit with
  | nil => rfl
  | cons gate circuit ih =>
      rw [earlyExpose, kindCount_earlyExposeInsert,
        FusionCircuit.kindCount_cons, FusionCircuit.kindCount_cons, ih]

private theorem kindCount_earlyInsert_of_ne_oneQubit {n : ℕ}
    (kind : PrimitiveKind) (hkind : kind ≠ .oneQubit)
    (gate : FusionPrimitive n) : ∀ circuit : FusionCircuit n,
    FusionCircuit.kindCount kind
        (NormalizeCore.insert earlyIsIdentity earlyCombine gate circuit) =
      FusionCircuit.kindCount kind (gate :: circuit) := by
  intro circuit
  induction circuit generalizing gate with
  | nil => simp [NormalizeCore.insert, earlyIsIdentity]
  | cons next rest ih =>
      cases gate with
      | cnot => rfl
      | twoQubit => rfl
      | oneQubit wire payload =>
          cases next with
          | cnot => rfl
          | twoQubit => rfl
          | oneQubit nextWire nextPayload =>
              by_cases hwire : wire = nextWire
              · subst nextWire
                rw [NormalizeCore.insert]
                simp only [earlyIsIdentity, Bool.false_eq_true, ↓reduceIte,
                  earlyCombine, ↓reduceIte]
                rw [ih]
                have hone : PrimitiveKind.oneQubit ≠ kind := Ne.symm hkind
                simp [FusionCircuit.kindCount_cons, FusionPrimitive.kind, hone]
              · simp [NormalizeCore.insert, earlyIsIdentity, earlyCombine, hwire]

private theorem kindCount_earlyAdjacentNormalize_of_ne_oneQubit {n : ℕ}
    (kind : PrimitiveKind) (hkind : kind ≠ .oneQubit)
    (circuit : FusionCircuit n) :
    FusionCircuit.kindCount kind (earlyAdjacentNormalize circuit) =
      FusionCircuit.kindCount kind circuit := by
  change FusionCircuit.kindCount kind
      (NormalizeCore.normalize earlyIsIdentity earlyCombine circuit) =
    FusionCircuit.kindCount kind circuit
  induction circuit with
  | nil => rfl
  | cons gate circuit ih =>
      rw [NormalizeCore.normalize,
        kindCount_earlyInsert_of_ne_oneQubit kind hkind,
        FusionCircuit.kindCount_cons, FusionCircuit.kindCount_cons, ih]

/-- The complete early pass preserves the exact number of literal CNOT nodes. -/
@[simp]
theorem cnotCount_normalizeEarly {n : ℕ} (circuit : FusionCircuit n) :
    FusionCircuit.cnotCount (normalizeEarly circuit) =
      FusionCircuit.cnotCount circuit := by
  rw [normalizeEarly]
  change FusionCircuit.kindCount .cnot
      (earlyAdjacentNormalize (earlyExpose circuit)) =
    FusionCircuit.kindCount .cnot circuit
  rw [kindCount_earlyAdjacentNormalize_of_ne_oneQubit .cnot (by decide),
    kindCount_earlyExpose]

/-- The complete early pass preserves every generic two-qubit node count. -/
@[simp]
theorem twoQubitCount_normalizeEarly {n : ℕ} (circuit : FusionCircuit n) :
    FusionCircuit.twoQubitCount (normalizeEarly circuit) =
      FusionCircuit.twoQubitCount circuit := by
  rw [normalizeEarly]
  change FusionCircuit.kindCount .arbitraryTwoQubit
      (earlyAdjacentNormalize (earlyExpose circuit)) =
    FusionCircuit.kindCount .arbitraryTwoQubit circuit
  rw [kindCount_earlyAdjacentNormalize_of_ne_oneQubit .arbitraryTwoQubit
      (by decide),
    kindCount_earlyExpose]

/-- Literal visible gate count for the early pass is nonincreasing. -/
theorem gateCount_normalizeEarly_le {n : ℕ} (circuit : FusionCircuit n) :
    FusionCircuit.gateCount (normalizeEarly circuit) ≤
      FusionCircuit.gateCount circuit :=
  length_normalizeEarly_le circuit

/-- The early pass can only fuse one-qubit nodes, so their count cannot grow. -/
theorem oneQubitCount_normalizeEarly_le {n : ℕ}
    (circuit : FusionCircuit n) :
    FusionCircuit.oneQubitCount (normalizeEarly circuit) ≤
      FusionCircuit.oneQubitCount circuit := by
  have htotal := gateCount_normalizeEarly_le circuit
  rw [FusionCircuit.gateCount_eq_componentCounts,
    FusionCircuit.gateCount_eq_componentCounts,
    cnotCount_normalizeEarly, twoQubitCount_normalizeEarly] at htotal
  omega

/--
When the input is accepted by the Sections 3--7 model, the literal early-pass
output remains accepted and has no larger cost.
-/
theorem normalizeEarly_oneQubitCNOT_acceptedCostNonincrease {n : ℕ}
    (circuit : FusionCircuit n) :
    AcceptedCostNonincrease
      (FusionCircuit.cost CostModel.oneQubitCNOT circuit)
      (FusionCircuit.cost CostModel.oneQubitCNOT (normalizeEarly circuit)) := by
  intro inputCost hinput
  rcases (FusionCircuit.oneQubitCNOT_cost_eq_some_iff circuit).mp hinput with
    ⟨htwo, hgate⟩
  refine ⟨FusionCircuit.gateCount (normalizeEarly circuit), ?_, ?_⟩
  · apply (FusionCircuit.oneQubitCNOT_cost_eq_some_iff _).2
    exact ⟨by simpa using htwo, rfl⟩
  · simpa [hgate] using gateCount_normalizeEarly_le circuit

/--
The early pass preserves unsupportedness in the one-qubit/CNOT model exactly:
generic two-qubit nodes are neither created nor removed.
-/
theorem normalizeEarly_oneQubitCNOT_cost_eq_none_iff {n : ℕ}
    (circuit : FusionCircuit n) :
    FusionCircuit.cost CostModel.oneQubitCNOT (normalizeEarly circuit) = none ↔
      FusionCircuit.cost CostModel.oneQubitCNOT circuit = none := by
  rw [FusionCircuit.oneQubitCNOT_cost_eq_none_iff,
    FusionCircuit.oneQubitCNOT_cost_eq_none_iff,
    twoQubitCount_normalizeEarly]

/-- The same accepted-cost theorem after exact lowering to trusted syntax. -/
theorem normalizeEarly_lower_oneQubitCNOT_acceptedCostNonincrease {n : ℕ}
    (circuit : FusionCircuit n) :
    AcceptedCostNonincrease
      (Circuit.cost CostModel.oneQubitCNOT circuit.lower)
      (Circuit.cost CostModel.oneQubitCNOT (normalizeEarly circuit).lower) := by
  simpa only [FusionCircuit.cost_lower] using
    normalizeEarly_oneQubitCNOT_acceptedCostNonincrease circuit

/-- Exact unsupportedness preservation after lowering the early visible pass. -/
theorem normalizeEarly_lower_oneQubitCNOT_cost_eq_none_iff {n : ℕ}
    (circuit : FusionCircuit n) :
    Circuit.cost CostModel.oneQubitCNOT (normalizeEarly circuit).lower = none ↔
      Circuit.cost CostModel.oneQubitCNOT circuit.lower = none := by
  simpa only [FusionCircuit.cost_lower] using
    normalizeEarly_oneQubitCNOT_cost_eq_none_iff circuit

/-! ## Section 8 visible resources -/

/-- The Section 8 visible pass has nonincreasing literal gate count. -/
theorem section8Normalize_gateCount_nonincrease {n : ℕ}
    (circuit : FusionCircuit n) :
    FusionCircuit.gateCount (section8Normalize circuit) ≤
      FusionCircuit.gateCount circuit :=
  gateCount_section8Normalize_le circuit

/--
The Section 8 model accepts every visible node, so the pass's literal
gate-count bound is exactly an accepted-cost nonincrease statement.
-/
theorem section8Normalize_arbitraryTwoQubit_acceptedCostNonincrease {n : ℕ}
    (circuit : FusionCircuit n) :
    AcceptedCostNonincrease
      (FusionCircuit.cost CostModel.arbitraryTwoQubit circuit)
      (FusionCircuit.cost CostModel.arbitraryTwoQubit
        (section8Normalize circuit)) := by
  intro inputCost hinput
  rw [FusionCircuit.arbitraryTwoQubit_cost_eq_gateCount] at hinput
  injection hinput with hinputCost
  refine ⟨FusionCircuit.gateCount (section8Normalize circuit), ?_, ?_⟩
  · exact FusionCircuit.arbitraryTwoQubit_cost_eq_gateCount _
  · simpa [hinputCost] using section8Normalize_gateCount_nonincrease circuit

/-- The Section 8 accepted-cost bound after exact lowering to trusted syntax. -/
theorem section8Normalize_lower_arbitraryTwoQubit_acceptedCostNonincrease
    {n : ℕ} (circuit : FusionCircuit n) :
    AcceptedCostNonincrease
      (Circuit.cost CostModel.arbitraryTwoQubit circuit.lower)
      (Circuit.cost CostModel.arbitraryTwoQubit
        (section8Normalize circuit).lower) := by
  simpa only [FusionCircuit.cost_lower] using
    section8Normalize_arbitraryTwoQubit_acceptedCostNonincrease circuit

/-! ## Symbolic cancellation resources -/

/--
After valuation and erasure, symbolic early normalization remains accepted by
the one-qubit/CNOT model and its literal accepted cost is nonincreasing.
-/
theorem SymbolicCircuit.normalize_erased_oneQubitCNOT_acceptedCostNonincrease
    [DecidableEq Atom] (valuation : Atom → QubitUnitary)
    (circuit : SymbolicCircuit Atom n) :
    AcceptedCostNonincrease
      (FusionCircuit.cost CostModel.oneQubitCNOT
        (SymbolicCircuit.erase valuation circuit))
      (FusionCircuit.cost CostModel.oneQubitCNOT
        (SymbolicCircuit.erase valuation (SymbolicCircuit.normalize circuit))) := by
  intro inputCost hinput
  rw [SymbolicCircuit.erase_oneQubitCNOTCost] at hinput
  injection hinput with hinputCost
  refine ⟨SymbolicCircuit.gateCount (SymbolicCircuit.normalize circuit), ?_, ?_⟩
  · exact SymbolicCircuit.erase_oneQubitCNOTCost valuation _
  · simpa [hinputCost] using SymbolicCircuit.gateCount_normalize_le circuit

/-- The symbolic accepted-cost bound after exact lowering to trusted syntax. -/
theorem SymbolicCircuit.normalize_lower_erased_oneQubitCNOT_acceptedCostNonincrease
    [DecidableEq Atom] (valuation : Atom → QubitUnitary)
    (circuit : SymbolicCircuit Atom n) :
    AcceptedCostNonincrease
      (Circuit.cost CostModel.oneQubitCNOT
        (SymbolicCircuit.erase valuation circuit).lower)
      (Circuit.cost CostModel.oneQubitCNOT
        (SymbolicCircuit.erase valuation
          (SymbolicCircuit.normalize circuit)).lower) := by
  simpa only [FusionCircuit.cost_lower] using
    SymbolicCircuit.normalize_erased_oneQubitCNOT_acceptedCostNonincrease
      valuation circuit

/-! ## Barrier-separated early-program resources -/

private theorem gateCount_earlyNormalizeProgramAux_le {n : ℕ}
    (visible : FusionCircuit n) (program : FusionProgram n) :
    FusionProgram.gateCount (earlyNormalizeProgramAux visible program) ≤
      FusionCircuit.gateCount visible + FusionProgram.gateCount program := by
  induction program generalizing visible with
  | nil =>
      simpa [earlyNormalizeProgramAux] using gateCount_normalizeEarly_le visible
  | cons step program ih =>
      cases step with
      | gate gate =>
          rw [earlyNormalizeProgramAux]
          have h := ih (FusionCircuit.append visible [gate])
          rw [FusionCircuit.gateCount_append] at h
          have hsingle : FusionCircuit.gateCount ([gate] : FusionCircuit n) = 1 := rfl
          rw [hsingle] at h
          rw [FusionProgram.gateCount_cons]
          omega
      | barrier primitive =>
          rw [earlyNormalizeProgramAux, FusionProgram.gateCount_append,
            FusionProgram.gateCount_visible, FusionProgram.gateCount_cons,
            FusionProgram.gateCount_cons]
          have hvis := gateCount_normalizeEarly_le visible
          have htail := ih ([] : FusionCircuit n)
          simp only [FusionCircuit.gateCount, List.length_nil, zero_add] at htail
          omega

/-- Early mixed-program normalization never increases literal step count. -/
theorem gateCount_normalizeEarlyProgram_le {n : ℕ}
    (program : FusionProgram n) :
    FusionProgram.gateCount (normalizeEarlyProgram program) ≤
      FusionProgram.gateCount program := by
  simpa [normalizeEarlyProgram] using
    gateCount_earlyNormalizeProgramAux_le ([] : FusionCircuit n) program

private theorem earlyNormalizeProgramAux_oneQubitCNOT_acceptedCostNonincrease
    {n : ℕ} (visible : FusionCircuit n) (program : FusionProgram n) :
    AcceptedCostNonincrease
      (Circuit.addCost
        (FusionCircuit.cost CostModel.oneQubitCNOT visible)
        (FusionProgram.cost CostModel.oneQubitCNOT program))
      (FusionProgram.cost CostModel.oneQubitCNOT
        (earlyNormalizeProgramAux visible program)) := by
  induction program generalizing visible with
  | nil =>
      rw [earlyNormalizeProgramAux, FusionProgram.cost_visible,
        FusionProgram.cost_nil, addCost_zero_right]
      exact normalizeEarly_oneQubitCNOT_acceptedCostNonincrease visible
  | cons step program ih =>
      cases step with
      | gate gate =>
          rw [earlyNormalizeProgramAux]
          have h := ih (FusionCircuit.append visible [gate])
          rw [FusionCircuit.cost_append, FusionCircuit.cost_cons,
            FusionCircuit.cost_nil, addCost_zero_right] at h
          rw [FusionProgram.cost_cons, FusionStep.cost_gate,
            Circuit.addCost_assoc]
          exact h
      | barrier primitive =>
          rw [earlyNormalizeProgramAux, FusionProgram.cost_append,
            FusionProgram.cost_visible, FusionProgram.cost_cons,
            FusionStep.cost_barrier, FusionProgram.cost_cons,
            FusionStep.cost_barrier]
          have hvis :=
            normalizeEarly_oneQubitCNOT_acceptedCostNonincrease visible
          have htail := ih ([] : FusionCircuit n)
          rw [FusionCircuit.cost_nil, addCost_zero_left] at htail
          exact AcceptedCostNonincrease.addCost hvis
            (AcceptedCostNonincrease.addCost
              (AcceptedCostNonincrease.refl
                (CostModel.oneQubitCNOT.primitiveCost primitive.kind))
              htail)

private theorem earlyNormalizeProgramAux_oneQubitCNOT_cost_eq_none_iff
    {n : ℕ} (visible : FusionCircuit n) (program : FusionProgram n) :
    FusionProgram.cost CostModel.oneQubitCNOT
        (earlyNormalizeProgramAux visible program) = none ↔
      Circuit.addCost
        (FusionCircuit.cost CostModel.oneQubitCNOT visible)
        (FusionProgram.cost CostModel.oneQubitCNOT program) = none := by
  induction program generalizing visible with
  | nil =>
      rw [earlyNormalizeProgramAux, FusionProgram.cost_visible,
        FusionProgram.cost_nil, addCost_zero_right]
      exact normalizeEarly_oneQubitCNOT_cost_eq_none_iff visible
  | cons step program ih =>
      cases step with
      | gate gate =>
          rw [earlyNormalizeProgramAux]
          have h := ih (FusionCircuit.append visible [gate])
          rw [FusionCircuit.cost_append, FusionCircuit.cost_cons,
            FusionCircuit.cost_nil, addCost_zero_right] at h
          rw [FusionProgram.cost_cons, FusionStep.cost_gate,
            Circuit.addCost_assoc]
          exact h
      | barrier primitive =>
          rw [earlyNormalizeProgramAux, FusionProgram.cost_append,
            FusionProgram.cost_visible, FusionProgram.cost_cons,
            FusionStep.cost_barrier, FusionProgram.cost_cons,
            FusionStep.cost_barrier]
          have hvis := normalizeEarly_oneQubitCNOT_cost_eq_none_iff visible
          have htail := ih ([] : FusionCircuit n)
          rw [FusionCircuit.cost_nil, addCost_zero_left] at htail
          simp only [addCost_eq_none_iff]
          rw [hvis, htail]

/--
If an early-model mixed program is accepted, normalization preserves acceptance
and produces a cost no larger than the input while copying barriers exactly.
-/
theorem normalizeEarlyProgram_oneQubitCNOT_acceptedCostNonincrease {n : ℕ}
    (program : FusionProgram n) :
    AcceptedCostNonincrease
      (FusionProgram.cost CostModel.oneQubitCNOT program)
      (FusionProgram.cost CostModel.oneQubitCNOT
        (normalizeEarlyProgram program)) := by
  have h :=
    earlyNormalizeProgramAux_oneQubitCNOT_acceptedCostNonincrease
      ([] : FusionCircuit n) program
  rw [FusionCircuit.cost_nil, addCost_zero_left] at h
  exact h

/--
Early mixed-program normalization preserves unsupportedness exactly. Visible
generic `U(4)` nodes persist, and every barrier remains the same primitive.
-/
theorem normalizeEarlyProgram_oneQubitCNOT_cost_eq_none_iff {n : ℕ}
    (program : FusionProgram n) :
    FusionProgram.cost CostModel.oneQubitCNOT
        (normalizeEarlyProgram program) = none ↔
      FusionProgram.cost CostModel.oneQubitCNOT program = none := by
  have h := earlyNormalizeProgramAux_oneQubitCNOT_cost_eq_none_iff
    ([] : FusionCircuit n) program
  rw [FusionCircuit.cost_nil, addCost_zero_left] at h
  exact h

/-- The early mixed-program cost theorem after exact lowering. -/
theorem normalizeEarlyProgram_lower_oneQubitCNOT_acceptedCostNonincrease
    {n : ℕ} (program : FusionProgram n) :
    AcceptedCostNonincrease
      (Circuit.cost CostModel.oneQubitCNOT program.lower)
      (Circuit.cost CostModel.oneQubitCNOT
        (normalizeEarlyProgram program).lower) := by
  simpa only [FusionProgram.cost_lower] using
    normalizeEarlyProgram_oneQubitCNOT_acceptedCostNonincrease program

/-- Exact early mixed-program unsupportedness preservation after lowering. -/
theorem normalizeEarlyProgram_lower_oneQubitCNOT_cost_eq_none_iff
    {n : ℕ} (program : FusionProgram n) :
    Circuit.cost CostModel.oneQubitCNOT
        (normalizeEarlyProgram program).lower = none ↔
      Circuit.cost CostModel.oneQubitCNOT program.lower = none := by
  simpa only [FusionProgram.cost_lower] using
    normalizeEarlyProgram_oneQubitCNOT_cost_eq_none_iff program

/-! ## Barrier-separated Section 8 program resources -/

private theorem gateCount_section8ProgramInsert_le {n : ℕ}
    (gate : FusionPrimitive n) : ∀ program : FusionProgram n,
    FusionProgram.gateCount (section8ProgramInsert gate program) ≤
      FusionProgram.gateCount program + 1 := by
  intro program
  induction program generalizing gate with
  | nil => exact Nat.le_refl 1
  | cons step program ih =>
      cases step with
      | barrier primitive => exact Nat.le_refl _
      | gate next =>
          rw [section8ProgramInsert]
          generalize hresult : section8Combine gate next = result
          cases result with
          | blocked => exact Nat.le_refl _
          | deleted =>
              simp only [FusionProgram.gateCount, List.length_cons]
              omega
          | fused fused =>
              have h := ih fused
              simp only [FusionProgram.gateCount, List.length_cons] at h ⊢
              omega

/-- Section 8 mixed-program normalization never increases literal step count. -/
theorem gateCount_section8NormalizeProgram_le {n : ℕ}
    (program : FusionProgram n) :
    FusionProgram.gateCount (section8NormalizeProgram program) ≤
      FusionProgram.gateCount program := by
  induction program with
  | nil => exact Nat.le_refl 0
  | cons step program ih =>
      cases step with
      | barrier primitive =>
          rw [section8NormalizeProgram, FusionProgram.gateCount_cons,
            FusionProgram.gateCount_cons]
          omega
      | gate gate =>
          rw [section8NormalizeProgram, FusionProgram.gateCount_cons]
          have hinsert := gateCount_section8ProgramInsert_le
            (promoteCNOT gate) (section8NormalizeProgram program)
          omega

private theorem section8ProgramInsert_arbitraryTwoQubit_acceptedCostNonincrease
    {n : ℕ} (gate : FusionPrimitive n) (program : FusionProgram n) :
    AcceptedCostNonincrease
      (FusionProgram.cost CostModel.arbitraryTwoQubit
        (.gate gate :: program))
      (FusionProgram.cost CostModel.arbitraryTwoQubit
        (section8ProgramInsert gate program)) := by
  induction program generalizing gate with
  | nil => exact AcceptedCostNonincrease.refl _
  | cons step program ih =>
      cases step with
      | barrier primitive => exact AcceptedCostNonincrease.refl _
      | gate next =>
          rw [section8ProgramInsert]
          generalize hresult : section8Combine gate next = result
          cases result with
          | blocked => exact AcceptedCostNonincrease.refl _
          | deleted =>
              simp only [FusionProgram.cost_cons, FusionStep.cost_gate,
                FusionPrimitive.arbitraryTwoQubit_cost]
              exact AcceptedCostNonincrease.trans
                (AcceptedCostNonincrease.dropLeft 1
                  (Circuit.addCost (some 1)
                    (FusionProgram.cost CostModel.arbitraryTwoQubit program)))
                (AcceptedCostNonincrease.dropLeft 1
                  (FusionProgram.cost CostModel.arbitraryTwoQubit program))
          | fused fused =>
              have h := ih fused
              simp only [FusionProgram.cost_cons, FusionStep.cost_gate,
                FusionPrimitive.arbitraryTwoQubit_cost] at h ⊢
              exact AcceptedCostNonincrease.trans
                (AcceptedCostNonincrease.dropLeft 1
                  (Circuit.addCost (some 1)
                    (FusionProgram.cost CostModel.arbitraryTwoQubit program)))
                h

@[simp]
private theorem arbitraryTwoQubit_gateStep_cost {n : ℕ}
    (gate : FusionPrimitive n) :
    FusionStep.cost CostModel.arbitraryTwoQubit (.gate gate) = some 1 := by
  rw [FusionStep.cost_gate]
  exact FusionPrimitive.arbitraryTwoQubit_cost gate

private theorem section8ProgramInsert_arbitraryTwoQubit_cost_eq_none_iff
    {n : ℕ} (gate : FusionPrimitive n) (program : FusionProgram n) :
    FusionProgram.cost CostModel.arbitraryTwoQubit
        (section8ProgramInsert gate program) = none ↔
      FusionProgram.cost CostModel.arbitraryTwoQubit program = none := by
  induction program generalizing gate with
  | nil =>
      simp only [section8ProgramInsert, FusionProgram.cost_cons,
        arbitraryTwoQubit_gateStep_cost, FusionProgram.cost_nil,
        addCost_eq_none_iff, Option.some_ne_none, false_or]
  | cons step program ih =>
      cases step with
      | barrier primitive =>
          simp only [section8ProgramInsert, FusionProgram.cost_cons,
            arbitraryTwoQubit_gateStep_cost, addCost_eq_none_iff,
            Option.some_ne_none, false_or]
      | gate next =>
          rw [section8ProgramInsert]
          generalize hresult : section8Combine gate next = result
          cases result with
          | blocked =>
              simp only [FusionProgram.cost_cons,
                arbitraryTwoQubit_gateStep_cost, addCost_eq_none_iff,
                Option.some_ne_none, false_or]
          | deleted =>
              simp only [FusionProgram.cost_cons,
                arbitraryTwoQubit_gateStep_cost, addCost_eq_none_iff,
                Option.some_ne_none, false_or]
          | fused fused =>
              have h := ih fused
              simp only [FusionProgram.cost_cons,
                arbitraryTwoQubit_gateStep_cost, addCost_eq_none_iff,
                Option.some_ne_none, false_or] at h ⊢
              exact h

/--
If a Section 8 mixed program is accepted, normalizing its visible runs preserves
acceptance and cannot increase cost. Unsupported barriers remain unsupported.
-/
theorem section8NormalizeProgram_arbitraryTwoQubit_acceptedCostNonincrease
    {n : ℕ} (program : FusionProgram n) :
    AcceptedCostNonincrease
      (FusionProgram.cost CostModel.arbitraryTwoQubit program)
      (FusionProgram.cost CostModel.arbitraryTwoQubit
        (section8NormalizeProgram program)) := by
  induction program with
  | nil => exact AcceptedCostNonincrease.refl _
  | cons step program ih =>
      cases step with
      | barrier primitive =>
          rw [section8NormalizeProgram]
          exact AcceptedCostNonincrease.addCost
            (AcceptedCostNonincrease.refl
              (CostModel.arbitraryTwoQubit.primitiveCost primitive.kind))
            ih
      | gate gate =>
          rw [section8NormalizeProgram]
          have htail :
              AcceptedCostNonincrease
                (FusionProgram.cost CostModel.arbitraryTwoQubit
                  (.gate gate :: program))
                (FusionProgram.cost CostModel.arbitraryTwoQubit
                  (.gate (promoteCNOT gate) ::
                    section8NormalizeProgram program)) := by
            simpa only [FusionProgram.cost_cons, FusionStep.cost_gate,
              FusionPrimitive.arbitraryTwoQubit_cost] using
              AcceptedCostNonincrease.addCost
                (AcceptedCostNonincrease.refl (some 1)) ih
          exact AcceptedCostNonincrease.trans htail
            (section8ProgramInsert_arbitraryTwoQubit_acceptedCostNonincrease
              (promoteCNOT gate) (section8NormalizeProgram program))

/--
Section 8 mixed-program normalization preserves unsupportedness exactly. Every
visible node is supported by this model, while exact barriers are copied and
therefore remain the sole possible source of `none`.
-/
theorem section8NormalizeProgram_arbitraryTwoQubit_cost_eq_none_iff
    {n : ℕ} (program : FusionProgram n) :
    FusionProgram.cost CostModel.arbitraryTwoQubit
        (section8NormalizeProgram program) = none ↔
      FusionProgram.cost CostModel.arbitraryTwoQubit program = none := by
  induction program with
  | nil => simp [section8NormalizeProgram, FusionProgram.cost]
  | cons step program ih =>
      cases step with
      | barrier primitive =>
          rw [section8NormalizeProgram]
          simp only [FusionProgram.cost_cons, FusionStep.cost_barrier,
            addCost_eq_none_iff, ih]
      | gate gate =>
          rw [section8NormalizeProgram,
            section8ProgramInsert_arbitraryTwoQubit_cost_eq_none_iff, ih]
          simp only [FusionProgram.cost_cons,
            arbitraryTwoQubit_gateStep_cost, addCost_eq_none_iff,
            Option.some_ne_none, false_or]

/-- The Section 8 mixed-program cost theorem after exact lowering. -/
theorem section8NormalizeProgram_lower_arbitraryTwoQubit_acceptedCostNonincrease
    {n : ℕ} (program : FusionProgram n) :
    AcceptedCostNonincrease
      (Circuit.cost CostModel.arbitraryTwoQubit program.lower)
      (Circuit.cost CostModel.arbitraryTwoQubit
        (section8NormalizeProgram program).lower) := by
  simpa only [FusionProgram.cost_lower] using
    section8NormalizeProgram_arbitraryTwoQubit_acceptedCostNonincrease program

/-- Exact Section 8 mixed-program unsupportedness preservation after lowering. -/
theorem section8NormalizeProgram_lower_arbitraryTwoQubit_cost_eq_none_iff
    {n : ℕ} (program : FusionProgram n) :
    Circuit.cost CostModel.arbitraryTwoQubit
        (section8NormalizeProgram program).lower = none ↔
      Circuit.cost CostModel.arbitraryTwoQubit program.lower = none := by
  simpa only [FusionProgram.cost_lower] using
    section8NormalizeProgram_arbitraryTwoQubit_cost_eq_none_iff program

end Barenco.Optimization
