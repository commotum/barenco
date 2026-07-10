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

/-- The same accepted-cost theorem after exact lowering to trusted syntax. -/
theorem normalizeEarly_lower_oneQubitCNOT_acceptedCostNonincrease {n : ℕ}
    (circuit : FusionCircuit n) :
    AcceptedCostNonincrease
      (Circuit.cost CostModel.oneQubitCNOT circuit.lower)
      (Circuit.cost CostModel.oneQubitCNOT (normalizeEarly circuit).lower) := by
  simpa only [FusionCircuit.cost_lower] using
    normalizeEarly_oneQubitCNOT_acceptedCostNonincrease circuit

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

end Barenco.Optimization
