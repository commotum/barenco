import Barenco.MultiControl.CleanAncilla
import Barenco.MultiControl.RecursiveExpansion
import Barenco.ControlledCircuit.Selected

/-!
# Primitive expansion of the one-clean-ancilla construction

This leaf expands all three macros in Barenco Lemma 7.11.  The two
prefix-controlled X gates use the exact corrected Corollary 7.4 expansion, with
the ordinary unitary target borrowed and restored as dirty workspace.  The
middle auxiliary-controlled `U` uses the selected six-node Corollary 5.3 circuit.

Only the final ordered control is declared clean.  The correctness theorem
assumes that wire is supported on zero and makes no initialization assumption on
the target, data controls, or ambient spectators.  Resource counts come from the
named primitive syntax, independently of the clean-subspace semantics.
-/

namespace Barenco.MultiControl

open Barenco.ControlledCircuit
open scoped Matrix

noncomputable section

namespace OrderedControlLayout

/-! ## Three-block primitive expansion -/

/--
The exact primitive chronology

`expanded MCX(data,aux); selected C(aux,U,target); expanded MCX(data,aux)`.
-/
def expandedCleanAncillaCircuit {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) (U : QubitUnitary) : Circuit ambientWidth :=
  Circuit.append
    (layout.expandedRecursivePrefixXCircuit hwidth)
    (Circuit.append
      (selectedControlledU2Circuit layout.cleanAncillaWire layout.targetWire
        layout.lastControlWire_ne_targetWire U)
      (layout.expandedRecursivePrefixXCircuit hwidth))

/-- Every primitive block has exactly the evaluator of its Lemma 7.11 macro. -/
@[simp]
theorem eval_expandedCleanAncillaCircuit_eq_cleanAncilla
    {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) (U : QubitUnitary) :
    Circuit.eval (layout.expandedCleanAncillaCircuit hwidth U) =
      Circuit.eval (layout.cleanAncillaCircuit U) := by
  simp [expandedCleanAncillaCircuit, cleanAncillaCircuit,
    Circuit.eval_append, lastControlledTarget]

/-! ## Transported exact semantics -/

/-- The expanded syntax retains the exact arbitrary-auxiliary basis formula. -/
theorem eval_expandedCleanAncillaCircuit_mulVec_basisKet
    {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) (U : QubitUnitary)
    (input : Basis ambientWidth) :
    (Circuit.eval (layout.expandedCleanAncillaCircuit hwidth U) :
        Gate ambientWidth) *ᵥ basisKet input =
      localRaw layout.targetWire (layout.cleanAncillaTargetProduct U input) *ᵥ
        basisKet input := by
  rw [eval_expandedCleanAncillaCircuit_eq_cleanAncilla,
    layout.eval_cleanAncillaCircuit_mulVec_basisKet]

/-- On a clean-zero basis input, the expansion is the desired data-controlled `U`. -/
theorem eval_expandedCleanAncillaCircuit_mulVec_basisKet_of_aux_false
    {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) (U : QubitUnitary)
    (input : Basis ambientWidth)
    (haux : input layout.cleanAncillaWire = false) :
    (Circuit.eval (layout.expandedCleanAncillaCircuit hwidth U) :
        Gate ambientWidth) *ᵥ basisKet input =
      (layout.prefixControlledTarget U).denotation *ᵥ basisKet input := by
  rw [eval_expandedCleanAncillaCircuit_eq_cleanAncilla]
  exact layout.eval_cleanAncillaCircuit_mulVec_basisKet_of_aux_false
    U input haux

/--
Exact Lemma 7.11 semantics on every clean-zero state, including arbitrary data,
target, and spectator superpositions.
-/
theorem eval_expandedCleanAncillaCircuit_mulVec_of_mem_cleanZero
    {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) (U : QubitUnitary)
    (state : State ambientWidth)
    (hstate : state ∈ cleanZeroSubspace layout.cleanAncillaWire) :
    (Circuit.eval (layout.expandedCleanAncillaCircuit hwidth U) :
        Gate ambientWidth) *ᵥ state =
      (layout.prefixControlledTarget U).denotation *ᵥ state := by
  rw [eval_expandedCleanAncillaCircuit_eq_cleanAncilla]
  exact layout.eval_cleanAncillaCircuit_mulVec_of_mem_cleanZero U state hstate

/-- The primitive expansion returns the auxiliary exactly to clean zero. -/
theorem eval_expandedCleanAncillaCircuit_mulVec_mem_cleanZero
    {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) (U : QubitUnitary)
    (state : State ambientWidth)
    (hstate : state ∈ cleanZeroSubspace layout.cleanAncillaWire) :
    (Circuit.eval (layout.expandedCleanAncillaCircuit hwidth U) :
        Gate ambientWidth) *ᵥ state ∈
      cleanZeroSubspace layout.cleanAncillaWire := by
  rw [eval_expandedCleanAncillaCircuit_eq_cleanAncilla]
  exact layout.eval_cleanAncillaCircuit_mulVec_mem_cleanZero U state hstate

/--
Explicit restored-output factorization: the expanded circuit returns `|0⟩` on
the auxiliary with no residual entanglement with the complementary register.
-/
theorem eval_expandedCleanAncillaCircuit_factorization
    {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) (U : QubitUnitary)
    (state : State ambientWidth)
    (hstate : state ∈ cleanZeroSubspace layout.cleanAncillaWire) :
    ∃ rest : ComplementBasis layout.cleanAncillaWire → ℂ,
      (Circuit.eval (layout.expandedCleanAncillaCircuit hwidth U) :
          Gate ambientWidth) *ᵥ state =
        fixedWireEmbed layout.cleanAncillaWire false rest := by
  rw [eval_expandedCleanAncillaCircuit_eq_cleanAncilla]
  exact layout.eval_cleanAncillaCircuit_factorization U state hstate

/-! ## Explicit clean-wire resource contract -/

/--
The syntactically declared clean-input requirement.  No other wire is required
to have a fixed initial value.
-/
def expandedCleanAncillaRequiredCleanWires {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth) :
    Finset (Fin ambientWidth) :=
  {layout.cleanAncillaWire}

@[simp]
theorem expandedCleanAncillaRequiredCleanWires_card {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth) :
    layout.expandedCleanAncillaRequiredCleanWires.card = 1 := by
  simp [expandedCleanAncillaRequiredCleanWires]

/--
Structural one-clean-ancilla contract: there are `p` data controls, exactly one
declared clean wire, and that wire is distinct from both the target and every
data control.  The width premise is the primitive expansion threshold.
-/
theorem expandedCleanAncillaCircuit_oneCleanAncillaContract
    {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) :
    5 ≤ p ∧
      layout.cleanDataLayout.controlSet.card = p ∧
      layout.expandedCleanAncillaRequiredCleanWires.card = 1 ∧
      layout.cleanAncillaWire ≠ layout.targetWire ∧
      ∀ control : Fin p,
        layout.controlWire control.castSucc ≠ layout.cleanAncillaWire := by
  refine ⟨by omega, ?_, by simp, layout.lastControlWire_ne_targetWire, ?_⟩
  · exact layout.cleanDataLayout.card_controlSet
  intro control
  exact layout.controlWire_ne (Fin.castSucc_ne_last control)

/-! ## Exact primitive resources -/

@[simp]
theorem expandedCleanAncillaCircuit_oneQubitCount {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) (U : QubitUnitary) :
    Circuit.kindCount .oneQubit
        (layout.expandedCleanAncillaCircuit hwidth U) = 64 * p - 156 := by
  simp [expandedCleanAncillaCircuit, Circuit.kindCount_append]
  omega

@[simp]
theorem expandedCleanAncillaCircuit_cnotCount {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) (U : QubitUnitary) :
    Circuit.kindCount .cnot
        (layout.expandedCleanAncillaCircuit hwidth U) = 48 * p - 102 := by
  simp [expandedCleanAncillaCircuit, Circuit.kindCount_append]
  omega

@[simp]
theorem expandedCleanAncillaCircuit_gateCount {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) (U : QubitUnitary) :
    Circuit.gateCount (layout.expandedCleanAncillaCircuit hwidth U) =
      112 * p - 258 := by
  simp [expandedCleanAncillaCircuit, Circuit.gateCount_append]
  omega

@[simp]
theorem expandedCleanAncillaCircuit_oneQubitCNOTCost {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) (U : QubitUnitary) :
    Circuit.cost CostModel.oneQubitCNOT
        (layout.expandedCleanAncillaCircuit hwidth U) =
      some (112 * p - 258) := by
  simp [expandedCleanAncillaCircuit, Circuit.cost_append, Circuit.addCost]
  have hmcx : 56 * p - 132 + 132 = 56 * p := by
    exact Nat.sub_add_cancel (by omega)
  have htotal : 112 * p - 258 + 258 = 112 * p := by
    exact Nat.sub_add_cancel (by omega)
  omega

/-! ## Logical-width forms -/

/-- One-qubit count for logical width `n = p + 2`. -/
theorem expandedCleanAncillaCircuit_oneQubitCount_logicalWidth
    {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) (U : QubitUnitary) :
    Circuit.kindCount .oneQubit
        (layout.expandedCleanAncillaCircuit hwidth U) =
      64 * (p + 2) - 284 := by
  rw [expandedCleanAncillaCircuit_oneQubitCount]
  omega

/-- CNOT count for logical width `n = p + 2`. -/
theorem expandedCleanAncillaCircuit_cnotCount_logicalWidth
    {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) (U : QubitUnitary) :
    Circuit.kindCount .cnot
        (layout.expandedCleanAncillaCircuit hwidth U) =
      48 * (p + 2) - 198 := by
  rw [expandedCleanAncillaCircuit_cnotCount]
  omega

/-- Total primitive count for logical width `n = p + 2`. -/
theorem expandedCleanAncillaCircuit_gateCount_logicalWidth
    {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) (U : QubitUnitary) :
    Circuit.gateCount (layout.expandedCleanAncillaCircuit hwidth U) =
      112 * (p + 2) - 482 := by
  rw [expandedCleanAncillaCircuit_gateCount]
  omega

/-- Accepted one-qubit/CNOT cost for logical width `n = p + 2`. -/
theorem expandedCleanAncillaCircuit_oneQubitCNOTCost_logicalWidth
    {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) (U : QubitUnitary) :
    Circuit.cost CostModel.oneQubitCNOT
        (layout.expandedCleanAncillaCircuit hwidth U) =
      some (112 * (p + 2) - 482) := by
  rw [expandedCleanAncillaCircuit_oneQubitCNOTCost]
  exact congrArg some (by omega)

/-! ## Smallest expanded logical width -/

/-- The logical-width-seven construction has profile `(164, 138, 302)`. -/
theorem expandedCleanAncillaCircuit_seven_resources {ambientWidth : ℕ}
    (layout : OrderedControlLayout 6 ambientWidth) (U : QubitUnitary) :
    layout.expandedCleanAncillaRequiredCleanWires.card = 1 ∧
      Circuit.kindCount .oneQubit
          (layout.expandedCleanAncillaCircuit (p := 5) (by omega) U) = 164 ∧
      Circuit.kindCount .cnot
          (layout.expandedCleanAncillaCircuit (p := 5) (by omega) U) = 138 ∧
      Circuit.gateCount
          (layout.expandedCleanAncillaCircuit (p := 5) (by omega) U) = 302 ∧
      Circuit.cost CostModel.oneQubitCNOT
          (layout.expandedCleanAncillaCircuit (p := 5) (by omega) U) =
        some 302 := by
  norm_num

end OrderedControlLayout

end

end Barenco.MultiControl
