import Barenco.Optimization.FusionIR
import Barenco.Cost

/-!
# Structural resources for payload-preserving fusion syntax

This module counts literal optimizer syntax and proves that every count agrees
exactly with the established `Circuit` resource after trusted lowering.  Total
structural counts are deliberately separate from partial model acceptance:
generic two-qubit nodes still have a gate count and a kind count when the
one-qubit/CNOT model rejects the containing circuit.

Mixed barriers receive no optimistic resource tag.  Their kind, support, and
partial price are inherited from the exact stored `Primitive`, and an
unsupported barrier makes the whole program cost `none` just as it does after
lowering.
-/

namespace Barenco.Optimization

open Barenco

namespace FusionPrimitive

/-- Partial price of one visible node under an arbitrary structural cost model. -/
def cost {n : ℕ} (model : CostModel) (primitive : FusionPrimitive n) : Option ℕ :=
  model.primitiveCost primitive.kind

/-- Node pricing agrees with the kind of the exact trusted lowering. -/
@[simp]
theorem cost_eq_lower {n : ℕ} (model : CostModel)
    (primitive : FusionPrimitive n) :
    primitive.cost model = model.primitiveCost primitive.lower.kind := by
  simp [cost]

/-- A visible one-qubit node is basic in the Sections 3--7 model. -/
@[simp]
theorem oneQubitCNOT_cost_oneQubit {n : ℕ} (target : Fin n)
    (U : QubitUnitary) :
    cost CostModel.oneQubitCNOT (.oneQubit target U) = some 1 := rfl

/-- A visible CNOT node is basic in the Sections 3--7 model. -/
@[simp]
theorem oneQubitCNOT_cost_cnot {n : ℕ} (control target : Fin n)
    (hcontrolTarget : control ≠ target) :
    cost CostModel.oneQubitCNOT
      (.cnot control target hcontrolTarget) = some 1 := rfl

/-- A generic visible `U(4)` node is unsupported in the Sections 3--7 model. -/
@[simp]
theorem oneQubitCNOT_cost_twoQubit {n : ℕ} (pair : OrderedWirePair n)
    (U : TwoQubitUnitary) :
    cost CostModel.oneQubitCNOT (.twoQubit pair U) = none := rfl

/-- Every node in the closed visible grammar costs one Section 8 operation. -/
@[simp]
theorem arbitraryTwoQubit_cost (primitive : FusionPrimitive n) :
    primitive.cost CostModel.arbitraryTwoQubit = some 1 := by
  cases primitive <;> rfl

end FusionPrimitive

namespace FusionCircuit

/-! ## Total visible-syntax resources -/

/-- Total number of literal visible nodes. -/
def gateCount {n : ℕ} (circuit : FusionCircuit n) : ℕ := circuit.length

/-- Number of visible nodes carrying exactly one structural kind. -/
def kindCount {n : ℕ} (kind : PrimitiveKind) (circuit : FusionCircuit n) : ℕ :=
  circuit.countP fun primitive => decide (primitive.kind = kind)

/-- Number of explicit one-qubit payload nodes. -/
def oneQubitCount {n : ℕ} (circuit : FusionCircuit n) : ℕ :=
  kindCount .oneQubit circuit

/-- Number of literal CNOT nodes. -/
def cnotCount {n : ℕ} (circuit : FusionCircuit n) : ℕ :=
  kindCount .cnot circuit

/-- Number of explicit generic two-qubit payload nodes. -/
def twoQubitCount {n : ℕ} (circuit : FusionCircuit n) : ℕ :=
  kindCount .arbitraryTwoQubit circuit

/-- Partial syntax-derived cost under an arbitrary structural model. -/
def cost {n : ℕ} (model : CostModel) : FusionCircuit n → Option ℕ
  | [] => some 0
  | primitive :: circuit =>
      Circuit.addCost (primitive.cost model) (cost model circuit)

@[simp]
theorem gateCount_nil (n : ℕ) : gateCount ([] : FusionCircuit n) = 0 := rfl

@[simp]
theorem gateCount_cons {n : ℕ} (primitive : FusionPrimitive n)
    (circuit : FusionCircuit n) :
    gateCount (primitive :: circuit) = gateCount circuit + 1 := by
  simp [gateCount]

@[simp]
theorem kindCount_nil {n : ℕ} (kind : PrimitiveKind) :
    kindCount kind ([] : FusionCircuit n) = 0 := rfl

@[simp]
theorem kindCount_cons {n : ℕ} (kind : PrimitiveKind)
    (primitive : FusionPrimitive n) (circuit : FusionCircuit n) :
    kindCount kind (primitive :: circuit) =
      kindCount kind circuit + if primitive.kind = kind then 1 else 0 := by
  simp only [kindCount, List.countP_cons]
  by_cases hkind : primitive.kind = kind <;> simp [hkind]

@[simp]
theorem twoQubitCount_cons_oneQubit {n : ℕ} (target : Fin n)
    (U : QubitUnitary) (circuit : FusionCircuit n) :
    twoQubitCount (FusionPrimitive.oneQubit target U :: circuit) =
      twoQubitCount circuit := by
  simp [twoQubitCount, FusionPrimitive.kind]

@[simp]
theorem twoQubitCount_cons_cnot {n : ℕ} (control target : Fin n)
    (hcontrolTarget : control ≠ target) (circuit : FusionCircuit n) :
    twoQubitCount
        (FusionPrimitive.cnot control target hcontrolTarget :: circuit) =
      twoQubitCount circuit := by
  simp [twoQubitCount, FusionPrimitive.kind]

@[simp]
theorem twoQubitCount_cons_twoQubit {n : ℕ} (pair : OrderedWirePair n)
    (U : TwoQubitUnitary) (circuit : FusionCircuit n) :
    twoQubitCount (FusionPrimitive.twoQubit pair U :: circuit) =
      twoQubitCount circuit + 1 := by
  simp [twoQubitCount, FusionPrimitive.kind]

@[simp]
theorem cost_nil (model : CostModel) (n : ℕ) :
    cost model ([] : FusionCircuit n) = some 0 := rfl

@[simp]
theorem cost_cons {n : ℕ} (model : CostModel)
    (primitive : FusionPrimitive n) (circuit : FusionCircuit n) :
    cost model (primitive :: circuit) =
      Circuit.addCost (primitive.cost model) (cost model circuit) := rfl

/-! ## Exact lowering bridges -/

/-- Literal visible length is exactly the lowered circuit gate count. -/
@[simp]
theorem gateCount_lower {n : ℕ} (circuit : FusionCircuit n) :
    Circuit.gateCount circuit.lower = gateCount circuit := by
  simp [Circuit.gateCount, FusionCircuit.lower, gateCount]

/-- Every visible structural kind count is preserved exactly by lowering. -/
@[simp]
theorem kindCount_lower {n : ℕ} (kind : PrimitiveKind)
    (circuit : FusionCircuit n) :
    Circuit.kindCount kind circuit.lower = kindCount kind circuit := by
  induction circuit with
  | nil => rfl
  | cons primitive circuit ih =>
      simp only [FusionCircuit.lower_cons, Circuit.kindCount, kindCount,
        List.countP_cons, FusionPrimitive.lower_kind] at ih ⊢
      rw [ih]

@[simp]
theorem oneQubitCount_lower {n : ℕ} (circuit : FusionCircuit n) :
    Circuit.kindCount .oneQubit circuit.lower = oneQubitCount circuit := by
  exact kindCount_lower .oneQubit circuit

@[simp]
theorem cnotCount_lower {n : ℕ} (circuit : FusionCircuit n) :
    Circuit.kindCount .cnot circuit.lower = cnotCount circuit := by
  exact kindCount_lower .cnot circuit

@[simp]
theorem twoQubitCount_lower {n : ℕ} (circuit : FusionCircuit n) :
    Circuit.kindCount .arbitraryTwoQubit circuit.lower =
      twoQubitCount circuit := by
  exact kindCount_lower .arbitraryTwoQubit circuit

/-- Visible structural support is exactly lowered touched support. -/
@[simp]
theorem support_lower {n : ℕ} (circuit : FusionCircuit n) :
    Circuit.touchedSupport circuit.lower = circuit.support := by
  induction circuit with
  | nil => rfl
  | cons primitive circuit ih =>
      simp only [FusionCircuit.lower_cons, Circuit.touchedSupport_cons,
        FusionCircuit.support_cons, FusionPrimitive.lower_support]
      rw [ih]

/-- Partial model acceptance and price are preserved exactly by lowering. -/
@[simp]
theorem cost_lower {n : ℕ} (model : CostModel)
    (circuit : FusionCircuit n) :
    Circuit.cost model circuit.lower = cost model circuit := by
  induction circuit with
  | nil => rfl
  | cons primitive circuit ih =>
      simp only [FusionCircuit.lower_cons, Circuit.cost_cons, cost_cons,
        FusionPrimitive.cost_eq_lower]
      rw [ih]

/-! ## Composition and adjoint resources -/

@[simp]
theorem gateCount_append {n : ℕ} (first second : FusionCircuit n) :
    gateCount (append first second) = gateCount first + gateCount second := by
  rw [← gateCount_lower, FusionCircuit.lower_append, Circuit.gateCount_append,
    gateCount_lower, gateCount_lower]

@[simp]
theorem kindCount_append {n : ℕ} (kind : PrimitiveKind)
    (first second : FusionCircuit n) :
    kindCount kind (append first second) =
      kindCount kind first + kindCount kind second := by
  rw [← kindCount_lower, FusionCircuit.lower_append, Circuit.kindCount_append,
    kindCount_lower, kindCount_lower]

@[simp]
theorem cost_append {n : ℕ} (model : CostModel)
    (first second : FusionCircuit n) :
    cost model (append first second) =
      Circuit.addCost (cost model first) (cost model second) := by
  rw [← cost_lower, FusionCircuit.lower_append, Circuit.cost_append,
    cost_lower, cost_lower]

@[simp]
theorem gateCount_adjoint {n : ℕ} (circuit : FusionCircuit n) :
    gateCount circuit.adjoint = gateCount circuit := by
  rw [← gateCount_lower, FusionCircuit.lower_adjoint,
    Circuit.gateCount_adjoint, gateCount_lower]

@[simp]
theorem kindCount_adjoint {n : ℕ} (kind : PrimitiveKind)
    (circuit : FusionCircuit n) :
    kindCount kind circuit.adjoint = kindCount kind circuit := by
  rw [← kindCount_lower, FusionCircuit.lower_adjoint,
    Circuit.kindCount_adjoint, kindCount_lower]

@[simp]
theorem cost_adjoint {n : ℕ} (model : CostModel)
    (circuit : FusionCircuit n) :
    cost model circuit.adjoint = cost model circuit := by
  rw [← cost_lower, FusionCircuit.lower_adjoint,
    Circuit.cost_adjoint, cost_lower]

/-! ## Closed-grammar profiles and model boundaries -/

/-- The visible grammar partitions every literal node into exactly three kinds. -/
theorem gateCount_eq_componentCounts {n : ℕ} (circuit : FusionCircuit n) :
    gateCount circuit =
      oneQubitCount circuit + cnotCount circuit + twoQubitCount circuit := by
  induction circuit with
  | nil => rfl
  | cons primitive circuit ih =>
      cases primitive <;>
        simp [gateCount, oneQubitCount, cnotCount, twoQubitCount, kindCount,
          FusionPrimitive.kind] at ih ⊢ <;>
        omega

/-- Section 8 accepts every visible node and charges literal gate count. -/
@[simp]
theorem arbitraryTwoQubit_cost_eq_gateCount {n : ℕ}
    (circuit : FusionCircuit n) :
    cost CostModel.arbitraryTwoQubit circuit = some (gateCount circuit) := by
  induction circuit with
  | nil => rfl
  | cons primitive circuit ih =>
      rw [cost_cons, FusionPrimitive.arbitraryTwoQubit_cost, ih]
      simp [Circuit.addCost, gateCount, Nat.add_comm]

/--
The Sections 3--7 model accepts visible syntax exactly when it contains no
generic two-qubit node; when accepted, every remaining literal node costs one.
-/
theorem oneQubitCNOT_cost_eq {n : ℕ} (circuit : FusionCircuit n) :
    cost CostModel.oneQubitCNOT circuit =
      if twoQubitCount circuit = 0 then some (gateCount circuit) else none := by
  induction circuit with
  | nil => rfl
  | cons primitive circuit ih =>
      cases primitive with
      | oneQubit target U =>
          rw [cost_cons, ih]
          by_cases htail : twoQubitCount circuit = 0
          · simp [htail, Circuit.addCost, FusionPrimitive.cost,
              FusionPrimitive.kind, Nat.add_comm]
          · simp [htail, Circuit.addCost, FusionPrimitive.cost,
              FusionPrimitive.kind]
      | cnot control target hcontrolTarget =>
          rw [cost_cons, ih]
          by_cases htail : twoQubitCount circuit = 0
          · simp [htail, Circuit.addCost, FusionPrimitive.cost,
              FusionPrimitive.kind, Nat.add_comm]
          · simp [htail, Circuit.addCost, FusionPrimitive.cost,
              FusionPrimitive.kind]
      | twoQubit pair U =>
          simp [cost, Circuit.addCost, FusionPrimitive.cost,
            FusionPrimitive.kind]

theorem oneQubitCNOT_cost_eq_some_iff {n total : ℕ}
    (circuit : FusionCircuit n) :
    cost CostModel.oneQubitCNOT circuit = some total ↔
      twoQubitCount circuit = 0 ∧ gateCount circuit = total := by
  rw [oneQubitCNOT_cost_eq]
  by_cases htwo : twoQubitCount circuit = 0
  · simp [htwo]
  · simp [htwo]

theorem oneQubitCNOT_cost_eq_none_iff {n : ℕ}
    (circuit : FusionCircuit n) :
    cost CostModel.oneQubitCNOT circuit = none ↔
      0 < twoQubitCount circuit := by
  rw [oneQubitCNOT_cost_eq]
  by_cases htwo : twoQubitCount circuit = 0
  · simp [htwo]
  · simp [htwo, Nat.pos_of_ne_zero htwo]

/-- Any unsupported visible node makes the full visible cost undefined. -/
theorem cost_eq_none_of_mem {n : ℕ} (model : CostModel)
    {primitive : FusionPrimitive n} {circuit : FusionCircuit n}
    (hmem : primitive ∈ circuit)
    (hunsupported : primitive.cost model = none) :
    cost model circuit = none := by
  induction circuit with
  | nil => simp at hmem
  | cons head circuit ih =>
      rw [cost_cons]
      rcases List.mem_cons.mp hmem with rfl | htail
      · rw [hunsupported]
        rfl
      · rw [ih htail]
        exact Circuit.addCost_none_right _

/-- A contained generic `U(4)` node makes the early-model cost undefined. -/
theorem oneQubitCNOT_cost_eq_none_of_twoQubit_mem {n : ℕ}
    {pair : OrderedWirePair n} {U : TwoQubitUnitary}
    {circuit : FusionCircuit n}
    (hmem : FusionPrimitive.twoQubit pair U ∈ circuit) :
    cost CostModel.oneQubitCNOT circuit = none := by
  exact cost_eq_none_of_mem CostModel.oneQubitCNOT hmem (by rfl)

end FusionCircuit

namespace FusionStep

/--
Partial price of one mixed step.  In particular, a barrier's price is derived
from the original stored primitive rather than an optimizer-supplied tag.
-/
def cost {n : ℕ} (model : CostModel) (step : FusionStep n) : Option ℕ :=
  model.primitiveCost step.kind

@[simp]
theorem cost_eq_lower {n : ℕ} (model : CostModel) (step : FusionStep n) :
    step.cost model = model.primitiveCost step.lower.kind := rfl

@[simp]
theorem cost_gate {n : ℕ} (model : CostModel)
    (primitive : FusionPrimitive n) :
    cost model (.gate primitive) = primitive.cost model := by
  simp [cost, FusionPrimitive.cost, FusionStep.kind, FusionStep.lower]

@[simp]
theorem cost_barrier {n : ℕ} (model : CostModel)
    (primitive : Primitive n) :
    cost model (.barrier primitive : FusionStep n) =
      model.primitiveCost primitive.kind := rfl

end FusionStep

namespace FusionProgram

/-! ## Total mixed-program resources -/

/-- Total number of visible gates and exact barriers. -/
def gateCount {n : ℕ} (program : FusionProgram n) : ℕ := program.length

/-- Number of mixed steps whose exact lowered primitive has one structural kind. -/
def kindCount {n : ℕ} (kind : PrimitiveKind) (program : FusionProgram n) : ℕ :=
  program.countP fun step => decide (step.kind = kind)

/-- Partial syntax-derived cost of visible gates and exact barriers. -/
def cost {n : ℕ} (model : CostModel) : FusionProgram n → Option ℕ
  | [] => some 0
  | step :: program =>
      Circuit.addCost (step.cost model) (cost model program)

@[simp]
theorem gateCount_nil (n : ℕ) : gateCount ([] : FusionProgram n) = 0 := rfl

@[simp]
theorem gateCount_cons {n : ℕ} (step : FusionStep n)
    (program : FusionProgram n) :
    gateCount (step :: program) = gateCount program + 1 := by
  simp [gateCount]

@[simp]
theorem kindCount_nil {n : ℕ} (kind : PrimitiveKind) :
    kindCount kind ([] : FusionProgram n) = 0 := rfl

@[simp]
theorem kindCount_cons {n : ℕ} (kind : PrimitiveKind)
    (step : FusionStep n) (program : FusionProgram n) :
    kindCount kind (step :: program) =
      kindCount kind program + if step.kind = kind then 1 else 0 := by
  simp only [kindCount, List.countP_cons]
  by_cases hkind : step.kind = kind <;> simp [hkind]

@[simp]
theorem cost_nil (model : CostModel) (n : ℕ) :
    cost model ([] : FusionProgram n) = some 0 := rfl

@[simp]
theorem cost_cons {n : ℕ} (model : CostModel)
    (step : FusionStep n) (program : FusionProgram n) :
    cost model (step :: program) =
      Circuit.addCost (step.cost model) (cost model program) := rfl

/-! ## Exact mixed lowering bridges -/

@[simp]
theorem gateCount_lower {n : ℕ} (program : FusionProgram n) :
    Circuit.gateCount program.lower = gateCount program := by
  simp [Circuit.gateCount, FusionProgram.lower, gateCount]

@[simp]
theorem kindCount_lower {n : ℕ} (kind : PrimitiveKind)
    (program : FusionProgram n) :
    Circuit.kindCount kind program.lower = kindCount kind program := by
  induction program with
  | nil => rfl
  | cons step program ih =>
      simp only [FusionProgram.lower_cons, Circuit.kindCount, kindCount,
        List.countP_cons, FusionStep.lower_kind] at ih ⊢
      rw [ih]
      rfl

@[simp]
theorem support_lower {n : ℕ} (program : FusionProgram n) :
    Circuit.touchedSupport program.lower = program.support := by
  induction program with
  | nil => rfl
  | cons step program ih =>
      simp only [FusionProgram.lower_cons, Circuit.touchedSupport_cons,
        FusionProgram.support_cons, FusionStep.lower_support]
      rw [ih]

@[simp]
theorem cost_lower {n : ℕ} (model : CostModel)
    (program : FusionProgram n) :
    Circuit.cost model program.lower = cost model program := by
  induction program with
  | nil => rfl
  | cons step program ih =>
      simp only [FusionProgram.lower_cons, Circuit.cost_cons, cost_cons,
        FusionStep.cost_eq_lower]
      rw [ih]

/-! ## Composition, adjoint, and preservation lifts -/

@[simp]
theorem gateCount_append {n : ℕ} (first second : FusionProgram n) :
    gateCount (append first second) = gateCount first + gateCount second := by
  rw [← gateCount_lower, FusionProgram.lower_append, Circuit.gateCount_append,
    gateCount_lower, gateCount_lower]

@[simp]
theorem kindCount_append {n : ℕ} (kind : PrimitiveKind)
    (first second : FusionProgram n) :
    kindCount kind (append first second) =
      kindCount kind first + kindCount kind second := by
  rw [← kindCount_lower, FusionProgram.lower_append, Circuit.kindCount_append,
    kindCount_lower, kindCount_lower]

@[simp]
theorem cost_append {n : ℕ} (model : CostModel)
    (first second : FusionProgram n) :
    cost model (append first second) =
      Circuit.addCost (cost model first) (cost model second) := by
  rw [← cost_lower, FusionProgram.lower_append, Circuit.cost_append,
    cost_lower, cost_lower]

@[simp]
theorem gateCount_adjoint {n : ℕ} (program : FusionProgram n) :
    gateCount program.adjoint = gateCount program := by
  rw [← gateCount_lower, FusionProgram.lower_adjoint,
    Circuit.gateCount_adjoint, gateCount_lower]

@[simp]
theorem kindCount_adjoint {n : ℕ} (kind : PrimitiveKind)
    (program : FusionProgram n) :
    kindCount kind program.adjoint = kindCount kind program := by
  rw [← kindCount_lower, FusionProgram.lower_adjoint,
    Circuit.kindCount_adjoint, kindCount_lower]

@[simp]
theorem cost_adjoint {n : ℕ} (model : CostModel)
    (program : FusionProgram n) :
    cost model program.adjoint = cost model program := by
  rw [← cost_lower, FusionProgram.lower_adjoint,
    Circuit.cost_adjoint, cost_lower]

/-- Embedding visible syntax in the mixed layer preserves literal gate count. -/
@[simp]
theorem gateCount_visible {n : ℕ} (circuit : FusionCircuit n) :
    gateCount (visible circuit) = FusionCircuit.gateCount circuit := by
  rw [← gateCount_lower, FusionProgram.lower_visible,
    FusionCircuit.gateCount_lower]

/-- Embedding visible syntax preserves every structural kind count. -/
@[simp]
theorem kindCount_visible {n : ℕ} (kind : PrimitiveKind)
    (circuit : FusionCircuit n) :
    kindCount kind (visible circuit) = FusionCircuit.kindCount kind circuit := by
  rw [← kindCount_lower, FusionProgram.lower_visible,
    FusionCircuit.kindCount_lower]

/-- Embedding visible syntax preserves structural touched support. -/
@[simp]
theorem support_visible {n : ℕ} (circuit : FusionCircuit n) :
    support (visible circuit) = circuit.support := by
  rw [← support_lower, FusionProgram.lower_visible, FusionCircuit.support_lower]

/-- Embedding visible syntax preserves partial acceptance and exact price. -/
@[simp]
theorem cost_visible {n : ℕ} (model : CostModel)
    (circuit : FusionCircuit n) :
    cost model (visible circuit) = FusionCircuit.cost model circuit := by
  rw [← cost_lower, FusionProgram.lower_visible, FusionCircuit.cost_lower]

/-- The all-barrier preservation path retains literal gate count exactly. -/
@[simp]
theorem gateCount_barriers {n : ℕ} (circuit : Circuit n) :
    gateCount (barriers circuit) = Circuit.gateCount circuit := by
  rw [← gateCount_lower, FusionProgram.lower_barriers]

/-- The all-barrier preservation path retains every structural kind count. -/
@[simp]
theorem kindCount_barriers {n : ℕ} (kind : PrimitiveKind)
    (circuit : Circuit n) :
    kindCount kind (barriers circuit) = Circuit.kindCount kind circuit := by
  rw [← kindCount_lower, FusionProgram.lower_barriers]

/-- The all-barrier preservation path retains touched support exactly. -/
@[simp]
theorem support_barriers {n : ℕ} (circuit : Circuit n) :
    support (barriers circuit) = Circuit.touchedSupport circuit := by
  rw [← support_lower, FusionProgram.lower_barriers]

/-- The all-barrier preservation path retains partial model cost exactly. -/
@[simp]
theorem cost_barriers {n : ℕ} (model : CostModel) (circuit : Circuit n) :
    cost model (barriers circuit) = Circuit.cost model circuit := by
  rw [← cost_lower, FusionProgram.lower_barriers]

/-! ## Unsupported-barrier propagation -/

/-- Any unsupported mixed step makes the complete program cost undefined. -/
theorem cost_eq_none_of_mem {n : ℕ} (model : CostModel)
    {step : FusionStep n} {program : FusionProgram n}
    (hmem : step ∈ program) (hunsupported : step.cost model = none) :
    cost model program = none := by
  induction program with
  | nil => simp at hmem
  | cons head program ih =>
      rw [cost_cons]
      rcases List.mem_cons.mp hmem with rfl | htail
      · rw [hunsupported]
        rfl
      · rw [ih htail]
        exact Circuit.addCost_none_right _

/--
An unsupported stored primitive stays unsupported when it appears as an exact
barrier.  No local payload or alternate cost is inferred for it.
-/
theorem cost_eq_none_of_barrier_mem {n : ℕ} (model : CostModel)
    {primitive : Primitive n} {program : FusionProgram n}
    (hmem : FusionStep.barrier primitive ∈ program)
    (hunsupported : model.primitiveCost primitive.kind = none) :
    cost model program = none := by
  apply cost_eq_none_of_mem model hmem
  change model.primitiveCost primitive.kind = none
  exact hunsupported

end FusionProgram

end Barenco.Optimization
