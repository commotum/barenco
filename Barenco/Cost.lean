import Barenco.Circuit

/-!
# Structural circuit resources and named cost models

Every definition in this module inspects circuit syntax. No resource result is
inferred from a semantic matrix. Cost evaluation is partial so unsupported or
unclassified primitives cannot silently count as free.
-/

namespace Barenco

/-- A named partial weight for structural primitive kinds. -/
structure CostModel where
  name : String
  primitiveCost : PrimitiveKind → Option ℕ

namespace Circuit

/-- Total number of syntactic primitive occurrences. -/
def gateCount {n : ℕ} (circuit : Circuit n) : ℕ := circuit.length

@[simp]
theorem gateCount_nil (n : ℕ) : gateCount (Circuit.identity n) = 0 := rfl

@[simp]
theorem gateCount_cons {n : ℕ} (primitive : Primitive n) (circuit : Circuit n) :
    gateCount (primitive :: circuit) = gateCount circuit + 1 := by
  simp [gateCount]

@[simp]
theorem gateCount_append {n : ℕ} (first second : Circuit n) :
    gateCount (Circuit.append first second) = gateCount first + gateCount second := by
  simp [gateCount, Circuit.append]

@[simp]
theorem gateCount_adjoint {n : ℕ} (circuit : Circuit n) :
    gateCount (Circuit.adjoint circuit) = gateCount circuit := by
  simp [gateCount, Circuit.adjoint]

/-- Number of occurrences carrying exactly one structural kind. -/
def kindCount {n : ℕ} (kind : PrimitiveKind) (circuit : Circuit n) : ℕ :=
  circuit.countP fun primitive => decide (primitive.kind = kind)

@[simp]
theorem kindCount_nil {n : ℕ} (kind : PrimitiveKind) :
    kindCount kind (Circuit.identity n) = 0 := rfl

@[simp]
theorem kindCount_append {n : ℕ} (kind : PrimitiveKind) (first second : Circuit n) :
    kindCount kind (Circuit.append first second) =
      kindCount kind first + kindCount kind second := by
  simp [kindCount, Circuit.append]

@[simp]
theorem kindCount_adjoint {n : ℕ} (kind : PrimitiveKind) (circuit : Circuit n) :
    kindCount kind (Circuit.adjoint circuit) = kindCount kind circuit := by
  simp [kindCount, Circuit.adjoint, Function.comp_def]
  congr 1

/-- Union of all wire supports named by a circuit's primitive syntax. -/
def touchedSupport {n : ℕ} : Circuit n → Finset (Fin n)
  | [] => ∅
  | primitive :: circuit => primitive.support ∪ touchedSupport circuit

@[simp]
theorem touchedSupport_nil (n : ℕ) :
    touchedSupport (Circuit.identity n) = ∅ := rfl

@[simp]
theorem touchedSupport_cons {n : ℕ} (primitive : Primitive n) (circuit : Circuit n) :
    touchedSupport (primitive :: circuit) =
      primitive.support ∪ touchedSupport circuit := rfl

@[simp]
theorem touchedSupport_append {n : ℕ} (first second : Circuit n) :
    touchedSupport (Circuit.append first second) =
      touchedSupport first ∪ touchedSupport second := by
  induction first with
  | nil => simp [Circuit.append, touchedSupport]
  | cons primitive first ih =>
      have ih' : touchedSupport (first ++ second) =
          touchedSupport first ∪ touchedSupport second := by
        simpa [Circuit.append] using ih
      change primitive.support ∪ touchedSupport (first ++ second) =
        (primitive.support ∪ touchedSupport first) ∪ touchedSupport second
      rw [ih', Finset.union_assoc]

theorem mem_touchedSupport_iff {n : ℕ} (wire : Fin n) (circuit : Circuit n) :
    wire ∈ touchedSupport circuit ↔
      ∃ primitive ∈ circuit, wire ∈ primitive.support := by
  induction circuit with
  | nil => simp [touchedSupport]
  | cons primitive circuit ih =>
      simp [ih]

@[simp]
theorem touchedSupport_adjoint {n : ℕ} (circuit : Circuit n) :
    touchedSupport (Circuit.adjoint circuit) = touchedSupport circuit := by
  ext wire
  simp only [mem_touchedSupport_iff, Circuit.adjoint, List.mem_map, List.mem_reverse]
  constructor
  · rintro ⟨adjointPrimitive, ⟨primitive, hprimitive, rfl⟩, hwire⟩
    exact ⟨primitive, hprimitive, by simpa using hwire⟩
  · rintro ⟨primitive, hprimitive, hwire⟩
    exact ⟨primitive.adjoint, ⟨primitive, hprimitive, rfl⟩, by simpa using hwire⟩

/-- Combine two partial costs, rejecting either unsupported side. -/
def addCost : Option ℕ → Option ℕ → Option ℕ
  | some first, some second => some (first + second)
  | _, _ => none

theorem addCost_assoc (first second third : Option ℕ) :
    addCost first (addCost second third) =
      addCost (addCost first second) third := by
  cases first <;> cases second <;> cases third <;>
    simp [addCost, Nat.add_assoc]

/-- Partial syntax-derived cost of a chronological circuit. -/
def cost {n : ℕ} (model : CostModel) : Circuit n → Option ℕ
  | [] => some 0
  | primitive :: circuit =>
      addCost (model.primitiveCost primitive.kind) (cost model circuit)

@[simp]
theorem cost_nil (model : CostModel) (n : ℕ) :
    cost model (Circuit.identity n) = some 0 := rfl

@[simp]
theorem cost_cons {n : ℕ} (model : CostModel) (primitive : Primitive n)
    (circuit : Circuit n) :
    cost model (primitive :: circuit) =
      addCost (model.primitiveCost primitive.kind) (cost model circuit) := rfl

/-- Any unsupported primitive makes the cost of the entire containing circuit undefined. -/
theorem cost_eq_none_of_mem {n : ℕ} (model : CostModel) {primitive : Primitive n}
    {circuit : Circuit n} (hmem : primitive ∈ circuit)
    (hunsupported : model.primitiveCost primitive.kind = none) :
    cost model circuit = none := by
  induction circuit with
  | nil => simp at hmem
  | cons head circuit ih =>
      rw [cost_cons]
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst head
        rw [hunsupported]
        exact addCost_none_left _
      · rw [ih htail]
        exact addCost_none_right _

@[simp]
theorem addCost_none_left (value : Option ℕ) : addCost none value = none := by
  cases value <;> rfl

@[simp]
theorem addCost_none_right (value : Option ℕ) : addCost value none = none := by
  cases value <;> rfl

@[simp]
theorem addCost_some (first second : ℕ) :
    addCost (some first) (some second) = some (first + second) := rfl

theorem cost_append {n : ℕ} (model : CostModel) (first second : Circuit n) :
    cost model (Circuit.append first second) =
      addCost (cost model first) (cost model second) := by
  induction first with
  | nil =>
      cases h : cost model second <;> simp [Circuit.append, cost, addCost, h]
  | cons primitive first ih =>
      have ih' : cost model (first ++ second) =
          addCost (cost model first) (cost model second) := by
        simpa [Circuit.append] using ih
      change addCost (model.primitiveCost primitive.kind)
          (cost model (first ++ second)) =
        addCost (addCost (model.primitiveCost primitive.kind) (cost model first))
          (cost model second)
      rw [ih']
      exact addCost_assoc _ _ _

theorem cost_append_of_eq {n : ℕ} (model : CostModel) (first second : Circuit n)
    {firstCost secondCost : ℕ} (hfirst : cost model first = some firstCost)
    (hsecond : cost model second = some secondCost) :
    cost model (Circuit.append first second) = some (firstCost + secondCost) := by
  rw [cost_append, hfirst, hsecond]
  rfl

theorem cost_reverse {n : ℕ} (model : CostModel) (circuit : Circuit n) :
    cost model circuit.reverse = cost model circuit := by
  induction circuit with
  | nil => rfl
  | cons primitive circuit ih =>
      rw [List.reverse_cons]
      change cost model (Circuit.append circuit.reverse [primitive]) =
        cost model (primitive :: circuit)
      rw [cost_append, ih]
      cases hp : model.primitiveCost primitive.kind <;>
        cases hc : cost model circuit <;>
          simp [cost, addCost, hp, hc, Nat.add_comm]

theorem cost_map_adjoint {n : ℕ} (model : CostModel) (circuit : Circuit n) :
    cost model (circuit.map Primitive.adjoint) = cost model circuit := by
  induction circuit with
  | nil => rfl
  | cons primitive circuit ih =>
      simp [cost, ih]

@[simp]
theorem cost_adjoint {n : ℕ} (model : CostModel) (circuit : Circuit n) :
    cost model (Circuit.adjoint circuit) = cost model circuit := by
  rw [Circuit.adjoint, cost_map_adjoint, cost_reverse]

end Circuit

namespace CostModel

/-- Sections 3–7: arbitrary one-qubit gates and CNOT are the only basic operations. -/
def oneQubitCNOT : CostModel where
  name := "one-qubit + CNOT (Sections 3–7)"
  primitiveCost
    | .oneQubit => some 1
    | .cnot => some 1
    | _ => none

/-- Section 8: any certified one- or two-qubit primitive counts as one operation. -/
def arbitraryTwoQubit : CostModel where
  name := "arbitrary at-most-two-qubit (Section 8)"
  primitiveCost
    | .oneQubit => some 1
    | .cnot => some 1
    | .arbitraryTwoQubit => some 1
    | _ => none

@[simp] theorem oneQubitCNOT_oneQubit :
    oneQubitCNOT.primitiveCost .oneQubit = some 1 := rfl

@[simp] theorem oneQubitCNOT_cnot :
    oneQubitCNOT.primitiveCost .cnot = some 1 := rfl

@[simp] theorem oneQubitCNOT_controlled (controls : ℕ) :
    oneQubitCNOT.primitiveCost (.controlledOneQubit controls) = none := rfl

@[simp] theorem oneQubitCNOT_toffoli :
    oneQubitCNOT.primitiveCost .toffoli = none := rfl

@[simp] theorem oneQubitCNOT_arbitraryTwoQubit :
    oneQubitCNOT.primitiveCost .arbitraryTwoQubit = none := rfl

@[simp] theorem oneQubitCNOT_other (tag : String) :
    oneQubitCNOT.primitiveCost (.other tag) = none := rfl

@[simp] theorem arbitraryTwoQubit_oneQubit :
    arbitraryTwoQubit.primitiveCost .oneQubit = some 1 := rfl

@[simp] theorem arbitraryTwoQubit_cnot :
    arbitraryTwoQubit.primitiveCost .cnot = some 1 := rfl

@[simp] theorem arbitraryTwoQubit_gate :
    arbitraryTwoQubit.primitiveCost .arbitraryTwoQubit = some 1 := rfl

@[simp] theorem arbitraryTwoQubit_controlled (controls : ℕ) :
    arbitraryTwoQubit.primitiveCost (.controlledOneQubit controls) = none := rfl

@[simp] theorem arbitraryTwoQubit_toffoli :
    arbitraryTwoQubit.primitiveCost .toffoli = none := rfl

@[simp] theorem arbitraryTwoQubit_other (tag : String) :
    arbitraryTwoQubit.primitiveCost (.other tag) = none := rfl

end CostModel

namespace Primitive

@[simp]
theorem oneQubitCNOT_cost_oneQubit {n : ℕ} (target : Fin n) (U : QubitUnitary) :
    Circuit.cost CostModel.oneQubitCNOT [Primitive.oneQubit target U] = some 1 := by
  simp [Circuit.cost, Circuit.addCost]

@[simp]
theorem oneQubitCNOT_cost_cnot {n : ℕ} (control target : Fin n)
    (h : control ≠ target) :
    Circuit.cost CostModel.oneQubitCNOT [Primitive.cnot control target h] = some 1 := by
  simp [Circuit.cost, Circuit.addCost]

@[simp]
theorem oneQubitCNOT_rejects_positiveControlled {n : ℕ} (target : Fin n)
    (controls : ControlSet target) (U : QubitUnitary) :
    Circuit.cost CostModel.oneQubitCNOT [Primitive.positiveControlled target controls U] =
      none := by
  simp [Circuit.cost, Circuit.addCost]

@[simp]
theorem namedModels_reject_unclassified {n : ℕ} (tag : String) (U : UnitaryGate n) :
    Circuit.cost CostModel.oneQubitCNOT [Primitive.unclassified tag U] = none ∧
      Circuit.cost CostModel.arbitraryTwoQubit [Primitive.unclassified tag U] = none := by
  simp [Circuit.cost, Circuit.addCost]

/-- Both paper cost models reject any circuit containing an unclassified primitive. -/
theorem namedModels_reject_unclassified_of_mem {n : ℕ} (tag : String) (U : UnitaryGate n)
    (circuit : Circuit n) (hmem : Primitive.unclassified tag U ∈ circuit) :
    Circuit.cost CostModel.oneQubitCNOT circuit = none ∧
      Circuit.cost CostModel.arbitraryTwoQubit circuit = none := by
  constructor
  · exact Circuit.cost_eq_none_of_mem CostModel.oneQubitCNOT hmem (by simp)
  · exact Circuit.cost_eq_none_of_mem CostModel.arbitraryTwoQubit hmem (by simp)

end Primitive

end Barenco
