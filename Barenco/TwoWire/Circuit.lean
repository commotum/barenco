import Barenco.Cost

/-!
# Trusted arbitrary two-wire circuit syntax

This module connects the certified ordered-pair embedding from
`Barenco.TwoWire.Semantics` to the chronological `Circuit` syntax and its two
named paper cost models.  The smart constructor itself lives in
`Barenco.Circuit`, alongside the private `Primitive.mk` trust boundary.  Every
resource theorem below is computed from a literal singleton list; none is
inferred from matrix equality.

The declared support `{pair.first, pair.second}` is structural.  In particular,
identity and scalar local payloads still occupy one arbitrary-two-qubit syntax
node in the Section 8 model.
-/

namespace Barenco

open scoped Matrix

namespace Primitive

/-! ## Exact structural and semantic bridges -/

/--
Reversing the ordered ambient pair and correspondingly swapping the two local
bits gives exactly the same primitive record, including its declared support.
-/
theorem twoQubit_swap {n : ℕ} (pair : OrderedWirePair n)
    (U : TwoQubitUnitary) :
    twoQubit pair.swap U =
      twoQubit pair (reindexUnitary reverseTwoQubitBasis U) := by
  simp [twoQubit, twoWireUnitary_swap, Finset.pair_comm]

/-- The generic primitive adjoint retains the explicit inverse local payload. -/
@[simp]
theorem adjoint_twoQubit {n : ℕ} (pair : OrderedWirePair n)
    (U : TwoQubitUnitary) :
    (twoQubit pair U).adjoint = twoQubit pair U⁻¹ := by
  simp [adjoint, twoQubit, twoWireUnitary_inv]

/-- Certified basis-column action of a trusted arbitrary two-wire primitive. -/
theorem twoQubit_denotation_mulVec_basisKet {n : ℕ}
    (pair : OrderedWirePair n) (U : TwoQubitUnitary) (input : Basis n) :
    ((twoQubit pair U).denotation : Gate n) *ᵥ basisKet input = fun row =>
      if AgreeOffTwoWire pair row input then
        U (twoWireLocalBits pair row) (twoWireLocalBits pair input)
      else 0 := by
  exact twoWireUnitary_mulVec_basisKet pair U input

/-- Exact selected-pair output amplitude of a trusted two-wire primitive. -/
@[simp]
theorem twoQubit_denotation_mulVec_basisKet_setTwoWire {n : ℕ}
    (pair : OrderedWirePair n) (U : TwoQubitUnitary)
    (input : Basis n) (output : Basis 2) :
    (((twoQubit pair U).denotation : Gate n) *ᵥ basisKet input)
        (setTwoWire pair input output) =
      U output (twoWireLocalBits pair input) := by
  exact twoWireUnitary_mulVec_basisKet_setTwoWire pair U input output

/-- A changed spectator has zero amplitude in a two-wire basis column. -/
theorem twoQubit_denotation_mulVec_basisKet_eq_zero_of_changed {n : ℕ}
    (pair : OrderedWirePair n) (U : TwoQubitUnitary)
    (input row : Basis n) (wire : Fin n)
    (hfirst : wire ≠ pair.first) (hsecond : wire ≠ pair.second)
    (hchanged : row wire ≠ input wire) :
    (((twoQubit pair U).denotation : Gate n) *ᵥ basisKet input) row = 0 := by
  exact twoWireUnitary_mulVec_basisKet_eq_zero_of_changed pair U input row wire
    hfirst hsecond hchanged

/-- Basis action as the explicit four-term local-output superposition. -/
theorem twoQubit_denotation_mulVec_basisKet_eq_sum {n : ℕ}
    (pair : OrderedWirePair n) (U : TwoQubitUnitary) (input : Basis n) :
    ((twoQubit pair U).denotation : Gate n) *ᵥ basisKet input =
      ∑ output : Basis 2,
        U output (twoWireLocalBits pair input) •
          basisKet (setTwoWire pair input output) := by
  exact twoWireUnitary_mulVec_basisKet_eq_sum pair U input

/-! ## Literal singleton resources -/

/-- One trusted local `U(4)` payload contributes one literal syntax node. -/
@[simp]
theorem twoQubit_singleton_gateCount {n : ℕ}
    (pair : OrderedWirePair n) (U : TwoQubitUnitary) :
    Circuit.gateCount [twoQubit pair U] = 1 := by
  rfl

/-- The literal node carries exactly the Section 8 arbitrary-two-qubit class. -/
@[simp]
theorem twoQubit_singleton_kindCount {n : ℕ}
    (pair : OrderedWirePair n) (U : TwoQubitUnitary) :
    Circuit.kindCount .arbitraryTwoQubit [twoQubit pair U] = 1 := by
  rfl

/-- No other structural class counts the trusted arbitrary-two-qubit node. -/
theorem twoQubit_singleton_kindCount_of_ne {n : ℕ}
    (pair : OrderedWirePair n) (U : TwoQubitUnitary)
    (kind : PrimitiveKind) (hne : kind ≠ .arbitraryTwoQubit) :
    Circuit.kindCount kind [twoQubit pair U] = 0 := by
  simp [Circuit.kindCount, Ne.symm hne]

/-- Singleton touched support is exactly the constructor's declared pair. -/
@[simp]
theorem twoQubit_singleton_touchedSupport {n : ℕ}
    (pair : OrderedWirePair n) (U : TwoQubitUnitary) :
    Circuit.touchedSupport [twoQubit pair U] =
      {pair.first, pair.second} := by
  simp [Circuit.touchedSupport]

/-- The Sections 3--7 one-qubit/CNOT model rejects a generic `U(4)` node. -/
@[simp]
theorem oneQubitCNOT_cost_twoQubit {n : ℕ}
    (pair : OrderedWirePair n) (U : TwoQubitUnitary) :
    Circuit.cost CostModel.oneQubitCNOT [twoQubit pair U] = none := by
  rfl

/-- Section 8 charges one operation for one literal arbitrary `U(4)` node. -/
@[simp]
theorem arbitraryTwoQubit_cost_twoQubit {n : ℕ}
    (pair : OrderedWirePair n) (U : TwoQubitUnitary) :
    Circuit.cost CostModel.arbitraryTwoQubit [twoQubit pair U] = some 1 := by
  rfl

/-! ## Adjoint resource specializations -/

/-- A singleton arbitrary-two-qubit circuit still has one node after adjointing. -/
@[simp]
theorem twoQubit_adjoint_singleton_gateCount {n : ℕ}
    (pair : OrderedWirePair n) (U : TwoQubitUnitary) :
    Circuit.gateCount (Circuit.adjoint [twoQubit pair U]) = 1 := by
  rw [Circuit.gateCount_adjoint]
  exact twoQubit_singleton_gateCount pair U

/-- Adjointing retains the arbitrary-two-qubit structural class. -/
@[simp]
theorem twoQubit_adjoint_singleton_kindCount {n : ℕ}
    (pair : OrderedWirePair n) (U : TwoQubitUnitary) :
    Circuit.kindCount .arbitraryTwoQubit
      (Circuit.adjoint [twoQubit pair U]) = 1 := by
  rw [Circuit.kindCount_adjoint]
  exact twoQubit_singleton_kindCount pair U

/-- Adjointing does not make a generic `U(4)` node early-basic syntax. -/
@[simp]
theorem oneQubitCNOT_cost_adjoint_twoQubit {n : ℕ}
    (pair : OrderedWirePair n) (U : TwoQubitUnitary) :
    Circuit.cost CostModel.oneQubitCNOT
      (Circuit.adjoint [twoQubit pair U]) = none := by
  rw [Circuit.cost_adjoint]
  exact oneQubitCNOT_cost_twoQubit pair U

/-- The Section 8 cost of a singleton is unchanged by circuit adjoint. -/
@[simp]
theorem arbitraryTwoQubit_cost_adjoint_twoQubit {n : ℕ}
    (pair : OrderedWirePair n) (U : TwoQubitUnitary) :
    Circuit.cost CostModel.arbitraryTwoQubit
      (Circuit.adjoint [twoQubit pair U]) = some 1 := by
  rw [Circuit.cost_adjoint]
  exact arbitraryTwoQubit_cost_twoQubit pair U

end Primitive

namespace Circuit

/-! ## Singleton evaluator bridges -/

/-- Exact arbitrary-register evaluation of one trusted two-wire node. -/
@[simp]
theorem eval_singleton_twoQubit {n : ℕ} (pair : OrderedWirePair n)
    (U : TwoQubitUnitary) :
    eval [Primitive.twoQubit pair U] = twoWireUnitary pair U := by
  simp

/-- Singleton basis-column action with spectator blocks explicit. -/
theorem eval_singleton_twoQubit_mulVec_basisKet {n : ℕ}
    (pair : OrderedWirePair n) (U : TwoQubitUnitary) (input : Basis n) :
    (eval [Primitive.twoQubit pair U] : Gate n) *ᵥ basisKet input = fun row =>
      if AgreeOffTwoWire pair row input then
        U (twoWireLocalBits pair row) (twoWireLocalBits pair input)
      else 0 := by
  rw [eval_singleton_twoQubit]
  exact twoWireUnitary_mulVec_basisKet pair U input

/-- Exact selected-pair output amplitude after evaluating the singleton. -/
@[simp]
theorem eval_singleton_twoQubit_mulVec_basisKet_setTwoWire {n : ℕ}
    (pair : OrderedWirePair n) (U : TwoQubitUnitary)
    (input : Basis n) (output : Basis 2) :
    ((eval [Primitive.twoQubit pair U] : Gate n) *ᵥ basisKet input)
        (setTwoWire pair input output) =
      U output (twoWireLocalBits pair input) := by
  rw [eval_singleton_twoQubit]
  exact twoWireUnitary_mulVec_basisKet_setTwoWire pair U input output

/-- Evaluating the singleton cannot create amplitude on a changed spectator. -/
theorem eval_singleton_twoQubit_mulVec_basisKet_eq_zero_of_changed {n : ℕ}
    (pair : OrderedWirePair n) (U : TwoQubitUnitary)
    (input row : Basis n) (wire : Fin n)
    (hfirst : wire ≠ pair.first) (hsecond : wire ≠ pair.second)
    (hchanged : row wire ≠ input wire) :
    ((eval [Primitive.twoQubit pair U] : Gate n) *ᵥ basisKet input) row = 0 := by
  rw [eval_singleton_twoQubit]
  exact twoWireUnitary_mulVec_basisKet_eq_zero_of_changed pair U input row wire
    hfirst hsecond hchanged

/-- Evaluated singleton basis action as the explicit four-term superposition. -/
theorem eval_singleton_twoQubit_mulVec_basisKet_eq_sum {n : ℕ}
    (pair : OrderedWirePair n) (U : TwoQubitUnitary) (input : Basis n) :
    (eval [Primitive.twoQubit pair U] : Gate n) *ᵥ basisKet input =
      ∑ output : Basis 2,
        U output (twoWireLocalBits pair input) •
          basisKet (setTwoWire pair input output) := by
  rw [eval_singleton_twoQubit]
  exact twoWireUnitary_mulVec_basisKet_eq_sum pair U input

end Circuit

end Barenco
