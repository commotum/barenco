import Barenco.Optimization.SymbolicExpose

/-!
# Scheduled target-directed symbolic normalization

This module lifts `SymbolicCircuit.normalizeAtWire` over an explicit list of
wires.  The schedule is data, not a hidden ambient ordering assumption.  Every
step preserves exact full-register evaluation and the complete ordered CNOT
trace, while one-qubit syntax can only decrease.
-/

namespace Barenco.Optimization

open Barenco

namespace SymbolicCircuit

/-- Apply the exact target-directed pass in the supplied wire order. -/
def normalizeWires {Atom : Type*} [DecidableEq Atom] {n : ℕ} :
    List (Fin n) → SymbolicCircuit Atom n → SymbolicCircuit Atom n
  | [], circuit => circuit
  | wire :: wires, circuit =>
      normalizeWires wires (normalizeAtWire wire circuit)

@[simp]
theorem normalizeWires_nil {Atom : Type*} [DecidableEq Atom] {n : ℕ}
    (circuit : SymbolicCircuit Atom n) :
    normalizeWires [] circuit = circuit := rfl

@[simp]
theorem normalizeWires_cons {Atom : Type*} [DecidableEq Atom] {n : ℕ}
    (wire : Fin n) (wires : List (Fin n))
    (circuit : SymbolicCircuit Atom n) :
    normalizeWires (wire :: wires) circuit =
      normalizeWires wires (normalizeAtWire wire circuit) := rfl

/-- Every scheduled sweep preserves exact valuation and full-register semantics. -/
@[simp]
theorem eval_erase_normalizeWires {Atom : Type*} [DecidableEq Atom] {n : ℕ}
    (valuation : Atom → QubitUnitary) (wires : List (Fin n))
    (circuit : SymbolicCircuit Atom n) :
    FusionCircuit.eval (erase valuation (normalizeWires wires circuit)) =
      FusionCircuit.eval (erase valuation circuit) := by
  induction wires generalizing circuit with
  | nil => rfl
  | cons wire wires ih =>
      rw [normalizeWires_cons, ih, eval_erase_normalizeAtWire]

/-- The trusted lowered evaluator is preserved by every scheduled sweep. -/
@[simp]
theorem eval_lower_erase_normalizeWires
    {Atom : Type*} [DecidableEq Atom] {n : ℕ}
    (valuation : Atom → QubitUnitary) (wires : List (Fin n))
    (circuit : SymbolicCircuit Atom n) :
    Circuit.eval (erase valuation (normalizeWires wires circuit)).lower =
      Circuit.eval (erase valuation circuit).lower := by
  simp

/-- Scheduled target exposure/cancellation retains every ordered CNOT endpoint. -/
@[simp]
theorem cnotTrace_normalizeWires {Atom : Type*} [DecidableEq Atom] {n : ℕ}
    (wires : List (Fin n)) (circuit : SymbolicCircuit Atom n) :
    cnotTrace (normalizeWires wires circuit) = cnotTrace circuit := by
  induction wires generalizing circuit with
  | nil => rfl
  | cons wire wires ih =>
      rw [normalizeWires_cons, ih, cnotTrace_normalizeAtWire]

@[simp]
theorem cnotCount_normalizeWires {Atom : Type*} [DecidableEq Atom] {n : ℕ}
    (wires : List (Fin n)) (circuit : SymbolicCircuit Atom n) :
    cnotCount (normalizeWires wires circuit) = cnotCount circuit := by
  rw [cnotCount_eq_length_cnotTrace, cnotCount_eq_length_cnotTrace,
    cnotTrace_normalizeWires]

/-- A scheduled sweep cannot increase the number of one-qubit syntax nodes. -/
theorem oneQubitCount_normalizeWires_le
    {Atom : Type*} [DecidableEq Atom] {n : ℕ}
    (wires : List (Fin n)) (circuit : SymbolicCircuit Atom n) :
    oneQubitCount (normalizeWires wires circuit) ≤ oneQubitCount circuit := by
  induction wires generalizing circuit with
  | nil => exact Nat.le_refl _
  | cons wire wires ih =>
      exact (ih (normalizeAtWire wire circuit)).trans
        (oneQubitCount_normalizeAtWire_le wire circuit)

/-- A scheduled sweep cannot increase total early-model syntax length. -/
theorem gateCount_normalizeWires_le
    {Atom : Type*} [DecidableEq Atom] {n : ℕ}
    (wires : List (Fin n)) (circuit : SymbolicCircuit Atom n) :
    gateCount (normalizeWires wires circuit) ≤ gateCount circuit := by
  rw [gateCount_eq_componentCounts, gateCount_eq_componentCounts,
    cnotCount_normalizeWires]
  exact Nat.add_le_add_right
    (oneQubitCount_normalizeWires_le wires circuit) _

/-- One ascending sweep over every ambient wire. -/
def sweepForward {Atom : Type*} [DecidableEq Atom] {n : ℕ}
    (circuit : SymbolicCircuit Atom n) : SymbolicCircuit Atom n :=
  normalizeWires (List.finRange n) circuit

/-- One descending sweep over every ambient wire. -/
def sweepReverse {Atom : Type*} [DecidableEq Atom] {n : ℕ}
    (circuit : SymbolicCircuit Atom n) : SymbolicCircuit Atom n :=
  normalizeWires (List.finRange n).reverse circuit

/-- Ascending followed by descending exact target-directed normalization. -/
def sweepBoth {Atom : Type*} [DecidableEq Atom] {n : ℕ}
    (circuit : SymbolicCircuit Atom n) : SymbolicCircuit Atom n :=
  sweepReverse (sweepForward circuit)

@[simp]
theorem eval_erase_sweepForward {Atom : Type*} [DecidableEq Atom] {n : ℕ}
    (valuation : Atom → QubitUnitary) (circuit : SymbolicCircuit Atom n) :
    FusionCircuit.eval (erase valuation (sweepForward circuit)) =
      FusionCircuit.eval (erase valuation circuit) := by
  simp [sweepForward]

@[simp]
theorem eval_erase_sweepReverse {Atom : Type*} [DecidableEq Atom] {n : ℕ}
    (valuation : Atom → QubitUnitary) (circuit : SymbolicCircuit Atom n) :
    FusionCircuit.eval (erase valuation (sweepReverse circuit)) =
      FusionCircuit.eval (erase valuation circuit) := by
  simp [sweepReverse]

@[simp]
theorem eval_erase_sweepBoth {Atom : Type*} [DecidableEq Atom] {n : ℕ}
    (valuation : Atom → QubitUnitary) (circuit : SymbolicCircuit Atom n) :
    FusionCircuit.eval (erase valuation (sweepBoth circuit)) =
      FusionCircuit.eval (erase valuation circuit) := by
  simp [sweepBoth]

@[simp]
theorem cnotTrace_sweepBoth {Atom : Type*} [DecidableEq Atom] {n : ℕ}
    (circuit : SymbolicCircuit Atom n) :
    cnotTrace (sweepBoth circuit) = cnotTrace circuit := by
  simp [sweepBoth, sweepForward, sweepReverse]

@[simp]
theorem cnotCount_sweepBoth {Atom : Type*} [DecidableEq Atom] {n : ℕ}
    (circuit : SymbolicCircuit Atom n) :
    cnotCount (sweepBoth circuit) = cnotCount circuit := by
  rw [cnotCount_eq_length_cnotTrace, cnotCount_eq_length_cnotTrace,
    cnotTrace_sweepBoth]

end SymbolicCircuit

end Barenco.Optimization
