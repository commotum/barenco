import Barenco.Optimization.SymbolicCancellation

/-!
# Literal adjoints of symbolic early-model circuits

Free-group words already retain exact inverse provenance.  This leaf lifts that
operation to symbolic primitives and chronological lists: reverse the list,
invert each one-qubit word, and retain each self-adjoint CNOT.  Erasure commutes
exactly with the established payload-preserving adjoint.
-/

namespace Barenco.Optimization

open Barenco

namespace SymbolicPrimitive

/-- Literal formal adjoint of one symbolic early-model node. -/
def adjoint {Atom : Type*} {n : ℕ} :
    SymbolicPrimitive Atom n → SymbolicPrimitive Atom n
  | .oneQubit target word => .oneQubit target word⁻¹
  | .cnot control target h => .cnot control target h

@[simp]
theorem adjoint_adjoint {Atom : Type*} {n : ℕ}
    (primitive : SymbolicPrimitive Atom n) :
    primitive.adjoint.adjoint = primitive := by
  cases primitive <;> simp [adjoint]

/-- Valuation and erasure preserve the literal adjoint exactly. -/
@[simp]
theorem erase_adjoint {Atom : Type*} {n : ℕ}
    (valuation : Atom → QubitUnitary)
    (primitive : SymbolicPrimitive Atom n) :
    erase valuation primitive.adjoint = (erase valuation primitive).adjoint := by
  cases primitive <;>
    simp [adjoint, erase, FusionPrimitive.adjoint]

end SymbolicPrimitive

namespace SymbolicCircuit

/-- Reverse chronology and formally adjoint every symbolic payload. -/
def adjoint {Atom : Type*} {n : ℕ}
    (circuit : SymbolicCircuit Atom n) : SymbolicCircuit Atom n :=
  circuit.reverse.map SymbolicPrimitive.adjoint

@[simp]
theorem adjoint_nil {Atom : Type*} {n : ℕ} :
    adjoint ([] : SymbolicCircuit Atom n) = [] := rfl

@[simp]
theorem adjoint_append {Atom : Type*} {n : ℕ}
    (first second : SymbolicCircuit Atom n) :
    adjoint (first ++ second) = adjoint second ++ adjoint first := by
  simp [adjoint, List.map_reverse]

@[simp]
theorem adjoint_adjoint {Atom : Type*} {n : ℕ}
    (circuit : SymbolicCircuit Atom n) :
    circuit.adjoint.adjoint = circuit := by
  simp [adjoint, List.map_reverse, List.map_map, Function.comp_def]

/-- Erasing a symbolic adjoint gives the visible fusion-circuit adjoint. -/
@[simp]
theorem erase_adjoint {Atom : Type*} {n : ℕ}
    (valuation : Atom → QubitUnitary)
    (circuit : SymbolicCircuit Atom n) :
    erase valuation circuit.adjoint = (erase valuation circuit).adjoint := by
  simp [adjoint, erase, FusionCircuit.adjoint, List.map_reverse,
    List.map_map, Function.comp_def]

/-- A symbolic adjoint evaluates to the exact inverse after every valuation. -/
@[simp]
theorem eval_erase_adjoint {Atom : Type*} {n : ℕ}
    (valuation : Atom → QubitUnitary)
    (circuit : SymbolicCircuit Atom n) :
    FusionCircuit.eval (erase valuation circuit.adjoint) =
      (FusionCircuit.eval (erase valuation circuit))⁻¹ := by
  rw [erase_adjoint, FusionCircuit.eval_adjoint]

@[simp]
theorem gateCount_adjoint {Atom : Type*} {n : ℕ}
    (circuit : SymbolicCircuit Atom n) :
    gateCount circuit.adjoint = gateCount circuit := by
  simp [adjoint, gateCount]

@[simp]
theorem oneQubitWeight_adjoint {Atom : Type*} {n : ℕ}
    (primitive : SymbolicPrimitive Atom n) :
    oneQubitWeight primitive.adjoint = oneQubitWeight primitive := by
  cases primitive <;> rfl

@[simp]
theorem cnotWeight_adjoint {Atom : Type*} {n : ℕ}
    (primitive : SymbolicPrimitive Atom n) :
    cnotWeight primitive.adjoint = cnotWeight primitive := by
  cases primitive <;> rfl

@[simp]
theorem oneQubitCount_adjoint {Atom : Type*} {n : ℕ}
    (circuit : SymbolicCircuit Atom n) :
    oneQubitCount circuit.adjoint = oneQubitCount circuit := by
  induction circuit with
  | nil => rfl
  | cons primitive circuit ih =>
      rw [show adjoint (primitive :: circuit) =
          adjoint circuit ++ [primitive.adjoint] by
        simp [adjoint]]
      simp [ih]
      omega

@[simp]
theorem cnotCount_adjoint {Atom : Type*} {n : ℕ}
    (circuit : SymbolicCircuit Atom n) :
    cnotCount circuit.adjoint = cnotCount circuit := by
  induction circuit with
  | nil => rfl
  | cons primitive circuit ih =>
      rw [show adjoint (primitive :: circuit) =
          adjoint circuit ++ [primitive.adjoint] by
        simp [adjoint]]
      simp [ih]
      omega

@[simp]
theorem cnotTrace_adjoint {Atom : Type*} {n : ℕ}
    (circuit : SymbolicCircuit Atom n) :
    cnotTrace circuit.adjoint = (cnotTrace circuit).reverse := by
  induction circuit with
  | nil => rfl
  | cons primitive circuit ih =>
      rw [show adjoint (primitive :: circuit) =
          adjoint circuit ++ [primitive.adjoint] by
        simp [adjoint]]
      rw [cnotTrace_append, ih]
      cases primitive <;> simp [cnotTrace, SymbolicPrimitive.adjoint]

end SymbolicCircuit

end Barenco.Optimization
