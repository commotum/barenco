import Barenco.Optimization.SymbolicExpose

/-!
# Symbolic cancellation across a wire-avoiding middle

`normalizeAtWire` can move a selected-wire word across any symbolic circuit whose
nodes are structurally disjoint from that wire.  This leaf packages the predicate
and proves the reusable endpoint-cancellation theorem without consulting matrix
payloads or support metadata.
-/

namespace Barenco.Optimization

open Barenco

namespace SymbolicPrimitive

/-- A symbolic node is structurally disjoint from the selected wire. -/
def AvoidsWire {Atom : Type*} {n : ℕ} (wire : Fin n) :
    SymbolicPrimitive Atom n → Prop
  | .oneQubit target _ => target ≠ wire
  | .cnot control target _ => wire ≠ control ∧ wire ≠ target

end SymbolicPrimitive

namespace SymbolicCircuit

/-- A formal inverse/atom suffix cancels after every earlier prefix. -/
@[simp]
theorem normalize_append_inverse_atom_atom {Atom : Type*} [DecidableEq Atom]
    {n : ℕ} (earlier : SymbolicCircuit Atom n) (wire : Fin n) (atom : Atom) :
    normalize
        (earlier ++ [SymbolicPrimitive.inverseAtom wire atom,
          SymbolicPrimitive.atom wire atom]) =
      normalize earlier := by
  induction earlier with
  | nil =>
      simp [normalize, NormalizeCore.normalize, NormalizeCore.insert,
        SymbolicPrimitive.isIdentity, SymbolicPrimitive.combine,
        SymbolicPrimitive.atom, SymbolicPrimitive.inverseAtom]
  | cons gate tail ih =>
      simp only [List.cons_append, normalize, NormalizeCore.normalize]
      simp only [normalize] at ih
      rw [ih]

/-- Exposure is inert when every node avoids the selected wire. -/
theorem exposeWire_eq_self_of_all_avoids {Atom : Type*} {n : ℕ}
    (wire : Fin n) (circuit : SymbolicCircuit Atom n)
    (havoid : ∀ gate ∈ circuit, SymbolicPrimitive.AvoidsWire wire gate) :
    exposeWire wire circuit = circuit := by
  induction circuit with
  | nil => rfl
  | cons gate circuit ih =>
      have hgate := havoid gate (by simp)
      have htail : ∀ next ∈ circuit,
          SymbolicPrimitive.AvoidsWire wire next := by
        intro next hnext
        exact havoid next (by simp [hnext])
      rw [exposeWire, ih htail]
      cases gate with
      | oneQubit target word =>
          simp [SymbolicPrimitive.AvoidsWire] at hgate
          cases circuit with
          | nil => rfl
          | cons next rest =>
              cases next <;> simp [exposeWireInsert, hgate]
      | cnot control target h =>
          cases circuit <;> rfl

/-- An earlier selected-wire word crosses every node in an avoiding circuit. -/
theorem exposeWireInsert_across_all_avoids {Atom : Type*} {n : ℕ}
    (wire : Fin n) (word : QubitWord Atom)
    (circuit : SymbolicCircuit Atom n)
    (havoid : ∀ gate ∈ circuit, SymbolicPrimitive.AvoidsWire wire gate) :
    exposeWireInsert wire (.oneQubit wire word) circuit =
      circuit ++ [.oneQubit wire word] := by
  induction circuit with
  | nil => rfl
  | cons gate circuit ih =>
      have hgate := havoid gate (by simp)
      have htail : ∀ next ∈ circuit,
          SymbolicPrimitive.AvoidsWire wire next := by
        intro next hnext
        exact havoid next (by simp [hnext])
      cases gate with
      | oneQubit target nextWord =>
          simp [SymbolicPrimitive.AvoidsWire] at hgate
          simp [exposeWireInsert, hgate, ih htail]
      | cnot control target h =>
          simp [SymbolicPrimitive.AvoidsWire] at hgate
          simp [exposeWireInsert, hgate, ih htail]

/-- An avoiding prefix remains ahead of a final selected-wire word. -/
theorem exposeWire_append_selected_of_all_avoids {Atom : Type*} {n : ℕ}
    (wire : Fin n) (word : QubitWord Atom)
    (circuit : SymbolicCircuit Atom n)
    (havoid : ∀ gate ∈ circuit, SymbolicPrimitive.AvoidsWire wire gate) :
    exposeWire wire (circuit ++ [.oneQubit wire word]) =
      circuit ++ [.oneQubit wire word] := by
  induction circuit with
  | nil => rfl
  | cons gate circuit ih =>
      have hgate := havoid gate (by simp)
      have htail : ∀ next ∈ circuit,
          SymbolicPrimitive.AvoidsWire wire next := by
        intro next hnext
        exact havoid next (by simp [hnext])
      rw [List.cons_append, exposeWire, ih htail]
      cases gate with
      | oneQubit target nextWord =>
          simp [SymbolicPrimitive.AvoidsWire] at hgate
          cases circuit with
          | nil => simp [exposeWireInsert, hgate]
          | cons next rest =>
              cases next <;> simp [exposeWireInsert, hgate]
      | cnot control target h =>
          cases circuit <;> rfl

/-- A selected-wire word crosses an avoiding prefix and stops at the next one. -/
theorem exposeWireInsert_before_same_after_all_avoids
    {Atom : Type*} {n : ℕ}
    (wire : Fin n) (first second : QubitWord Atom)
    (circuit : SymbolicCircuit Atom n)
    (havoid : ∀ gate ∈ circuit, SymbolicPrimitive.AvoidsWire wire gate) :
    exposeWireInsert wire (.oneQubit wire first)
        (circuit ++ [.oneQubit wire second]) =
      circuit ++ [.oneQubit wire first, .oneQubit wire second] := by
  induction circuit with
  | nil => simp [exposeWireInsert]
  | cons gate circuit ih =>
      have hgate := havoid gate (by simp)
      have htail : ∀ next ∈ circuit,
          SymbolicPrimitive.AvoidsWire wire next := by
        intro next hnext
        exact havoid next (by simp [hnext])
      cases gate with
      | oneQubit target nextWord =>
          simp [SymbolicPrimitive.AvoidsWire] at hgate
          simp [exposeWireInsert, hgate, ih htail]
      | cnot control target h =>
          simp [SymbolicPrimitive.AvoidsWire] at hgate
          simp [exposeWireInsert, hgate, ih htail]

/-- Exact formal inverse cancellation across an arbitrary avoiding middle. -/
theorem normalizeAtWire_inverse_across_avoiding {Atom : Type*}
    [DecidableEq Atom] {n : ℕ} (wire : Fin n) (atom : Atom)
    (middle : SymbolicCircuit Atom n)
    (havoid : ∀ gate ∈ middle, SymbolicPrimitive.AvoidsWire wire gate) :
    normalizeAtWire wire
        ([SymbolicPrimitive.inverseAtom wire atom] ++ middle ++
          [SymbolicPrimitive.atom wire atom]) =
      normalize middle := by
  rw [normalizeAtWire]
  simp only [SymbolicPrimitive.inverseAtom, SymbolicPrimitive.atom,
    List.singleton_append]
  have htail := exposeWire_append_selected_of_all_avoids wire
    (FreeGroup.of atom) middle havoid
  change normalize
      (exposeWireInsert wire (.oneQubit wire (FreeGroup.of atom)⁻¹)
        (exposeWire wire
          (middle ++ [.oneQubit wire (FreeGroup.of atom)]))) =
    normalize middle
  rw [htail]
  rw [exposeWireInsert_before_same_after_all_avoids wire
    ((FreeGroup.of atom)⁻¹) (FreeGroup.of atom) middle havoid]
  exact normalize_append_inverse_atom_atom middle wire atom

end SymbolicCircuit

end Barenco.Optimization
