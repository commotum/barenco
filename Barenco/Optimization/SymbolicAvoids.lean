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

/-- A formal atom/inverse suffix also cancels after every earlier prefix. -/
@[simp]
theorem normalize_append_atom_inverse {Atom : Type*} [DecidableEq Atom]
    {n : ℕ} (earlier : SymbolicCircuit Atom n) (wire : Fin n) (atom : Atom) :
    normalize
        (earlier ++ [SymbolicPrimitive.atom wire atom,
          SymbolicPrimitive.inverseAtom wire atom]) =
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

/--
Tail-first normalization replaces two final same-wire words by their exact
chronological product before processing any earlier prefix.
-/
theorem normalize_append_oneQubit_pair {Atom : Type*} [DecidableEq Atom]
    {n : ℕ} (earlier : SymbolicCircuit Atom n) (wire : Fin n)
    (first second : QubitWord Atom) :
    normalize
        (earlier ++ [.oneQubit wire first, .oneQubit wire second]) =
      normalize
        (earlier ++ [.oneQubit wire (second * first)]) := by
  induction earlier with
  | nil =>
      by_cases hsecond : second = 1
      · subst second
        simp [normalize, NormalizeCore.normalize, NormalizeCore.insert,
          SymbolicPrimitive.isIdentity]
      · by_cases hfirst : first = 1
        · subst first
          simp [normalize, NormalizeCore.normalize, NormalizeCore.insert,
            SymbolicPrimitive.isIdentity, hsecond]
        · simp [normalize, NormalizeCore.normalize, NormalizeCore.insert,
            SymbolicPrimitive.isIdentity, SymbolicPrimitive.combine,
            hsecond, hfirst]
  | cons gate earlier ih =>
      simp only [List.cons_append, normalize, NormalizeCore.normalize]
      simp only [normalize] at ih
      rw [ih]

/--
Appending a nonidentity selected-wire word preserves stability when every
existing node is structurally disjoint from that wire.
-/
theorem Stable.append_selected_of_all_avoids {Atom : Type*}
    [DecidableEq Atom] {n : ℕ}
    (wire : Fin n) (word : QubitWord Atom)
    (circuit : SymbolicCircuit Atom n)
    (hstable : Stable circuit)
    (havoid : ∀ gate ∈ circuit, SymbolicPrimitive.AvoidsWire wire gate)
    (hne : word ≠ 1) :
    Stable (circuit ++ [.oneQubit wire word]) := by
  induction circuit with
  | nil =>
      simp [Stable, NormalizeCore.Stable,
        SymbolicPrimitive.isIdentity, hne]
  | cons gate circuit ih =>
      cases circuit with
      | nil =>
          have hgate := havoid gate (by simp)
          cases gate with
          | oneQubit target gateWord =>
              simp [Stable, NormalizeCore.Stable,
                SymbolicPrimitive.isIdentity, SymbolicPrimitive.combine,
                SymbolicPrimitive.AvoidsWire, hne] at hstable hgate ⊢
              aesop
          | cnot control target h =>
              simp [Stable, NormalizeCore.Stable,
                SymbolicPrimitive.isIdentity, SymbolicPrimitive.combine,
                SymbolicPrimitive.AvoidsWire, hne] at hstable hgate ⊢
      | cons next rest =>
          have htailAvoid : ∀ later ∈ next :: rest,
              SymbolicPrimitive.AvoidsWire wire later := by
            intro later hlater
            exact havoid later (by simp [hlater])
          exact ⟨hstable.1, hstable.2.1,
            ih hstable.2.2 htailAvoid⟩

/--
Two selected-wire words fuse across an arbitrary stable avoiding middle.  The
emitted word uses the library's head-first chronology: `second * first`.
-/
theorem normalizeAtWire_words_across_avoiding {Atom : Type*}
    [DecidableEq Atom] {n : ℕ}
    (wire : Fin n) (first second : QubitWord Atom)
    (middle : SymbolicCircuit Atom n)
    (havoid : ∀ gate ∈ middle, SymbolicPrimitive.AvoidsWire wire gate)
    (hstable : Stable middle)
    (hne : second * first ≠ 1) :
    normalizeAtWire wire
        ([.oneQubit wire first] ++ middle ++ [.oneQubit wire second]) =
      middle ++ [.oneQubit wire (second * first)] := by
  rw [normalizeAtWire]
  have htail := exposeWire_append_selected_of_all_avoids wire second middle havoid
  change normalize
      (exposeWireInsert wire (.oneQubit wire first)
        (exposeWire wire (middle ++ [.oneQubit wire second]))) = _
  rw [htail]
  rw [exposeWireInsert_before_same_after_all_avoids wire
    first second middle havoid]
  rw [normalize_append_oneQubit_pair]
  exact normalize_eq_self_of_stable
    (Stable.append_selected_of_all_avoids wire
      (second * first) middle hstable havoid hne)

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

/-- Exact formal atom/inverse cancellation across an arbitrary avoiding middle. -/
theorem normalizeAtWire_atom_across_avoiding_inverse {Atom : Type*}
    [DecidableEq Atom] {n : ℕ} (wire : Fin n) (atom : Atom)
    (middle : SymbolicCircuit Atom n)
    (havoid : ∀ gate ∈ middle, SymbolicPrimitive.AvoidsWire wire gate) :
    normalizeAtWire wire
        ([SymbolicPrimitive.atom wire atom] ++ middle ++
          [SymbolicPrimitive.inverseAtom wire atom]) =
      normalize middle := by
  rw [normalizeAtWire]
  simp only [SymbolicPrimitive.inverseAtom, SymbolicPrimitive.atom,
    List.singleton_append]
  have htail := exposeWire_append_selected_of_all_avoids wire
    (FreeGroup.of atom)⁻¹ middle havoid
  change normalize
      (exposeWireInsert wire (.oneQubit wire (FreeGroup.of atom))
        (exposeWire wire
          (middle ++ [.oneQubit wire (FreeGroup.of atom)⁻¹]))) =
    normalize middle
  rw [htail]
  rw [exposeWireInsert_before_same_after_all_avoids wire
    (FreeGroup.of atom) ((FreeGroup.of atom)⁻¹) middle havoid]
  exact normalize_append_atom_inverse middle wire atom

/--
Deleting a formal inverse/atom pair across a structurally avoiding middle is an
exact evaluator-preserving rewrite, even when the middle is not normalized.
-/
theorem eval_erase_delete_inverse_across_avoiding {Atom : Type*}
    [DecidableEq Atom] {n : ℕ}
    (valuation : Atom → QubitUnitary) (wire : Fin n) (atom : Atom)
    (middle : SymbolicCircuit Atom n)
    (havoid : ∀ gate ∈ middle, SymbolicPrimitive.AvoidsWire wire gate) :
    FusionCircuit.eval
        (erase valuation
          ([SymbolicPrimitive.inverseAtom wire atom] ++ middle ++
            [SymbolicPrimitive.atom wire atom])) =
      FusionCircuit.eval (erase valuation middle) := by
  calc
    FusionCircuit.eval
        (erase valuation
          ([SymbolicPrimitive.inverseAtom wire atom] ++ middle ++
            [SymbolicPrimitive.atom wire atom])) =
        FusionCircuit.eval
          (erase valuation
            (normalizeAtWire wire
              ([SymbolicPrimitive.inverseAtom wire atom] ++ middle ++
                [SymbolicPrimitive.atom wire atom]))) :=
      (eval_erase_normalizeAtWire valuation wire _).symm
    _ = FusionCircuit.eval (erase valuation (normalize middle)) := by
      rw [normalizeAtWire_inverse_across_avoiding wire atom middle havoid]
    _ = FusionCircuit.eval (erase valuation middle) :=
      eval_erase_normalize valuation middle

/-- The symmetric formal atom/inverse deletion is also exact. -/
theorem eval_erase_delete_atom_across_avoiding_inverse {Atom : Type*}
    [DecidableEq Atom] {n : ℕ}
    (valuation : Atom → QubitUnitary) (wire : Fin n) (atom : Atom)
    (middle : SymbolicCircuit Atom n)
    (havoid : ∀ gate ∈ middle, SymbolicPrimitive.AvoidsWire wire gate) :
    FusionCircuit.eval
        (erase valuation
          ([SymbolicPrimitive.atom wire atom] ++ middle ++
            [SymbolicPrimitive.inverseAtom wire atom])) =
      FusionCircuit.eval (erase valuation middle) := by
  calc
    FusionCircuit.eval
        (erase valuation
          ([SymbolicPrimitive.atom wire atom] ++ middle ++
            [SymbolicPrimitive.inverseAtom wire atom])) =
        FusionCircuit.eval
          (erase valuation
            (normalizeAtWire wire
              ([SymbolicPrimitive.atom wire atom] ++ middle ++
                [SymbolicPrimitive.inverseAtom wire atom]))) :=
      (eval_erase_normalizeAtWire valuation wire _).symm
    _ = FusionCircuit.eval (erase valuation (normalize middle)) := by
      rw [normalizeAtWire_atom_across_avoiding_inverse wire atom middle havoid]
    _ = FusionCircuit.eval (erase valuation middle) :=
      eval_erase_normalize valuation middle

/-- Join two stable circuits across one explicitly blocked boundary. -/
theorem Stable.append_of_last_first {Atom : Type*} [DecidableEq Atom]
    {n : ℕ} (earlier : SymbolicCircuit Atom n)
    (last next : SymbolicPrimitive Atom n) (later : SymbolicCircuit Atom n)
    (hfirst : Stable (earlier ++ [last]))
    (hsecond : Stable (next :: later))
    (hblocked : SymbolicPrimitive.combine last next =
      NormalizeCore.CombineResult.blocked) :
    Stable ((earlier ++ [last]) ++ next :: later) := by
  induction earlier with
  | nil =>
      exact ⟨hfirst, hblocked, hsecond⟩
  | cons gate earlier ih =>
      cases earlier with
      | nil =>
          exact ⟨hfirst.1, hfirst.2.1,
            ih hfirst.2.2⟩
      | cons second rest =>
          exact ⟨hfirst.1, hfirst.2.1,
            ih hfirst.2.2⟩

end SymbolicCircuit

end Barenco.Optimization
