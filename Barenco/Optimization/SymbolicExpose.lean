import Barenco.Optimization.SymbolicCancellation
import Barenco.Optimization.FusionCommutation

/-!
# Target-directed exposure for symbolic one-qubit provenance

`exposeWire wire` moves an earlier symbolic one-qubit word on `wire` to the
right across concrete gates certified disjoint from that wire.  It stops at a
one-qubit word on the same wire or at a CNOT touching the wire.  The policy is
independent of ambient `Fin` ordering and never inspects a matrix payload.

Composing exposure with the existing free-group normalizer makes inverse words
separated only by off-wire gates executable cancellation opportunities.  All
equalities are exact on the complete ambient register; the ordered literal CNOT
trace is preserved.
-/

namespace Barenco.Optimization

open Barenco

namespace SymbolicCircuit

/--
Insert an earlier symbolic gate while moving a word on `wire` rightward across
one-qubit words on other wires and CNOTs disjoint from `wire`.
-/
def exposeWireInsert {Atom : Type*} {n : ℕ} (wire : Fin n) :
    SymbolicPrimitive Atom n → SymbolicCircuit Atom n →
      SymbolicCircuit Atom n
  | gate@(.oneQubit _ _), [] => [gate]
  | gate@(.oneQubit gateWire _), next@(.oneQubit nextWire _) :: circuit =>
      if gateWire = wire ∧ nextWire ≠ wire then
        next :: exposeWireInsert wire gate circuit
      else
        gate :: next :: circuit
  | gate@(.oneQubit gateWire _), next@(.cnot control target _) :: circuit =>
      if gateWire = wire ∧ wire ≠ control ∧ wire ≠ target then
        next :: exposeWireInsert wire gate circuit
      else
        gate :: next :: circuit
  | gate, circuit => gate :: circuit

/-- Tail-first exposure of all symbolic words on one selected wire. -/
def exposeWire {Atom : Type*} {n : ℕ} (wire : Fin n) :
    SymbolicCircuit Atom n → SymbolicCircuit Atom n
  | [] => []
  | gate :: circuit => exposeWireInsert wire gate (exposeWire wire circuit)

/-- Expose one wire and then run exact free-group cancellation. -/
def normalizeAtWire {Atom : Type*} [DecidableEq Atom] {n : ℕ}
    (wire : Fin n) (circuit : SymbolicCircuit Atom n) :
    SymbolicCircuit Atom n :=
  normalize (exposeWire wire circuit)

/-! ## Exact arbitrary-register semantics -/

private theorem eval_erase_exposeWireInsert {Atom : Type*} {n : ℕ}
    (valuation : Atom → QubitUnitary) (wire : Fin n)
    (gate : SymbolicPrimitive Atom n) :
    ∀ circuit : SymbolicCircuit Atom n,
      FusionCircuit.eval
          (erase valuation (exposeWireInsert wire gate circuit)) =
        FusionCircuit.eval (erase valuation circuit) *
          (SymbolicPrimitive.erase valuation gate).denotation := by
  intro circuit
  induction circuit generalizing gate with
  | nil =>
      cases gate <;> rfl
  | cons next circuit ih =>
      cases gate with
      | cnot => rfl
      | oneQubit gateWire gateWord =>
          cases next with
          | oneQubit nextWire nextWord =>
              by_cases hmove : gateWire = wire ∧ nextWire ≠ wire
              · rcases hmove with ⟨hgate, hnext⟩
                simp only [exposeWireInsert, hgate, true_and]
                rw [if_pos hnext]
                simp only [erase_cons, FusionCircuit.eval_cons]
                rw [ih]
                subst gateWire
                have hcommute := oneQubit_denotationsCommute_of_ne
                  wire nextWire (Ne.symm hnext)
                  (QubitWord.evaluate valuation gateWord)
                  (QubitWord.evaluate valuation nextWord)
                calc
                  (FusionCircuit.eval (erase valuation circuit) *
                        (SymbolicPrimitive.erase valuation
                          (.oneQubit wire gateWord)).denotation) *
                      (SymbolicPrimitive.erase valuation
                        (.oneQubit nextWire nextWord)).denotation =
                    FusionCircuit.eval (erase valuation circuit) *
                      ((SymbolicPrimitive.erase valuation
                          (.oneQubit wire gateWord)).denotation *
                        (SymbolicPrimitive.erase valuation
                          (.oneQubit nextWire nextWord)).denotation) :=
                            mul_assoc _ _ _
                  _ = FusionCircuit.eval (erase valuation circuit) *
                      ((SymbolicPrimitive.erase valuation
                          (.oneQubit nextWire nextWord)).denotation *
                        (SymbolicPrimitive.erase valuation
                          (.oneQubit wire gateWord)).denotation) := by
                            simp only [SymbolicPrimitive.erase]
                            rw [hcommute]
                  _ = (FusionCircuit.eval (erase valuation circuit) *
                        (SymbolicPrimitive.erase valuation
                          (.oneQubit nextWire nextWord)).denotation) *
                      (SymbolicPrimitive.erase valuation
                        (.oneQubit wire gateWord)).denotation :=
                            (mul_assoc _ _ _).symm
              · simp [exposeWireInsert, hmove]
          | cnot control target hcontrolTarget =>
              by_cases hmove :
                  gateWire = wire ∧ wire ≠ control ∧ wire ≠ target
              · rcases hmove with ⟨hgate, hwireControl, hwireTarget⟩
                simp only [exposeWireInsert, hgate, true_and]
                rw [if_pos ⟨hwireControl, hwireTarget⟩]
                simp only [erase_cons, FusionCircuit.eval_cons]
                rw [ih]
                subst gateWire
                have hcommute := oneQubit_cnot_denotationsCommute_of_disjoint
                  wire control target hcontrolTarget
                    hwireControl.symm hwireTarget.symm
                    (QubitWord.evaluate valuation gateWord)
                calc
                  (FusionCircuit.eval (erase valuation circuit) *
                        (SymbolicPrimitive.erase valuation
                          (.oneQubit wire gateWord)).denotation) *
                      (SymbolicPrimitive.erase valuation
                        (.cnot control target hcontrolTarget)).denotation =
                    FusionCircuit.eval (erase valuation circuit) *
                      ((SymbolicPrimitive.erase valuation
                          (.oneQubit wire gateWord)).denotation *
                        (SymbolicPrimitive.erase valuation
                          (.cnot control target hcontrolTarget)).denotation) :=
                            mul_assoc _ _ _
                  _ = FusionCircuit.eval (erase valuation circuit) *
                      ((SymbolicPrimitive.erase valuation
                          (.cnot control target hcontrolTarget)).denotation *
                        (SymbolicPrimitive.erase valuation
                          (.oneQubit wire gateWord)).denotation) := by
                            simp only [SymbolicPrimitive.erase]
                            rw [hcommute]
                  _ = (FusionCircuit.eval (erase valuation circuit) *
                        (SymbolicPrimitive.erase valuation
                          (.cnot control target hcontrolTarget)).denotation) *
                      (SymbolicPrimitive.erase valuation
                        (.oneQubit wire gateWord)).denotation :=
                            (mul_assoc _ _ _).symm
              · simp [exposeWireInsert, hmove]

/-- Target-directed exposure preserves exact full-register evaluation. -/
@[simp]
theorem eval_erase_exposeWire {Atom : Type*} {n : ℕ}
    (valuation : Atom → QubitUnitary) (wire : Fin n)
    (circuit : SymbolicCircuit Atom n) :
    FusionCircuit.eval (erase valuation (exposeWire wire circuit)) =
      FusionCircuit.eval (erase valuation circuit) := by
  induction circuit with
  | nil => rfl
  | cons gate circuit ih =>
      rw [exposeWire, eval_erase_exposeWireInsert, ih]
      rfl

/-- Exposure followed by symbolic cancellation remains exactly sound. -/
@[simp]
theorem eval_erase_normalizeAtWire {Atom : Type*} [DecidableEq Atom] {n : ℕ}
    (valuation : Atom → QubitUnitary) (wire : Fin n)
    (circuit : SymbolicCircuit Atom n) :
    FusionCircuit.eval (erase valuation (normalizeAtWire wire circuit)) =
      FusionCircuit.eval (erase valuation circuit) := by
  rw [normalizeAtWire, eval_erase_normalize, eval_erase_exposeWire]

/-- Exact soundness also holds after lowering into trusted public circuit syntax. -/
theorem eval_lower_erase_normalizeAtWire {Atom : Type*} [DecidableEq Atom]
    {n : ℕ} (valuation : Atom → QubitUnitary) (wire : Fin n)
    (circuit : SymbolicCircuit Atom n) :
    Circuit.eval (erase valuation (normalizeAtWire wire circuit)).lower =
      Circuit.eval (erase valuation circuit).lower := by
  simp

/-! ## Literal chronology and component preservation -/

private theorem length_exposeWireInsert {Atom : Type*} {n : ℕ}
    (wire : Fin n) (gate : SymbolicPrimitive Atom n) :
    ∀ circuit : SymbolicCircuit Atom n,
      (exposeWireInsert wire gate circuit).length = circuit.length + 1 := by
  intro circuit
  induction circuit generalizing gate with
  | nil => cases gate <;> rfl
  | cons next circuit ih =>
      cases gate with
      | cnot => rfl
      | oneQubit gateWire gateWord =>
          cases next with
          | oneQubit nextWire nextWord =>
              by_cases hmove : gateWire = wire ∧ nextWire ≠ wire
              · simp [exposeWireInsert, hmove, ih]
              · simp [exposeWireInsert, hmove]
          | cnot control target hcontrolTarget =>
              by_cases hmove :
                  gateWire = wire ∧ wire ≠ control ∧ wire ≠ target
              · simp [exposeWireInsert, hmove, ih]
              · simp [exposeWireInsert, hmove]

@[simp]
theorem length_exposeWire {Atom : Type*} {n : ℕ} (wire : Fin n)
    (circuit : SymbolicCircuit Atom n) :
    (exposeWire wire circuit).length = circuit.length := by
  induction circuit with
  | nil => rfl
  | cons gate circuit ih =>
      rw [exposeWire, length_exposeWireInsert, ih]
      rfl

@[simp]
theorem gateCount_exposeWire {Atom : Type*} {n : ℕ} (wire : Fin n)
    (circuit : SymbolicCircuit Atom n) :
    gateCount (exposeWire wire circuit) = gateCount circuit := by
  exact length_exposeWire wire circuit

private theorem cnotTrace_exposeWireInsert {Atom : Type*} {n : ℕ}
    (wire : Fin n) (gate : SymbolicPrimitive Atom n) :
    ∀ circuit : SymbolicCircuit Atom n,
      cnotTrace (exposeWireInsert wire gate circuit) =
        cnotTrace (gate :: circuit) := by
  intro circuit
  induction circuit generalizing gate with
  | nil => cases gate <;> rfl
  | cons next circuit ih =>
      cases gate with
      | cnot => rfl
      | oneQubit gateWire gateWord =>
          cases next with
          | oneQubit nextWire nextWord =>
              by_cases hmove : gateWire = wire ∧ nextWire ≠ wire
              · simp [exposeWireInsert, hmove, ih, cnotTrace]
              · simp [exposeWireInsert, hmove, cnotTrace]
          | cnot control target hcontrolTarget =>
              by_cases hmove :
                  gateWire = wire ∧ wire ≠ control ∧ wire ≠ target
              · simp [exposeWireInsert, hmove, ih, cnotTrace]
              · simp [exposeWireInsert, hmove, cnotTrace]

/-- Exposure preserves every CNOT occurrence and its ordered endpoints exactly. -/
@[simp]
theorem cnotTrace_exposeWire {Atom : Type*} {n : ℕ} (wire : Fin n)
    (circuit : SymbolicCircuit Atom n) :
    cnotTrace (exposeWire wire circuit) = cnotTrace circuit := by
  induction circuit with
  | nil => rfl
  | cons gate circuit ih =>
      rw [exposeWire, cnotTrace_exposeWireInsert]
      cases gate <;> simp [ih]

@[simp]
theorem cnotCount_exposeWire {Atom : Type*} {n : ℕ} (wire : Fin n)
    (circuit : SymbolicCircuit Atom n) :
    cnotCount (exposeWire wire circuit) = cnotCount circuit := by
  rw [cnotCount_eq_length_cnotTrace, cnotCount_eq_length_cnotTrace,
    cnotTrace_exposeWire]

@[simp]
theorem oneQubitCount_exposeWire {Atom : Type*} {n : ℕ} (wire : Fin n)
    (circuit : SymbolicCircuit Atom n) :
    oneQubitCount (exposeWire wire circuit) = oneQubitCount circuit := by
  have htotal := gateCount_eq_componentCounts (exposeWire wire circuit)
  rw [gateCount_exposeWire, cnotCount_exposeWire] at htotal
  have horiginal := gateCount_eq_componentCounts circuit
  omega

/-- Exposure plus cancellation preserves the complete ordered CNOT trace. -/
@[simp]
theorem cnotTrace_normalizeAtWire {Atom : Type*} [DecidableEq Atom] {n : ℕ}
    (wire : Fin n) (circuit : SymbolicCircuit Atom n) :
    cnotTrace (normalizeAtWire wire circuit) = cnotTrace circuit := by
  simp [normalizeAtWire]

@[simp]
theorem cnotCount_normalizeAtWire {Atom : Type*} [DecidableEq Atom] {n : ℕ}
    (wire : Fin n) (circuit : SymbolicCircuit Atom n) :
    cnotCount (normalizeAtWire wire circuit) = cnotCount circuit := by
  rw [cnotCount_eq_length_cnotTrace, cnotCount_eq_length_cnotTrace,
    cnotTrace_normalizeAtWire]

/-- Target-directed symbolic normalization cannot increase one-qubit syntax. -/
theorem oneQubitCount_normalizeAtWire_le {Atom : Type*} [DecidableEq Atom]
    {n : ℕ} (wire : Fin n) (circuit : SymbolicCircuit Atom n) :
    oneQubitCount (normalizeAtWire wire circuit) ≤ oneQubitCount circuit := by
  rw [normalizeAtWire]
  exact (oneQubitCount_normalize_le (exposeWire wire circuit)).trans_eq
    (oneQubitCount_exposeWire wire circuit)

end SymbolicCircuit

end Barenco.Optimization
