import Barenco.Optimization.NormalizeCore
import Barenco.Optimization.FusionLaws
import Barenco.Optimization.FusionResources
import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# Executable symbolic cancellation for one-qubit gates

Arbitrary complex unitary matrices do not have a computational equality test.
This module therefore keeps one-qubit payload provenance in a free group over a
decidable atom type.  A valuation interprets each atom as a certified one-qubit
unitary, while the free-group word supplies executable, exact syntactic
identity and inverse cancellation without inspecting matrix entries.

The supported early-model syntax consists only of symbolic one-qubit words and
literal CNOT nodes.  Normalization combines adjacent words on the same wire in
head-first chronological order and deletes a word exactly when the reduced free
group recognizes it as identity.  CNOT pairs are always blocked: CNOT nodes,
their order, and their exact count are preserved.
-/

namespace Barenco.Optimization

open Barenco

/-- A decidable symbolic word of one-qubit atoms and formal inverses. -/
abbrev QubitWord (Atom : Type*) := FreeGroup Atom

namespace QubitWord

/-- Interpret a symbolic word under a certified one-qubit valuation. -/
def evaluate (valuation : Atom → QubitUnitary)
    (word : QubitWord Atom) : QubitUnitary :=
  FreeGroup.lift valuation word

@[simp]
theorem evaluate_of (valuation : Atom → QubitUnitary) (atom : Atom) :
    evaluate valuation (FreeGroup.of atom) = valuation atom := by
  exact FreeGroup.lift_apply_of

@[simp]
theorem evaluate_one (valuation : Atom → QubitUnitary) :
    evaluate valuation (1 : QubitWord Atom) = 1 := by
  exact map_one (FreeGroup.lift valuation)

@[simp]
theorem evaluate_mul (valuation : Atom → QubitUnitary)
    (first second : QubitWord Atom) :
    evaluate valuation (first * second) =
      evaluate valuation first * evaluate valuation second := by
  exact map_mul (FreeGroup.lift valuation) first second

@[simp]
theorem evaluate_inv (valuation : Atom → QubitUnitary)
    (word : QubitWord Atom) :
    evaluate valuation word⁻¹ = (evaluate valuation word)⁻¹ := by
  exact map_inv (FreeGroup.lift valuation) word

end QubitWord

/--
Early-model syntax retaining symbolic one-qubit provenance and literal CNOTs.
There is deliberately no arbitrary-two-qubit constructor.
-/
inductive SymbolicPrimitive (Atom : Type*) (n : ℕ) where
  | oneQubit (target : Fin n) (word : QubitWord Atom)
  | cnot (control target : Fin n) (hcontrolTarget : control ≠ target)

namespace SymbolicPrimitive

/-- Interpret one symbolic node as payload-preserving visible circuit syntax. -/
def erase (valuation : Atom → QubitUnitary) :
    SymbolicPrimitive Atom n → FusionPrimitive n
  | .oneQubit target word =>
      .oneQubit target (QubitWord.evaluate valuation word)
  | .cnot control target h => .cnot control target h

@[simp]
theorem erase_oneQubit (valuation : Atom → QubitUnitary)
    (target : Fin n) (word : QubitWord Atom) :
    erase valuation (.oneQubit target word) =
      .oneQubit target (QubitWord.evaluate valuation word) := rfl

@[simp]
theorem erase_cnot (valuation : Atom → QubitUnitary)
    (control target : Fin n) (h : control ≠ target) :
    erase valuation (.cnot control target h) = .cnot control target h := rfl

/-- Exact full-register denotation obtained after valuation and erasure. -/
def denotation (valuation : Atom → QubitUnitary)
    (primitive : SymbolicPrimitive Atom n) : UnitaryGate n :=
  (erase valuation primitive).denotation

/--
Executable identity recognizer.  CNOT is never an identity for normalization
purposes, even when it is adjacent to an identical CNOT.
-/
def isIdentity [DecidableEq Atom] : SymbolicPrimitive Atom n → Bool
  | .oneQubit _ word => decide (word = 1)
  | .cnot _ _ _ => false

/--
Combine adjacent same-wire one-qubit words in chronological order.  Every pair
containing a CNOT is blocked, so this layer never cancels CNOT pairs.
-/
def combine [DecidableEq Atom] :
    SymbolicPrimitive Atom n → SymbolicPrimitive Atom n →
      NormalizeCore.CombineResult (SymbolicPrimitive Atom n)
  | .oneQubit firstTarget firstWord,
      .oneQubit secondTarget secondWord =>
      if firstTarget = secondTarget then
        .fused (.oneQubit firstTarget (secondWord * firstWord))
      else .blocked
  | _, _ => .blocked

/-- A positive symbolic atom on one wire. -/
def atom (target : Fin n) (name : Atom) : SymbolicPrimitive Atom n :=
  .oneQubit target (FreeGroup.of name)

/-- The formal inverse of one symbolic atom on one wire. -/
def inverseAtom (target : Fin n) (name : Atom) : SymbolicPrimitive Atom n :=
  .oneQubit target (FreeGroup.of name)⁻¹

private theorem localUnitary_one (target : Fin n) :
    localUnitary target (1 : QubitUnitary) = 1 := by
  apply Subtype.ext
  change Matrix.reindexAlgEquiv ℂ ℂ (splitTarget target).symm
      (Matrix.blockDiagonal (1 : ComplementBasis target → QubitMatrix)) = 1
  rw [Matrix.blockDiagonal_one, map_one]

/-- The symbolic identity recognizer is semantically exact under every valuation. -/
theorem isIdentity_sound [DecidableEq Atom]
    (valuation : Atom → QubitUnitary) :
    ∀ primitive : SymbolicPrimitive Atom n,
      isIdentity primitive = true → denotation valuation primitive = 1 := by
  intro primitive hidentity
  cases primitive with
  | oneQubit target word =>
      simp only [isIdentity, decide_eq_true_eq] at hidentity
      subst word
      change localUnitary target (QubitWord.evaluate valuation 1) = 1
      rw [QubitWord.evaluate_one]
      exact localUnitary_one target
  | cnot control target h =>
      simp [isIdentity] at hidentity

/-- The adjacent symbolic combiner satisfies NormalizeCore's exact group contract. -/
theorem combine_sound [DecidableEq Atom]
    (valuation : Atom → QubitUnitary) :
    ∀ first second : SymbolicPrimitive Atom n,
      NormalizeCore.CombineResult.Sound (denotation valuation)
        first second (combine first second) := by
  intro first second
  cases first with
  | oneQubit firstTarget firstWord =>
      cases second with
      | oneQubit secondTarget secondWord =>
          simp only [combine]
          split <;> rename_i htarget
          · subst secondTarget
            simp only [NormalizeCore.CombineResult.Sound, denotation,
              erase_oneQubit, FusionPrimitive.denotation,
              QubitWord.evaluate_mul]
            exact oneQubit_chronological firstTarget
              (QubitWord.evaluate valuation firstWord)
              (QubitWord.evaluate valuation secondWord)
          · trivial
      | cnot control target h => trivial
  | cnot control target h =>
      cases second <;> trivial

end SymbolicPrimitive

/-- A chronological list of symbolic one-qubit words and literal CNOTs. -/
abbrev SymbolicCircuit (Atom : Type*) (n : ℕ) :=
  List (SymbolicPrimitive Atom n)

namespace SymbolicCircuit

/-- Interpret every symbolic node as a visible fusion node. -/
def erase (valuation : Atom → QubitUnitary)
    (circuit : SymbolicCircuit Atom n) : FusionCircuit n :=
  circuit.map (SymbolicPrimitive.erase valuation)

@[simp]
theorem erase_nil (valuation : Atom → QubitUnitary) :
    erase valuation ([] : SymbolicCircuit Atom n) = [] := rfl

@[simp]
theorem erase_cons (valuation : Atom → QubitUnitary)
    (primitive : SymbolicPrimitive Atom n) (circuit : SymbolicCircuit Atom n) :
    erase valuation (primitive :: circuit) =
      SymbolicPrimitive.erase valuation primitive :: erase valuation circuit := rfl

/-- Executable adjacent symbolic normalization. -/
def normalize [DecidableEq Atom] (circuit : SymbolicCircuit Atom n) :
    SymbolicCircuit Atom n :=
  NormalizeCore.normalize SymbolicPrimitive.isIdentity
    SymbolicPrimitive.combine circuit

/-- A word already equal to identity is deleted without consulting its valuation. -/
@[simp]
theorem normalize_identity_singleton [DecidableEq Atom] (target : Fin n) :
    normalize [SymbolicPrimitive.oneQubit target (1 : QubitWord Atom)] = [] := by
  simp [normalize, NormalizeCore.normalize, NormalizeCore.insert,
    SymbolicPrimitive.isIdentity]

/-- An atom followed by its formal inverse cancels syntactically and exactly. -/
@[simp]
theorem normalize_atom_inverse [DecidableEq Atom]
    (target : Fin n) (name : Atom) :
    normalize
        [SymbolicPrimitive.atom target name,
          SymbolicPrimitive.inverseAtom target name] = [] := by
  simp [normalize, NormalizeCore.normalize, NormalizeCore.insert,
    SymbolicPrimitive.isIdentity, SymbolicPrimitive.combine,
    SymbolicPrimitive.atom, SymbolicPrimitive.inverseAtom]

/-- The reverse inverse/atom chronology also cancels syntactically. -/
@[simp]
theorem normalize_inverse_atom [DecidableEq Atom]
    (target : Fin n) (name : Atom) :
    normalize
        [SymbolicPrimitive.inverseAtom target name,
          SymbolicPrimitive.atom target name] = [] := by
  simp [normalize, NormalizeCore.normalize, NormalizeCore.insert,
    SymbolicPrimitive.isIdentity, SymbolicPrimitive.combine,
    SymbolicPrimitive.atom, SymbolicPrimitive.inverseAtom]

/-- Identical adjacent CNOTs are deliberately retained, not cancelled. -/
@[simp]
theorem normalize_cnot_pair [DecidableEq Atom]
    (control target : Fin n) (h : control ≠ target) :
    normalize
        [SymbolicPrimitive.cnot control target h,
          SymbolicPrimitive.cnot control target h] =
      [SymbolicPrimitive.cnot control target h,
        SymbolicPrimitive.cnot control target h] := by
  change normalize
      ([SymbolicPrimitive.cnot control target h,
        SymbolicPrimitive.cnot control target h] : SymbolicCircuit Atom n) = _
  rfl

/-- Exact local fixed-point predicate for the symbolic normalization policy. -/
def Stable [DecidableEq Atom] (circuit : SymbolicCircuit Atom n) : Prop :=
  NormalizeCore.Stable SymbolicPrimitive.isIdentity
    SymbolicPrimitive.combine circuit

/-- Literal number of symbolic primitive occurrences. -/
def gateCount (circuit : SymbolicCircuit Atom n) : ℕ := circuit.length

/-- One if the node is a symbolic one-qubit word and zero for a CNOT. -/
def oneQubitWeight : SymbolicPrimitive Atom n → ℕ
  | .oneQubit _ _ => 1
  | .cnot _ _ _ => 0

/-- One if the node is a literal CNOT and zero for a one-qubit word. -/
def cnotWeight : SymbolicPrimitive Atom n → ℕ
  | .oneQubit _ _ => 0
  | .cnot _ _ _ => 1

/-- Literal number of symbolic one-qubit nodes. -/
def oneQubitCount (circuit : SymbolicCircuit Atom n) : ℕ :=
  circuit.foldr (fun primitive count => oneQubitWeight primitive + count) 0

/-- Literal number of CNOT nodes. -/
def cnotCount (circuit : SymbolicCircuit Atom n) : ℕ :=
  circuit.foldr (fun primitive count => cnotWeight primitive + count) 0

@[simp]
theorem gateCount_nil : gateCount ([] : SymbolicCircuit Atom n) = 0 := rfl

@[simp]
theorem gateCount_cons (primitive : SymbolicPrimitive Atom n)
    (circuit : SymbolicCircuit Atom n) :
    gateCount (primitive :: circuit) = gateCount circuit + 1 := by
  simp [gateCount]

@[simp]
theorem oneQubitCount_nil : oneQubitCount ([] : SymbolicCircuit Atom n) = 0 := rfl

@[simp]
theorem oneQubitCount_cons (primitive : SymbolicPrimitive Atom n)
    (circuit : SymbolicCircuit Atom n) :
    oneQubitCount (primitive :: circuit) =
      oneQubitWeight primitive + oneQubitCount circuit := rfl

@[simp]
theorem cnotCount_nil : cnotCount ([] : SymbolicCircuit Atom n) = 0 := rfl

@[simp]
theorem cnotCount_cons (primitive : SymbolicPrimitive Atom n)
    (circuit : SymbolicCircuit Atom n) :
    cnotCount (primitive :: circuit) =
      cnotWeight primitive + cnotCount circuit := rfl

/-- Every symbolic node belongs to exactly one supported early-model class. -/
theorem gateCount_eq_componentCounts (circuit : SymbolicCircuit Atom n) :
    gateCount circuit = oneQubitCount circuit + cnotCount circuit := by
  induction circuit with
  | nil => rfl
  | cons primitive circuit ih =>
      cases primitive <;>
        simp [gateCount, oneQubitCount, oneQubitWeight,
          cnotCount, cnotWeight] at ih ⊢ <;>
        omega

/-! ## Exact erasure resources -/

@[simp]
theorem erase_gateCount (valuation : Atom → QubitUnitary)
    (circuit : SymbolicCircuit Atom n) :
    FusionCircuit.gateCount (erase valuation circuit) = gateCount circuit := by
  simp [FusionCircuit.gateCount, erase, gateCount]

@[simp]
theorem erase_oneQubitCount (valuation : Atom → QubitUnitary)
    (circuit : SymbolicCircuit Atom n) :
    FusionCircuit.oneQubitCount (erase valuation circuit) =
      oneQubitCount circuit := by
  induction circuit with
  | nil => rfl
  | cons primitive circuit ih =>
      rw [erase_cons]
      change FusionCircuit.kindCount .oneQubit
          (SymbolicPrimitive.erase valuation primitive :: erase valuation circuit) =
        oneQubitWeight primitive + oneQubitCount circuit
      rw [FusionCircuit.kindCount_cons]
      change FusionCircuit.oneQubitCount (erase valuation circuit) +
          (if (SymbolicPrimitive.erase valuation primitive).kind = .oneQubit
            then 1 else 0) =
        oneQubitWeight primitive + oneQubitCount circuit
      rw [ih]
      cases primitive <;> simp [SymbolicPrimitive.erase,
        FusionPrimitive.kind, oneQubitWeight]
      all_goals omega

@[simp]
theorem erase_cnotCount (valuation : Atom → QubitUnitary)
    (circuit : SymbolicCircuit Atom n) :
    FusionCircuit.cnotCount (erase valuation circuit) = cnotCount circuit := by
  induction circuit with
  | nil => rfl
  | cons primitive circuit ih =>
      rw [erase_cons]
      change FusionCircuit.kindCount .cnot
          (SymbolicPrimitive.erase valuation primitive :: erase valuation circuit) =
        cnotWeight primitive + cnotCount circuit
      rw [FusionCircuit.kindCount_cons]
      change FusionCircuit.cnotCount (erase valuation circuit) +
          (if (SymbolicPrimitive.erase valuation primitive).kind = .cnot
            then 1 else 0) =
        cnotWeight primitive + cnotCount circuit
      rw [ih]
      cases primitive <;> simp [SymbolicPrimitive.erase,
        FusionPrimitive.kind, cnotWeight]
      all_goals omega

@[simp]
theorem erase_twoQubitCount (valuation : Atom → QubitUnitary)
    (circuit : SymbolicCircuit Atom n) :
    FusionCircuit.twoQubitCount (erase valuation circuit) = 0 := by
  induction circuit with
  | nil => rfl
  | cons primitive circuit ih =>
      rw [erase_cons]
      change FusionCircuit.kindCount .arbitraryTwoQubit
          (SymbolicPrimitive.erase valuation primitive :: erase valuation circuit) = 0
      rw [FusionCircuit.kindCount_cons]
      change FusionCircuit.twoQubitCount (erase valuation circuit) +
          (if (SymbolicPrimitive.erase valuation primitive).kind =
              .arbitraryTwoQubit then 1 else 0) = 0
      rw [ih]
      cases primitive <;> rfl

/-- Every erased symbolic circuit is accepted by the one-qubit/CNOT model. -/
@[simp]
theorem erase_oneQubitCNOTCost (valuation : Atom → QubitUnitary)
    (circuit : SymbolicCircuit Atom n) :
    FusionCircuit.cost CostModel.oneQubitCNOT (erase valuation circuit) =
      some (gateCount circuit) := by
  rw [FusionCircuit.oneQubitCNOT_cost_eq, erase_twoQubitCount,
    if_pos rfl, erase_gateCount]

/-! ## Exact semantic soundness -/

private theorem evalChronological_eq_eval_erase
    (valuation : Atom → QubitUnitary)
    (circuit : SymbolicCircuit Atom n) :
    NormalizeCore.evalChronological
        (SymbolicPrimitive.denotation valuation) circuit =
      FusionCircuit.eval (erase valuation circuit) := by
  induction circuit with
  | nil => rfl
  | cons primitive circuit ih =>
      simp [NormalizeCore.evalChronological, erase,
        SymbolicPrimitive.denotation, ih]

/-- Symbolic normalization preserves exact arbitrary-register evaluation. -/
theorem eval_erase_normalize [DecidableEq Atom]
    (valuation : Atom → QubitUnitary)
    (circuit : SymbolicCircuit Atom n) :
    FusionCircuit.eval (erase valuation (normalize circuit)) =
      FusionCircuit.eval (erase valuation circuit) := by
  rw [← evalChronological_eq_eval_erase,
    ← evalChronological_eq_eval_erase]
  exact NormalizeCore.evalChronological_normalize
    (SymbolicPrimitive.denotation valuation)
    SymbolicPrimitive.isIdentity SymbolicPrimitive.combine
    (SymbolicPrimitive.isIdentity_sound valuation)
    (SymbolicPrimitive.combine_sound valuation) circuit

/-- The same exact soundness statement after trusted lowering to `Circuit`. -/
theorem eval_lower_erase_normalize [DecidableEq Atom]
    (valuation : Atom → QubitUnitary)
    (circuit : SymbolicCircuit Atom n) :
    Circuit.eval (FusionCircuit.lower (erase valuation (normalize circuit))) =
      Circuit.eval (FusionCircuit.lower (erase valuation circuit)) := by
  simp only [FusionCircuit.eval_lower]
  exact eval_erase_normalize valuation circuit

/-! ## CNOT preservation and total-count behavior -/

private theorem cnotCount_insert [DecidableEq Atom]
    (primitive : SymbolicPrimitive Atom n) :
    ∀ circuit : SymbolicCircuit Atom n,
      cnotCount
          (NormalizeCore.insert SymbolicPrimitive.isIdentity
            SymbolicPrimitive.combine primitive circuit) =
        cnotWeight primitive + cnotCount circuit := by
  intro circuit
  induction circuit generalizing primitive with
  | nil =>
      cases primitive with
      | oneQubit target word =>
          by_cases hidentity : word = 1 <;>
            simp [NormalizeCore.insert, SymbolicPrimitive.isIdentity,
              hidentity, cnotCount, cnotWeight]
      | cnot control target h =>
          simp [NormalizeCore.insert, SymbolicPrimitive.isIdentity,
            cnotCount, cnotWeight]
  | cons next rest ih =>
      cases primitive with
      | oneQubit target word =>
          cases next with
          | oneQubit nextTarget nextWord =>
              by_cases hidentity : word = 1
              · simp [NormalizeCore.insert, SymbolicPrimitive.isIdentity,
                  hidentity, cnotCount, cnotWeight]
              · by_cases htarget : target = nextTarget
                · have hfused :=
                    ih (SymbolicPrimitive.oneQubit target (nextWord * word))
                  simpa [NormalizeCore.insert, SymbolicPrimitive.isIdentity,
                    SymbolicPrimitive.combine, hidentity, htarget,
                    cnotCount, cnotWeight] using hfused
                · simp [NormalizeCore.insert, SymbolicPrimitive.isIdentity,
                    SymbolicPrimitive.combine, hidentity, htarget,
                    cnotCount, cnotWeight]
          | cnot control nextTarget h =>
              by_cases hidentity : word = 1 <;>
                simp [NormalizeCore.insert, SymbolicPrimitive.isIdentity,
                  SymbolicPrimitive.combine, hidentity, cnotCount, cnotWeight]
      | cnot control target h =>
          cases next <;>
            simp [NormalizeCore.insert, SymbolicPrimitive.isIdentity,
              SymbolicPrimitive.combine, cnotCount, cnotWeight]

/-- Normalization preserves the exact number of literal CNOT nodes. -/
@[simp]
theorem cnotCount_normalize [DecidableEq Atom]
    (circuit : SymbolicCircuit Atom n) :
    cnotCount (normalize circuit) = cnotCount circuit := by
  induction circuit with
  | nil => rfl
  | cons primitive circuit ih =>
      have ih' :
          cnotCount
              (NormalizeCore.normalize SymbolicPrimitive.isIdentity
                SymbolicPrimitive.combine circuit) = cnotCount circuit := by
        simpa only [normalize] using ih
      rw [normalize, NormalizeCore.normalize, cnotCount_insert, ih']
      rfl

/-- Normalization never increases the total number of literal nodes. -/
theorem gateCount_normalize_le [DecidableEq Atom]
    (circuit : SymbolicCircuit Atom n) :
    gateCount (normalize circuit) ≤ gateCount circuit := by
  exact NormalizeCore.length_normalize_le
    SymbolicPrimitive.isIdentity SymbolicPrimitive.combine circuit

/-- Consequently normalization never increases symbolic one-qubit count. -/
theorem oneQubitCount_normalize_le [DecidableEq Atom]
    (circuit : SymbolicCircuit Atom n) :
    oneQubitCount (normalize circuit) ≤ oneQubitCount circuit := by
  have htotal := gateCount_normalize_le circuit
  rw [gateCount_eq_componentCounts, gateCount_eq_componentCounts,
    cnotCount_normalize] at htotal
  omega

/-! ## Stability and repeatability -/

/-- Every symbolic normalization output is locally stable. -/
theorem normalize_stable [DecidableEq Atom]
    (circuit : SymbolicCircuit Atom n) : Stable (normalize circuit) :=
  NormalizeCore.normalize_stable SymbolicPrimitive.isIdentity
    SymbolicPrimitive.combine circuit

/-- A stable symbolic circuit is an exact fixed point. -/
theorem normalize_eq_self_of_stable [DecidableEq Atom]
    {circuit : SymbolicCircuit Atom n} (hstable : Stable circuit) :
    normalize circuit = circuit :=
  NormalizeCore.normalize_eq_self_of_stable
    SymbolicPrimitive.isIdentity SymbolicPrimitive.combine hstable

/-- Symbolic normalization is executable and idempotent. -/
@[simp]
theorem normalize_idempotent [DecidableEq Atom]
    (circuit : SymbolicCircuit Atom n) :
    normalize (normalize circuit) = normalize circuit :=
  NormalizeCore.normalize_idempotent
    SymbolicPrimitive.isIdentity SymbolicPrimitive.combine circuit

end SymbolicCircuit

end Barenco.Optimization
