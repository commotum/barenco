import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Bool.Basic
import Mathlib.Data.List.Basic

/-!
# Generic deterministic adjacent normalization

This low-dependency module supplies the terminating list engine used by later
circuit normalization policies.  It knows nothing about matrices, wires, or
quantum gates.  A caller supplies:

* an executable Boolean identity recognizer;
* an executable adjacent combiner; and
* proof-side certificates that those two functions preserve a group-valued
  chronological denotation.

Chronology is head-first.  If `first` executes before `second`, replacing the
pair by `fused` is sound exactly when
`denote fused = denote second * denote first`.

The engine normalizes the tail and then structurally inserts the earlier head.
Every recursive call consumes a proper list tail, so termination is independent
of the supplied rewrite functions.  Its exported stability statement is local:
no output node is recognized as identity and every adjacent output pair is
blocked by the supplied combiner.  This supports an exact fixed-point theorem
and idempotence, but deliberately makes no completeness, canonicality, or
minimality claim.
-/

namespace Barenco.Optimization.NormalizeCore

/-- Result of attempting one deterministic adjacent rewrite. -/
inductive CombineResult (α : Type*) where
  /-- The pair is retained in its original chronological order. -/
  | blocked
  /-- Both adjacent nodes are deleted. -/
  | deleted
  /-- Both adjacent nodes are replaced by one supplied node. -/
  | fused (gate : α)

namespace CombineResult

/--
Proof-side semantic contract for one combination result.

`first` executes before `second`, hence their chronological denotation is
`denote second * denote first`.
-/
def Sound {α G : Type*} [Group G] (denote : α → G)
    (first second : α) : CombineResult α → Prop
  | .blocked => True
  | .deleted => denote second * denote first = 1
  | .fused gate => denote gate = denote second * denote first

end CombineResult

/-- Head-first chronological evaluation into an arbitrary group. -/
def evalChronological {α G : Type*} [Group G]
    (denote : α → G) : List α → G
  | [] => 1
  | gate :: circuit => evalChronological denote circuit * denote gate

/--
Insert an earlier gate before an already normalized tail.

Identity deletion is driven only by the supplied Boolean.  A fused result is
reinserted into the strictly shorter remaining tail, allowing deterministic
cascading combinations without a fuel parameter.
-/
def insert {α : Type*} (isIdentity : α → Bool)
    (combine : α → α → CombineResult α) (gate : α) : List α → List α
  | [] => if isIdentity gate then [] else [gate]
  | next :: rest =>
      if isIdentity gate then next :: rest
      else
        match combine gate next with
        | .blocked => gate :: next :: rest
        | .deleted => rest
        | .fused fused => insert isIdentity combine fused rest

/-- Tail-first deterministic normalization. -/
def normalize {α : Type*} (isIdentity : α → Bool)
    (combine : α → α → CombineResult α) : List α → List α
  | [] => []
  | gate :: circuit =>
      insert isIdentity combine gate (normalize isIdentity combine circuit)

/-- Inserting one earlier gate preserves exact chronological denotation. -/
theorem evalChronological_insert {α G : Type*} [Group G]
    (denote : α → G) (isIdentity : α → Bool)
    (combine : α → α → CombineResult α)
    (identity_sound : ∀ gate, isIdentity gate = true → denote gate = 1)
    (combine_sound : ∀ first second,
      CombineResult.Sound denote first second (combine first second))
    (gate : α) (circuit : List α) :
    evalChronological denote (insert isIdentity combine gate circuit) =
      evalChronological denote circuit * denote gate := by
  induction circuit generalizing gate with
  | nil =>
      simp only [insert, evalChronological]
      split <;> rename_i hidentity
      · simp [identity_sound gate hidentity, evalChronological]
      · rfl
  | cons next rest ih =>
      simp only [insert]
      split <;> rename_i hidentity
      · simp only [evalChronological]
        rw [identity_sound gate hidentity, mul_one]
      · generalize hresult : combine gate next = result
        cases result with
        | blocked => rfl
        | deleted =>
            have hsound := combine_sound gate next
            rw [hresult] at hsound
            simp only [evalChronological]
            rw [mul_assoc, hsound, mul_one]
        | fused fused =>
            rw [ih]
            have hsound := combine_sound gate next
            rw [hresult] at hsound
            simp only [evalChronological]
            rw [hsound, mul_assoc]

/-- The complete normalization pass preserves exact chronological denotation. -/
theorem evalChronological_normalize {α G : Type*} [Group G]
    (denote : α → G) (isIdentity : α → Bool)
    (combine : α → α → CombineResult α)
    (identity_sound : ∀ gate, isIdentity gate = true → denote gate = 1)
    (combine_sound : ∀ first second,
      CombineResult.Sound denote first second (combine first second)) :
    ∀ circuit,
      evalChronological denote (normalize isIdentity combine circuit) =
        evalChronological denote circuit := by
  intro circuit
  induction circuit with
  | nil => rfl
  | cons gate circuit ih =>
      rw [normalize,
        evalChronological_insert denote isIdentity combine
          identity_sound combine_sound,
        ih]
      rfl

/-- Inserting one gate never creates more than one net syntax occurrence. -/
theorem length_insert_le {α : Type*} (isIdentity : α → Bool)
    (combine : α → α → CombineResult α) (gate : α) :
    ∀ circuit,
      (insert isIdentity combine gate circuit).length ≤ circuit.length + 1 := by
  intro circuit
  induction circuit generalizing gate with
  | nil =>
      by_cases hidentity : isIdentity gate = true <;>
        simp [insert, hidentity]
  | cons next rest ih =>
      simp only [insert]
      split
      · simp
      · generalize combine gate next = result
        cases result with
        | blocked => simp
        | deleted =>
            simp only [List.length_cons]
            rw [Nat.add_assoc]
            exact Nat.le_add_right rest.length 2
        | fused fused =>
            have hle := ih fused
            simp only [List.length_cons]
            exact Nat.le_trans hle (Nat.le_add_right _ 1)

/-- Normalization never increases literal list length. -/
theorem length_normalize_le {α : Type*} (isIdentity : α → Bool)
    (combine : α → α → CombineResult α) :
    ∀ circuit,
      (normalize isIdentity combine circuit).length ≤ circuit.length := by
  intro circuit
  induction circuit with
  | nil => exact Nat.le_refl 0
  | cons gate circuit ih =>
      rw [normalize]
      have hins := length_insert_le isIdentity combine gate
        (normalize isIdentity combine circuit)
      simp only [List.length_cons]
      exact Nat.le_trans hins (Nat.add_le_add_right ih 1)

/--
Exact local fixed-point predicate: no identity-recognized node remains and every
adjacent pair is blocked by the supplied combination policy.
-/
def Stable {α : Type*} (isIdentity : α → Bool)
    (combine : α → α → CombineResult α) : List α → Prop
  | [] => True
  | [gate] => isIdentity gate = false
  | first :: second :: rest =>
      isIdentity first = false ∧
        combine first second = .blocked ∧
        Stable isIdentity combine (second :: rest)

/-- Every tail of a stable nonempty list is stable. -/
theorem Stable.tail {α : Type*} {isIdentity : α → Bool}
    {combine : α → α → CombineResult α} :
    ∀ {first : α} {circuit : List α},
      Stable isIdentity combine (first :: circuit) →
        Stable isIdentity combine circuit := by
  intro first circuit hstable
  cases circuit with
  | nil => trivial
  | cons second rest =>
      cases rest with
      | nil => exact hstable.2.2
      | cons third rest => exact hstable.2.2

/-- The head of every stable nonempty list is not recognized as identity. -/
theorem Stable.head_not_identity {α : Type*}
    {isIdentity : α → Bool}
    {combine : α → α → CombineResult α} :
    ∀ {first : α} {circuit : List α},
      Stable isIdentity combine (first :: circuit) →
        isIdentity first = false := by
  intro first circuit hstable
  cases circuit with
  | nil => exact hstable
  | cons second rest => exact hstable.1

/-- Insertion into a stable tail produces another stable list. -/
theorem insert_stable {α : Type*} (isIdentity : α → Bool)
    (combine : α → α → CombineResult α) (gate : α) :
    ∀ {circuit : List α}, Stable isIdentity combine circuit →
      Stable isIdentity combine (insert isIdentity combine gate circuit) := by
  intro circuit hstable
  induction circuit generalizing gate with
  | nil =>
      simp only [insert]
      split <;> rename_i hidentity
      · trivial
      · exact Bool.eq_false_of_not_eq_true hidentity
  | cons next rest ih =>
      simp only [insert]
      split <;> rename_i hidentity
      · exact hstable
      · generalize hresult : combine gate next = result
        cases result with
        | blocked =>
            exact ⟨Bool.eq_false_of_not_eq_true hidentity, hresult, hstable⟩
        | deleted => exact Stable.tail hstable
        | fused fused => exact ih fused (Stable.tail hstable)

/-- Every normalization output satisfies the exact local stability predicate. -/
theorem normalize_stable {α : Type*} (isIdentity : α → Bool)
    (combine : α → α → CombineResult α) :
    ∀ circuit, Stable isIdentity combine (normalize isIdentity combine circuit) := by
  intro circuit
  induction circuit with
  | nil => trivial
  | cons gate circuit ih =>
      rw [normalize]
      exact insert_stable isIdentity combine gate ih

/-- Stable lists are exact fixed points of normalization. -/
theorem normalize_eq_self_of_stable {α : Type*}
    (isIdentity : α → Bool)
    (combine : α → α → CombineResult α) :
    ∀ {circuit}, Stable isIdentity combine circuit →
      normalize isIdentity combine circuit = circuit := by
  intro circuit hstable
  induction circuit with
  | nil => rfl
  | cons gate circuit ih =>
      rw [normalize, ih (Stable.tail hstable)]
      cases circuit with
      | nil =>
          simp only [insert]
          rw [Stable.head_not_identity hstable]
          rfl
      | cons next rest =>
          simp only [insert]
          rw [Stable.head_not_identity hstable, hstable.2.1]
          rfl

/-- Deterministic normalization is idempotent. -/
@[simp]
theorem normalize_idempotent {α : Type*} (isIdentity : α → Bool)
    (combine : α → α → CombineResult α) (circuit : List α) :
    normalize isIdentity combine (normalize isIdentity combine circuit) =
      normalize isIdentity combine circuit :=
  normalize_eq_self_of_stable isIdentity combine
    (normalize_stable isIdentity combine circuit)

end Barenco.Optimization.NormalizeCore
