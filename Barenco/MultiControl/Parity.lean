import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Data.Nat.Choose.Sum

/-!
# Finite XOR parity and the alternating subset identity

This file isolates the representation-independent arithmetic behind the
Gray-code constructions of Barenco et al.  A mask is an arbitrary finite set of
controls, and `xorParity mask bits` is their Boolean XOR.  The signed contribution
of a nonempty mask `mask` is

`(-1) ^ (mask.card - 1) * xorParity(mask)`.

The main theorem proves that summing these contributions over all nonempty
subsets of a nonempty control set gives `2 ^ (card - 1)` exactly when every
control bit is true, and gives zero otherwise.  No ordering or concrete
enumeration of the controls is used.
-/

namespace Barenco.MultiControl

open scoped BigOperators

section

variable {ι : Type*}

/-- Boolean XOR of the input bits selected by a finite mask. -/
def xorParity (mask : Finset ι) (bits : ι → Bool) : Bool :=
  ∑ control ∈ mask, bits control

@[simp]
theorem xorParity_empty (bits : ι → Bool) :
    xorParity (∅ : Finset ι) bits = false := by
  simp [xorParity, Bool.zero_eq_false]

@[simp]
theorem xorParity_insert {mask : Finset ι} {control : ι}
    [DecidableEq ι] (hcontrol : control ∉ mask) (bits : ι → Bool) :
    xorParity (insert control mask) bits = bits control + xorParity mask bits := by
  simp [xorParity, hcontrol]

/-- Interpret a Boolean as the integer `0` or `1`. -/
def boolInt (bit : Bool) : ℤ :=
  if bit then 1 else 0

@[simp]
theorem boolInt_false : boolInt false = 0 := rfl

@[simp]
theorem boolInt_true : boolInt true = 1 := rfl

@[simp]
theorem boolInt_zero : boolInt (0 : Bool) = 0 := rfl

/-- XOR with a false bit does not change the integer parity indicator. -/
@[simp]
theorem boolInt_false_add (bit : Bool) :
    boolInt (false + bit) = boolInt bit := by
  cases bit <;> rfl

/-- XOR with a true bit complements the integer parity indicator. -/
@[simp]
theorem boolInt_true_add (bit : Bool) :
    boolInt (true + bit) = 1 - boolInt bit := by
  cases bit <;> rfl

/-- Integer indicator of odd parity on a finite mask. -/
def xorParityInt (mask : Finset ι) (bits : ι → Bool) : ℤ :=
  boolInt (xorParity mask bits)

@[simp]
theorem xorParityInt_empty (bits : ι → Bool) :
    xorParityInt (∅ : Finset ι) bits = 0 := by
  simp [xorParityInt]

/--
The alternating integer contribution attached to a subset.

For nonempty `mask` this is the paper's coefficient
`(-1)^(mask.card-1)` times its XOR parity.  The same total definition is useful
at the empty set, where the parity indicator makes the contribution zero.
-/
def signedParityContribution (mask : Finset ι) (bits : ι → Bool) : ℤ :=
  (-1 : ℤ) ^ (mask.card - 1) * xorParityInt mask bits

@[simp]
theorem signedParityContribution_empty (bits : ι → Bool) :
    signedParityContribution (∅ : Finset ι) bits = 0 := by
  simp [signedParityContribution]

/-- Raising `-1` to a positive cardinality flips the predecessor sign. -/
theorem neg_one_pow_card_eq_neg_pred {mask : Finset ι} (hmask : mask.Nonempty) :
    (-1 : ℤ) ^ mask.card = -((-1 : ℤ) ^ (mask.card - 1)) := by
  obtain ⟨card, hcard⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Finset.card_ne_zero.mpr hmask)
  rw [hcard]
  simp [pow_succ]

/--
Adding a selected false bit pairs every subset contribution with its additive
inverse.
-/
theorem signedParityContribution_insert_false {mask : Finset ι} {control : ι}
    [DecidableEq ι] (hcontrol : control ∉ mask) (bits : ι → Bool)
    (hbit : bits control = false) :
    signedParityContribution (insert control mask) bits =
      -signedParityContribution mask bits := by
  by_cases hmask : mask = ∅
  · subst mask
    simp [signedParityContribution, xorParityInt, xorParity, hbit]
  · have hmaskNonempty : mask.Nonempty := Finset.nonempty_iff_ne_empty.mpr hmask
    rw [signedParityContribution, signedParityContribution,
      Finset.card_insert_of_notMem hcontrol, Nat.succ_sub_one,
      xorParityInt, xorParity_insert hcontrol, hbit, boolInt_false_add,
      neg_one_pow_card_eq_neg_pred hmaskNonempty]
    simp only [xorParityInt]
    ring

/--
Adding a selected true bit contributes the old term plus the ordinary
alternating sign `(-1)^card`.
-/
theorem signedParityContribution_insert_true {mask : Finset ι} {control : ι}
    [DecidableEq ι] (hcontrol : control ∉ mask) (bits : ι → Bool)
    (hbit : bits control = true) :
    signedParityContribution (insert control mask) bits =
      signedParityContribution mask bits + (-1 : ℤ) ^ mask.card := by
  by_cases hmask : mask = ∅
  · subst mask
    simp [signedParityContribution, xorParityInt, xorParity, hbit]
  · have hmaskNonempty : mask.Nonempty := Finset.nonempty_iff_ne_empty.mpr hmask
    rw [signedParityContribution, signedParityContribution,
      Finset.card_insert_of_notMem hcontrol, Nat.succ_sub_one,
      xorParityInt, xorParity_insert hcontrol, hbit, boolInt_true_add,
      neg_one_pow_card_eq_neg_pred hmaskNonempty]
    simp only [xorParityInt]
    ring

/-- Auxiliary sum over the whole powerset; the empty contribution is zero. -/
def allSubsetParitySum [DecidableEq ι]
    (controls : Finset ι) (bits : ι → Bool) : ℤ :=
  ∑ mask ∈ controls.powerset, signedParityContribution mask bits

@[simp]
theorem allSubsetParitySum_empty [DecidableEq ι] (bits : ι → Bool) :
    allSubsetParitySum (∅ : Finset ι) bits = 0 := by
  simp [allSubsetParitySum]

/-- A false inserted control makes the two halves of the powerset sum cancel. -/
theorem allSubsetParitySum_insert_false {controls : Finset ι} {control : ι}
    [DecidableEq ι] (hcontrol : control ∉ controls) (bits : ι → Bool)
    (hbit : bits control = false) :
    allSubsetParitySum (insert control controls) bits = 0 := by
  rw [allSubsetParitySum, Finset.sum_powerset_insert hcontrol]
  have hinsert :
      (∑ mask ∈ controls.powerset,
          signedParityContribution (insert control mask) bits) =
        ∑ mask ∈ controls.powerset, -signedParityContribution mask bits := by
    apply Finset.sum_congr rfl
    intro mask hmask
    exact signedParityContribution_insert_false
      (Finset.notMem_mono (Finset.mem_powerset.mp hmask) hcontrol) bits hbit
  rw [hinsert]
  simp [allSubsetParitySum]

/--
A true inserted control doubles the previous parity sum and adds the ordinary
alternating powerset sum.
-/
theorem allSubsetParitySum_insert_true {controls : Finset ι} {control : ι}
    [DecidableEq ι] (hcontrol : control ∉ controls) (bits : ι → Bool)
    (hbit : bits control = true) :
    allSubsetParitySum (insert control controls) bits =
      2 * allSubsetParitySum controls bits +
        ∑ mask ∈ controls.powerset, (-1 : ℤ) ^ mask.card := by
  rw [allSubsetParitySum, Finset.sum_powerset_insert hcontrol]
  have hinsert :
      (∑ mask ∈ controls.powerset,
          signedParityContribution (insert control mask) bits) =
        ∑ mask ∈ controls.powerset,
          (signedParityContribution mask bits + (-1 : ℤ) ^ mask.card) := by
    apply Finset.sum_congr rfl
    intro mask hmask
    exact signedParityContribution_insert_true
      (Finset.notMem_mono (Finset.mem_powerset.mp hmask) hcontrol) bits hbit
  rw [hinsert]
  rw [Finset.sum_add_distrib]
  change allSubsetParitySum controls bits +
      (allSubsetParitySum controls bits +
        ∑ mask ∈ controls.powerset, (-1 : ℤ) ^ mask.card) = _
  ring

/-- All nonempty subsets of a finite control set. -/
def nonemptySubsets [DecidableEq ι] (controls : Finset ι) : Finset (Finset ι) :=
  controls.powerset.erase ∅

/-- The paper's alternating XOR sum over all nonempty control subsets. -/
def parityInclusionExclusionSum [DecidableEq ι]
    (controls : Finset ι) (bits : ι → Bool) : ℤ :=
  ∑ mask ∈ nonemptySubsets controls, signedParityContribution mask bits

@[simp]
theorem nonemptySubsets_empty [DecidableEq ι] :
    nonemptySubsets (∅ : Finset ι) = ∅ := by
  simp [nonemptySubsets]

@[simp]
theorem parityInclusionExclusionSum_empty [DecidableEq ι] (bits : ι → Bool) :
    parityInclusionExclusionSum (∅ : Finset ι) bits = 0 := by
  simp [parityInclusionExclusionSum]

/-- Erasing the empty subset does not change the alternating parity sum. -/
theorem allSubsetParitySum_eq_parityInclusionExclusionSum [DecidableEq ι]
    (controls : Finset ι) (bits : ι → Bool) :
    allSubsetParitySum controls bits = parityInclusionExclusionSum controls bits := by
  have hempty : (∅ : Finset ι) ∈ controls.powerset := by simp
  rw [allSubsetParitySum, parityInclusionExclusionSum, nonemptySubsets,
    ← Finset.sum_erase_add controls.powerset
      (fun mask => signedParityContribution mask bits) hempty]
  simp

end

end Barenco.MultiControl
