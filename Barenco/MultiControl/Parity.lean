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

variable {ι : Type*} [DecidableEq ι]

/-- Boolean XOR of the input bits selected by a finite mask. -/
def xorParity (mask : Finset ι) (bits : ι → Bool) : Bool :=
  ∑ control ∈ mask, bits control

@[simp]
theorem xorParity_empty (bits : ι → Bool) :
    xorParity (∅ : Finset ι) bits = false := by
  simp [xorParity, Bool.zero_eq_false]

@[simp]
theorem xorParity_insert {mask : Finset ι} {control : ι}
    (hcontrol : control ∉ mask) (bits : ι → Bool) :
    xorParity (insert control mask) bits = bits control + xorParity mask bits := by
  simp [xorParity, hcontrol]

/-- Interpret a Boolean as the integer `0` or `1`. -/
def boolInt (bit : Bool) : ℤ :=
  if bit then 1 else 0

@[simp]
theorem boolInt_false : boolInt false = 0 := rfl

@[simp]
theorem boolInt_true : boolInt true = 1 := rfl

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

/-- All nonempty subsets of a finite control set. -/
def nonemptySubsets (controls : Finset ι) : Finset (Finset ι) :=
  controls.powerset.erase ∅

/-- The paper's alternating XOR sum over all nonempty control subsets. -/
def parityInclusionExclusionSum (controls : Finset ι) (bits : ι → Bool) : ℤ :=
  ∑ mask ∈ nonemptySubsets controls, signedParityContribution mask bits

@[simp]
theorem nonemptySubsets_empty :
    nonemptySubsets (∅ : Finset ι) = ∅ := by
  simp [nonemptySubsets]

@[simp]
theorem parityInclusionExclusionSum_empty (bits : ι → Bool) :
    parityInclusionExclusionSum (∅ : Finset ι) bits = 0 := by
  simp [parityInclusionExclusionSum]

end

end Barenco.MultiControl
