import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Finset.SymmDiff

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

open scoped BigOperators symmDiff

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

@[simp]
theorem xorParity_singleton [DecidableEq ι] (control : ι) (bits : ι → Bool) :
    xorParity ({control} : Finset ι) bits = bits control := by
  simp [xorParity]

/-- XOR parity sends finite symmetric difference to Boolean addition. -/
theorem xorParity_symmDiff [DecidableEq ι]
    (first second : Finset ι) (bits : ι → Bool) :
    xorParity (first ∆ second) bits = xorParity first bits + xorParity second bits := by
  have hleftRight : Disjoint (first \ second) (second \ first) := by
    rw [Finset.disjoint_left]
    intro control hfirst hsecond
    exact (Finset.mem_sdiff.mp hfirst).2 (Finset.mem_sdiff.mp hsecond).1
  have hfirstCommon : Disjoint (first \ second) (first ∩ second) :=
    Finset.disjoint_sdiff_inter first second
  have hsymm :
      xorParity (first ∆ second) bits =
        xorParity (first \ second) bits + xorParity (second \ first) bits := by
    rw [Finset.symmDiff_def, xorParity, Finset.sum_union hleftRight]
    rfl
  have hfirst :
      xorParity first bits =
        xorParity (first \ second) bits + xorParity (first ∩ second) bits := by
    conv_lhs => rw [← Finset.sdiff_union_inter first second]
    rw [xorParity, Finset.sum_union hfirstCommon]
    rfl
  have hsecond :
      xorParity second bits =
        xorParity (second \ first) bits + xorParity (first ∩ second) bits := by
    conv_lhs => rw [← Finset.sdiff_union_inter second first]
    rw [xorParity, Finset.sum_union (Finset.disjoint_sdiff_inter second first),
      Finset.inter_comm second first]
    rfl
  rw [hsymm, hfirst, hsecond]
  have hcommonCancel :
      xorParity (first ∩ second) bits + xorParity (first ∩ second) bits = 0 := by
    rw [← Bool.neg_eq_id (xorParity (first ∩ second) bits)]
    exact add_neg_cancel _
  symm
  calc
    (xorParity (first \ second) bits + xorParity (first ∩ second) bits) +
        (xorParity (second \ first) bits + xorParity (first ∩ second) bits) =
      (xorParity (first \ second) bits + xorParity (second \ first) bits) +
        (xorParity (first ∩ second) bits + xorParity (first ∩ second) bits) := by
          ac_rfl
    _ = xorParity (first \ second) bits + xorParity (second \ first) bits := by
      rw [hcommonCancel, add_zero]

/--
Across a Gray-code edge, symmetric difference by one control toggles parity by
exactly that control bit.
-/
theorem xorParity_eq_add_of_symmDiff_eq_singleton [DecidableEq ι]
    {first second : Finset ι} {changed : ι}
    (hchange : first ∆ second = {changed}) (bits : ι → Bool) :
    xorParity second bits = xorParity first bits + bits changed := by
  have hparity := xorParity_symmDiff first second bits
  rw [hchange, xorParity_singleton] at hparity
  calc
    xorParity second bits =
        -xorParity first bits +
          (xorParity first bits + xorParity second bits) := by simp
    _ = xorParity first bits + bits changed := by
      rw [← hparity, Bool.neg_eq_id]

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

@[simp]
theorem signedParityContribution_of_parity_false {mask : Finset ι} {bits : ι → Bool}
    (hparity : xorParity mask bits = false) :
    signedParityContribution mask bits = 0 := by
  simp [signedParityContribution, xorParityInt, hparity]

theorem signedParityContribution_of_parity_true {mask : Finset ι} {bits : ι → Bool}
    (hparity : xorParity mask bits = true) :
    signedParityContribution mask bits = (-1 : ℤ) ^ (mask.card - 1) := by
  simp [signedParityContribution, xorParityInt, hparity]

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
  simp

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

@[simp]
theorem mem_nonemptySubsets [DecidableEq ι]
    {controls mask : Finset ι} :
    mask ∈ nonemptySubsets controls ↔ mask ⊆ controls ∧ mask.Nonempty := by
  simp [nonemptySubsets, Finset.nonempty_iff_ne_empty, and_comm]

@[simp]
theorem card_nonemptySubsets [DecidableEq ι] (controls : Finset ι) :
    (nonemptySubsets controls).card = 2 ^ controls.card - 1 := by
  rw [nonemptySubsets, Finset.card_erase_of_mem (by simp), Finset.card_powerset]

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

/-- Every selected control carries the Boolean value `true`. -/
def AllBitsTrue (controls : Finset ι) (bits : ι → Bool) : Prop :=
  ∀ control ∈ controls, bits control = true

instance instDecidableAllBitsTrue [DecidableEq ι]
    (controls : Finset ι) (bits : ι → Bool) : Decidable (AllBitsTrue controls bits) := by
  unfold AllBitsTrue
  infer_instance

@[simp]
theorem allBitsTrue_empty (bits : ι → Bool) :
    AllBitsTrue (∅ : Finset ι) bits := by
  simp [AllBitsTrue]

@[simp]
theorem allBitsTrue_insert [DecidableEq ι] (control : ι) (controls : Finset ι)
    (bits : ι → Bool) :
    AllBitsTrue (insert control controls) bits ↔
      bits control = true ∧ AllBitsTrue controls bits := by
  simp [AllBitsTrue]

/--
Closed form of the whole-powerset auxiliary sum, including the empty-control
boundary case.
-/
theorem allSubsetParitySum_formula [DecidableEq ι]
    (controls : Finset ι) (bits : ι → Bool) :
    allSubsetParitySum controls bits =
      if controls = ∅ then 0
      else if AllBitsTrue controls bits then (2 : ℤ) ^ (controls.card - 1) else 0 := by
  induction controls using Finset.induction_on with
  | empty => simp
  | @insert control controls hcontrol ih =>
      have hinsertNonempty : insert control controls ≠ ∅ := by simp
      rw [if_neg hinsertNonempty]
      cases hbit : bits control with
      | false =>
          rw [allSubsetParitySum_insert_false hcontrol bits hbit]
          have hnotAll : ¬AllBitsTrue (insert control controls) bits := by
            intro hall
            have hcontrolTrue :=
              ((allBitsTrue_insert control controls bits).mp hall).1
            rw [hbit] at hcontrolTrue
            exact Bool.false_ne_true hcontrolTrue
          rw [if_neg hnotAll]
      | true =>
          rw [allSubsetParitySum_insert_true hcontrol bits hbit]
          by_cases hcontrols : controls = ∅
          · subst controls
            rw [if_pos]
            · simp
            · exact (allBitsTrue_insert control ∅ bits).mpr ⟨hbit, by simp⟩
          · have hcontrolsNonempty : controls.Nonempty :=
              Finset.nonempty_iff_ne_empty.mpr hcontrols
            rw [Finset.sum_powerset_neg_one_pow_card_of_nonempty hcontrolsNonempty]
            by_cases hall : AllBitsTrue controls bits
            · rw [if_pos ((allBitsTrue_insert control controls bits).mpr ⟨hbit, hall⟩)]
              rw [ih, if_neg hcontrols, if_pos hall]
              obtain ⟨card, hcard⟩ :=
                Nat.exists_eq_succ_of_ne_zero
                  (Finset.card_ne_zero.mpr hcontrolsNonempty)
              rw [Finset.card_insert_of_notMem hcontrol, hcard]
              simp [pow_succ]
              ring
            · rw [if_neg]
              · rw [ih, if_neg hcontrols, if_neg hall]
                simp
              · exact fun hinsertAll => hall
                  ((allBitsTrue_insert control controls bits).mp hinsertAll).2

/--
Finite inclusion-exclusion for XOR parity.

For a nonempty finite control set, the alternating signed sum over all nonempty
subsets is `2^(card-1)` exactly on the all-true input and is zero otherwise.
-/
theorem parityInclusionExclusionSum_formula [DecidableEq ι]
    {controls : Finset ι} (hcontrols : controls.Nonempty) (bits : ι → Bool) :
    parityInclusionExclusionSum controls bits =
      if AllBitsTrue controls bits then (2 : ℤ) ^ (controls.card - 1) else 0 := by
  rw [← allSubsetParitySum_eq_parityInclusionExclusionSum,
    allSubsetParitySum_formula, if_neg (Finset.nonempty_iff_ne_empty.mp hcontrols)]

/-- The all-true branch of the finite XOR inclusion-exclusion identity. -/
theorem parityInclusionExclusionSum_of_all_true [DecidableEq ι]
    {controls : Finset ι} (hcontrols : controls.Nonempty) (bits : ι → Bool)
    (hall : AllBitsTrue controls bits) :
    parityInclusionExclusionSum controls bits =
      (2 : ℤ) ^ (controls.card - 1) := by
  rw [parityInclusionExclusionSum_formula hcontrols, if_pos hall]

/-- Any false selected input makes the finite XOR inclusion-exclusion sum zero. -/
theorem parityInclusionExclusionSum_of_not_all_true [DecidableEq ι]
    {controls : Finset ι} (hcontrols : controls.Nonempty) (bits : ι → Bool)
    (hall : ¬AllBitsTrue controls bits) :
    parityInclusionExclusionSum controls bits = 0 := by
  rw [parityInclusionExclusionSum_formula hcontrols, if_neg hall]

/-- A witness false control is a convenient sufficient form of the zero branch. -/
theorem parityInclusionExclusionSum_of_exists_false [DecidableEq ι]
    {controls : Finset ι} (hcontrols : controls.Nonempty) (bits : ι → Bool)
    {control : ι} (hcontrol : control ∈ controls) (hbit : bits control = false) :
    parityInclusionExclusionSum controls bits = 0 := by
  apply parityInclusionExclusionSum_of_not_all_true hcontrols bits
  intro hall
  have htrue := hall control hcontrol
  rw [hbit] at htrue
  exact Bool.false_ne_true htrue

/-- One selected control contributes precisely its `0`/`1` integer value. -/
@[simp]
theorem parityInclusionExclusionSum_singleton [DecidableEq ι]
    (control : ι) (bits : ι → Bool) :
    parityInclusionExclusionSum ({control} : Finset ι) bits = boolInt (bits control) := by
  rw [parityInclusionExclusionSum_formula (Finset.singleton_nonempty control)]
  cases hbit : bits control <;> simp [AllBitsTrue, hbit, boolInt]

/-- Whole finite-type specialization of the representation-independent theorem. -/
theorem parityInclusionExclusionSum_univ [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (bits : ι → Bool) :
    parityInclusionExclusionSum (Finset.univ : Finset ι) bits =
      if (∀ control, bits control = true) then
        (2 : ℤ) ^ (Fintype.card ι - 1)
      else 0 := by
  simpa [AllBitsTrue] using
    parityInclusionExclusionSum_formula (Finset.univ_nonempty :
      (Finset.univ : Finset ι).Nonempty) bits

end

end Barenco.MultiControl
