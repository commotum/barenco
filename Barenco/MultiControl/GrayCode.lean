import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic

/-!
# Bit-reversed reflected Gray masks

The opening construction of Barenco et al. Section 7 traverses every nonempty
control mask in bit-reversed reflected Gray order.  A mask is represented directly
as a finite set of control positions.  `fullGrayCode` includes the empty mask;
`grayCode` removes it and is the runtime schedule used by Lemma 7.1.

This module is purely combinatorial.  It defines no quantum gate or circuit and
makes no resource claim.  Mask and schedule definitions are public runtime API;
their coverage, adjacency, pivot, and counting laws are public proof-side API.
-/

namespace Barenco.MultiControl

open scoped symmDiff

/-- A subset of `width` ordered control positions. -/
abbrev GrayMask (width : ℕ) := Finset (Fin width)

/-- Embed a mask into a register with one new final control position. -/
def liftGrayMask {width : ℕ} (mask : GrayMask width) : GrayMask (width + 1) :=
  mask.map Fin.castSuccEmb

/-- Embed a mask and include the new final control position. -/
def liftGrayMaskWithLast {width : ℕ} (mask : GrayMask width) : GrayMask (width + 1) :=
  insert (Fin.last width) (liftGrayMask mask)

@[simp]
theorem mem_liftGrayMask {width : ℕ} (mask : GrayMask width) (wire : Fin width) :
    wire.castSucc ∈ liftGrayMask mask ↔ wire ∈ mask := by
  simp [liftGrayMask]

@[simp]
theorem last_notMem_liftGrayMask {width : ℕ} (mask : GrayMask width) :
    Fin.last width ∉ liftGrayMask mask := by
  simp [liftGrayMask]

@[simp]
theorem mem_liftGrayMaskWithLast_castSucc {width : ℕ} (mask : GrayMask width)
    (wire : Fin width) :
    wire.castSucc ∈ liftGrayMaskWithLast mask ↔ wire ∈ mask := by
  simp [liftGrayMaskWithLast]

@[simp]
theorem last_mem_liftGrayMaskWithLast {width : ℕ} (mask : GrayMask width) :
    Fin.last width ∈ liftGrayMaskWithLast mask := by
  simp [liftGrayMaskWithLast]

@[simp]
theorem card_liftGrayMask {width : ℕ} (mask : GrayMask width) :
    (liftGrayMask mask).card = mask.card := by
  simp [liftGrayMask]

@[simp]
theorem card_liftGrayMaskWithLast {width : ℕ} (mask : GrayMask width) :
    (liftGrayMaskWithLast mask).card = mask.card + 1 := by
  simp [liftGrayMaskWithLast]

theorem liftGrayMask_injective {width : ℕ} :
    Function.Injective (@liftGrayMask width) := by
  intro first second h
  apply Finset.map_injective Fin.castSuccEmb
  exact h

theorem liftGrayMaskWithLast_injective {width : ℕ} :
    Function.Injective (@liftGrayMaskWithLast width) := by
  intro first second h
  apply liftGrayMask_injective
  ext wire
  by_cases hwire : wire = Fin.last width
  · subst wire
    simp
  · simpa [liftGrayMaskWithLast, hwire] using Finset.ext_iff.mp h wire

/-- Restrict a mask to the positions preceding the final position. -/
def dropLastGrayMask {width : ℕ} (mask : GrayMask (width + 1)) : GrayMask width :=
  Finset.univ.filter fun wire => wire.castSucc ∈ mask

@[simp]
theorem mem_dropLastGrayMask {width : ℕ} (mask : GrayMask (width + 1))
    (wire : Fin width) :
    wire ∈ dropLastGrayMask mask ↔ wire.castSucc ∈ mask := by
  simp [dropLastGrayMask]

@[simp]
theorem dropLastGrayMask_liftGrayMask {width : ℕ} (mask : GrayMask width) :
    dropLastGrayMask (liftGrayMask mask) = mask := by
  ext wire
  simp

theorem liftGrayMask_dropLastGrayMask_of_last_notMem {width : ℕ}
    (mask : GrayMask (width + 1)) (hlast : Fin.last width ∉ mask) :
    liftGrayMask (dropLastGrayMask mask) = mask := by
  ext wire
  rcases Fin.eq_castSucc_or_eq_last wire with ⟨wire, rfl⟩ | rfl
  · simp
  · simp [hlast]

theorem liftGrayMaskWithLast_dropLastGrayMask_of_last_mem {width : ℕ}
    (mask : GrayMask (width + 1)) (hlast : Fin.last width ∈ mask) :
    liftGrayMaskWithLast (dropLastGrayMask mask) = mask := by
  ext wire
  rcases Fin.eq_castSucc_or_eq_last wire with ⟨wire, rfl⟩ | rfl
  · simp
  · simp [hlast]

/--
The full bit-reversed reflected Gray traversal, including the empty mask first.

The old traversal is embedded without the new final position, then its reversal
is embedded with that position inserted.  Reversing bit significance relative to
the usual presentation gives the paper's `100,110,010,011,111,101,001` order.
-/
def fullGrayCode : (width : ℕ) → List (GrayMask width)
  | 0 => [∅]
  | width + 1 =>
      (fullGrayCode width).map liftGrayMask ++
        (fullGrayCode width).reverse.map liftGrayMaskWithLast

/-- The paper schedule: every nonempty Gray mask, with the initial empty mask removed. -/
def grayCode (width : ℕ) : List (GrayMask width) :=
  (fullGrayCode width).tail

@[simp]
theorem fullGrayCode_zero : fullGrayCode 0 = [∅] := rfl

@[simp]
theorem fullGrayCode_succ (width : ℕ) :
    fullGrayCode (width + 1) =
      (fullGrayCode width).map liftGrayMask ++
        (fullGrayCode width).reverse.map liftGrayMaskWithLast := rfl

@[simp]
theorem length_fullGrayCode : ∀ width, (fullGrayCode width).length = 2 ^ width := by
  intro width
  induction width with
  | zero => simp
  | succ width ih =>
      simp [fullGrayCode, ih, pow_succ]
      omega

theorem fullGrayCode_ne_nil (width : ℕ) : fullGrayCode width ≠ [] := by
  intro h
  have := congrArg List.length h
  simp at this

@[simp]
theorem head?_fullGrayCode : ∀ width, (fullGrayCode width).head? = some ∅ := by
  intro width
  induction width with
  | zero => simp
  | succ width ih =>
      rw [fullGrayCode_succ, List.head?_append]
      simp [ih, fullGrayCode_ne_nil]

/-- The full traversal is the empty mask followed by the paper schedule. -/
theorem empty_cons_grayCode (width : ℕ) :
    ∅ :: grayCode width = fullGrayCode width := by
  rw [grayCode]
  nth_rw 2 [← List.cons_head?_tail (fullGrayCode width)]
  rw [head?_fullGrayCode]

/-- Every mask occurs in the full reflected traversal. -/
theorem mem_fullGrayCode : ∀ {width : ℕ} (mask : GrayMask width),
    mask ∈ fullGrayCode width := by
  intro width
  induction width with
  | zero =>
      intro mask
      have hmask : mask = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun wire => Fin.elim0 wire
      simp [hmask]
  | succ width ih =>
      intro mask
      by_cases hlast : Fin.last width ∈ mask
      · rw [fullGrayCode_succ, List.mem_append]
        right
        rw [List.mem_map]
        refine ⟨dropLastGrayMask mask, ?_, ?_⟩
        · simpa using ih (dropLastGrayMask mask)
        · exact liftGrayMaskWithLast_dropLastGrayMask_of_last_mem mask hlast
      · rw [fullGrayCode_succ, List.mem_append]
        left
        rw [List.mem_map]
        refine ⟨dropLastGrayMask mask, ih (dropLastGrayMask mask), ?_⟩
        exact liftGrayMask_dropLastGrayMask_of_last_notMem mask hlast

/-- No mask is repeated in the full reflected traversal. -/
theorem nodup_fullGrayCode : ∀ width, (fullGrayCode width).Nodup := by
  intro width
  induction width with
  | zero => simp
  | succ width ih =>
      rw [fullGrayCode_succ]
      apply List.Nodup.append
      · exact ih.map liftGrayMask_injective
      · exact (List.nodup_reverse.mpr ih).map liftGrayMaskWithLast_injective
      · rw [List.disjoint_left]
        intro mask hfirst hsecond
        rw [List.mem_map] at hfirst hsecond
        rcases hfirst with ⟨first, _, rfl⟩
        rcases hsecond with ⟨second, _, heq⟩
        have hnot : Fin.last width ∉ liftGrayMask first := last_notMem_liftGrayMask first
        have hmem : Fin.last width ∈ liftGrayMask first := by
          rw [← heq]
          exact last_mem_liftGrayMaskWithLast second
        exact hnot hmem

/-- No nonempty mask is repeated in the paper schedule. -/
theorem nodup_grayCode (width : ℕ) : (grayCode width).Nodup := by
  exact (nodup_fullGrayCode width).tail

/-- The paper schedule contains exactly the nonempty control masks. -/
theorem mem_grayCode_iff {width : ℕ} (mask : GrayMask width) :
    mask ∈ grayCode width ↔ mask.Nonempty := by
  constructor
  · intro hmem
    intro hempty
    have hall := nodup_fullGrayCode width
    rw [← empty_cons_grayCode width] at hall
    exact (List.nodup_cons.mp hall).1 (hempty ▸ hmem)
  · intro hnonempty
    have hfull := mem_fullGrayCode mask
    rw [← empty_cons_grayCode width] at hfull
    rcases List.mem_cons.mp hfull with hempty | hmem
    · exact (hnonempty.ne_empty hempty.symm).elim
    · exact hmem

@[simp]
theorem length_grayCode (width : ℕ) : (grayCode width).length = 2 ^ width - 1 := by
  rw [grayCode, List.length_tail, length_fullGrayCode]

@[simp]
theorem grayCode_zero : grayCode 0 = [] := rfl

/-- The one-control schedule contains its unique nonempty mask. -/
theorem grayCode_one : grayCode 1 = [{0}] := by
  decide

/-- The two-control schedule is the bit-reversed path `10,11,01`. -/
theorem grayCode_two : grayCode 2 = [{0}, {0, 1}, {1}] := by
  decide

/-- The paper's seven masks for the displayed four-bit construction. -/
theorem grayCode_three :
    grayCode 3 = [{0}, {0, 1}, {1}, {1, 2}, {0, 1, 2}, {0, 2}, {2}] := by
  decide

/-- Two masks are Gray-adjacent when they differ at exactly one position. -/
def GrayAdjacent {width : ℕ} (first second : GrayMask width) : Prop :=
  (first ∆ second).card = 1

theorem GrayAdjacent.symmetric {width : ℕ} {first second : GrayMask width}
    (h : GrayAdjacent first second) : GrayAdjacent second first := by
  simpa [GrayAdjacent, symmDiff_comm] using h

end Barenco.MultiControl
