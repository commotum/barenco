import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Forall2
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

/--
The position toggled between each consecutive pair in `fullGrayCode`.

At the recursive reflection boundary the new final position is toggled; the
second half then traverses the old toggle list in reverse.
-/
def fullGrayToggles : (width : ℕ) → List (Fin width)
  | 0 => []
  | width + 1 =>
      (fullGrayToggles width).map Fin.castSucc ++ [Fin.last width] ++
        (fullGrayToggles width).reverse.map Fin.castSucc

/-- CNOT/parity-mask transitions after removing the initial empty-to-singleton edge. -/
def grayToggles (width : ℕ) : List (Fin width) :=
  (fullGrayToggles width).tail

/--
Accumulator position for each nonempty Gray mask.

The first recursive block retains its previous pivot.  Every mask in the reflected
block contains the new final position, which is therefore its maximum and pivot.
-/
def grayPivots : (width : ℕ) → List (Fin width)
  | 0 => []
  | width + 1 =>
      (grayPivots width).map Fin.castSucc ++
        List.replicate (2 ^ width) (Fin.last width)

@[simp]
theorem fullGrayCode_zero : fullGrayCode 0 = [∅] := rfl

@[simp]
theorem fullGrayCode_succ (width : ℕ) :
    fullGrayCode (width + 1) =
      (fullGrayCode width).map liftGrayMask ++
        (fullGrayCode width).reverse.map liftGrayMaskWithLast := rfl

@[simp]
theorem fullGrayToggles_zero : fullGrayToggles 0 = [] := rfl

@[simp]
theorem fullGrayToggles_succ (width : ℕ) :
    fullGrayToggles (width + 1) =
      (fullGrayToggles width).map Fin.castSucc ++ [Fin.last width] ++
        (fullGrayToggles width).reverse.map Fin.castSucc := rfl

@[simp]
theorem grayPivots_zero : grayPivots 0 = [] := rfl

@[simp]
theorem grayPivots_succ (width : ℕ) :
    grayPivots (width + 1) =
      (grayPivots width).map Fin.castSucc ++
        List.replicate (2 ^ width) (Fin.last width) := rfl

@[simp]
theorem length_fullGrayCode : ∀ width, (fullGrayCode width).length = 2 ^ width := by
  intro width
  induction width with
  | zero => simp
  | succ width ih =>
      simp [fullGrayCode, ih, pow_succ]
      omega

@[simp]
theorem length_fullGrayToggles : ∀ width, (fullGrayToggles width).length = 2 ^ width - 1 := by
  intro width
  induction width with
  | zero => simp
  | succ width ih =>
      have hpow : 0 < 2 ^ width := pow_pos (by omega) width
      simp [fullGrayToggles, ih, pow_succ]
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
      simp [ih, liftGrayMask]

/-- The full traversal is the empty mask followed by the paper schedule. -/
theorem empty_cons_grayCode (width : ℕ) :
    ∅ :: grayCode width = fullGrayCode width := by
  change ∅ :: (fullGrayCode width).tail = fullGrayCode width
  apply List.cons_head?_tail
  rw [head?_fullGrayCode]
  simp

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
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hall := nodup_fullGrayCode width
    rw [← empty_cons_grayCode width] at hall
    exact (List.nodup_cons.mp hall).1 (hempty ▸ hmem)
  · intro hnonempty
    have hfull := mem_fullGrayCode mask
    rw [← empty_cons_grayCode width] at hfull
    rcases List.mem_cons.mp hfull with hempty | hmem
    · exact (hnonempty.ne_empty hempty).elim
    · exact hmem

@[simp]
theorem length_grayCode (width : ℕ) : (grayCode width).length = 2 ^ width - 1 := by
  rw [grayCode, List.length_tail, length_fullGrayCode]

@[simp]
theorem length_grayToggles (width : ℕ) :
    (grayToggles width).length = 2 ^ width - 2 := by
  rw [grayToggles, List.length_tail, length_fullGrayToggles]
  have hpow : 0 < 2 ^ width := pow_pos (by omega) width
  omega

@[simp]
theorem length_grayPivots : ∀ width, (grayPivots width).length = 2 ^ width - 1 := by
  intro width
  induction width with
  | zero => simp
  | succ width ih =>
      have hpow : 0 < 2 ^ width := pow_pos (by omega) width
      simp [grayPivots, ih, pow_succ]
      omega

theorem length_grayPivots_eq_grayCode (width : ℕ) :
    (grayPivots width).length = (grayCode width).length := by
  rw [length_grayPivots, length_grayCode]

@[simp]
theorem grayCode_zero : grayCode 0 = [] := rfl

theorem grayCode_succ (width : ℕ) :
    grayCode (width + 1) =
      (grayCode width).map liftGrayMask ++
        (fullGrayCode width).reverse.map liftGrayMaskWithLast := by
  have hmap : (fullGrayCode width).map liftGrayMask ≠ [] := by
    simpa using fullGrayCode_ne_nil width
  rw [grayCode, fullGrayCode_succ, List.tail_append_of_ne_nil hmap]
  rw [← List.map_tail]
  rfl

/-- The full traversal on a positive width ends at the singleton final position. -/
@[simp]
theorem getLast?_fullGrayCode_succ (width : ℕ) :
    (fullGrayCode (width + 1)).getLast? = some {Fin.last width} := by
  rw [fullGrayCode_succ]
  have hsecond :
      (fullGrayCode width).reverse.map liftGrayMaskWithLast ≠ [] := by
    simp [fullGrayCode_ne_nil width]
  rw [List.getLast?_append_of_ne_nil _ hsecond, List.getLast?_map]
  simp [head?_fullGrayCode, liftGrayMaskWithLast, liftGrayMask]

/-- The nonempty runtime schedule has the same singleton final endpoint. -/
@[simp]
theorem getLast?_grayCode_succ (width : ℕ) :
    (grayCode (width + 1)).getLast? = some {Fin.last width} := by
  rw [grayCode_succ]
  have hsecond :
      (fullGrayCode width).reverse.map liftGrayMaskWithLast ≠ [] := by
    simp [fullGrayCode_ne_nil width]
  rw [List.getLast?_append_of_ne_nil _ hsecond, List.getLast?_map]
  simp [head?_fullGrayCode, liftGrayMaskWithLast, liftGrayMask]

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

/-- Toggle positions for the paper's seven-mask, six-CNOT traversal. -/
theorem grayToggles_three : grayToggles 3 = [1, 0, 2, 0, 1, 0] := by
  decide

/-- Maximum-mask pivots for the paper's seven controlled-root gates. -/
theorem grayPivots_three : grayPivots 3 = [0, 1, 1, 2, 2, 2, 2] := by
  decide

/-- Two masks are Gray-adjacent when they differ at exactly one position. -/
def GrayAdjacent {width : ℕ} (first second : GrayMask width) : Prop :=
  (first ∆ second).card = 1

theorem GrayAdjacent.symmetric {width : ℕ} {first second : GrayMask width}
    (h : GrayAdjacent first second) : GrayAdjacent second first := by
  simpa [GrayAdjacent, symmDiff_comm] using h

theorem symmDiff_liftGrayMask {width : ℕ} (first second : GrayMask width) :
    liftGrayMask first ∆ liftGrayMask second = liftGrayMask (first ∆ second) := by
  ext wire
  rcases Fin.eq_castSucc_or_eq_last wire with ⟨wire, rfl⟩ | rfl
  · simp [Finset.mem_symmDiff]
  · simp [Finset.mem_symmDiff]

theorem symmDiff_liftGrayMaskWithLast {width : ℕ} (first second : GrayMask width) :
    liftGrayMaskWithLast first ∆ liftGrayMaskWithLast second =
      liftGrayMask (first ∆ second) := by
  ext wire
  rcases Fin.eq_castSucc_or_eq_last wire with ⟨wire, rfl⟩ | rfl
  · simp [Finset.mem_symmDiff]
  · simp [Finset.mem_symmDiff]

theorem GrayAdjacent.lift {width : ℕ} {first second : GrayMask width}
    (h : GrayAdjacent first second) :
    GrayAdjacent (liftGrayMask first) (liftGrayMask second) := by
  rw [GrayAdjacent, symmDiff_liftGrayMask, card_liftGrayMask]
  exact h

theorem GrayAdjacent.withLast {width : ℕ} {first second : GrayMask width}
    (h : GrayAdjacent first second) :
    GrayAdjacent (liftGrayMaskWithLast first) (liftGrayMaskWithLast second) := by
  rw [GrayAdjacent, symmDiff_liftGrayMaskWithLast, card_liftGrayMask]
  exact h

/-- The reflection boundary differs only at the newly introduced final position. -/
theorem GrayAdjacent.lift_withLast {width : ℕ} (mask : GrayMask width) :
    GrayAdjacent (liftGrayMask mask) (liftGrayMaskWithLast mask) := by
  rw [GrayAdjacent]
  have hdiff :
      liftGrayMask mask ∆ liftGrayMaskWithLast mask = {Fin.last width} := by
    ext wire
    rcases Fin.eq_castSucc_or_eq_last wire with ⟨wire, rfl⟩ | rfl
    · simp [Finset.mem_symmDiff]
    · simp [Finset.mem_symmDiff]
  rw [hdiff]
  simp

/-- Every consecutive pair in the full reflected traversal differs at one position. -/
theorem fullGrayCode_isChain : ∀ width,
    (fullGrayCode width).IsChain GrayAdjacent := by
  intro width
  induction width with
  | zero => simp
  | succ width ih =>
      rw [fullGrayCode_succ]
      apply List.IsChain.append
      · exact List.isChain_map_of_isChain liftGrayMask
          (fun _ _ h => h.lift) ih
      · have hreverse :
            (fullGrayCode width).reverse.IsChain GrayAdjacent := by
          apply List.isChain_reverse.mpr
          exact ih.imp fun _ _ h => h.symmetric
        exact List.isChain_map_of_isChain liftGrayMaskWithLast
          (fun _ _ h => h.withLast) hreverse
      · intro first hfirst second hsecond
        rw [List.getLast?_map] at hfirst
        rw [List.head?_map, List.head?_reverse] at hsecond
        rw [Option.mem_def] at hfirst hsecond
        cases hlast : (fullGrayCode width).getLast? with
        | none => simp [hlast] at hfirst
        | some mask =>
            simp [hlast] at hfirst hsecond
            subst first
            subst second
            exact GrayAdjacent.lift_withLast mask

/-- Every consecutive pair in the paper's nonempty schedule is Gray-adjacent. -/
theorem grayCode_isChain (width : ℕ) :
    (grayCode width).IsChain GrayAdjacent := by
  exact (fullGrayCode_isChain width).tail

/-- Adjacency exposes the unique position changed by a Gray step. -/
theorem GrayAdjacent.exists_unique_changed {width : ℕ} {first second : GrayMask width}
    (h : GrayAdjacent first second) :
    ∃ changed : Fin width, first ∆ second = {changed} := by
  exact Finset.card_eq_one.mp h

/-! ## Maximum-mask pivots -/

/--
One plus the largest selected position, with rank zero assigned to the empty mask.

Unlike a `Fin`-valued maximum, `pivotRank` is total.  Its codomain also records
the empty/nonempty distinction: every selected position has positive rank, while
the rank is always bounded by the register width.
-/
def pivotRank {width : ℕ} (mask : GrayMask width) : ℕ :=
  mask.sup fun wire => wire.val + 1

@[simp]
theorem pivotRank_empty (width : ℕ) : pivotRank (∅ : GrayMask width) = 0 := by
  simp [pivotRank]

/-- A mask's total pivot rank cannot exceed its register width. -/
theorem pivotRank_le_width {width : ℕ} (mask : GrayMask width) :
    pivotRank mask ≤ width := by
  rw [pivotRank]
  exact Finset.sup_le fun wire _ => wire.isLt

/-- Embedding a mask without the new final position preserves its pivot rank. -/
@[simp]
theorem pivotRank_liftGrayMask {width : ℕ} (mask : GrayMask width) :
    pivotRank (liftGrayMask mask) = pivotRank mask := by
  rw [pivotRank, pivotRank, liftGrayMask, Finset.sup_map]
  rfl

/-- Adding the new final position gives the maximum possible pivot rank. -/
@[simp]
theorem pivotRank_liftGrayMaskWithLast {width : ℕ} (mask : GrayMask width) :
    pivotRank (liftGrayMaskWithLast mask) = width + 1 := by
  rw [pivotRank, liftGrayMaskWithLast, Finset.sup_insert]
  change max (width + 1) (pivotRank (liftGrayMask mask)) = width + 1
  rw [pivotRank_liftGrayMask]
  exact max_eq_left (pivotRank_le_width mask |>.trans (Nat.le_succ width))

/--
The schedule-specific progress relation between consecutive masks.

It records both monotonicity of the total pivot rank and the structural fact
needed to move an XOR accumulator: when the rank rises, the previous mask has
at most one selected position.
-/
def GrayPivotStep {width : ℕ} (first second : GrayMask width) : Prop :=
  pivotRank first ≤ pivotRank second ∧
    (pivotRank first < pivotRank second → first.card ≤ 1)

theorem GrayPivotStep.rank_le {width : ℕ} {first second : GrayMask width}
    (h : GrayPivotStep first second) : pivotRank first ≤ pivotRank second :=
  h.1

theorem GrayPivotStep.card_le_one_of_lt {width : ℕ}
    {first second : GrayMask width} (h : GrayPivotStep first second)
    (hlt : pivotRank first < pivotRank second) : first.card ≤ 1 :=
  h.2 hlt

theorem GrayPivotStep.lift {width : ℕ} {first second : GrayMask width}
    (h : GrayPivotStep first second) :
    GrayPivotStep (liftGrayMask first) (liftGrayMask second) := by
  constructor
  · simpa using h.rank_le
  · intro hlt
    rw [pivotRank_liftGrayMask, pivotRank_liftGrayMask] at hlt
    simpa using h.card_le_one_of_lt hlt

private theorem grayPivotStep_liftWithLast {width : ℕ}
    (first second : GrayMask width) :
    GrayPivotStep (liftGrayMaskWithLast first) (liftGrayMaskWithLast second) := by
  simp [GrayPivotStep]

private theorem grayPivotStep_reflectionBoundary {width : ℕ}
    (mask : GrayMask width) (hcard : mask.card ≤ 1) :
    GrayPivotStep (liftGrayMask mask) (liftGrayMaskWithLast mask) := by
  constructor
  · rw [pivotRank_liftGrayMask, pivotRank_liftGrayMaskWithLast]
    exact (pivotRank_le_width mask).trans (Nat.le_succ width)
  · intro _
    simpa using hcard

private theorem card_le_one_of_mem_getLast?_fullGrayCode {width : ℕ}
    {mask : GrayMask width} (hmask : mask ∈ (fullGrayCode width).getLast?) :
    mask.card ≤ 1 := by
  cases width with
  | zero =>
      simp at hmask
      subst mask
      simp
  | succ width =>
      rw [getLast?_fullGrayCode_succ] at hmask
      simp at hmask
      subst mask
      simp

private theorem isChain_liftGrayMaskWithLast {width : ℕ}
    (masks : List (GrayMask width)) :
    (masks.map liftGrayMaskWithLast).IsChain GrayPivotStep := by
  induction masks with
  | nil => simp
  | cons first rest ih =>
      cases rest with
      | nil => simp
      | cons second tail =>
          rw [List.map_cons, List.map_cons, List.isChain_cons_cons]
          exact ⟨grayPivotStep_liftWithLast first second, ih⟩

/--
Pivot ranks are nondecreasing along the full traversal, and a strict increase
can occur only after a mask of cardinality at most one.
-/
theorem fullGrayCode_pivotRank_isChain : ∀ width,
    (fullGrayCode width).IsChain GrayPivotStep := by
  intro width
  induction width with
  | zero => simp
  | succ width ih =>
      rw [fullGrayCode_succ]
      apply List.IsChain.append
      · exact List.isChain_map_of_isChain liftGrayMask
          (fun _ _ h => h.lift) ih
      · exact isChain_liftGrayMaskWithLast (fullGrayCode width).reverse
      · intro first hfirst second hsecond
        rw [List.getLast?_map] at hfirst
        rw [List.head?_map, List.head?_reverse] at hsecond
        rw [Option.mem_def] at hfirst hsecond
        cases hlast : (fullGrayCode width).getLast? with
        | none => simp [hlast] at hfirst
        | some mask =>
            simp [hlast] at hfirst hsecond
            subst first
            subst second
            exact grayPivotStep_reflectionBoundary mask
              (card_le_one_of_mem_getLast?_fullGrayCode (by simp [hlast]))

/-- The paper's nonempty schedule inherits the full traversal's pivot progress. -/
theorem grayCode_pivotRank_isChain (width : ℕ) :
    (grayCode width).IsChain GrayPivotStep := by
  exact (fullGrayCode_pivotRank_isChain width).tail

/-- A nonempty previous mask is a singleton whenever its pivot rank rises. -/
theorem GrayPivotStep.first_eq_singleton_of_lt {width : ℕ}
    {first second : GrayMask width} (h : GrayPivotStep first second)
    (hfirst : first.Nonempty) (hlt : pivotRank first < pivotRank second) :
    ∃ wire : Fin width, first = {wire} := by
  have hcardLe : first.card ≤ 1 := h.card_le_one_of_lt hlt
  have hcardPos : 0 < first.card := Finset.card_pos.mpr hfirst
  have hcard : first.card = 1 := by omega
  exact Finset.card_eq_one.mp hcard

/--
For an actual consecutive pair in `grayCode`, strict pivot-rank increase exposes
the previous mask as a singleton.  This indexed form is convenient for compiling
the schedule into one CNOT per transition.
-/
theorem grayCode_previous_singleton_of_pivotRank_lt {width index : ℕ}
    (hindex : index + 1 < (grayCode width).length)
    (hlt : pivotRank (grayCode width)[index] <
      pivotRank (grayCode width)[index + 1]) :
    ∃ wire : Fin width, (grayCode width)[index] = {wire} := by
  have hstep : GrayPivotStep (grayCode width)[index]
      (grayCode width)[index + 1] :=
    (grayCode_pivotRank_isChain width).getElem index hindex
  have hmem : (grayCode width)[index] ∈ grayCode width :=
    List.getElem_mem _
  exact hstep.first_eq_singleton_of_lt
    ((mem_grayCode_iff (grayCode width)[index]).mp hmem) hlt

/-- `pivot` is a member of `mask` no smaller than any other selected position. -/
def IsGrayPivot {width : ℕ} (mask : GrayMask width) (pivot : Fin width) : Prop :=
  pivot ∈ mask ∧ ∀ wire ∈ mask, wire ≤ pivot

theorem IsGrayPivot.nonempty {width : ℕ} {mask : GrayMask width} {pivot : Fin width}
    (h : IsGrayPivot mask pivot) : mask.Nonempty :=
  ⟨pivot, h.1⟩

theorem IsGrayPivot.eq_max' {width : ℕ} {mask : GrayMask width} {pivot : Fin width}
    (h : IsGrayPivot mask pivot) : mask.max' h.nonempty = pivot := by
  apply le_antisymm
  · exact h.2 _ (Finset.max'_mem mask h.nonempty)
  · exact Finset.le_max' mask pivot h.1

theorem IsGrayPivot.lift {width : ℕ} {mask : GrayMask width} {pivot : Fin width}
    (h : IsGrayPivot mask pivot) :
    IsGrayPivot (liftGrayMask mask) pivot.castSucc := by
  constructor
  · simp [h.1]
  · intro wire hwire
    rw [liftGrayMask, Finset.mem_map] at hwire
    rcases hwire with ⟨source, _, rfl⟩
    simpa using h.2 source (by assumption)

theorem isGrayPivot_liftWithLast {width : ℕ} (mask : GrayMask width) :
    IsGrayPivot (liftGrayMaskWithLast mask) (Fin.last width) := by
  constructor
  · simp
  · intro wire _
    exact Fin.le_last wire

private theorem forall₂_liftGrayPivots {width : ℕ}
    {masks : List (GrayMask width)} {pivots : List (Fin width)}
    (h : List.Forall₂ IsGrayPivot masks pivots) :
    List.Forall₂ IsGrayPivot (masks.map liftGrayMask) (pivots.map Fin.castSucc) := by
  exact List.rel_map (fun _ _ hpivot => IsGrayPivot.lift hpivot) h

private theorem forall₂_liftWithLast_replicate {width : ℕ}
    (masks : List (GrayMask width)) :
    List.Forall₂ IsGrayPivot
      (masks.map liftGrayMaskWithLast)
      (List.replicate masks.length (Fin.last width)) := by
  induction masks with
  | nil => simp
  | cons mask masks ih =>
      simp only [List.map_cons, List.length_cons, List.replicate_succ]
      exact List.Forall₂.cons (isGrayPivot_liftWithLast mask) ih

/-- Every runtime pivot is exactly the maximum selected position of its paired mask. -/
theorem grayCode_pivots : ∀ width,
    List.Forall₂ IsGrayPivot (grayCode width) (grayPivots width) := by
  intro width
  induction width with
  | zero => simp
  | succ width ih =>
      rw [grayCode_succ, grayPivots_succ, ← length_fullGrayCode]
      apply List.rel_append
      · exact forall₂_liftGrayPivots ih
      · simpa using forall₂_liftWithLast_replicate (fullGrayCode width).reverse

/-- Accumulator pivots never move toward a lower-index control wire. -/
theorem grayPivots_isChain : ∀ width,
    (grayPivots width).IsChain (· ≤ ·) := by
  intro width
  induction width with
  | zero => simp
  | succ width ih =>
      rw [grayPivots_succ]
      apply List.IsChain.append
      · exact List.isChain_map_of_isChain Fin.castSucc
          (fun _ _ h => by simpa using h) ih
      · exact List.isChain_replicate_of_rel _ le_rfl
      · intro first _ second hsecond
        have hsecondEq : second = Fin.last width := by
          exact (List.mem_replicate.mp (List.mem_of_mem_head? hsecond)).2
        subst second
        exact Fin.le_last first

end Barenco.MultiControl
