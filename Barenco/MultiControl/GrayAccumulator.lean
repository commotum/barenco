import Barenco.MultiControl.GrayCode
import Barenco.MultiControl.Parity

/-!
# Boolean accumulator semantics for Gray-code CNOT schedules

Lemma 7.1 stores the XOR parity of the current nonempty Gray mask in its maximum
selected control wire.  This file formalizes that classical state invariant before
introducing quantum circuit syntax.

`xorWireUpdate` is the basis-state action of one CNOT.  A fixed-pivot Gray step
toggles one lower input into the accumulator; a pivot-transfer step moves from a
singleton old mask to a two-position mask and starts a new accumulator.  These
two exact update lemmas are the local proof rules needed by the full schedule.
-/

namespace Barenco.MultiControl

open scoped symmDiff

/-!
## Alignment of masks and generated toggle positions

`GrayTransitionAlignment masks toggles` says that `toggles` labels every
consecutive edge of `masks`, in order, by the unique position in the symmetric
difference.  It is private implementation machinery; the public interface below
is the indexed specification of the generated schedule.
-/

private inductive GrayTransitionAlignment {width : ℕ} :
    List (GrayMask width) → List (Fin width) → Prop
  | nil : GrayTransitionAlignment [] []
  | singleton (mask : GrayMask width) : GrayTransitionAlignment [mask] []
  | cons {first second : GrayMask width} {rest : List (GrayMask width)}
      {changed : Fin width} {changes : List (Fin width)}
      (hchange : first ∆ second = {changed})
      (tail : GrayTransitionAlignment (second :: rest) changes) :
      GrayTransitionAlignment (first :: second :: rest) (changed :: changes)

private theorem GrayTransitionAlignment.tail {width : ℕ}
    {first : GrayMask width} {masks : List (GrayMask width)}
    {changes : List (Fin width)}
    (h : GrayTransitionAlignment (first :: masks) changes) :
    GrayTransitionAlignment masks changes.tail := by
  cases h with
  | singleton => exact .nil
  | cons _ htail => exact htail

private theorem GrayTransitionAlignment.lift {width : ℕ}
    {masks : List (GrayMask width)} {changes : List (Fin width)}
    (h : GrayTransitionAlignment masks changes) :
    GrayTransitionAlignment
      (masks.map liftGrayMask) (changes.map Fin.castSucc) := by
  induction h with
  | nil => exact .nil
  | singleton mask => exact .singleton (liftGrayMask mask)
  | @cons first second rest changed changes hchange _ ih =>
      apply GrayTransitionAlignment.cons
      · rw [symmDiff_liftGrayMask, hchange]
        simp [liftGrayMask]
      · exact ih

private theorem GrayTransitionAlignment.withLast {width : ℕ}
    {masks : List (GrayMask width)} {changes : List (Fin width)}
    (h : GrayTransitionAlignment masks changes) :
    GrayTransitionAlignment
      (masks.map liftGrayMaskWithLast) (changes.map Fin.castSucc) := by
  induction h with
  | nil => exact .nil
  | singleton mask => exact .singleton (liftGrayMaskWithLast mask)
  | @cons first second rest changed changes hchange _ ih =>
      apply GrayTransitionAlignment.cons
      · rw [symmDiff_liftGrayMaskWithLast, hchange]
        simp [liftGrayMask]
      · exact ih

private theorem GrayTransitionAlignment.append_cons {width : ℕ}
    {masks : List (GrayMask width)} {changes : List (Fin width)}
    {next : GrayMask width} {rest : List (GrayMask width)}
    {nextChanges : List (Fin width)} {changed : Fin width}
    (h : GrayTransitionAlignment masks changes) (hne : masks ≠ [])
    (hnext : GrayTransitionAlignment (next :: rest) nextChanges)
    (hboundary : ∀ last, last ∈ masks.getLast? → last ∆ next = {changed}) :
    GrayTransitionAlignment (masks ++ next :: rest)
      (changes ++ changed :: nextChanges) := by
  induction h with
  | nil => exact (hne rfl).elim
  | singleton mask =>
      exact GrayTransitionAlignment.cons (hboundary mask (by simp)) hnext
  | @cons first second tail oldChange oldChanges hchange htail ih =>
      apply GrayTransitionAlignment.cons hchange
      apply ih
      · simp
      · intro last hlast
        apply hboundary last
        simpa using hlast

private theorem GrayTransitionAlignment.append {width : ℕ}
    {firstMasks secondMasks : List (GrayMask width)}
    {firstChanges secondChanges : List (Fin width)} {changed : Fin width}
    (hfirst : GrayTransitionAlignment firstMasks firstChanges)
    (hsecond : GrayTransitionAlignment secondMasks secondChanges)
    (hfirstNe : firstMasks ≠ []) (hsecondNe : secondMasks ≠ [])
    (hboundary : ∀ first second,
      first ∈ firstMasks.getLast? → second ∈ secondMasks.head? →
        first ∆ second = {changed}) :
    GrayTransitionAlignment (firstMasks ++ secondMasks)
      (firstChanges ++ changed :: secondChanges) := by
  cases secondMasks with
  | nil => exact (hsecondNe rfl).elim
  | cons second rest =>
      exact hfirst.append_cons hfirstNe hsecond fun first hlast =>
        hboundary first second hlast (by simp)

private theorem GrayTransitionAlignment.reverse {width : ℕ}
    {masks : List (GrayMask width)} {changes : List (Fin width)}
    (h : GrayTransitionAlignment masks changes) :
    GrayTransitionAlignment masks.reverse changes.reverse := by
  induction h with
  | nil => exact .nil
  | singleton mask => exact .singleton mask
  | @cons first second rest changed changes hchange htail ih =>
      have happend :
          GrayTransitionAlignment ((second :: rest).reverse ++ [first])
            (changes.reverse ++ [changed]) := by
        apply ih.append_cons
        · simp
        · exact .singleton first
        · intro last hlast
          have hlastEq : last = second := by
            exact (by simpa using hlast : second = last).symm
          subst last
          simpa [symmDiff_comm] using hchange
      simpa [List.reverse_cons, List.append_assoc] using happend

private theorem liftGrayMask_symmDiff_liftGrayMaskWithLast {width : ℕ}
    (mask : GrayMask width) :
    liftGrayMask mask ∆ liftGrayMaskWithLast mask = {Fin.last width} := by
  ext wire
  rcases Fin.eq_castSucc_or_eq_last wire with ⟨wire, rfl⟩ | rfl
  · simp [Finset.mem_symmDiff]
  · simp [Finset.mem_symmDiff]

private theorem fullGrayTransitionAlignment : ∀ width,
    GrayTransitionAlignment (fullGrayCode width) (fullGrayToggles width) := by
  intro width
  induction width with
  | zero => exact .singleton ∅
  | succ width ih =>
      rw [fullGrayCode_succ, fullGrayToggles_succ]
      have hfirst := ih.lift
      have hsecond := ih.reverse.withLast
      have happend := hfirst.append (changed := Fin.last width) hsecond
        (by simpa using fullGrayCode_ne_nil width)
        (by simp [fullGrayCode_ne_nil width])
        (by
          intro first second hfirstLast hsecondHead
          rw [List.getLast?_map] at hfirstLast
          rw [List.head?_map, List.head?_reverse] at hsecondHead
          rw [Option.mem_def] at hfirstLast hsecondHead
          cases hlast : (fullGrayCode width).getLast? with
          | none => simp [hlast] at hfirstLast
          | some mask =>
              simp [hlast] at hfirstLast hsecondHead
              subst first
              subst second
              exact liftGrayMask_symmDiff_liftGrayMaskWithLast mask)
      simpa [List.append_assoc] using happend

private theorem grayTransitionAlignment (width : ℕ) :
    GrayTransitionAlignment (grayCode width) (grayToggles width) := by
  have hfull := fullGrayTransitionAlignment width
  rw [← empty_cons_grayCode width] at hfull
  exact hfull.tail

private theorem GrayTransitionAlignment.length_changes {width : ℕ}
    {masks : List (GrayMask width)} {changes : List (Fin width)}
    (h : GrayTransitionAlignment masks changes) :
    changes.length = masks.length - 1 := by
  induction h with
  | nil => simp
  | singleton mask => simp
  | cons _ _ ih => simp [ih]

private theorem GrayTransitionAlignment.getElem {width : ℕ}
    {masks : List (GrayMask width)} {changes : List (Fin width)}
    (h : GrayTransitionAlignment masks changes) (index : ℕ)
    (hindex : index + 1 < masks.length)
    (hchangeIndex : index < changes.length) :
    masks[index] ∆ masks[index + 1] = {changes[index]} := by
  induction h generalizing index with
  | nil => simp at hindex
  | singleton mask => simp at hindex
  | @cons first second rest changed changes hchange htail ih =>
      cases index with
      | zero => simpa using hchange
      | succ index =>
          simp only [List.getElem_cons_succ]
          have htailIndex : index + 1 < (second :: rest).length := by
            simpa using hindex
          have hrestIndex : index < rest.length := by
            simpa using htailIndex
          have htailStep := ih index htailIndex (by simpa using hchangeIndex)
          have hget : (second :: rest)[index + 1]'htailIndex =
              rest[index]'hrestIndex := by
            rfl
          rw [hget] at htailStep
          exact htailStep

private theorem grayToggle_index_lt {width index : ℕ}
    (hindex : index + 1 < (grayCode width).length) :
    index < (grayToggles width).length := by
  rw [length_grayCode] at hindex
  rw [length_grayToggles]
  omega

/-- The generated toggle at each index is exactly the bit changed by that Gray edge. -/
theorem grayCode_symmDiff_eq_singleton_grayToggle {width index : ℕ}
    (hindex : index + 1 < (grayCode width).length) :
    (grayCode width)[index] ∆ (grayCode width)[index + 1] =
      {(grayToggles width)[index]'(grayToggle_index_lt hindex)} := by
  exact GrayTransitionAlignment.getElem (grayTransitionAlignment width)
    index hindex (grayToggle_index_lt hindex)

/-- Consecutive accumulator pivots, before choosing each CNOT's control wire. -/
def grayPivotPairs (width : ℕ) : List (Fin width × Fin width) :=
  (grayPivots width).zip (grayPivots width).tail

/--
Choose the CNOT edge for one Gray transition.

With an unchanged pivot, the changed mask position is XORed into that pivot.
When the pivot changes, the old pivot is XORed into the new pivot.
-/
private def grayCNOTEdge {width : ℕ} (changed : Fin width)
    (pivots : Fin width × Fin width) : Fin width × Fin width :=
  if pivots.1 = pivots.2 then (changed, pivots.2) else pivots

/-- The ordered CNOT edges interleaved between the paper's controlled-root gates. -/
def grayCNOTEdges (width : ℕ) : List (Fin width × Fin width) :=
  List.zipWith grayCNOTEdge (grayToggles width) (grayPivotPairs width)

/--
Semantic specification of one generated CNOT transition.

The public relation exposes the two masks, their generated toggle and pivots,
and the resulting concrete edge without exposing the private edge selector.
-/
structure GrayCNOTStep {width : ℕ} (first second : GrayMask width)
    (changed oldPivot newPivot : Fin width) (edge : Fin width × Fin width) : Prop where
  change_eq : first ∆ second = {changed}
  first_pivot : IsGrayPivot first oldPivot
  second_pivot : IsGrayPivot second newPivot
  pivot_le : oldPivot ≤ newPivot
  edge_eq : edge =
    if oldPivot = newPivot then (changed, newPivot) else (oldPivot, newPivot)
  previous_singleton : oldPivot < newPivot → first = {oldPivot}

@[simp]
theorem length_grayPivotPairs (width : ℕ) :
    (grayPivotPairs width).length = 2 ^ width - 2 := by
  rw [grayPivotPairs, List.length_zip, length_grayPivots,
    List.length_tail, length_grayPivots]
  have hpow : 0 < 2 ^ width := pow_pos (by omega) width
  omega

@[simp]
theorem length_grayCNOTEdges (width : ℕ) :
    (grayCNOTEdges width).length = 2 ^ width - 2 := by
  rw [grayCNOTEdges, List.length_zipWith, length_grayToggles,
    length_grayPivotPairs]
  simp

private theorem grayPivot_index_lt {width index : ℕ}
    (hindex : index < (grayCode width).length) :
    index < (grayPivots width).length := by
  rw [length_grayPivots_eq_grayCode]
  exact hindex

private theorem grayCNOTEdge_index_lt {width index : ℕ}
    (hindex : index + 1 < (grayCode width).length) :
    index < (grayCNOTEdges width).length := by
  rw [length_grayCode] at hindex
  rw [length_grayCNOTEdges]
  omega

private theorem grayPivotPair_index_lt {width index : ℕ}
    (hindex : index + 1 < (grayCode width).length) :
    index < (grayPivotPairs width).length := by
  rw [length_grayCode] at hindex
  rw [length_grayPivotPairs]
  omega

/-- The generated pivot at an index is the maximum member of its Gray mask. -/
theorem grayCode_getElem_isGrayPivot {width index : ℕ}
    (hindex : index < (grayCode width).length) :
    IsGrayPivot
      ((grayCode width)[index]'hindex)
      ((grayPivots width)[index]'(grayPivot_index_lt hindex)) := by
  exact (grayCode_pivots width).get hindex (grayPivot_index_lt hindex)

/--
Every generated edge is aligned pointwise with consecutive masks, the generated
toggle, and the two generated maximum-mask pivots.
-/
theorem grayCNOTEdges_getElem_spec {width index : ℕ}
    (hindex : index + 1 < (grayCode width).length) :
    GrayCNOTStep
      ((grayCode width)[index]'(by omega))
      ((grayCode width)[index + 1]'hindex)
      ((grayToggles width)[index]'(grayToggle_index_lt hindex))
      ((grayPivots width)[index]'(grayPivot_index_lt (by omega)))
      ((grayPivots width)[index + 1]'(grayPivot_index_lt hindex))
      ((grayCNOTEdges width)[index]'(grayCNOTEdge_index_lt hindex)) := by
  have hfirstPivot := grayCode_getElem_isGrayPivot (width := width)
    (index := index) (by omega)
  have hsecondPivot := grayCode_getElem_isGrayPivot (width := width)
    (index := index + 1) hindex
  refine
    { change_eq := grayCode_symmDiff_eq_singleton_grayToggle hindex
      first_pivot := hfirstPivot
      second_pivot := hsecondPivot
      pivot_le := (grayPivots_isChain width).getElem index
        (grayPivot_index_lt hindex)
      edge_eq := ?_
      previous_singleton := ?_ }
  · simp [grayCNOTEdges, grayPivotPairs, grayCNOTEdge]
  · intro hpivotLt
    have hrankLt :
        pivotRank ((grayCode width)[index]'(by omega)) <
          pivotRank ((grayCode width)[index + 1]'hindex) := by
      rw [pivotRank_eq_max'_add_one _ hfirstPivot.nonempty,
        hfirstPivot.eq_max',
        pivotRank_eq_max'_add_one _ hsecondPivot.nonempty,
        hsecondPivot.eq_max']
      exact Nat.succ_lt_succ hpivotLt
    rcases grayCode_previous_singleton_of_pivotRank_lt hindex hrankLt with
      ⟨wire, hfirstEq⟩
    have hpivotEq :
        (grayPivots width)[index]'(grayPivot_index_lt (by omega)) = wire := by
      have hpivotMem := hfirstPivot.1
      rw [hfirstEq] at hpivotMem
      simpa using hpivotMem
    simpa [hpivotEq] using hfirstEq

/-- The six CNOTs in the paper's displayed four-bit Gray construction. -/
theorem grayCNOTEdges_three :
    grayCNOTEdges 3 = [(0, 1), (0, 1), (1, 2), (0, 2), (1, 2), (0, 2)] := by
  decide

/-- Boolean register update performed by a CNOT from `control` to `target`. -/
def xorWireUpdate {width : ℕ} (control target : Fin width)
    (state : Fin width → Bool) : Fin width → Bool :=
  Function.update state target (state target + state control)

@[simp]
theorem xorWireUpdate_apply_target {width : ℕ} (control target : Fin width)
    (state : Fin width → Bool) :
    xorWireUpdate control target state target = state target + state control := by
  simp [xorWireUpdate]

@[simp]
theorem xorWireUpdate_apply_of_ne {width : ℕ} (control target wire : Fin width)
    (state : Fin width → Bool) (hwire : wire ≠ target) :
    xorWireUpdate control target state wire = state wire := by
  simp [xorWireUpdate, hwire]

@[simp]
theorem xorWireUpdate_apply_control {width : ℕ} (control target : Fin width)
    (state : Fin width → Bool) (h : control ≠ target) :
    xorWireUpdate control target state control = state control := by
  simp [xorWireUpdate, h]

/-- A CNOT basis update is an involution when its wires are distinct. -/
theorem xorWireUpdate_involutive {width : ℕ} (control target : Fin width)
    (h : control ≠ target) (state : Fin width → Bool) :
    xorWireUpdate control target (xorWireUpdate control target state) = state := by
  funext wire
  by_cases hwire : wire = target
  · subst wire
    simp only [xorWireUpdate_apply_target, xorWireUpdate_apply_control _ _ _ h]
    change Bool.xor (Bool.xor (state target) (state control)) (state control) = state target
    rw [Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
  · rw [xorWireUpdate_apply_of_ne _ _ _ _ hwire,
      xorWireUpdate_apply_of_ne _ _ _ _ hwire]

/-- Execute an ordered list of classical CNOT edges on a Boolean register state. -/
def runXorEdges {width : ℕ} (edges : List (Fin width × Fin width))
    (state : Fin width → Bool) : Fin width → Bool :=
  edges.foldl (fun current edge => xorWireUpdate edge.1 edge.2 current) state

@[simp]
theorem runXorEdges_nil {width : ℕ} (state : Fin width → Bool) :
    runXorEdges [] state = state := rfl

@[simp]
theorem runXorEdges_cons {width : ℕ} (edge : Fin width × Fin width)
    (edges : List (Fin width × Fin width)) (state : Fin width → Bool) :
    runXorEdges (edge :: edges) state =
      runXorEdges edges (xorWireUpdate edge.1 edge.2 state) := by
  simp [runXorEdges, List.foldl_cons]

/-- Execution over concatenated edge lists is sequential composition. -/
theorem runXorEdges_append {width : ℕ} (first second : List (Fin width × Fin width))
    (state : Fin width → Bool) :
    runXorEdges (first ++ second) state =
      runXorEdges second (runXorEdges first state) := by
  simp [runXorEdges, List.foldl_append]

/--
Register state in which `pivot` stores the XOR parity of `mask` and every other
wire retains its original input value.
-/
def parityAccumulatorState {width : ℕ} (mask : GrayMask width) (pivot : Fin width)
    (input : Fin width → Bool) : Fin width → Bool :=
  Function.update input pivot (xorParity mask input)

@[simp]
theorem parityAccumulatorState_apply_pivot {width : ℕ} (mask : GrayMask width)
    (pivot : Fin width) (input : Fin width → Bool) :
    parityAccumulatorState mask pivot input pivot = xorParity mask input := by
  simp [parityAccumulatorState]

@[simp]
theorem parityAccumulatorState_apply_of_ne {width : ℕ} (mask : GrayMask width)
    (pivot wire : Fin width) (input : Fin width → Bool) (hwire : wire ≠ pivot) :
    parityAccumulatorState mask pivot input wire = input wire := by
  simp [parityAccumulatorState, hwire]

/-- A singleton mask already has its parity in its own wire, so no update is needed. -/
@[simp]
theorem parityAccumulatorState_singleton {width : ℕ} (pivot : Fin width)
    (input : Fin width → Bool) :
    parityAccumulatorState ({pivot} : GrayMask width) pivot input = input := by
  funext wire
  by_cases hwire : wire = pivot
  · subst wire
    simp
  · simp [hwire]

/-- A changed Gray position cannot be a pivot selected in both endpoint masks. -/
theorem changed_ne_common_member {width : ℕ} {first second : GrayMask width}
    {changed pivot : Fin width} (hchange : first ∆ second = {changed})
    (hfirst : pivot ∈ first) (hsecond : pivot ∈ second) :
    changed ≠ pivot := by
  intro heq
  subst changed
  have hpivot : pivot ∈ first ∆ second := by
    rw [hchange]
    simp
  rw [Finset.mem_symmDiff] at hpivot
  rcases hpivot with hpivot | hpivot
  · exact hpivot.2 hsecond
  · exact hpivot.2 hfirst

/--
When a Gray edge retains its pivot, one CNOT from the changed raw wire to that
pivot updates exactly from the first parity-accumulator state to the second.
-/
theorem xorWireUpdate_parityAccumulator_samePivot {width : ℕ}
    {first second : GrayMask width} {changed pivot : Fin width}
    (hchange : first ∆ second = {changed})
    (hfirst : pivot ∈ first) (hsecond : pivot ∈ second)
    (input : Fin width → Bool) :
    xorWireUpdate changed pivot (parityAccumulatorState first pivot input) =
      parityAccumulatorState second pivot input := by
  have hchanged : changed ≠ pivot :=
    changed_ne_common_member hchange hfirst hsecond
  funext wire
  by_cases hwire : wire = pivot
  · subst wire
    rw [xorWireUpdate_apply_target, parityAccumulatorState_apply_pivot,
      parityAccumulatorState_apply_of_ne first pivot changed input hchanged,
      parityAccumulatorState_apply_pivot,
      xorParity_eq_add_of_symmDiff_eq_singleton hchange]
  · rw [xorWireUpdate_apply_of_ne _ _ _ _ hwire,
      parityAccumulatorState_apply_of_ne first pivot wire input hwire,
      parityAccumulatorState_apply_of_ne second pivot wire input hwire]

/--
At the only kind of pivot increase in the reflected schedule, one CNOT transfers
the raw singleton old pivot into the new pivot and establishes the two-bit parity.
-/
theorem xorWireUpdate_parityAccumulator_transfer {width : ℕ}
    (oldPivot newPivot : Fin width) (h : oldPivot ≠ newPivot)
    (input : Fin width → Bool) :
    xorWireUpdate oldPivot newPivot
        (parityAccumulatorState ({oldPivot} : GrayMask width) oldPivot input) =
      parityAccumulatorState ({oldPivot, newPivot} : GrayMask width) newPivot input := by
  rw [parityAccumulatorState_singleton]
  funext wire
  by_cases hwire : wire = newPivot
  · subst wire
    simp [parityAccumulatorState, xorParity, h, add_comm]
  · simp [xorWireUpdate, parityAccumulatorState, hwire]

/-- At a strict pivot increase, the toggle is the new pivot and both masks are fixed. -/
theorem GrayCNOTStep.strict_shape {width : ℕ}
    {first second : GrayMask width} {changed oldPivot newPivot : Fin width}
    {edge : Fin width × Fin width}
    (h : GrayCNOTStep first second changed oldPivot newPivot edge)
    (hlt : oldPivot < newPivot) :
    changed = newPivot ∧ first = {oldPivot} ∧ second = {oldPivot, newPivot} := by
  have hfirstEq : first = {oldPivot} := h.previous_singleton hlt
  have hnewNotFirst : newPivot ∉ first := by
    rw [hfirstEq]
    simpa using ne_of_gt hlt
  have hnewDiff : newPivot ∈ first ∆ second :=
    Finset.mem_symmDiff.mpr (Or.inr ⟨h.second_pivot.1, hnewNotFirst⟩)
  rw [h.change_eq] at hnewDiff
  have hchangedEq : changed = newPivot := by
    exact (by simpa using hnewDiff : newPivot = changed).symm
  have hsecondFromDiff : second = first ∆ {changed} := by
    calc
      second = first ∆ (first ∆ second) :=
        (symmDiff_symmDiff_cancel_left first second).symm
      _ = first ∆ {changed} := by rw [h.change_eq]
  have hsecondEq : second = {oldPivot, newPivot} := by
    rw [hfirstEq, hchangedEq] at hsecondFromDiff
    calc
      second = {oldPivot} ∆ {newPivot} := hsecondFromDiff
      _ = {oldPivot, newPivot} := by
        ext wire
        simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
        constructor
        · rintro (⟨hwire, _⟩ | ⟨hwire, _⟩)
          · exact Or.inl hwire
          · exact Or.inr hwire
        · rintro (hwire | hwire)
          · exact Or.inl ⟨hwire, fun hnew =>
              (ne_of_lt hlt) (hwire.symm.trans hnew)⟩
          · exact Or.inr ⟨hwire, fun hold =>
              (ne_of_lt hlt) (hold.symm.trans hwire)⟩
  exact ⟨hchangedEq, hfirstEq, hsecondEq⟩

/-- Every edge satisfying the generated-step specification has distinct wires. -/
theorem GrayCNOTStep.edge_ne {width : ℕ}
    {first second : GrayMask width} {changed oldPivot newPivot : Fin width}
    {edge : Fin width × Fin width}
    (h : GrayCNOTStep first second changed oldPivot newPivot edge) :
    edge.1 ≠ edge.2 := by
  by_cases hpivot : oldPivot = newPivot
  · subst newPivot
    rw [h.edge_eq, if_pos rfl]
    exact changed_ne_common_member h.change_eq
      h.first_pivot.1 h.second_pivot.1
  · rw [h.edge_eq, if_neg hpivot]
    exact hpivot

/-- One specified generated edge advances the parity-accumulator invariant exactly. -/
theorem GrayCNOTStep.xorWireUpdate_parityAccumulator {width : ℕ}
    {first second : GrayMask width} {changed oldPivot newPivot : Fin width}
    {edge : Fin width × Fin width}
    (h : GrayCNOTStep first second changed oldPivot newPivot edge)
    (input : Fin width → Bool) :
    xorWireUpdate edge.1 edge.2
        (parityAccumulatorState first oldPivot input) =
      parityAccumulatorState second newPivot input := by
  by_cases hpivot : oldPivot = newPivot
  · subst newPivot
    rw [h.edge_eq, if_pos rfl]
    exact xorWireUpdate_parityAccumulator_samePivot h.change_eq
      h.first_pivot.1 h.second_pivot.1 input
  · have hpivotLt : oldPivot < newPivot := lt_of_le_of_ne h.pivot_le hpivot
    rcases h.strict_shape hpivotLt with ⟨_, hfirstEq, hsecondEq⟩
    rw [h.edge_eq, if_neg hpivot, hfirstEq, hsecondEq]
    exact xorWireUpdate_parityAccumulator_transfer oldPivot newPivot hpivot input

private theorem grayCode_transition_index_lt_of_edge {width index : ℕ}
    (hindex : index < (grayCNOTEdges width).length) :
    index + 1 < (grayCode width).length := by
  rw [length_grayCNOTEdges] at hindex
  rw [length_grayCode]
  omega

/-- The control and target of every indexed generated CNOT edge are distinct. -/
theorem grayCNOTEdges_getElem_ne {width index : ℕ}
    (hindex : index < (grayCNOTEdges width).length) :
    ((grayCNOTEdges width)[index]'hindex).1 ≠
      ((grayCNOTEdges width)[index]'hindex).2 := by
  exact (grayCNOTEdges_getElem_spec
    (grayCode_transition_index_lt_of_edge hindex)).edge_ne

/-- Every member of the generated schedule is a valid distinct-wire CNOT edge. -/
theorem grayCNOTEdges_wires_ne {width : ℕ} {edge : Fin width × Fin width}
    (hedge : edge ∈ grayCNOTEdges width) : edge.1 ≠ edge.2 := by
  rcases List.mem_iff_getElem.mp hedge with ⟨index, hindex, hedgeEq⟩
  rw [← hedgeEq]
  exact grayCNOTEdges_getElem_ne hindex

/-- One indexed generated edge advances its paired mask/pivot accumulator state. -/
theorem xorWireUpdate_grayCNOTEdges_getElem {width index : ℕ}
    (hindex : index + 1 < (grayCode width).length)
    (input : Fin width → Bool) :
    xorWireUpdate
        ((grayCNOTEdges width)[index]'(grayCNOTEdge_index_lt hindex)).1
        ((grayCNOTEdges width)[index]'(grayCNOTEdge_index_lt hindex)).2
        (parityAccumulatorState
          ((grayCode width)[index]'(by omega))
          ((grayPivots width)[index]'(grayPivot_index_lt (by omega))) input) =
      parityAccumulatorState
        ((grayCode width)[index + 1]'hindex)
        ((grayPivots width)[index + 1]'(grayPivot_index_lt hindex)) input := by
  exact (grayCNOTEdges_getElem_spec hindex).xorWireUpdate_parityAccumulator input

private theorem head?_grayCode_succ : ∀ width,
    (grayCode (width + 1)).head? = some {0} := by
  intro width
  induction width with
  | zero => simp [grayCode_one]
  | succ width ih =>
      rw [grayCode_succ, List.head?_append, List.head?_map, ih]
      simp [liftGrayMask]

/-- The positive-width runtime schedule begins at the singleton first control. -/
theorem grayCode_head?_succ (width : ℕ) :
    (grayCode (width + 1)).head? = some {0} :=
  head?_grayCode_succ width

private theorem parityAccumulatorState_grayCode_head (width : ℕ)
    (input : Fin (width + 1) → Bool) :
    parityAccumulatorState
        ((grayCode (width + 1))[0]'(by simp))
        ((grayPivots (width + 1))[0]'(by simp)) input = input := by
  have hhead := head?_grayCode_succ width
  have hmaskEq : (grayCode (width + 1))[0]'(by simp) = {0} := by
    apply Option.some.inj
    rw [← List.getElem?_eq_getElem (by simp), ← List.head?_eq_getElem?]
    exact hhead
  have hpivot := grayCode_getElem_isGrayPivot (width := width + 1)
    (index := 0) (by simp)
  have hpivotEq : (grayPivots (width + 1))[0]'(by simp) = 0 := by
    have hpivotMem := hpivot.1
    rw [hmaskEq] at hpivotMem
    simpa using hpivotMem
  rw [hmaskEq, hpivotEq]
  exact parityAccumulatorState_singleton 0 input

/--
After any valid prefix of the generated CNOT schedule, the current generated
pivot stores exactly the parity of the corresponding Gray mask, and every other
wire still contains its original input bit.
-/
theorem runXorEdges_take_grayCNOTEdges {width count : ℕ}
    (hwidth : 0 < width) (hcount : count < (grayCode width).length)
    (input : Fin width → Bool) :
    runXorEdges ((grayCNOTEdges width).take count) input =
      parityAccumulatorState
        ((grayCode width)[count]'hcount)
        ((grayPivots width)[count]'(grayPivot_index_lt hcount)) input := by
  obtain ⟨width, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hwidth)
  induction count with
  | zero =>
      simpa using (parityAccumulatorState_grayCode_head width input).symm
  | succ count ih =>
      have htransition : count + 1 < (grayCode (width + 1)).length := by
        simpa using hcount
      have hedgeIndex := grayCNOTEdge_index_lt htransition
      rw [List.take_succ_eq_append_getElem hedgeIndex, runXorEdges_append]
      simp only [runXorEdges_cons, runXorEdges_nil]
      rw [ih (by omega)]
      exact xorWireUpdate_grayCNOTEdges_getElem htransition input

/-- The complete generated CNOT schedule restores every input control wire. -/
theorem runXorEdges_grayCNOTEdges (width : ℕ) (input : Fin width → Bool) :
    runXorEdges (grayCNOTEdges width) input = input := by
  cases width with
  | zero => rfl
  | succ width =>
      have hlastIndex :
          (grayCNOTEdges (width + 1)).length <
            (grayCode (width + 1)).length := by
        rw [length_grayCNOTEdges, length_grayCode]
        have hpow : 0 < 2 ^ (width + 1) := pow_pos (by omega) _
        omega
      have hrun := runXorEdges_take_grayCNOTEdges
        (width := width + 1) (count := (grayCNOTEdges (width + 1)).length)
        (by omega) hlastIndex input
      rw [List.take_length] at hrun
      have hlastIndexEq :
          (grayCNOTEdges (width + 1)).length =
            (grayCode (width + 1)).length - 1 := by
        rw [length_grayCNOTEdges, length_grayCode]
        omega
      have hlastMask :
          (grayCode (width + 1))[(grayCNOTEdges (width + 1)).length]'hlastIndex =
            {Fin.last width} := by
        have hlast := getLast?_grayCode_succ width
        rw [List.getLast?_eq_getElem?, ← hlastIndexEq,
          List.getElem?_eq_getElem hlastIndex] at hlast
        exact Option.some.inj hlast
      have hpivot := grayCode_getElem_isGrayPivot hlastIndex
      have hlastPivot :
          (grayPivots (width + 1))[(grayCNOTEdges (width + 1)).length]'
              (grayPivot_index_lt hlastIndex) = Fin.last width := by
        rw [hlastMask] at hpivot
        simpa using hpivot.1
      rw [hlastMask, hlastPivot, parityAccumulatorState_singleton] at hrun
      exact hrun

end Barenco.MultiControl
