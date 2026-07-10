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

end Barenco.MultiControl
