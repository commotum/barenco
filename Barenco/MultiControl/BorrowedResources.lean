import Barenco.MultiControl.Borrowed

/-!
# Structural resources for dirty-borrowed inward ladders

This leaf records the width, support, and partial-cost facts that follow from the
explicit Lemma 7.2 syntax.  Toffoli nodes remain macros: both named paper cost
models reject the half and full ladders until those nodes are replaced by
explicit primitive expansions.
-/

namespace Barenco.MultiControl

namespace InwardLadderLayout

/-! ## Logical capacity and touched support -/

/-- Every inward-ladder layout carries exactly `2 * b + 3` distinct logical wires. -/
theorem slotCount_le_ambientWidth {b n : ℕ} (layout : InwardLadderLayout b n) :
    2 * b + 3 ≤ n := by
  have hcard := Fintype.card_le_of_injective layout.wire layout.wire.injective
  simp [InwardLadderSlot] at hcard
  omega

/-- The image of every logical control, borrowed wire, and target in the ambient register. -/
def logicalSupport {b n : ℕ} (layout : InwardLadderLayout b n) : Finset (Fin n) :=
  Finset.univ.map layout.wire

@[simp]
theorem logicalSupport_card {b n : ℕ} (layout : InwardLadderLayout b n) :
    layout.logicalSupport.card = 2 * b + 3 := by
  simp [logicalSupport, InwardLadderSlot]
  omega

@[simp]
theorem controlWire_mem_logicalSupport {b n : ℕ} (layout : InwardLadderLayout b n)
    (control : Fin (b + 2)) :
    layout.controlWire control ∈ layout.logicalSupport := by
  rw [logicalSupport, Finset.mem_map]
  exact ⟨Sum.inl control, Finset.mem_univ _, rfl⟩

@[simp]
theorem workWire_mem_logicalSupport {b n : ℕ} (layout : InwardLadderLayout b n)
    (work : Fin (b + 1)) :
    layout.workWire work ∈ layout.logicalSupport := by
  rw [logicalSupport, Finset.mem_map]
  exact ⟨Sum.inr work, Finset.mem_univ _, rfl⟩

@[simp]
theorem borrowedWire_mem_logicalSupport {b n : ℕ}
    (layout : InwardLadderLayout b n) (borrowed : Fin b) :
    layout.borrowedWire borrowed ∈ layout.logicalSupport := by
  exact layout.workWire_mem_logicalSupport borrowed.castSucc

@[simp]
theorem targetWire_mem_logicalSupport {b n : ℕ} (layout : InwardLadderLayout b n) :
    layout.targetWire ∈ layout.logicalSupport := by
  exact layout.workWire_mem_logicalSupport (Fin.last b)

/-- The smaller recursive layout uses only logical wires of its parent layout. -/
theorem logicalSupport_smaller_subset {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    layout.smaller.logicalSupport ⊆ layout.logicalSupport := by
  intro wire hwire
  rw [logicalSupport, Finset.mem_map] at hwire ⊢
  rcases hwire with ⟨slot, _, rfl⟩
  exact ⟨prefixSlotEmbedding b slot, Finset.mem_univ _, rfl⟩

private theorem baseToffoli_support_subset {n : ℕ}
    (layout : InwardLadderLayout 0 n) :
    layout.baseToffoli.support ⊆ layout.logicalSupport := by
  intro wire hwire
  rw [baseToffoli, Primitive.toffoli_support] at hwire
  simp only [Finset.mem_insert, Finset.mem_singleton] at hwire
  rcases hwire with hwire | hwire | hwire
  · subst wire
    exact layout.controlWire_mem_logicalSupport 0
  · subst wire
    exact layout.controlWire_mem_logicalSupport 1
  · subst wire
    exact layout.targetWire_mem_logicalSupport

private theorem outerToffoli_support_subset {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    layout.outerToffoli.support ⊆ layout.logicalSupport := by
  intro wire hwire
  rw [outerToffoli, Primitive.toffoli_support] at hwire
  simp only [Finset.mem_insert, Finset.mem_singleton] at hwire
  rcases hwire with hwire | hwire | hwire
  · subst wire
    exact layout.controlWire_mem_logicalSupport _
  · subst wire
    exact layout.borrowedWire_mem_logicalSupport _
  · subst wire
    exact layout.targetWire_mem_logicalSupport

/-- No half-ladder primitive names a wire outside its supplied logical layout. -/
theorem touchedSupport_halfLadderCircuit_subset {b n : ℕ}
    (layout : InwardLadderLayout b n) :
    Circuit.touchedSupport (halfLadderCircuit b layout) ⊆ layout.logicalSupport := by
  revert layout
  induction b with
  | zero =>
      intro layout
      change layout.baseToffoli.support ∪ ∅ ⊆ layout.logicalSupport
      simpa using baseToffoli_support_subset layout
  | succ b ih =>
      intro layout
      have houter : Circuit.touchedSupport [layout.outerToffoli] ⊆
          layout.logicalSupport := by
        change layout.outerToffoli.support ∪ ∅ ⊆ layout.logicalSupport
        simpa using outerToffoli_support_subset layout
      rw [halfLadderCircuit, Circuit.touchedSupport_append,
        Circuit.touchedSupport_append]
      refine Finset.union_subset houter (Finset.union_subset ?_ houter)
      exact (ih layout.smaller).trans (logicalSupport_smaller_subset layout)

/-- No complete inward ladder primitive touches an ambient spectator wire. -/
theorem touchedSupport_inwardLadderCircuit_subset {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    Circuit.touchedSupport (inwardLadderCircuit layout) ⊆ layout.logicalSupport := by
  rw [inwardLadderCircuit, Circuit.touchedSupport_append]
  exact Finset.union_subset (touchedSupport_halfLadderCircuit_subset layout)
    ((touchedSupport_halfLadderCircuit_subset layout.smaller).trans
      (logicalSupport_smaller_subset layout))

/-- A half ladder touches at most the `2 * b + 3` logical wires in its layout. -/
theorem touchedSupport_halfLadderCircuit_card_le {b n : ℕ}
    (layout : InwardLadderLayout b n) :
    (Circuit.touchedSupport (halfLadderCircuit b layout)).card ≤ 2 * b + 3 := by
  calc
    (Circuit.touchedSupport (halfLadderCircuit b layout)).card ≤
        layout.logicalSupport.card :=
      Finset.card_le_card (touchedSupport_halfLadderCircuit_subset layout)
    _ = 2 * b + 3 := logicalSupport_card layout

/-- The full positive-borrow ladder touches at most all of its logical wires. -/
theorem touchedSupport_inwardLadderCircuit_card_le {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    (Circuit.touchedSupport (inwardLadderCircuit layout)).card ≤
      2 * (b + 1) + 3 := by
  calc
    (Circuit.touchedSupport (inwardLadderCircuit layout)).card ≤
        layout.logicalSupport.card :=
      Finset.card_le_card (touchedSupport_inwardLadderCircuit_subset layout)
    _ = 2 * (b + 1) + 3 := logicalSupport_card layout

/-! ## Named cost-model rejection -/

/-- An unexpanded half ladder has no one-qubit+CNOT cost. -/
@[simp]
theorem halfLadderCircuit_oneQubitCNOTCost {b n : ℕ}
    (layout : InwardLadderLayout b n) :
    Circuit.cost CostModel.oneQubitCNOT (halfLadderCircuit b layout) = none := by
  cases b with
  | zero => simp [halfLadderCircuit, Circuit.cost, Circuit.addCost]
  | succ b =>
      simp [halfLadderCircuit, Circuit.cost_append, Circuit.cost, Circuit.addCost]

/-- An unexpanded half ladder is also unsupported by the at-most-two-qubit model. -/
@[simp]
theorem halfLadderCircuit_arbitraryTwoQubitCost {b n : ℕ}
    (layout : InwardLadderLayout b n) :
    Circuit.cost CostModel.arbitraryTwoQubit (halfLadderCircuit b layout) = none := by
  cases b with
  | zero => simp [halfLadderCircuit, Circuit.cost, Circuit.addCost]
  | succ b =>
      simp [halfLadderCircuit, Circuit.cost_append, Circuit.cost, Circuit.addCost]

/-- The full unexpanded Lemma 7.2 syntax has no one-qubit+CNOT cost. -/
@[simp]
theorem inwardLadderCircuit_oneQubitCNOTCost {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    Circuit.cost CostModel.oneQubitCNOT (inwardLadderCircuit layout) = none := by
  rw [inwardLadderCircuit, Circuit.cost_append,
    halfLadderCircuit_oneQubitCNOTCost]
  simp

/-- The full unexpanded ladder is not an at-most-two-qubit circuit either. -/
@[simp]
theorem inwardLadderCircuit_arbitraryTwoQubitCost {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    Circuit.cost CostModel.arbitraryTwoQubit (inwardLadderCircuit layout) = none := by
  rw [inwardLadderCircuit, Circuit.cost_append,
    halfLadderCircuit_arbitraryTwoQubitCost]
  simp

end InwardLadderLayout

end Barenco.MultiControl
