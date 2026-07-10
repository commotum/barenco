import Barenco.MultiControl.BorrowedResources
import Barenco.MultiControl.BorrowedSemantics
import Barenco.MultiControl.FourBlock

/-!
# Exact Toffoli-macro expansion for Corollary 7.4

This module composes the exact dirty-borrowed inward ladders of Lemma 7.2 with
the checked `A; B; A; B` substitution theorem of Lemma 7.3.  In the live
`FourBlockLayout l r` parameters, block A has `l + 2` controls and therefore
uses `l` borrowed wires, while block B has `r + 2` controls and uses `r`
borrowed wires.  Both parameters must consequently be positive.

The A ladder borrows from the second data-control group and, if needed, the
final target.  The B ladder borrows from the first data-control group.  Each
complete ladder restores its borrowed wires before the next block executes, so
the composition is exact for arbitrary dirty inputs and arbitrary ambient
spectators.

Only Toffoli macros are counted here.  The named one-qubit+CNOT model rejects
the circuit until a later module supplies an explicit basic-gate expansion.
-/

namespace Barenco.MultiControl

namespace FourBlockLayout

/-! ## Workspace embeddings -/

/-- Available A-workspace slots: second-group controls, followed by the final target. -/
def aWorkspaceSumEmbedding (l r : ℕ) :
    (Fin (r + 1) ⊕ Fin 1) ↪ FourBlockSlot l r where
  toFun
    | Sum.inl right => Sum.inr (Sum.inl right)
    | Sum.inr _ => Sum.inr (Sum.inr 1)
  inj' := by
    intro first second h
    cases first with
    | inl firstRight =>
        cases second with
        | inl secondRight =>
            exact congrArg Sum.inl (Sum.inl.inj (Sum.inr.inj h))
        | inr secondTarget =>
            have : (Sum.inl firstRight : Fin (r + 1) ⊕ Fin 2) = Sum.inr 1 :=
              Sum.inr.inj h
            cases this
    | inr firstTarget =>
        cases second with
        | inl secondRight =>
            have : (Sum.inr 1 : Fin (r + 1) ⊕ Fin 2) = Sum.inl secondRight :=
              Sum.inr.inj h
            cases this
        | inr secondTarget =>
            exact congrArg Sum.inr (Subsingleton.elim firstTarget secondTarget)

/-- The A-workspace register as a single finite interval of size `r + 2`. -/
def aWorkspaceSlotEmbedding (l r : ℕ) :
    Fin ((r + 1) + 1) ↪ FourBlockSlot l r :=
  (@finSumFinEquiv (r + 1) 1).symm.toEmbedding.trans
    (aWorkspaceSumEmbedding l r)

/-- Choose the first `l` available A-workspace slots under the exact capacity bound. -/
def aBorrowSlotEmbedding {l r : ℕ} (hcapacity : l ≤ r + 2) :
    Fin l ↪ FourBlockSlot l r :=
  (Fin.castLEEmb hcapacity).trans (aWorkspaceSlotEmbedding l r)

/-- Under the stronger prefix bound, A's chosen workspace stays in the right group. -/
theorem aBorrowSlotEmbedding_eq_rightControl {l r : ℕ}
    (hcapacity : l ≤ r + 2) (htargetFree : l ≤ r + 1) (borrowed : Fin l) :
    aBorrowSlotEmbedding hcapacity borrowed =
      Sum.inr (Sum.inl (Fin.castLE htargetFree borrowed)) := by
  have hcast : Fin.castLE hcapacity borrowed =
      Fin.castAdd 1 (Fin.castLE htargetFree borrowed) := by
    apply Fin.ext
    rfl
  simp [aBorrowSlotEmbedding, aWorkspaceSlotEmbedding,
    aWorkspaceSumEmbedding, hcast]

/-- Thus the target slot is not borrowed whenever the right group alone has capacity. -/
theorem aBorrowSlotEmbedding_ne_target {l r : ℕ}
    (hcapacity : l ≤ r + 2) (htargetFree : l ≤ r + 1) (borrowed : Fin l) :
    aBorrowSlotEmbedding hcapacity borrowed ≠
      (Sum.inr (Sum.inr 1) : FourBlockSlot l r) := by
  rw [aBorrowSlotEmbedding_eq_rightControl hcapacity htargetFree]
  intro h
  cases Sum.inr.inj h

/-- First-group controls as possible dirty workspace for block B. -/
def leftControlSlotEmbedding (l r : ℕ) :
    Fin (l + 2) ↪ FourBlockSlot l r where
  toFun := Sum.inl
  inj' := Sum.inl_injective

/-- Choose the first `r` first-group controls as B's dirty workspace. -/
def bBorrowSlotEmbedding {l r : ℕ} (hcapacity : r ≤ l + 2) :
    Fin r ↪ FourBlockSlot l r :=
  (Fin.castLEEmb hcapacity).trans (leftControlSlotEmbedding l r)

/-! ## Concrete inward-ladder layouts -/

/-- Work-register embedding for A: `l` borrowed slots followed by A's dirty target. -/
def aWorkSumEmbedding {l r : ℕ} (hcapacity : l ≤ r + 2) :
    (Fin l ⊕ Fin 1) ↪ FourBlockSlot l r where
  toFun
    | Sum.inl borrowed => aBorrowSlotEmbedding hcapacity borrowed
    | Sum.inr _ => Sum.inr (Sum.inr 0)
  inj' := by
    intro first second h
    cases first with
    | inl firstBorrowed =>
        cases second with
        | inl secondBorrowed =>
            exact congrArg Sum.inl ((aBorrowSlotEmbedding hcapacity).injective h)
        | inr secondTarget =>
            change aBorrowSlotEmbedding hcapacity firstBorrowed =
              (Sum.inr (Sum.inr 0) : FourBlockSlot l r) at h
            cases hsplit : (@finSumFinEquiv (r + 1) 1).symm
                (Fin.castLE hcapacity firstBorrowed) with
            | inl right =>
                simp [aBorrowSlotEmbedding, aWorkspaceSlotEmbedding,
                  aWorkspaceSumEmbedding, hsplit] at h
            | inr last =>
                have hlast : last = 0 := Subsingleton.elim _ _
                subst last
                simp [aBorrowSlotEmbedding, aWorkspaceSlotEmbedding,
                  aWorkspaceSumEmbedding, hsplit] at h
    | inr firstTarget =>
        cases second with
        | inl secondBorrowed =>
            change (Sum.inr (Sum.inr 0) : FourBlockSlot l r) =
              aBorrowSlotEmbedding hcapacity secondBorrowed at h
            cases hsplit : (@finSumFinEquiv (r + 1) 1).symm
                (Fin.castLE hcapacity secondBorrowed) with
            | inl right =>
                simp [aBorrowSlotEmbedding, aWorkspaceSlotEmbedding,
                  aWorkspaceSumEmbedding, hsplit] at h
            | inr last =>
                have hlast : last = 0 := Subsingleton.elim _ _
                subst last
                simp [aBorrowSlotEmbedding, aWorkspaceSlotEmbedding,
                  aWorkspaceSumEmbedding, hsplit] at h
        | inr secondTarget =>
            exact congrArg Sum.inr (Subsingleton.elim firstTarget secondTarget)

/-- A's complete work register, with its target in the final position. -/
def aWorkSlotEmbedding {l r : ℕ} (hcapacity : l ≤ r + 2) :
    Fin (l + 1) ↪ FourBlockSlot l r :=
  (@finSumFinEquiv l 1).symm.toEmbedding.trans
    (aWorkSumEmbedding hcapacity)

private theorem aWorkSlotEmbedding_eq_inr {l r : ℕ}
    (hcapacity : l ≤ r + 2) (work : Fin (l + 1)) :
    ∃ inner : Fin (r + 1) ⊕ Fin 2,
      aWorkSlotEmbedding hcapacity work = Sum.inr inner := by
  cases hwork : (@finSumFinEquiv l 1).symm work with
  | inl borrowed =>
      cases hborrow : (@finSumFinEquiv (r + 1) 1).symm
          (Fin.castLE hcapacity borrowed) with
      | inl right =>
          exact ⟨Sum.inl right, by simp [aWorkSlotEmbedding, aWorkSumEmbedding,
            aBorrowSlotEmbedding, aWorkspaceSlotEmbedding,
            aWorkspaceSumEmbedding, hwork, hborrow]⟩
      | inr target =>
          exact ⟨Sum.inr 1, by simp [aWorkSlotEmbedding, aWorkSumEmbedding,
            aBorrowSlotEmbedding, aWorkspaceSlotEmbedding,
            aWorkspaceSumEmbedding, hwork, hborrow]⟩
  | inr target =>
      exact ⟨Sum.inr 0, by simp [aWorkSlotEmbedding, aWorkSumEmbedding, hwork]⟩

/-- All A-ladder logical slots inside the common four-block slot layout. -/
def aLadderSlotEmbedding {l r : ℕ} (hcapacity : l ≤ r + 2) :
    InwardLadderSlot l ↪ FourBlockSlot l r where
  toFun
    | Sum.inl control => Sum.inl control
    | Sum.inr work => aWorkSlotEmbedding hcapacity work
  inj' := by
    intro first second h
    cases first with
    | inl firstControl =>
        cases second with
        | inl secondControl => exact congrArg Sum.inl (Sum.inl.inj h)
        | inr secondWork =>
            change (Sum.inl firstControl : FourBlockSlot l r) =
              aWorkSlotEmbedding hcapacity secondWork at h
            rcases aWorkSlotEmbedding_eq_inr hcapacity secondWork with
              ⟨inner, hinner⟩
            rw [hinner] at h
            cases h
    | inr firstWork =>
        cases second with
        | inl secondControl =>
            change aWorkSlotEmbedding hcapacity firstWork =
              (Sum.inl secondControl : FourBlockSlot l r) at h
            rcases aWorkSlotEmbedding_eq_inr hcapacity firstWork with
              ⟨inner, hinner⟩
            rw [hinner] at h
            cases h
        | inr secondWork =>
            exact congrArg Sum.inr ((aWorkSlotEmbedding hcapacity).injective h)

/-- The exact Lemma 7.2 implementation of block A in the common ambient register. -/
def aInwardLadderLayout {l r n : ℕ} (layout : FourBlockLayout l r n)
    (hcapacity : l ≤ r + 2) : InwardLadderLayout l n where
  wire := (aLadderSlotEmbedding hcapacity).trans layout.wire

/-- Work-register embedding for B: `r` borrowed first-group controls, then target. -/
def bWorkSumEmbedding {l r : ℕ} (hcapacity : r ≤ l + 2) :
    (Fin r ⊕ Fin 1) ↪ FourBlockSlot l r where
  toFun
    | Sum.inl borrowed => bBorrowSlotEmbedding hcapacity borrowed
    | Sum.inr _ => Sum.inr (Sum.inr 1)
  inj' := by
    intro first second h
    cases first with
    | inl firstBorrowed =>
        cases second with
        | inl secondBorrowed =>
            exact congrArg Sum.inl ((bBorrowSlotEmbedding hcapacity).injective h)
        | inr secondTarget =>
            change bBorrowSlotEmbedding hcapacity firstBorrowed =
              (Sum.inr (Sum.inr 1) : FourBlockSlot l r) at h
            simp [bBorrowSlotEmbedding, leftControlSlotEmbedding] at h
    | inr firstTarget =>
        cases second with
        | inl secondBorrowed =>
            change (Sum.inr (Sum.inr 1) : FourBlockSlot l r) =
              bBorrowSlotEmbedding hcapacity secondBorrowed at h
            simp [bBorrowSlotEmbedding, leftControlSlotEmbedding] at h
        | inr secondTarget =>
            exact congrArg Sum.inr (Subsingleton.elim firstTarget secondTarget)

/-- B's complete work register, with the final circuit target last. -/
def bWorkSlotEmbedding {l r : ℕ} (hcapacity : r ≤ l + 2) :
    Fin (r + 1) ↪ FourBlockSlot l r :=
  (@finSumFinEquiv r 1).symm.toEmbedding.trans
    (bWorkSumEmbedding hcapacity)

private theorem bControlSlotEmbedding_ne_bWorkSlotEmbedding {l r : ℕ}
    (hcapacity : r ≤ l + 2) (control : Fin (r + 2))
    (work : Fin (r + 1)) :
    bControlSlotEmbedding l r control ≠ bWorkSlotEmbedding hcapacity work := by
  intro h
  cases hcontrol : (@finSumFinEquiv (r + 1) 1).symm control with
  | inl right =>
      cases hwork : (@finSumFinEquiv r 1).symm work with
      | inl borrowed =>
          simp [bControlSlotEmbedding, bControlSumEmbedding,
            bWorkSlotEmbedding, bWorkSumEmbedding, bBorrowSlotEmbedding,
            leftControlSlotEmbedding, hcontrol, hwork] at h
      | inr target =>
          simp [bControlSlotEmbedding, bControlSumEmbedding,
            bWorkSlotEmbedding, bWorkSumEmbedding, hcontrol, hwork] at h
  | inr dirty =>
      cases hwork : (@finSumFinEquiv r 1).symm work with
      | inl borrowed =>
          simp [bControlSlotEmbedding, bControlSumEmbedding,
            bWorkSlotEmbedding, bWorkSumEmbedding, bBorrowSlotEmbedding,
            leftControlSlotEmbedding, hcontrol, hwork] at h
      | inr target =>
          simp [bControlSlotEmbedding, bControlSumEmbedding,
            bWorkSlotEmbedding, bWorkSumEmbedding, hcontrol, hwork] at h

/-- All B-ladder logical slots inside the common four-block slot layout. -/
def bLadderSlotEmbedding {l r : ℕ} (hcapacity : r ≤ l + 2) :
    InwardLadderSlot r ↪ FourBlockSlot l r where
  toFun
    | Sum.inl control => bControlSlotEmbedding l r control
    | Sum.inr work => bWorkSlotEmbedding hcapacity work
  inj' := by
    intro first second h
    cases first with
    | inl firstControl =>
        cases second with
        | inl secondControl =>
            exact congrArg Sum.inl ((bControlSlotEmbedding l r).injective h)
        | inr secondWork =>
            change bControlSlotEmbedding l r firstControl =
              bWorkSlotEmbedding hcapacity secondWork at h
            exact (bControlSlotEmbedding_ne_bWorkSlotEmbedding
              hcapacity firstControl secondWork h).elim
    | inr firstWork =>
        cases second with
        | inl secondControl =>
            change bWorkSlotEmbedding hcapacity firstWork =
              bControlSlotEmbedding l r secondControl at h
            exact (bControlSlotEmbedding_ne_bWorkSlotEmbedding
              hcapacity secondControl firstWork h.symm).elim
        | inr secondWork =>
            exact congrArg Sum.inr ((bWorkSlotEmbedding hcapacity).injective h)

/-- The exact Lemma 7.2 implementation of block B in the common ambient register. -/
def bInwardLadderLayout {l r n : ℕ} (layout : FourBlockLayout l r n)
    (hcapacity : r ≤ l + 2) : InwardLadderLayout r n where
  wire := (bLadderSlotEmbedding hcapacity).trans layout.wire

@[simp]
theorem aInwardLadderLayout_controlWire {l r n : ℕ}
    (layout : FourBlockLayout l r n) (hcapacity : l ≤ r + 2)
    (control : Fin (l + 2)) :
    (layout.aInwardLadderLayout hcapacity).controlWire control =
      layout.leftControlWire control :=
  rfl

@[simp]
theorem aInwardLadderLayout_targetWire {l r n : ℕ}
    (layout : FourBlockLayout l r n) (hcapacity : l ≤ r + 2) :
    (layout.aInwardLadderLayout hcapacity).targetWire = layout.dirtyWire := by
  simp [aInwardLadderLayout, InwardLadderLayout.targetWire,
    InwardLadderLayout.workWire, aLadderSlotEmbedding, aWorkSlotEmbedding,
    aWorkSumEmbedding, dirtyWire]

@[simp]
theorem bInwardLadderLayout_controlWire {l r n : ℕ}
    (layout : FourBlockLayout l r n) (hcapacity : r ≤ l + 2)
    (control : Fin (r + 2)) :
    (layout.bInwardLadderLayout hcapacity).controlWire control =
      layout.bControlEmbedding control :=
  rfl

@[simp]
theorem bInwardLadderLayout_targetWire {l r n : ℕ}
    (layout : FourBlockLayout l r n) (hcapacity : r ≤ l + 2) :
    (layout.bInwardLadderLayout hcapacity).targetWire = layout.targetWire := by
  simp [bInwardLadderLayout, InwardLadderLayout.targetWire,
    InwardLadderLayout.workWire, bLadderSlotEmbedding, bWorkSlotEmbedding,
    bWorkSumEmbedding, targetWire]

theorem aInwardLadderLayout_orderedControlLayout {l r n : ℕ}
    (layout : FourBlockLayout l r n) (hcapacity : l ≤ r + 2) :
    (layout.aInwardLadderLayout hcapacity).orderedControlLayout =
      layout.aLayout := by
  rw [OrderedControlLayout.mk.injEq]
  constructor
  · apply Function.Embedding.ext
    intro control
    rfl
  · exact layout.aInwardLadderLayout_targetWire hcapacity

theorem bInwardLadderLayout_orderedControlLayout {l r n : ℕ}
    (layout : FourBlockLayout l r n) (hcapacity : r ≤ l + 2) :
    (layout.bInwardLadderLayout hcapacity).orderedControlLayout =
      layout.bLayout := by
  rw [OrderedControlLayout.mk.injEq]
  constructor
  · apply Function.Embedding.ext
    intro control
    rfl
  · exact layout.bInwardLadderLayout_targetWire hcapacity

/-- If A fits in the right group alone, its complete logical support excludes the final target. -/
theorem targetWire_not_mem_aInwardLadderLogicalSupport {l r n : ℕ}
    (layout : FourBlockLayout l r n) (hcapacity : l ≤ r + 2)
    (htargetFree : l ≤ r + 1) :
    layout.targetWire ∉
      (layout.aInwardLadderLayout hcapacity).logicalSupport := by
  intro hmem
  rw [InwardLadderLayout.logicalSupport, Finset.mem_map] at hmem
  rcases hmem with ⟨slot, _, hslot⟩
  have hslot' : aLadderSlotEmbedding hcapacity slot =
      (Sum.inr (Sum.inr 1) : FourBlockSlot l r) := by
    apply layout.wire.injective
    simpa [aInwardLadderLayout, targetWire] using hslot
  cases slot with
  | inl control => cases hslot'
  | inr work =>
      cases hwork : (@finSumFinEquiv l 1).symm work with
      | inl borrowed =>
          apply aBorrowSlotEmbedding_ne_target hcapacity htargetFree borrowed
          simpa [aLadderSlotEmbedding, aWorkSlotEmbedding, aWorkSumEmbedding,
            hwork] using hslot'
      | inr last =>
          have hlast : last = 0 := Subsingleton.elim _ _
          subst last
          simp [aLadderSlotEmbedding, aWorkSlotEmbedding, aWorkSumEmbedding,
            hwork] at hslot'

/-! ## Positive-tail Corollary 7.4 circuit -/

/-- Lemma 7.2 layout for A, indexed by the subtraction-free borrowed tail `leftTail`. -/
def corollary74ALayout {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hcapacity : leftTail ≤ rightTail + 2) :
    InwardLadderLayout (leftTail + 1) n :=
  layout.aInwardLadderLayout (by omega)

/-- Lemma 7.2 layout for B, indexed by the subtraction-free borrowed tail `rightTail`. -/
def corollary74BLayout {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hcapacity : rightTail ≤ leftTail + 2) :
    InwardLadderLayout (rightTail + 1) n :=
  layout.bInwardLadderLayout (by omega)

/-- The exact inward-ladder implementation of A. -/
def corollary74AImplementation {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hcapacity : leftTail ≤ rightTail + 2) : Circuit n :=
  InwardLadderLayout.inwardLadderCircuit
    (layout.corollary74ALayout hcapacity)

/-- The exact inward-ladder implementation of B. -/
def corollary74BImplementation {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hcapacity : rightTail ≤ leftTail + 2) : Circuit n :=
  InwardLadderLayout.inwardLadderCircuit
    (layout.corollary74BLayout hcapacity)

/-- Corrected Corollary 7.4, still expressed as exact Toffoli macros. -/
def corollary74Circuit {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2) (hright : rightTail ≤ leftTail + 2) :
    Circuit n :=
  fourBlockSubstitutionCircuit
    (layout.corollary74AImplementation hleft)
    (layout.corollary74BImplementation hright)

private theorem eval_corollary74AImplementation {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hcapacity : leftTail ≤ rightTail + 2) :
    Circuit.eval (layout.corollary74AImplementation hcapacity) =
      layout.blockA.denotation := by
  rw [corollary74AImplementation,
    InwardLadderLayout.eval_inwardLadderCircuit]
  change positiveControlledUnitary
      (layout.corollary74ALayout hcapacity).orderedControlLayout.targetWire
      (layout.corollary74ALayout hcapacity).orderedControlLayout.controlSet pauliX =
    positiveControlledUnitary layout.aLayout.targetWire layout.aLayout.controlSet pauliX
  rw [show (layout.corollary74ALayout hcapacity).orderedControlLayout =
      layout.aLayout by
    exact layout.aInwardLadderLayout_orderedControlLayout _]

private theorem eval_corollary74BImplementation {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hcapacity : rightTail ≤ leftTail + 2) :
    Circuit.eval (layout.corollary74BImplementation hcapacity) =
      layout.blockB.denotation := by
  rw [corollary74BImplementation,
    InwardLadderLayout.eval_inwardLadderCircuit]
  change positiveControlledUnitary
      (layout.corollary74BLayout hcapacity).orderedControlLayout.targetWire
      (layout.corollary74BLayout hcapacity).orderedControlLayout.controlSet pauliX =
    positiveControlledUnitary layout.bLayout.targetWire layout.bLayout.controlSet pauliX
  rw [show (layout.corollary74BLayout hcapacity).orderedControlLayout =
      layout.bLayout by
    exact layout.bInwardLadderLayout_orderedControlLayout _]

/--
Exact full-register semantics of the corrected Toffoli-macro construction.
All borrowed data wires and all ambient spectators are restored.
-/
@[simp]
theorem eval_corollary74Circuit {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2) (hright : rightTail ≤ leftTail + 2) :
    Circuit.eval (layout.corollary74Circuit hleft hright) =
      positiveControlledUnitary layout.targetWire layout.dataLayout.controlSet pauliX := by
  exact eval_fourBlockSubstitutionCircuit layout _ _
    (eval_corollary74AImplementation layout hleft)
    (eval_corollary74BImplementation layout hright)

/-! ## Exact Toffoli-macro resources -/

@[simp]
theorem corollary74AImplementation_gateCount {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hcapacity : leftTail ≤ rightTail + 2) :
    Circuit.gateCount (layout.corollary74AImplementation hcapacity) =
      4 * (leftTail + 1) := by
  simp [corollary74AImplementation]

@[simp]
theorem corollary74AImplementation_toffoliCount {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hcapacity : leftTail ≤ rightTail + 2) :
    Circuit.kindCount .toffoli (layout.corollary74AImplementation hcapacity) =
      4 * (leftTail + 1) := by
  simp [corollary74AImplementation]

@[simp]
theorem corollary74BImplementation_gateCount {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hcapacity : rightTail ≤ leftTail + 2) :
    Circuit.gateCount (layout.corollary74BImplementation hcapacity) =
      4 * (rightTail + 1) := by
  simp [corollary74BImplementation]

@[simp]
theorem corollary74BImplementation_toffoliCount {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hcapacity : rightTail ≤ leftTail + 2) :
    Circuit.kindCount .toffoli (layout.corollary74BImplementation hcapacity) =
      4 * (rightTail + 1) := by
  simp [corollary74BImplementation]

/-- The exact circuit contains `8(leftTail + rightTail + 2)` Toffoli macros. -/
@[simp]
theorem corollary74Circuit_gateCount {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2) (hright : rightTail ≤ leftTail + 2) :
    Circuit.gateCount (layout.corollary74Circuit hleft hright) =
      8 * (leftTail + rightTail + 2) := by
  simp [corollary74Circuit]
  omega

/-- Every syntactic node in the exact expansion is a trusted Toffoli macro. -/
@[simp]
theorem corollary74Circuit_toffoliCount {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2) (hright : rightTail ≤ leftTail + 2) :
    Circuit.kindCount .toffoli (layout.corollary74Circuit hleft hright) =
      8 * (leftTail + rightTail + 2) := by
  simp [corollary74Circuit]
  omega

/-- The unexpanded Toffoli circuit has no cost in the early basic-operation model. -/
@[simp]
theorem corollary74Circuit_oneQubitCNOTCost {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2) (hright : rightTail ≤ leftTail + 2) :
    Circuit.cost CostModel.oneQubitCNOT
        (layout.corollary74Circuit hleft hright) = none := by
  simp [corollary74Circuit, fourBlockSubstitutionCircuit, Circuit.cost_append,
    corollary74AImplementation, corollary74BImplementation]

/-- Under the stronger prefix bound, A's exact ladder never touches the final target. -/
theorem targetWire_not_mem_corollary74AImplementation_touchedSupport
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hcapacity : leftTail ≤ rightTail + 2)
    (htargetFree : leftTail ≤ rightTail + 1) :
    layout.targetWire ∉
      Circuit.touchedSupport (layout.corollary74AImplementation hcapacity) := by
  intro hmem
  apply layout.targetWire_not_mem_aInwardLadderLogicalSupport
      (by omega) (by omega)
  apply InwardLadderLayout.touchedSupport_inwardLadderCircuit_subset
      (layout.corollary74ALayout hcapacity)
  exact hmem

/-! ## Balanced source-width partition -/

/-- Left borrowed tail in the repaired floor partition for source width `sourceWidth`. -/
def balancedLeftTail (sourceWidth : ℕ) : ℕ := sourceWidth / 2 - 3

/-- Right borrowed tail in the repaired floor partition for source width `sourceWidth`. -/
def balancedRightTail (sourceWidth : ℕ) : ℕ :=
  sourceWidth - sourceWidth / 2 - 4

/-- The two positive borrowed counts consume exactly the source's `n` logical wires. -/
theorem balancedTails_add_seven {sourceWidth : ℕ} (hwidth : 7 ≤ sourceWidth) :
    balancedLeftTail sourceWidth + balancedRightTail sourceWidth + 7 = sourceWidth := by
  simp [balancedLeftTail, balancedRightTail]
  omega

/-- Subtraction-safe form used by the exact `8(n-5)` resource equation. -/
theorem balancedTails_add_two {sourceWidth : ℕ} (hwidth : 7 ≤ sourceWidth) :
    balancedLeftTail sourceWidth + balancedRightTail sourceWidth + 2 =
      sourceWidth - 5 := by
  have := balancedTails_add_seven hwidth
  omega

/-- The left tail never exceeds the right tail by more than one. -/
theorem balancedLeftTail_le_right_add_one {sourceWidth : ℕ}
    (hwidth : 7 ≤ sourceWidth) :
    balancedLeftTail sourceWidth ≤ balancedRightTail sourceWidth + 1 := by
  simp [balancedLeftTail, balancedRightTail]
  omega

/-- The right tail never exceeds the left tail. -/
theorem balancedRightTail_le_left {sourceWidth : ℕ}
    (hwidth : 7 ≤ sourceWidth) :
    balancedRightTail sourceWidth ≤ balancedLeftTail sourceWidth := by
  simp [balancedLeftTail, balancedRightTail]
  omega

/-- In particular, the A ladder fits and does not need to borrow the final target. -/
theorem balancedLeftCapacity {sourceWidth : ℕ} (hwidth : 7 ≤ sourceWidth) :
    balancedLeftTail sourceWidth ≤ balancedRightTail sourceWidth + 2 :=
  (balancedLeftTail_le_right_add_one hwidth).trans (by omega)

/-- The B ladder fits inside the first-group data controls. -/
theorem balancedRightCapacity {sourceWidth : ℕ} (hwidth : 7 ≤ sourceWidth) :
    balancedRightTail sourceWidth ≤ balancedLeftTail sourceWidth + 2 :=
  (balancedRightTail_le_left hwidth).trans (by omega)

/-- The stronger balanced A bound certifies that A never borrows the final target. -/
theorem balancedABorrowSlotEmbedding_ne_target {sourceWidth : ℕ}
    (hwidth : 7 ≤ sourceWidth)
    (borrowed : Fin (balancedLeftTail sourceWidth + 1)) :
    aBorrowSlotEmbedding
        (l := balancedLeftTail sourceWidth + 1)
        (r := balancedRightTail sourceWidth + 1) (by
          have := balancedLeftTail_le_right_add_one hwidth
          omega) borrowed ≠
      (Sum.inr (Sum.inr 1) :
        FourBlockSlot (balancedLeftTail sourceWidth + 1)
          (balancedRightTail sourceWidth + 1)) := by
  apply aBorrowSlotEmbedding_ne_target
  have := balancedLeftTail_le_right_add_one hwidth
  omega

/-! ## Canonical exact-width circuit -/

/-- Consecutive embedding of the nested four-block slots into their logical width. -/
def consecutiveSlotEmbedding (l r : ℕ) :
    FourBlockSlot l r ↪ Fin (logicalWidth l r) :=
  (Equiv.sumCongr (Equiv.refl _) (@finSumFinEquiv (r + 1) 2)).toEmbedding |>.trans
    ((@finSumFinEquiv (l + 2) ((r + 1) + 2)).toEmbedding |>.trans
      (Fin.castLEEmb (by simp [logicalWidth]; omega)))

/-- A canonical adjacent placement of every logical four-block wire. -/
def consecutiveLayout (l r : ℕ) : FourBlockLayout l r (logicalWidth l r) where
  wire := consecutiveSlotEmbedding l r

/-- Canonical source-width placement for every legal width `sourceWidth ≥ 7`. -/
def balancedLayout (sourceWidth : ℕ) (hwidth : 7 ≤ sourceWidth) :
    FourBlockLayout (balancedLeftTail sourceWidth + 1)
      (balancedRightTail sourceWidth + 1) sourceWidth where
  wire :=
    (consecutiveSlotEmbedding (balancedLeftTail sourceWidth + 1)
      (balancedRightTail sourceWidth + 1)).trans
      (Fin.castLEEmb (by
        have hsum := balancedTails_add_seven hwidth
        simp only [logicalWidth]
        omega))

/-- The canonical layout uses exactly `sourceWidth` logical slots. -/
theorem balancedLayout_logicalWidth (sourceWidth : ℕ) (hwidth : 7 ≤ sourceWidth) :
    logicalWidth (balancedLeftTail sourceWidth + 1)
      (balancedRightTail sourceWidth + 1) = sourceWidth := by
  have hsum := balancedTails_add_seven hwidth
  simp only [logicalWidth]
  omega

/-- The canonical target is controlled by exactly the paper's `sourceWidth - 2` wires. -/
@[simp]
theorem balancedLayout_dataControlCount (sourceWidth : ℕ)
    (hwidth : 7 ≤ sourceWidth) :
    (balancedLayout sourceWidth hwidth).dataLayout.controlSet.card =
      sourceWidth - 2 := by
  rw [dataLayout_controlSet_card]
  have hsum := balancedTails_add_seven hwidth
  omega

/-- In the balanced circuit, A's full Toffoli ladder never names the final target wire. -/
theorem balancedLayout_targetWire_not_mem_aImplementation_touchedSupport
    (sourceWidth : ℕ) (hwidth : 7 ≤ sourceWidth) :
    (balancedLayout sourceWidth hwidth).targetWire ∉
      Circuit.touchedSupport
        ((balancedLayout sourceWidth hwidth).corollary74AImplementation
          (balancedLeftCapacity hwidth)) := by
  apply targetWire_not_mem_corollary74AImplementation_touchedSupport
  exact balancedLeftTail_le_right_add_one hwidth

/-- The repaired floor-partition construction on exactly `sourceWidth` wires. -/
def balancedCorollary74Circuit (sourceWidth : ℕ) (hwidth : 7 ≤ sourceWidth) :
    Circuit sourceWidth :=
  (balancedLayout sourceWidth hwidth).corollary74Circuit
    (balancedLeftCapacity hwidth) (balancedRightCapacity hwidth)

/-- Exact semantics of the canonical balanced construction. -/
@[simp]
theorem eval_balancedCorollary74Circuit (sourceWidth : ℕ)
    (hwidth : 7 ≤ sourceWidth) :
    Circuit.eval (balancedCorollary74Circuit sourceWidth hwidth) =
      positiveControlledUnitary
        (balancedLayout sourceWidth hwidth).targetWire
        (balancedLayout sourceWidth hwidth).dataLayout.controlSet pauliX := by
  exact eval_corollary74Circuit _ _ _

/-- Corrected Corollary 7.4's exact `8(sourceWidth - 5)` Toffoli count. -/
@[simp]
theorem balancedCorollary74Circuit_gateCount (sourceWidth : ℕ)
    (hwidth : 7 ≤ sourceWidth) :
    Circuit.gateCount (balancedCorollary74Circuit sourceWidth hwidth) =
      8 * (sourceWidth - 5) := by
  rw [balancedCorollary74Circuit, corollary74Circuit_gateCount]
  rw [balancedTails_add_two hwidth]

/-- Every node in the canonical exact expansion is a Toffoli macro. -/
@[simp]
theorem balancedCorollary74Circuit_toffoliCount (sourceWidth : ℕ)
    (hwidth : 7 ≤ sourceWidth) :
    Circuit.kindCount .toffoli (balancedCorollary74Circuit sourceWidth hwidth) =
      8 * (sourceWidth - 5) := by
  rw [balancedCorollary74Circuit, corollary74Circuit_toffoliCount]
  rw [balancedTails_add_two hwidth]

/-- The exact-width circuit carries the requested source register width. -/
@[simp]
theorem balancedCorollary74Circuit_registerWidth (sourceWidth : ℕ)
    (hwidth : 7 ≤ sourceWidth) :
    Circuit.registerWidth (balancedCorollary74Circuit sourceWidth hwidth) = sourceWidth :=
  rfl

/-- The canonical Toffoli-macro circuit remains unsupported by one-qubit+CNOT cost. -/
@[simp]
theorem balancedCorollary74Circuit_oneQubitCNOTCost (sourceWidth : ℕ)
    (hwidth : 7 ≤ sourceWidth) :
    Circuit.cost CostModel.oneQubitCNOT
        (balancedCorollary74Circuit sourceWidth hwidth) = none := by
  apply corollary74Circuit_oneQubitCNOTCost

/-- The repaired construction includes the formerly problematic `sourceWidth = 7` boundary. -/
theorem balancedCorollary74Circuit_seven_gateCount :
    Circuit.gateCount (balancedCorollary74Circuit 7 (by omega)) = 16 := by
  rw [balancedCorollary74Circuit_gateCount]

/-- At width seven, all sixteen syntactic nodes are Toffoli macros. -/
theorem balancedCorollary74Circuit_seven_toffoliCount :
    Circuit.kindCount .toffoli (balancedCorollary74Circuit 7 (by omega)) = 16 := by
  rw [balancedCorollary74Circuit_toffoliCount]

end FourBlockLayout

end Barenco.MultiControl
