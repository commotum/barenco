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
                have hbad : False := by
                  simpa [aBorrowSlotEmbedding, aWorkspaceSlotEmbedding,
                    aWorkspaceSumEmbedding, hsplit] using h
                exact hbad.elim
            | inr last =>
                have hlast : last = 0 := Subsingleton.elim _ _
                subst last
                have hbad : False := by
                  simpa [aBorrowSlotEmbedding, aWorkspaceSlotEmbedding,
                    aWorkspaceSumEmbedding, hsplit] using h
                exact hbad.elim
    | inr firstTarget =>
        cases second with
        | inl secondBorrowed =>
            change (Sum.inr (Sum.inr 0) : FourBlockSlot l r) =
              aBorrowSlotEmbedding hcapacity secondBorrowed at h
            cases hsplit : (@finSumFinEquiv (r + 1) 1).symm
                (Fin.castLE hcapacity secondBorrowed) with
            | inl right =>
                have hbad : False := by
                  simpa [aBorrowSlotEmbedding, aWorkspaceSlotEmbedding,
                    aWorkspaceSumEmbedding, hsplit] using h
                exact hbad.elim
            | inr last =>
                have hlast : last = 0 := Subsingleton.elim _ _
                subst last
                have hbad : False := by
                  simpa [aBorrowSlotEmbedding, aWorkspaceSlotEmbedding,
                    aWorkspaceSumEmbedding, hsplit] using h
                exact hbad.elim
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
          have hbad : False := by
            simpa [bControlSlotEmbedding, bControlSumEmbedding,
              bWorkSlotEmbedding, bWorkSumEmbedding, bBorrowSlotEmbedding,
              leftControlSlotEmbedding, hcontrol, hwork] using h
          exact hbad.elim
      | inr target =>
          have hbad : False := by
            simpa [bControlSlotEmbedding, bControlSumEmbedding,
              bWorkSlotEmbedding, bWorkSumEmbedding, hcontrol, hwork] using h
          exact hbad.elim
  | inr dirty =>
      cases hwork : (@finSumFinEquiv r 1).symm work with
      | inl borrowed =>
          have hbad : False := by
            simpa [bControlSlotEmbedding, bControlSumEmbedding,
              bWorkSlotEmbedding, bWorkSumEmbedding, bBorrowSlotEmbedding,
              leftControlSlotEmbedding, hcontrol, hwork] using h
          exact hbad.elim
      | inr target =>
          have hbad : False := by
            simpa [bControlSlotEmbedding, bControlSumEmbedding,
              bWorkSlotEmbedding, bWorkSumEmbedding, hcontrol, hwork] using h
          exact hbad.elim

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
  apply OrderedControlLayout.mk.injEq.mpr
  constructor
  · apply Function.Embedding.ext
    intro control
    rfl
  · exact layout.aInwardLadderLayout_targetWire hcapacity

theorem bInwardLadderLayout_orderedControlLayout {l r n : ℕ}
    (layout : FourBlockLayout l r n) (hcapacity : r ≤ l + 2) :
    (layout.bInwardLadderLayout hcapacity).orderedControlLayout =
      layout.bLayout := by
  apply OrderedControlLayout.mk.injEq.mpr
  constructor
  · apply Function.Embedding.ext
    intro control
    rfl
  · exact layout.bInwardLadderLayout_targetWire hcapacity

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

end FourBlockLayout

end Barenco.MultiControl
