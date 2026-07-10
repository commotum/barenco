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
            simp [aBorrowSlotEmbedding, aWorkspaceSlotEmbedding,
              aWorkspaceSumEmbedding] at h
    | inr firstTarget =>
        cases second with
        | inl secondBorrowed =>
            change (Sum.inr (Sum.inr 0) : FourBlockSlot l r) =
              aBorrowSlotEmbedding hcapacity secondBorrowed at h
            simp [aBorrowSlotEmbedding, aWorkspaceSlotEmbedding,
              aWorkspaceSumEmbedding] at h
        | inr secondTarget =>
            exact congrArg Sum.inr (Subsingleton.elim firstTarget secondTarget)

/-- A's complete work register, with its target in the final position. -/
def aWorkSlotEmbedding {l r : ℕ} (hcapacity : l ≤ r + 2) :
    Fin (l + 1) ↪ FourBlockSlot l r :=
  (@finSumFinEquiv l 1).symm.toEmbedding.trans
    (aWorkSumEmbedding hcapacity)

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
            simp [aWorkSlotEmbedding, aWorkSumEmbedding,
              aBorrowSlotEmbedding, aWorkspaceSlotEmbedding,
              aWorkspaceSumEmbedding] at h
    | inr firstWork =>
        cases second with
        | inl secondControl =>
            change aWorkSlotEmbedding hcapacity firstWork =
              (Sum.inl secondControl : FourBlockSlot l r) at h
            simp [aWorkSlotEmbedding, aWorkSumEmbedding,
              aBorrowSlotEmbedding, aWorkspaceSlotEmbedding,
              aWorkspaceSumEmbedding] at h
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
            simp [bControlSlotEmbedding, bControlSumEmbedding,
              bWorkSlotEmbedding, bWorkSumEmbedding,
              bBorrowSlotEmbedding, leftControlSlotEmbedding] at h
    | inr firstWork =>
        cases second with
        | inl secondControl =>
            change bWorkSlotEmbedding hcapacity firstWork =
              bControlSlotEmbedding l r secondControl at h
            simp [bControlSlotEmbedding, bControlSumEmbedding,
              bWorkSlotEmbedding, bWorkSumEmbedding,
              bBorrowSlotEmbedding, leftControlSlotEmbedding] at h
        | inr secondWork =>
            exact congrArg Sum.inr ((bWorkSlotEmbedding hcapacity).injective h)

/-- The exact Lemma 7.2 implementation of block B in the common ambient register. -/
def bInwardLadderLayout {l r n : ℕ} (layout : FourBlockLayout l r n)
    (hcapacity : r ≤ l + 2) : InwardLadderLayout r n where
  wire := (bLadderSlotEmbedding hcapacity).trans layout.wire

end FourBlockLayout

end Barenco.MultiControl
