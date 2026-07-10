import Barenco.MultiControl.Recursive
import Barenco.MultiControl.GrayExpansion
import Barenco.MultiControl.Corollary74Expansion

/-!
# Primitive expansion of the recursive multi-control construction

This leaf gives the syntax-level expansion promised by Barenco Lemma 7.5 and
the construction-specific part of Corollary 7.6.  A recursive step uses two
selected six-node singly controlled circuits, two literal corrected
Corollary 7.4 multi-controlled-X circuits, and the smaller recursive circuit.

The recursion stops at six controls, where `sixControlExpandedGrayCircuit`
provides a directly expanded exact base.  All circuits act on the original
ambient register: the Corollary 7.4 workspace embeds the prefix controls, uses
the final unitary target as a dirty wire, and temporarily targets the last
control.  Thus evaluator preservation includes arbitrary spectator wires and
restoration of the dirty target wire.
-/

namespace Barenco.MultiControl

open Barenco.OneQubit
open Barenco.ControlledCircuit

noncomputable section

namespace OrderedControlLayout

/-! ## Ambient workspace for an expanded prefix-controlled X -/

/--
Inject the `p + 2` logical Corollary 7.4 wires into a recursive layout.

The first `p` positions are the prefix controls, position `p` is the original
unitary target (used as dirty workspace), and the final position is the last
control (used as the multi-controlled-X target).
-/
def recursivePrefixWorkspaceEmbedding {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth) :
    Fin (p + 2) ↪ Fin ambientWidth where
  toFun index :=
    Fin.lastCases layout.lastControlWire
      (fun prior =>
        Fin.lastCases layout.targetWire
          (fun control => layout.controlWire control.castSucc) prior)
      index
  inj' := by
    intro first second
    refine Fin.lastCases ?_ (fun firstPrior => ?_) first <;>
      refine Fin.lastCases ?_ (fun secondPrior => ?_) second
    · intro
      rfl
    · refine Fin.lastCases ?_ (fun secondControl => ?_) secondPrior
      · intro heq
        simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at heq
        exact False.elim (layout.lastControlWire_ne_targetWire heq)
      · intro heq
        simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at heq
        exact False.elim
          (layout.controlWire_ne (Fin.castSucc_ne_last secondControl) heq.symm)
    · refine Fin.lastCases ?_ (fun firstControl => ?_) firstPrior
      · intro heq
        simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at heq
        exact False.elim (layout.lastControlWire_ne_targetWire heq.symm)
      · intro heq
        simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at heq
        exact False.elim
          (layout.controlWire_ne (Fin.castSucc_ne_last firstControl) heq)
    · refine Fin.lastCases ?_ (fun firstControl => ?_) firstPrior
      · refine Fin.lastCases ?_ (fun secondControl => ?_) secondPrior
        · intro
          rfl
        · intro heq
          simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at heq
          exact False.elim (layout.control_ne_target secondControl.castSucc heq.symm)
      · refine Fin.lastCases ?_ (fun secondControl => ?_) secondPrior
        · intro heq
          simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at heq
          exact False.elim (layout.control_ne_target firstControl.castSucc heq)
        · intro heq
          simp only [Fin.lastCases_castSucc] at heq
          have hcast : firstControl.castSucc = secondControl.castSucc :=
            layout.controlWire.injective heq
          have hcontrol : firstControl = secondControl :=
            Fin.castSucc_injective _ hcast
          subst secondControl
          rfl

@[simp]
theorem recursivePrefixWorkspaceEmbedding_control {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth) (control : Fin p) :
    layout.recursivePrefixWorkspaceEmbedding control.castSucc.castSucc =
      layout.controlWire control.castSucc := by
  simp [recursivePrefixWorkspaceEmbedding]

@[simp]
theorem recursivePrefixWorkspaceEmbedding_dirty {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth) :
    layout.recursivePrefixWorkspaceEmbedding (Fin.last p).castSucc =
      layout.targetWire := by
  simp [recursivePrefixWorkspaceEmbedding]

@[simp]
theorem recursivePrefixWorkspaceEmbedding_target {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth) :
    layout.recursivePrefixWorkspaceEmbedding (Fin.last (p + 1)) =
      layout.lastControlWire := by
  simp [recursivePrefixWorkspaceEmbedding]

/-- The canonical balanced four-block layout transported into the ambient recursion. -/
def recursivePrefixFourBlockLayout {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) :
    FourBlockLayout (FourBlockLayout.balancedLeftTail (p + 2) + 1)
      (FourBlockLayout.balancedRightTail (p + 2) + 1) ambientWidth where
  wire :=
    ((FourBlockLayout.balancedLayout (p + 2) hwidth).wire).trans
      layout.recursivePrefixWorkspaceEmbedding

private theorem balancedLayout_targetWire_eq_last (p : ℕ) (hwidth : 7 ≤ p + 2) :
    (FourBlockLayout.balancedLayout (p + 2) hwidth).targetWire =
      Fin.last (p + 1) := by
  apply Fin.ext
  simp [FourBlockLayout.targetWire, FourBlockLayout.balancedLayout,
    FourBlockLayout.consecutiveSlotEmbedding, FourBlockLayout.logicalWidth]
  have hsum := FourBlockLayout.balancedTails_add_seven hwidth
  omega

private theorem balancedLayout_dirtyWire_eq_penultimate
    (p : ℕ) (hwidth : 7 ≤ p + 2) :
    (FourBlockLayout.balancedLayout (p + 2) hwidth).dirtyWire =
      (Fin.last p).castSucc := by
  apply Fin.ext
  simp [FourBlockLayout.dirtyWire, FourBlockLayout.balancedLayout,
    FourBlockLayout.consecutiveSlotEmbedding, FourBlockLayout.logicalWidth]
  have hsum := FourBlockLayout.balancedTails_add_seven hwidth
  omega

private theorem balancedLayout_dataCount_eq (p : ℕ) (hwidth : 7 ≤ p + 2) :
    ((FourBlockLayout.balancedLeftTail (p + 2) + 1 + 2) +
      (FourBlockLayout.balancedRightTail (p + 2) + 1 + 1)) = p := by
  have hsum := FourBlockLayout.balancedTails_add_seven hwidth
  omega

private theorem balancedLayout_dataControlWire_eq_cast
    (p : ℕ) (hwidth : 7 ≤ p + 2)
    (control : Fin
      ((FourBlockLayout.balancedLeftTail (p + 2) + 1 + 2) +
        (FourBlockLayout.balancedRightTail (p + 2) + 1 + 1))) :
    (FourBlockLayout.balancedLayout (p + 2) hwidth).dataLayout.controlWire control =
      (Fin.cast (balancedLayout_dataCount_eq p hwidth) control).castSucc.castSucc := by
  apply Fin.ext
  simp [FourBlockLayout.dataLayout, FourBlockLayout.dataControlEmbedding,
    FourBlockLayout.dataControlSlotEmbedding,
    FourBlockLayout.dataControlSumEmbedding, FourBlockLayout.balancedLayout,
    FourBlockLayout.consecutiveSlotEmbedding, FourBlockLayout.logicalWidth]

theorem recursivePrefixFourBlockLayout_dataControlWire {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2)
    (control : Fin
      ((FourBlockLayout.balancedLeftTail (p + 2) + 1 + 2) +
        (FourBlockLayout.balancedRightTail (p + 2) + 1 + 1))) :
    (layout.recursivePrefixFourBlockLayout hwidth).dataLayout.controlWire control =
      layout.controlWire
        (Fin.cast (balancedLayout_dataCount_eq p hwidth) control).castSucc := by
  change layout.recursivePrefixWorkspaceEmbedding
      ((FourBlockLayout.balancedLayout (p + 2) hwidth).dataLayout.controlWire
        control) = _
  rw [balancedLayout_dataControlWire_eq_cast]
  exact layout.recursivePrefixWorkspaceEmbedding_control _

@[simp]
theorem recursivePrefixFourBlockLayout_targetWire {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) :
    (layout.recursivePrefixFourBlockLayout hwidth).targetWire =
      layout.lastControlWire := by
  change layout.recursivePrefixWorkspaceEmbedding
      (FourBlockLayout.balancedLayout (p + 2) hwidth).targetWire = _
  rw [balancedLayout_targetWire_eq_last]
  exact layout.recursivePrefixWorkspaceEmbedding_target

@[simp]
theorem recursivePrefixFourBlockLayout_dirtyWire {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) :
    (layout.recursivePrefixFourBlockLayout hwidth).dirtyWire =
      layout.targetWire := by
  change layout.recursivePrefixWorkspaceEmbedding
      (FourBlockLayout.balancedLayout (p + 2) hwidth).dirtyWire = _
  rw [balancedLayout_dirtyWire_eq_penultimate]
  exact layout.recursivePrefixWorkspaceEmbedding_dirty

end OrderedControlLayout

end

end Barenco.MultiControl
