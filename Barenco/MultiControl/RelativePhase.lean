import Barenco.MultiControl.Corollary74
import Barenco.MultiControl.RelativeHalf

/-!
# Contextual relative-phase version of Corollary 7.4

This module separates the contextual phase argument from the signed ladder
calculation in `RelativeHalf`.  The B implementation keeps the two outer
Toffolis that target the final wire exact and replaces only the repeated
smaller half by the seven-node relative-phase implementation.  The full
four-block chronology is `Arel; Bhybrid; adjoint Arel; Bhybrid`: using the same
all-relative A circuit twice is not correct for the ordered Section 6 phase.

The first section records syntax-derived counts.  Semantic theorems below use
the signed basis actions; no phase-relaxed congruence is used as a substitute
for exact contextual equality.
-/

namespace Barenco.MultiControl

open scoped Matrix

namespace InwardLadderLayout

noncomputable section

/-! ## Hybrid final-target ladder -/

/--
The phase-safe B ladder.  Its chronology is
`exactOuter; relativeSmallerHalf; exactOuter; relativeSmallerHalf`.

Only the two outer occurrences target the ladder's final target.  The repeated
smaller half is a signed involution on wires disjoint from that target.
-/
def hybridInwardLadderCircuit {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) : Circuit n :=
  Circuit.append [layout.outerToffoli]
    (Circuit.append (relativeHalfLadderCircuit b layout.smaller)
      (Circuit.append [layout.outerToffoli]
        (relativeHalfLadderCircuit b layout.smaller)))

/-- One trusted outer node has the expected structural kind. -/
@[simp]
theorem outerToffoli_singleton_toffoliCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    Circuit.kindCount .toffoli [layout.outerToffoli] = 1 := rfl

@[simp]
theorem outerToffoli_singleton_oneQubitCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    Circuit.kindCount .oneQubit [layout.outerToffoli] = 0 := rfl

@[simp]
theorem outerToffoli_singleton_cnotCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    Circuit.kindCount .cnot [layout.outerToffoli] = 0 := rfl

/-- A trusted outer macro contributes one node to the mixed syntax. -/
@[simp]
theorem outerToffoli_singleton_gateCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    Circuit.gateCount [layout.outerToffoli] = 1 := rfl

/-- A seven-node relative base contains no trusted Toffoli macro. -/
@[simp]
theorem relativeBaseCircuit_toffoliCount {n : ℕ}
    (layout : InwardLadderLayout 0 n) :
    Circuit.kindCount .toffoli layout.relativeBaseCircuit = 0 := rfl

/-- A seven-node relative outer circuit contains no trusted Toffoli macro. -/
@[simp]
theorem relativeOuterCircuit_toffoliCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    Circuit.kindCount .toffoli layout.relativeOuterCircuit = 0 := rfl

/-- Expanded relative halves contain no trusted Toffoli macro nodes. -/
@[simp]
theorem relativeHalfLadderCircuit_toffoliCount {b n : ℕ}
    (layout : InwardLadderLayout b n) :
    Circuit.kindCount .toffoli (relativeHalfLadderCircuit b layout) = 0 := by
  revert layout
  induction b with
  | zero =>
      intro layout
      simp [relativeHalfLadderCircuit]
  | succ b ih =>
      intro layout
      simp [relativeHalfLadderCircuit, ih]

/-- A complete all-relative ladder also contains no trusted Toffoli macros. -/
@[simp]
theorem relativeInwardLadderCircuit_toffoliCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    Circuit.kindCount .toffoli (relativeInwardLadderCircuit layout) = 0 := by
  simp [relativeInwardLadderCircuit]

/-- The hybrid syntax contains exactly the two retained exact Toffoli macros. -/
@[simp]
theorem hybridInwardLadderCircuit_toffoliCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    Circuit.kindCount .toffoli (hybridInwardLadderCircuit layout) = 2 := by
  simp [hybridInwardLadderCircuit]

/-- One-qubit primitives contributed by the two relative smaller halves. -/
@[simp]
theorem hybridInwardLadderCircuit_oneQubitCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    Circuit.kindCount .oneQubit (hybridInwardLadderCircuit layout) =
      8 * (2 * b + 1) := by
  simp [hybridInwardLadderCircuit]
  omega

/-- CNOT primitives contributed by the two relative smaller halves. -/
@[simp]
theorem hybridInwardLadderCircuit_cnotCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    Circuit.kindCount .cnot (hybridInwardLadderCircuit layout) =
      6 * (2 * b + 1) := by
  simp [hybridInwardLadderCircuit]
  omega

/-- Total nodes before the two exact Toffolis are expanded. -/
@[simp]
theorem hybridInwardLadderCircuit_gateCount {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    Circuit.gateCount (hybridInwardLadderCircuit layout) =
      14 * (2 * b + 1) + 2 := by
  simp only [hybridInwardLadderCircuit, Circuit.gateCount_append,
    outerToffoli_singleton_gateCount, relativeHalfLadderCircuit_gateCount]
  omega

/-- The mixed syntax is deliberately unsupported by the one-qubit+CNOT model. -/
@[simp]
theorem hybridInwardLadderCircuit_oneQubitCNOTCost {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    Circuit.cost CostModel.oneQubitCNOT (hybridInwardLadderCircuit layout) = none := by
  simp [hybridInwardLadderCircuit, Circuit.cost_append, Circuit.addCost]

/-! ## Exact hybrid semantics -/

/--
The two relative smaller halves contribute the same Boolean exponent.  The
intervening exact outer Toffoli changes only the larger target, which is outside
the smaller phase support.
-/
theorem relativeHalfPhaseExponent_after_hybrid_middle {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) (input : Basis n) :
    relativeHalfPhaseExponent b layout.smaller
        (outerUpdate layout
          (halfLadderUpdate b layout.smaller (outerUpdate layout input))) =
      relativeHalfPhaseExponent b layout.smaller (outerUpdate layout input) := by
  rw [smaller_relativeHalfPhaseExponent_outerUpdate]
  rw [relativeHalfPhaseExponent_halfLadderUpdate]

/--
The hybrid B ladder is exact on every ambient computational-basis assignment.
Its dirty borrowed wires and all spectators are restored by the same Boolean
update as the trusted inward ladder.
-/
theorem eval_hybridInwardLadderCircuit_mulVec_basisKet {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) (input : Basis n) :
    (Circuit.eval (hybridInwardLadderCircuit layout) : Gate n) *ᵥ basisKet input =
      basisKet (inwardLadderUpdate layout input) := by
  rw [hybridInwardLadderCircuit, Circuit.eval_append, Circuit.eval_append,
    Circuit.eval_append]
  simp only [Submonoid.coe_mul, Circuit.eval_singleton]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [outerToffoli_denotation_mulVec_basisKet]
  rw [eval_relativeHalfLadderCircuit_mulVec_basisKet]
  rw [Matrix.mulVec_smul]
  rw [← Matrix.mulVec_mulVec]
  rw [outerToffoli_denotation_mulVec_basisKet]
  rw [eval_relativeHalfLadderCircuit_mulVec_basisKet]
  rw [smul_smul]
  rw [← relativePhaseSign_add]
  rw [relativeHalfPhaseExponent_after_hybrid_middle]
  rw [show relativeHalfPhaseExponent b layout.smaller (outerUpdate layout input) +
      relativeHalfPhaseExponent b layout.smaller (outerUpdate layout input) = false by
    cases relativeHalfPhaseExponent b layout.smaller (outerUpdate layout input) <;> rfl]
  simp only [relativePhaseSign_false, one_smul]
  rfl

/-- Exact full-register unitary equality for the hybrid ladder. -/
@[simp]
theorem eval_hybridInwardLadderCircuit {b n : ℕ}
    (layout : InwardLadderLayout (b + 1) n) :
    Circuit.eval (hybridInwardLadderCircuit layout) =
      positiveControlledUnitary layout.targetWire layout.controlSet pauliX := by
  apply Subtype.ext
  rw [matrix_eq_iff_mulVec_basisKet_eq]
  intro input
  rw [eval_hybridInwardLadderCircuit_mulVec_basisKet]
  rw [inwardLadderUpdate_eq_update]
  exact (positiveControlledUnitary_pauliX_mulVec_basisKet layout input).symm

end

end InwardLadderLayout

namespace FourBlockLayout

noncomputable section

/-! ## Correct contextual four-block syntax -/

/-- All-relative implementation of A on the checked Corollary 7.4 layout. -/
def relativeCorollary74AImplementation {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hcapacity : leftTail ≤ rightTail + 2) : Circuit n :=
  InwardLadderLayout.relativeInwardLadderCircuit
    (layout.corollary74ALayout hcapacity)

/-- Hybrid B: exact only at its two final-target outer occurrences. -/
def hybridCorollary74BImplementation {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hcapacity : rightTail ≤ leftTail + 2) : Circuit n :=
  InwardLadderLayout.hybridInwardLadderCircuit
    (layout.corollary74BLayout hcapacity)

/--
Phase-corrected contextual chronology.  The second A occurrence is the circuit
adjoint, not a second forward copy.
-/
def relativeCorollary74Circuit {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2) (hright : rightTail ≤ leftTail + 2) :
    Circuit n :=
  let a := layout.relativeCorollary74AImplementation hleft
  let b := layout.hybridCorollary74BImplementation hright
  Circuit.append a
    (Circuit.append b (Circuit.append (Circuit.adjoint a) b))

/-! ## Basis semantics of the contextual blocks -/

/-- A's ladder control product is the first-group product from Lemma 7.3. -/
@[simp]
theorem relativeCorollary74A_controlProduct {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hcapacity : leftTail ≤ rightTail + 2) (input : Basis n) :
    InwardLadderLayout.controlProduct
        (layout.corollary74ALayout hcapacity) input =
      layout.leftProduct input := by
  rfl

/-- A's exact Boolean permutation is precisely `blockAUpdate`. -/
theorem relativeCorollary74A_update_eq {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hcapacity : leftTail ≤ rightTail + 2) (input : Basis n) :
    InwardLadderLayout.inwardLadderUpdate
        (layout.corollary74ALayout hcapacity) input =
      layout.blockAUpdate input := by
  rw [InwardLadderLayout.inwardLadderUpdate_eq_update]
  rw [show (layout.corollary74ALayout hcapacity).targetWire =
      layout.dirtyWire by
    exact layout.aInwardLadderLayout_targetWire _]
  rw [relativeCorollary74A_controlProduct]
  rfl

/-- Exact signed action of the all-relative A implementation. -/
theorem eval_relativeCorollary74AImplementation_mulVec_basisKet
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hcapacity : leftTail ≤ rightTail + 2) (input : Basis n) :
    (Circuit.eval (layout.relativeCorollary74AImplementation hcapacity) : Gate n) *ᵥ
        basisKet input =
      InwardLadderLayout.relativePhaseSign
          (InwardLadderLayout.relativeInwardPhaseExponent
            (layout.corollary74ALayout hcapacity) input) •
        basisKet (layout.blockAUpdate input) := by
  rw [relativeCorollary74AImplementation,
    InwardLadderLayout.eval_relativeInwardLadderCircuit_mulVec_basisKet]
  rw [← InwardLadderLayout.inwardLadderUpdate_eq_update]
  rw [relativeCorollary74A_update_eq]

/-- The hybrid B implementation has exactly the macro denotation of block B. -/
@[simp]
theorem eval_hybridCorollary74BImplementation {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hcapacity : rightTail ≤ leftTail + 2) :
    Circuit.eval (layout.hybridCorollary74BImplementation hcapacity) =
      layout.blockB.denotation := by
  rw [hybridCorollary74BImplementation,
    InwardLadderLayout.eval_hybridInwardLadderCircuit]
  rw [blockB, Primitive.positiveControlled_denotation]
  change positiveControlledUnitary
      (layout.corollary74BLayout hcapacity).orderedControlLayout.targetWire
      (layout.corollary74BLayout hcapacity).orderedControlLayout.controlSet pauliX =
    positiveControlledUnitary layout.bLayout.targetWire layout.bLayout.controlSet pauliX
  rw [show (layout.corollary74BLayout hcapacity).orderedControlLayout =
      layout.bLayout by
    exact layout.bInwardLadderLayout_orderedControlLayout _]

/-- Exact basis action of the phase-safe B implementation. -/
theorem eval_hybridCorollary74BImplementation_mulVec_basisKet
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hcapacity : rightTail ≤ leftTail + 2) (input : Basis n) :
    (Circuit.eval (layout.hybridCorollary74BImplementation hcapacity) : Gate n) *ᵥ
        basisKet input = basisKet (layout.blockBUpdate input) := by
  rw [eval_hybridCorollary74BImplementation]
  exact blockB_denotation_mulVec_basisKet layout input

/-- Block A is an involution on the complete ambient basis assignment. -/
theorem blockAUpdate_involutive {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n) :
    Function.Involutive layout.blockAUpdate := by
  intro input
  funext wire
  by_cases hwire : wire = layout.dirtyWire
  · subst wire
    rw [blockAUpdate_apply_dirtyWire, blockAUpdate_apply_dirtyWire,
      leftProduct_blockAUpdate]
    generalize input layout.dirtyWire = dirty
    generalize layout.leftProduct input = controls
    cases dirty <;> cases controls <;> rfl
  · rw [blockAUpdate_apply_of_ne layout _ wire hwire,
      blockAUpdate_apply_of_ne layout _ wire hwire]

private theorem relativePhaseSign_mul_self (exponent : Bool) :
    InwardLadderLayout.relativePhaseSign exponent *
        InwardLadderLayout.relativePhaseSign exponent = 1 := by
  cases exponent <;> simp

/-- Inverse action of a signed involutive basis permutation. -/
private theorem inverse_signedInvolution_mulVec_basisKet
    {n : ℕ} (unitary : UnitaryGate n) (update : Basis n → Basis n)
    (exponent : Basis n → Bool)
    (hupdate : Function.Involutive update)
    (haction : ∀ input,
      (unitary : Gate n) *ᵥ basisKet input =
        InwardLadderLayout.relativePhaseSign (exponent input) •
          basisKet (update input))
    (input : Basis n) :
    ((unitary⁻¹ : UnitaryGate n) : Gate n) *ᵥ basisKet input =
      InwardLadderLayout.relativePhaseSign (exponent (update input)) •
        basisKet (update input) := by
  have hforward := haction (update input)
  rw [hupdate input] at hforward
  have hinverse := congrArg
    (fun state => ((unitary⁻¹ : UnitaryGate n) : Gate n) *ᵥ state) hforward
  simp only [Matrix.mulVec_smul] at hinverse
  rw [Matrix.mulVec_mulVec] at hinverse
  change (((unitary⁻¹ * unitary : UnitaryGate n) : Gate n) *ᵥ
      basisKet (update input)) = _ at hinverse
  rw [inv_mul_cancel] at hinverse
  simp only [Submonoid.coe_one, Matrix.one_mulVec] at hinverse
  calc
    ((unitary⁻¹ : UnitaryGate n) : Gate n) *ᵥ basisKet input =
        (1 : ℂ) • (((unitary⁻¹ : UnitaryGate n) : Gate n) *ᵥ basisKet input) := by
          simp
    _ = (InwardLadderLayout.relativePhaseSign (exponent (update input)) *
          InwardLadderLayout.relativePhaseSign (exponent (update input))) •
        (((unitary⁻¹ : UnitaryGate n) : Gate n) *ᵥ basisKet input) := by
          rw [relativePhaseSign_mul_self]
    _ = InwardLadderLayout.relativePhaseSign (exponent (update input)) •
        (InwardLadderLayout.relativePhaseSign (exponent (update input)) •
          (((unitary⁻¹ : UnitaryGate n) : Gate n) *ᵥ basisKet input)) := by
          rw [smul_smul]
    _ = InwardLadderLayout.relativePhaseSign (exponent (update input)) •
        basisKet (update input) := by
          rw [← hinverse]

/-- Exact signed basis action of the required adjoint A occurrence. -/
theorem eval_adjoint_relativeCorollary74AImplementation_mulVec_basisKet
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hcapacity : leftTail ≤ rightTail + 2) (input : Basis n) :
    (Circuit.eval
        (Circuit.adjoint (layout.relativeCorollary74AImplementation hcapacity)) :
      Gate n) *ᵥ basisKet input =
      InwardLadderLayout.relativePhaseSign
          (InwardLadderLayout.relativeInwardPhaseExponent
            (layout.corollary74ALayout hcapacity) (layout.blockAUpdate input)) •
        basisKet (layout.blockAUpdate input) := by
  rw [Circuit.eval_adjoint]
  apply inverse_signedInvolution_mulVec_basisKet
      (Circuit.eval (layout.relativeCorollary74AImplementation hcapacity))
      layout.blockAUpdate
      (InwardLadderLayout.relativeInwardPhaseExponent
        (layout.corollary74ALayout hcapacity))
      (blockAUpdate_involutive layout)
  exact eval_relativeCorollary74AImplementation_mulVec_basisKet layout hcapacity

/-- Under the stronger capacity bound, A's last borrowed wire is not the final target. -/
theorem relativeCorollary74A_lastBorrow_ne_targetWire
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hcapacity : leftTail ≤ rightTail + 2)
    (htargetFree : leftTail ≤ rightTail + 1) :
    (layout.corollary74ALayout hcapacity).borrowedWire (Fin.last leftTail) ≠
      layout.targetWire := by
  intro heq
  apply layout.targetWire_not_mem_aInwardLadderLogicalSupport
      (by omega) (by omega)
  rw [← heq]
  exact InwardLadderLayout.borrowedWire_mem_logicalSupport _ _

/--
The adjoint-A input phase equals the first A input phase along the exact
`A;B;A` Boolean path.  This is the contextual cancellation obligation that
basis-phase equivalence alone cannot discharge.
-/
theorem relativeCorollary74A_phase_after_ABA
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hcapacity : leftTail ≤ rightTail + 2)
    (htargetFree : leftTail ≤ rightTail + 1) (input : Basis n) :
    InwardLadderLayout.relativeInwardPhaseExponent
        (layout.corollary74ALayout hcapacity)
        (layout.blockAUpdate (layout.blockBUpdate (layout.blockAUpdate input))) =
      InwardLadderLayout.relativeInwardPhaseExponent
        (layout.corollary74ALayout hcapacity) input := by
  let lastBorrow :=
    (layout.corollary74ALayout hcapacity).borrowedWire (Fin.last leftTail)
  have hborrowDirty : lastBorrow ≠ layout.dirtyWire := by
    dsimp [lastBorrow]
    rw [← show (layout.corollary74ALayout hcapacity).targetWire =
        layout.dirtyWire by
      exact layout.aInwardLadderLayout_targetWire _]
    exact (layout.corollary74ALayout hcapacity).borrowedWire_ne_targetWire _
  have hborrowTarget : lastBorrow ≠ layout.targetWire :=
    relativeCorollary74A_lastBorrow_ne_targetWire layout hcapacity htargetFree
  have hlastBorrow :
      layout.blockAUpdate (layout.blockBUpdate (layout.blockAUpdate input))
          lastBorrow = input lastBorrow := by
    rw [blockAUpdate_apply_of_ne layout _ lastBorrow hborrowDirty,
      blockBUpdate_apply_of_ne layout _ lastBorrow hborrowTarget,
      blockAUpdate_apply_of_ne layout _ lastBorrow hborrowDirty]
  have hdirty :
      layout.blockAUpdate (layout.blockBUpdate (layout.blockAUpdate input))
          layout.dirtyWire = input layout.dirtyWire := by
    rw [blockAUpdate_apply_dirtyWire,
      blockBUpdate_apply_of_ne layout _ layout.dirtyWire
        layout.dirtyWire_ne_targetWire,
      blockAUpdate_apply_dirtyWire]
    simp only [leftProduct_blockAUpdate, leftProduct_blockBUpdate]
    generalize input layout.dirtyWire = dirty
    generalize layout.leftProduct input = controls
    cases dirty <;> cases controls <;> rfl
  rw [InwardLadderLayout.relativeInwardPhaseExponent,
    InwardLadderLayout.relativeInwardPhaseExponent]
  rw [relativeCorollary74A_controlProduct,
    relativeCorollary74A_controlProduct]
  simp only [leftProduct_blockAUpdate, leftProduct_blockBUpdate]
  rw [show (layout.corollary74ALayout hcapacity).targetWire =
      layout.dirtyWire by
    exact layout.aInwardLadderLayout_targetWire _]
  rw [hlastBorrow, hdirty]

/--
Exact arbitrary-width basis action of the contextual relative-phase circuit.
The two A signs cancel only under the explicit target-free capacity bound.
-/
theorem eval_relativeCorollary74Circuit_mulVec_basisKet
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2) (hright : rightTail ≤ leftTail + 2)
    (htargetFree : leftTail ≤ rightTail + 1) (input : Basis n) :
    (Circuit.eval (layout.relativeCorollary74Circuit hleft hright) : Gate n) *ᵥ
        basisKet input = basisKet (layout.fourBlockUpdate input) := by
  rw [relativeCorollary74Circuit, Circuit.eval_append, Circuit.eval_append,
    Circuit.eval_append]
  simp only [Submonoid.coe_mul]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [eval_relativeCorollary74AImplementation_mulVec_basisKet]
  rw [Matrix.mulVec_smul]
  rw [eval_hybridCorollary74BImplementation_mulVec_basisKet]
  rw [Matrix.mulVec_smul]
  rw [eval_adjoint_relativeCorollary74AImplementation_mulVec_basisKet]
  rw [smul_smul]
  rw [Matrix.mulVec_smul]
  rw [eval_hybridCorollary74BImplementation_mulVec_basisKet]
  rw [relativeCorollary74A_phase_after_ABA layout hleft htargetFree]
  rw [show InwardLadderLayout.relativePhaseSign
          (InwardLadderLayout.relativeInwardPhaseExponent
            (layout.corollary74ALayout hleft) input) *
        InwardLadderLayout.relativePhaseSign
          (InwardLadderLayout.relativeInwardPhaseExponent
            (layout.corollary74ALayout hleft) input) = 1 by
      cases InwardLadderLayout.relativeInwardPhaseExponent
        (layout.corollary74ALayout hleft) input <;> simp]
  simp only [one_smul]
  rfl

/--
Corrected contextual Corollary 7.4: exact full-register equality, not merely
agreement up to basis-dependent phase.
-/
@[simp]
theorem eval_relativeCorollary74Circuit
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2) (hright : rightTail ≤ leftTail + 2)
    (htargetFree : leftTail ≤ rightTail + 1) :
    Circuit.eval (layout.relativeCorollary74Circuit hleft hright) =
      positiveControlledUnitary layout.targetWire layout.dataLayout.controlSet pauliX := by
  calc
    Circuit.eval (layout.relativeCorollary74Circuit hleft hright) =
        Circuit.eval layout.fourBlockCircuit := by
      apply Subtype.ext
      rw [matrix_eq_iff_mulVec_basisKet_eq]
      intro input
      rw [eval_relativeCorollary74Circuit_mulVec_basisKet
        layout hleft hright htargetFree]
      exact (eval_fourBlockCircuit_mulVec_basisKet layout input).symm
    _ = _ := eval_fourBlockCircuit layout

/-! ## Contextual occurrence accounting -/

/--
Construction-specific number of seven-node relative-Toffoli occurrences: two
complete A ladders and four smaller B halves.
-/
def relativeCorollary74RelativeOccurrenceCount
    (leftTail rightTail : ℕ) : ℕ :=
  2 * InwardLadderLayout.relativeInwardOccurrenceCount leftTail +
    4 * InwardLadderLayout.relativeHalfOccurrenceCount rightTail

@[simp]
theorem relativeCorollary74RelativeOccurrenceCount_eq
    (leftTail rightTail : ℕ) :
    relativeCorollary74RelativeOccurrenceCount leftTail rightTail =
      8 * (leftTail + rightTail) + 12 := by
  simp [relativeCorollary74RelativeOccurrenceCount]
  omega

@[simp]
theorem relativeCorollary74Circuit_toffoliCount {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2) (hright : rightTail ≤ leftTail + 2) :
    Circuit.kindCount .toffoli (layout.relativeCorollary74Circuit hleft hright) = 4 := by
  simp [relativeCorollary74Circuit, relativeCorollary74AImplementation,
    hybridCorollary74BImplementation]

/--
The number of seven-node relative-Toffoli occurrences, witnessed by their four
one-qubit primitives per occurrence.
-/
@[simp]
theorem relativeCorollary74Circuit_oneQubitCount {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2) (hright : rightTail ≤ leftTail + 2) :
    Circuit.kindCount .oneQubit (layout.relativeCorollary74Circuit hleft hright) =
      4 * (8 * (leftTail + rightTail) + 12) := by
  simp [relativeCorollary74Circuit, relativeCorollary74AImplementation,
    hybridCorollary74BImplementation]
  omega

/-- Three CNOTs occur in every seven-node relative-Toffoli implementation. -/
@[simp]
theorem relativeCorollary74Circuit_cnotCount {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2) (hright : rightTail ≤ leftTail + 2) :
    Circuit.kindCount .cnot (layout.relativeCorollary74Circuit hleft hright) =
      3 * (8 * (leftTail + rightTail) + 12) := by
  simp [relativeCorollary74Circuit, relativeCorollary74AImplementation,
    hybridCorollary74BImplementation]
  omega

/-- Total mixed-syntax nodes: four exact macros plus seven nodes per relative occurrence. -/
@[simp]
theorem relativeCorollary74Circuit_gateCount {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2) (hright : rightTail ≤ leftTail + 2) :
    Circuit.gateCount (layout.relativeCorollary74Circuit hleft hright) =
      7 * (8 * (leftTail + rightTail) + 12) + 4 := by
  simp [relativeCorollary74Circuit, relativeCorollary74AImplementation,
    hybridCorollary74BImplementation]
  omega

@[simp]
theorem relativeCorollary74Circuit_oneQubitCNOTCost {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2) (hright : rightTail ≤ leftTail + 2) :
    Circuit.cost CostModel.oneQubitCNOT
        (layout.relativeCorollary74Circuit hleft hright) = none := by
  simp [relativeCorollary74Circuit, relativeCorollary74AImplementation,
    hybridCorollary74BImplementation, Circuit.cost_append, Circuit.addCost]

/-! ## Balanced source-width construction -/

/-- Canonical phase-safe contextual circuit on exactly `sourceWidth` wires. -/
def balancedRelativeCorollary74Circuit (sourceWidth : ℕ)
    (hwidth : 7 ≤ sourceWidth) : Circuit sourceWidth :=
  (balancedLayout sourceWidth hwidth).relativeCorollary74Circuit
    (balancedLeftCapacity hwidth) (balancedRightCapacity hwidth)

/-- Exact corrected Corollary 7.4 semantics for every source width at least seven. -/
@[simp]
theorem eval_balancedRelativeCorollary74Circuit (sourceWidth : ℕ)
    (hwidth : 7 ≤ sourceWidth) :
    Circuit.eval (balancedRelativeCorollary74Circuit sourceWidth hwidth) =
      positiveControlledUnitary
        (balancedLayout sourceWidth hwidth).targetWire
        (balancedLayout sourceWidth hwidth).dataLayout.controlSet pauliX := by
  apply eval_relativeCorollary74Circuit
  exact balancedLeftTail_le_right_add_one hwidth

/-- Exactly `8n−44` Toffoli occurrences use the seven-node relative circuit. -/
@[simp]
theorem balancedRelativeCorollary74RelativeOccurrenceCount
    (sourceWidth : ℕ) (hwidth : 7 ≤ sourceWidth) :
    relativeCorollary74RelativeOccurrenceCount
        (balancedLeftTail sourceWidth) (balancedRightTail sourceWidth) =
      8 * sourceWidth - 44 := by
  rw [relativeCorollary74RelativeOccurrenceCount_eq]
  have hsum := balancedTails_add_seven hwidth
  omega

/-- The remaining four syntactic nodes are the exact final-target Toffolis. -/
@[simp]
theorem balancedRelativeCorollary74Circuit_toffoliCount
    (sourceWidth : ℕ) (hwidth : 7 ≤ sourceWidth) :
    Circuit.kindCount .toffoli
        (balancedRelativeCorollary74Circuit sourceWidth hwidth) = 4 := by
  apply relativeCorollary74Circuit_toffoliCount

/-- Four one-qubit nodes per relative occurrence, before exact-node expansion. -/
@[simp]
theorem balancedRelativeCorollary74Circuit_oneQubitCount
    (sourceWidth : ℕ) (hwidth : 7 ≤ sourceWidth) :
    Circuit.kindCount .oneQubit
        (balancedRelativeCorollary74Circuit sourceWidth hwidth) =
      4 * (8 * sourceWidth - 44) := by
  rw [balancedRelativeCorollary74Circuit,
    relativeCorollary74Circuit_oneQubitCount]
  have hsum := balancedTails_add_seven hwidth
  omega

/-- Three CNOT nodes per relative occurrence, before exact-node expansion. -/
@[simp]
theorem balancedRelativeCorollary74Circuit_cnotCount
    (sourceWidth : ℕ) (hwidth : 7 ≤ sourceWidth) :
    Circuit.kindCount .cnot
        (balancedRelativeCorollary74Circuit sourceWidth hwidth) =
      3 * (8 * sourceWidth - 44) := by
  rw [balancedRelativeCorollary74Circuit,
    relativeCorollary74Circuit_cnotCount]
  have hsum := balancedTails_add_seven hwidth
  omega

/-- Mixed-syntax size: seven nodes per relative occurrence plus four exact macros. -/
@[simp]
theorem balancedRelativeCorollary74Circuit_gateCount
    (sourceWidth : ℕ) (hwidth : 7 ≤ sourceWidth) :
    Circuit.gateCount (balancedRelativeCorollary74Circuit sourceWidth hwidth) =
      7 * (8 * sourceWidth - 44) + 4 := by
  rw [balancedRelativeCorollary74Circuit,
    relativeCorollary74Circuit_gateCount]
  have hsum := balancedTails_add_seven hwidth
  omega

/-- Mixed syntax still contains four unsupported exact Toffoli macros. -/
@[simp]
theorem balancedRelativeCorollary74Circuit_oneQubitCNOTCost
    (sourceWidth : ℕ) (hwidth : 7 ≤ sourceWidth) :
    Circuit.cost CostModel.oneQubitCNOT
        (balancedRelativeCorollary74Circuit sourceWidth hwidth) = none := by
  apply relativeCorollary74Circuit_oneQubitCNOTCost

/-- Width-seven sanity check: four exact and twelve relative occurrences. -/
theorem balancedRelativeCorollary74Circuit_seven_occurrences :
    Circuit.kindCount .toffoli
        (balancedRelativeCorollary74Circuit 7 (by omega)) = 4 ∧
      relativeCorollary74RelativeOccurrenceCount
          (balancedLeftTail 7) (balancedRightTail 7) = 12 := by
  constructor
  · simp
  · norm_num [balancedLeftTail, balancedRightTail]

end


end FourBlockLayout

end Barenco.MultiControl
