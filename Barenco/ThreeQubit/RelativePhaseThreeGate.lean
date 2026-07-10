import Barenco.Optimization.Section8Normalize
import Barenco.ThreeQubit.RelativePhaseFusion

/-!
# Three-gate Section 8 relative-phase Toffoli construction

The paper's Section 8 cost model charges every certified operation on at most
two wires as one basic operation.  Applying the general exact Section 8
normalizer to the transparent seven-node relative-phase Toffoli A circuit emits
the explicit three-`U(4)` circuit in this file.  The construction works in an
arbitrary ambient register and therefore preserves every spectator wire.

This is a constructive upper count, not a minimality theorem.  Its evaluator is
exactly `relativeToffoliUnitary`, with the established `101` input-column sign.
Under pairwise-distinct named wires the strongest Toffoli-relative statement
exported here is `BasisPhaseEq`; no exact-Toffoli or global-phase theorem is
claimed.  The corresponding classical-basis and computational-basis measurement
consequences are stated separately.
-/

namespace Barenco.ThreeQubit

open Barenco.OneQubit
open Barenco.Optimization
open scoped Matrix

noncomputable section

/-! ## Explicit local payloads and syntax -/

/--
Local payload for the chronological two-gate fragment
`oneQubit(second,before); CNOT(first,second)` on an ordered pair.
-/
def targetThenCNOTPayload (before : QubitUnitary) : TwoQubitUnitary :=
  localCNOTPayload * localOnePayload before

/--
Local payload for the chronological sandwich
`oneQubit(second,before); CNOT(first,second); oneQubit(second,after)`.

The reversed-looking product is forced by the library's head-first circuit
chronology: the last gate multiplies on the left.
-/
def targetCNOTTargetPayload (before after : QubitUnitary) :
    TwoQubitUnitary :=
  localOnePayload after * localCNOTPayload * localOnePayload before

/--
The named three-node output of Section 8 normalization of the A diagram.

The ordered pairs are `(second,target)`, `(first,target)`, and
`(second,target)`.  Every node retains a certified local `U(4)` payload; no
full-register matrix is reclassified as a two-wire operation.
-/
def relativePhaseToffoliThreeGateFusionCircuit {n : ℕ}
    (first second target : Fin n)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    FusionCircuit n :=
  [FusionPrimitive.twoQubit ⟨second, target, hsecondTarget⟩
      (targetThenCNOTPayload (ryUnitary (Real.pi / 4))),
    FusionPrimitive.twoQubit ⟨first, target, hfirstTarget⟩
      (targetThenCNOTPayload (ryUnitary (Real.pi / 4))),
    FusionPrimitive.twoQubit ⟨second, target, hsecondTarget⟩
      (targetCNOTTargetPayload
        (ryUnitary (-(Real.pi / 4)))
        (ryUnitary (-(Real.pi / 4))))]

/-- Trusted lowering of the explicit three local payloads to public syntax. -/
def relativePhaseToffoliThreeGateCircuit {n : ℕ}
    (first second target : Fin n)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    Circuit n :=
  (relativePhaseToffoliThreeGateFusionCircuit first second target
    hfirstTarget hsecondTarget).lower

@[simp]
theorem lower_relativePhaseToffoliThreeGateFusionCircuit {n : ℕ}
    (first second target : Fin n)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    (relativePhaseToffoliThreeGateFusionCircuit first second target
        hfirstTarget hsecondTarget).lower =
      relativePhaseToffoliThreeGateCircuit first second target
        hfirstTarget hsecondTarget := rfl

/-! ## Exact normalization and evaluator bridges -/

/--
The general payload-preserving Section 8 pass emits exactly the named
three-element list.  Pairwise distinctness prevents fusion across the two
ordered-pair changes.
-/
theorem section8Normalize_relativePhaseToffoliAFusionCircuit {n : ℕ}
    (first second target : Fin n) (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    section8Normalize
        (relativePhaseToffoliAFusionCircuit first second target
          hfirstTarget hsecondTarget) =
      relativePhaseToffoliThreeGateFusionCircuit first second target
        hfirstTarget hsecondTarget := by
  have hsecondFirst : second ≠ first := hfirstSecond.symm
  have htargetFirst : target ≠ first := hfirstTarget.symm
  have htargetSecond : target ≠ second := hsecondTarget.symm
  simp [relativePhaseToffoliAFusionCircuit,
    relativePhaseToffoliThreeGateFusionCircuit, targetThenCNOTPayload,
    targetCNOTTargetPayload, section8Normalize, promoteCNOTCircuit,
    promoteCNOT, cnotAsTwoQubit, NormalizeCore.normalize,
    NormalizeCore.insert, section8IsIdentity, section8Combine,
    OrderedWirePair.eq_iff, *]

/-- Exact visible evaluator equality with the original seven-node A circuit. -/
theorem eval_relativePhaseToffoliThreeGateFusionCircuit_eq_A {n : ℕ}
    (first second target : Fin n)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    FusionCircuit.eval
        (relativePhaseToffoliThreeGateFusionCircuit first second target
          hfirstTarget hsecondTarget) =
      FusionCircuit.eval
        (relativePhaseToffoliAFusionCircuit first second target
          hfirstTarget hsecondTarget) := by
  simp [relativePhaseToffoliThreeGateFusionCircuit,
    relativePhaseToffoliAFusionCircuit, targetThenCNOTPayload,
    targetCNOTTargetPayload, FusionCircuit.eval, FusionPrimitive.denotation,
    twoWireUnitary_mul, mul_assoc]

/-- Exact lowered evaluator equality with the original seven-node A circuit. -/
theorem eval_relativePhaseToffoliThreeGateCircuit_eq_A {n : ℕ}
    (first second target : Fin n)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    Circuit.eval
        (relativePhaseToffoliThreeGateCircuit first second target
          hfirstTarget hsecondTarget) =
      Circuit.eval
        (relativePhaseToffoliACircuit first second target
          hfirstTarget hsecondTarget) := by
  change Circuit.eval
      (relativePhaseToffoliThreeGateFusionCircuit first second target
        hfirstTarget hsecondTarget).lower = _
  rw [← lower_relativePhaseToffoliAFusionCircuit,
    FusionCircuit.eval_lower, FusionCircuit.eval_lower]
  exact eval_relativePhaseToffoliThreeGateFusionCircuit_eq_A first second target
    hfirstTarget hsecondTarget

/-- Exact arbitrary-register semantics of the named three-node fusion syntax. -/
theorem eval_relativePhaseToffoliThreeGateFusionCircuit {n : ℕ}
    (first second target : Fin n)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    FusionCircuit.eval
        (relativePhaseToffoliThreeGateFusionCircuit first second target
          hfirstTarget hsecondTarget) =
      relativeToffoliUnitary first second target
        hfirstTarget hsecondTarget := by
  rw [eval_relativePhaseToffoliThreeGateFusionCircuit_eq_A first second target
      hfirstTarget hsecondTarget,
    eval_relativePhaseToffoliAFusionCircuit]

/-- Exact arbitrary-register semantics after trusted lowering. -/
theorem eval_relativePhaseToffoliThreeGateCircuit {n : ℕ}
    (first second target : Fin n)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    Circuit.eval
        (relativePhaseToffoliThreeGateCircuit first second target
          hfirstTarget hsecondTarget) =
      relativeToffoliUnitary first second target
        hfirstTarget hsecondTarget := by
  rw [← lower_relativePhaseToffoliThreeGateFusionCircuit,
    FusionCircuit.eval_lower,
    eval_relativePhaseToffoliThreeGateFusionCircuit first second target
      hfirstTarget hsecondTarget]

/-! ## Exact signed action and the strongest justified phase relations -/

/--
Exact signed computational-basis action of the lowered three-gate circuit.  The
input-column sign is negative precisely on the established `101` case.
-/
theorem relativePhaseToffoliThreeGateCircuit_mulVec_basisKet {n : ℕ}
    (first second target : Fin n) (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target)
    (input : Basis n) :
    (Circuit.eval
        (relativePhaseToffoliThreeGateCircuit first second target
          hfirstTarget hsecondTarget) : Gate n) *ᵥ basisKet input =
      (relativeToffoliPhase first second target hfirstTarget hsecondTarget
        (splitTarget target input).2 (input target) : ℂ) •
        basisKet (toffoliOutput first second target input) := by
  rw [eval_relativePhaseToffoliThreeGateCircuit first second target
    hfirstTarget hsecondTarget]
  exact relativeToffoliUnitary_mulVec_basisKet first second target hfirstSecond
    hfirstTarget hsecondTarget input

/-- The exact `101`-sign circuit agrees with Toffoli up to input-column phases. -/
theorem relativePhaseToffoliThreeGateCircuit_basisPhaseEq_toffoli {n : ℕ}
    (first second target : Fin n) (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    BasisPhaseEq
      (toffoliUnitary first second target hfirstTarget hsecondTarget : Gate n)
      (Circuit.eval
        (relativePhaseToffoliThreeGateCircuit first second target
          hfirstTarget hsecondTarget) : Gate n) := by
  rw [eval_relativePhaseToffoliThreeGateCircuit first second target
    hfirstTarget hsecondTarget]
  exact relativeToffoliUnitary_basisPhaseEq_toffoli first second target
    hfirstSecond hfirstTarget hsecondTarget

/-- The named construction has the same classical reversible basis behavior. -/
theorem relativePhaseToffoliThreeGateCircuit_sameBasisBehavior {n : ℕ}
    (first second target : Fin n) (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    SameBasisBehavior
      (toffoliUnitary first second target hfirstTarget hsecondTarget : Gate n)
      (Circuit.eval
        (relativePhaseToffoliThreeGateCircuit first second target
          hfirstTarget hsecondTarget) : Gate n) :=
  BasisPhaseEq.toSameBasisBehavior
    (relativePhaseToffoliThreeGateCircuit_basisPhaseEq_toffoli
      first second target hfirstSecond hfirstTarget hsecondTarget)

/-- The named construction preserves computational-basis measurement outcomes. -/
theorem relativePhaseToffoliThreeGateCircuit_basisMeasurementEq {n : ℕ}
    (first second target : Fin n) (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    BasisMeasurementEq
      (toffoliUnitary first second target hfirstTarget hsecondTarget : Gate n)
      (Circuit.eval
        (relativePhaseToffoliThreeGateCircuit first second target
          hfirstTarget hsecondTarget) : Gate n) :=
  BasisPhaseEq.toBasisMeasurementEq
    (relativePhaseToffoliThreeGateCircuit_basisPhaseEq_toffoli
      first second target hfirstSecond hfirstTarget hsecondTarget)

/-! ## Literal syntax-derived resources -/

@[simp]
theorem relativePhaseToffoliThreeGateFusionCircuit_oneQubitCount {n : ℕ}
    (first second target : Fin n)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    FusionCircuit.oneQubitCount
        (relativePhaseToffoliThreeGateFusionCircuit first second target
          hfirstTarget hsecondTarget) = 0 := rfl

@[simp]
theorem relativePhaseToffoliThreeGateFusionCircuit_cnotCount {n : ℕ}
    (first second target : Fin n)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    FusionCircuit.cnotCount
        (relativePhaseToffoliThreeGateFusionCircuit first second target
          hfirstTarget hsecondTarget) = 0 := rfl

@[simp]
theorem relativePhaseToffoliThreeGateFusionCircuit_twoQubitCount {n : ℕ}
    (first second target : Fin n)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    FusionCircuit.twoQubitCount
        (relativePhaseToffoliThreeGateFusionCircuit first second target
          hfirstTarget hsecondTarget) = 3 := rfl

@[simp]
theorem relativePhaseToffoliThreeGateFusionCircuit_gateCount {n : ℕ}
    (first second target : Fin n)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    FusionCircuit.gateCount
        (relativePhaseToffoliThreeGateFusionCircuit first second target
          hfirstTarget hsecondTarget) = 3 := rfl

/-- Section 8 charges the explicit three-node fusion circuit exactly three. -/
@[simp]
theorem relativePhaseToffoliThreeGateFusionCircuit_arbitraryTwoQubitCost
    {n : ℕ} (first second target : Fin n)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    FusionCircuit.cost CostModel.arbitraryTwoQubit
        (relativePhaseToffoliThreeGateFusionCircuit first second target
          hfirstTarget hsecondTarget) = some 3 := rfl

/-- The earlier one-qubit/CNOT model does not price generic `U(4)` nodes. -/
@[simp]
theorem relativePhaseToffoliThreeGateFusionCircuit_oneQubitCNOTCost
    {n : ℕ} (first second target : Fin n)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    FusionCircuit.cost CostModel.oneQubitCNOT
        (relativePhaseToffoliThreeGateFusionCircuit first second target
          hfirstTarget hsecondTarget) = none := rfl

@[simp]
theorem relativePhaseToffoliThreeGateCircuit_oneQubitCount {n : ℕ}
    (first second target : Fin n)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    Circuit.kindCount .oneQubit
        (relativePhaseToffoliThreeGateCircuit first second target
          hfirstTarget hsecondTarget) = 0 := by
  rw [← lower_relativePhaseToffoliThreeGateFusionCircuit,
    FusionCircuit.oneQubitCount_lower]
  simp

@[simp]
theorem relativePhaseToffoliThreeGateCircuit_cnotCount {n : ℕ}
    (first second target : Fin n)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    Circuit.kindCount .cnot
        (relativePhaseToffoliThreeGateCircuit first second target
          hfirstTarget hsecondTarget) = 0 := by
  rw [← lower_relativePhaseToffoliThreeGateFusionCircuit,
    FusionCircuit.cnotCount_lower]
  simp

@[simp]
theorem relativePhaseToffoliThreeGateCircuit_twoQubitCount {n : ℕ}
    (first second target : Fin n)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    Circuit.kindCount .arbitraryTwoQubit
        (relativePhaseToffoliThreeGateCircuit first second target
          hfirstTarget hsecondTarget) = 3 := by
  rw [← lower_relativePhaseToffoliThreeGateFusionCircuit,
    FusionCircuit.twoQubitCount_lower]
  simp

@[simp]
theorem relativePhaseToffoliThreeGateCircuit_gateCount {n : ℕ}
    (first second target : Fin n)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    Circuit.gateCount
        (relativePhaseToffoliThreeGateCircuit first second target
          hfirstTarget hsecondTarget) = 3 := by
  rw [← lower_relativePhaseToffoliThreeGateFusionCircuit,
    FusionCircuit.gateCount_lower]
  simp

/-- Section 8 charges the trusted lowered circuit exactly three. -/
@[simp]
theorem relativePhaseToffoliThreeGateCircuit_arbitraryTwoQubitCost {n : ℕ}
    (first second target : Fin n)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    Circuit.cost CostModel.arbitraryTwoQubit
        (relativePhaseToffoliThreeGateCircuit first second target
          hfirstTarget hsecondTarget) = some 3 := by
  rw [← lower_relativePhaseToffoliThreeGateFusionCircuit,
    FusionCircuit.cost_lower]
  simp

/-- The trusted lowered circuit remains unsupported in the earlier model. -/
@[simp]
theorem relativePhaseToffoliThreeGateCircuit_oneQubitCNOTCost {n : ℕ}
    (first second target : Fin n)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    Circuit.cost CostModel.oneQubitCNOT
        (relativePhaseToffoliThreeGateCircuit first second target
          hfirstTarget hsecondTarget) = none := by
  rw [← lower_relativePhaseToffoliThreeGateFusionCircuit,
    FusionCircuit.cost_lower]
  simp

end

end Barenco.ThreeQubit
