import Barenco.Optimization.FusionResources
import Barenco.ThreeQubit.RelativePhase

/-!
# Optimizer-visible relative-phase Toffoli input

This module reconstructs the paper's first seven-node relative-phase Toffoli
diagram in payload-preserving fusion syntax.  The chronology is

`A; CNOT(second,target); A; CNOT(first,target);`
`A†; CNOT(second,target); A†`,

where `A = R_y(π/4)`.  Trusted lowering is definitionally the established
`relativePhaseToffoliACircuit`; its exact arbitrary-register evaluator theorem
therefore transfers without any phase relaxation.  The literal pre-normalization
profile is four one-qubit gates, three CNOTs, and seven total gates under either
named model.
-/

namespace Barenco.ThreeQubit

open Barenco.OneQubit
open Barenco.Optimization

noncomputable section

/--
The first relative-phase Toffoli diagram as a transparent chronological fusion
circuit retaining every local payload.
-/
def relativePhaseToffoliAFusionCircuit {n : ℕ}
    (first second target : Fin n)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    FusionCircuit n :=
  [FusionPrimitive.oneQubit target (ryUnitary (Real.pi / 4)),
    FusionPrimitive.cnot second target hsecondTarget,
    FusionPrimitive.oneQubit target (ryUnitary (Real.pi / 4)),
    FusionPrimitive.cnot first target hfirstTarget,
    FusionPrimitive.oneQubit target (ryUnitary (-(Real.pi / 4))),
    FusionPrimitive.cnot second target hsecondTarget,
    FusionPrimitive.oneQubit target (ryUnitary (-(Real.pi / 4)))]

/--
The transparent fusion input lowers exactly to the existing seven-node circuit,
including chronology, local payloads, and distinctness witnesses.
-/
@[simp]
theorem lower_relativePhaseToffoliAFusionCircuit {n : ℕ}
    (first second target : Fin n)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    FusionCircuit.lower
        (relativePhaseToffoliAFusionCircuit first second target
          hfirstTarget hsecondTarget) =
      relativePhaseToffoliACircuit first second target
        hfirstTarget hsecondTarget := rfl

/-- The fusion evaluator is exactly the evaluator of the established circuit. -/
theorem eval_relativePhaseToffoliAFusionCircuit_eq_existing {n : ℕ}
    (first second target : Fin n)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    FusionCircuit.eval
        (relativePhaseToffoliAFusionCircuit first second target
          hfirstTarget hsecondTarget) =
      Circuit.eval
        (relativePhaseToffoliACircuit first second target
          hfirstTarget hsecondTarget) := by
  rw [← FusionCircuit.eval_lower,
    lower_relativePhaseToffoliAFusionCircuit]

/--
Exact arbitrary-register semantics of the transparent optimizer input.  This is
matrix equality, not merely equality up to a global or basis-dependent phase.
-/
theorem eval_relativePhaseToffoliAFusionCircuit {n : ℕ}
    (first second target : Fin n)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    FusionCircuit.eval
        (relativePhaseToffoliAFusionCircuit first second target
          hfirstTarget hsecondTarget) =
      relativeToffoliUnitary first second target
        hfirstTarget hsecondTarget := by
  rw [eval_relativePhaseToffoliAFusionCircuit_eq_existing,
    eval_relativePhaseToffoliACircuit]

/-! ## Literal pre-normalization resources -/

/-- The transparent input contains four literal one-qubit payload nodes. -/
@[simp]
theorem relativePhaseToffoliAFusionCircuit_oneQubitCount {n : ℕ}
    (first second target : Fin n)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    FusionCircuit.oneQubitCount
        (relativePhaseToffoliAFusionCircuit first second target
          hfirstTarget hsecondTarget) = 4 := rfl

/-- The transparent input contains three literal CNOT nodes. -/
@[simp]
theorem relativePhaseToffoliAFusionCircuit_cnotCount {n : ℕ}
    (first second target : Fin n)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    FusionCircuit.cnotCount
        (relativePhaseToffoliAFusionCircuit first second target
          hfirstTarget hsecondTarget) = 3 := rfl

/-- The unnormalized transparent input contains no generic `U(4)` node. -/
@[simp]
theorem relativePhaseToffoliAFusionCircuit_twoQubitCount {n : ℕ}
    (first second target : Fin n)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    FusionCircuit.twoQubitCount
        (relativePhaseToffoliAFusionCircuit first second target
          hfirstTarget hsecondTarget) = 0 := rfl

/-- The transparent input contains seven literal syntax nodes. -/
@[simp]
theorem relativePhaseToffoliAFusionCircuit_gateCount {n : ℕ}
    (first second target : Fin n)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    FusionCircuit.gateCount
        (relativePhaseToffoliAFusionCircuit first second target
          hfirstTarget hsecondTarget) = 7 := rfl

/-- Sections 3--7 accept the literal input and charge all seven nodes. -/
@[simp]
theorem relativePhaseToffoliAFusionCircuit_oneQubitCNOTCost {n : ℕ}
    (first second target : Fin n)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    FusionCircuit.cost CostModel.oneQubitCNOT
        (relativePhaseToffoliAFusionCircuit first second target
          hfirstTarget hsecondTarget) = some 7 := rfl

/-- Section 8 also accepts the literal input and charges all seven nodes. -/
@[simp]
theorem relativePhaseToffoliAFusionCircuit_arbitraryTwoQubitCost {n : ℕ}
    (first second target : Fin n)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    FusionCircuit.cost CostModel.arbitraryTwoQubit
        (relativePhaseToffoliAFusionCircuit first second target
          hfirstTarget hsecondTarget) = some 7 := rfl

end

end Barenco.ThreeQubit
