import Barenco.LowerBounds.ScalarObstruction

/-!
# Barenco Lemma 7.7: a CNOT connectivity lower bound

This module combines the three independent ingredients behind the paper's
lower-bound argument:

* the CNOT interaction graph has no more distinct edges than CNOT occurrences;
* a disconnected target component makes every proof-carrying basic circuit
  factor exactly across that wire cut;
* a fully controlled nonscalar one-qubit target cannot have that factorization.

The resulting theorem is stronger and more precise than the source wording: an
exact no-ancilla implementation needs at least `n - 1` CNOT occurrences even if
it may use arbitrarily many one-qubit gates.  The total-basic-gate and named-cost
statements are corollaries of this structural CNOT bound.
-/

namespace Barenco.LowerBounds

open Barenco.OneQubit

noncomputable section

namespace BasicCircuit

/--
Exact implementation of a fully controlled nonscalar target forces the CNOT
interaction graph to be connected.

The target controls are literally every other wire in the same register.  No
ancilla, approximation, measurement, or phase-relaxed target relation is hidden
in this statement.
-/
theorem interactionGraph_connected_of_eval_fullyControlled {n : ℕ}
    (circuit : BasicCircuit n) (target : Fin n) (U : QubitUnitary)
    (hnonscalar : ¬IsScalarQubitMatrix (U : QubitMatrix))
    (heval : BasicCircuit.eval circuit =
      positiveControlledUnitary target (Finset.univ : ControlSet target) U) :
    circuit.interactionGraph.Connected := by
  by_contra hdisconnected
  let cut := circuit.targetComponent target
  have htarget : target ∈ cut := by
    exact circuit.target_mem_targetComponent target
  have hcomplement : ∃ wire : Fin n, wire ∉ cut := by
    have hnonempty :=
      circuit.targetComponent_compl_nonempty_of_not_connected target hdisconnected
    rcases hnonempty with ⟨wire, hwire⟩
    refine ⟨wire, ?_⟩
    change wire ∉ circuit.targetComponent target
    simpa only [Finset.mem_compl] using hwire
  have hfactorEval :
      TensorFactorsAcross cut (BasicCircuit.eval circuit : Gate n) := by
    exact circuit.eval_tensorFactorsAcross_targetComponent target
  have hevalRaw :
      (BasicCircuit.eval circuit : Gate n) =
        positiveControlledRaw target (Finset.univ : ControlSet target) U := by
    have h := congrArg Subtype.val heval
    simpa only [coe_positiveControlledUnitary] using h
  have hfactorTarget :
      TensorFactorsAcross cut
        (positiveControlledRaw target (Finset.univ : ControlSet target) U) := by
    rw [← hevalRaw]
    exact hfactorEval
  exact
    (not_tensorFactorsAcross_fullyControlled_of_exists_not_mem_of_not_scalar
      cut target U htarget hcomplement hnonscalar) hfactorTarget

/--
Barenco Lemma 7.7 in its strongest form justified by the source proof: at least
`n - 1` CNOT occurrences are required for an exact fully controlled nonscalar
target, regardless of how many arbitrary one-qubit gates are available.
-/
theorem fullyControlled_cnotCount_lowerBound {n : ℕ}
    (circuit : BasicCircuit n) (target : Fin n) (U : QubitUnitary)
    (hnonscalar : ¬IsScalarQubitMatrix (U : QubitMatrix))
    (heval : BasicCircuit.eval circuit =
      positiveControlledUnitary target (Finset.univ : ControlSet target) U) :
    n - 1 ≤ circuit.cnotCount := by
  exact circuit.cnotCount_lowerBound_of_interactionGraph_connected
    (circuit.interactionGraph_connected_of_eval_fullyControlled
      target U hnonscalar heval)

/-- Paper-facing scalar-phase formulation of the same CNOT lower bound. -/
theorem fullyControlled_cnotCount_lowerBound_of_not_exists_phaseShiftUnitary
    {n : ℕ} (circuit : BasicCircuit n) (target : Fin n) (U : QubitUnitary)
    (hnonscalar : ¬∃ delta : ℝ, U = phaseShiftUnitary delta)
    (heval : BasicCircuit.eval circuit =
      positiveControlledUnitary target (Finset.univ : ControlSet target) U) :
    n - 1 ≤ circuit.cnotCount := by
  apply circuit.fullyControlled_cnotCount_lowerBound target U
  · intro hscalar
    exact hnonscalar
      ((isScalarQubitMatrix_coe_iff_exists_phaseShiftUnitary U).mp hscalar)
  · exact heval

/-- The paper's weaker total-basic-operation lower bound. -/
theorem fullyControlled_gateCount_lowerBound {n : ℕ}
    (circuit : BasicCircuit n) (target : Fin n) (U : QubitUnitary)
    (hnonscalar : ¬IsScalarQubitMatrix (U : QubitMatrix))
    (heval : BasicCircuit.eval circuit =
      positiveControlledUnitary target (Finset.univ : ControlSet target) U) :
    n - 1 ≤ circuit.gateCount := by
  exact (circuit.fullyControlled_cnotCount_lowerBound target U hnonscalar heval).trans
    circuit.cnotCount_le_gateCount

/--
Any numeric cost assigned to the erased circuit by the Sections 3--7 named model
is at least `n - 1`.  The accepted-cost hypothesis is syntax based; no cost is
inferred from the target matrix equality.
-/
theorem fullyControlled_oneQubitCNOTCost_lowerBound {n cost : ℕ}
    (circuit : BasicCircuit n) (target : Fin n) (U : QubitUnitary)
    (hnonscalar : ¬IsScalarQubitMatrix (U : QubitMatrix))
    (heval : BasicCircuit.eval circuit =
      positiveControlledUnitary target (Finset.univ : ControlSet target) U)
    (hcost : Circuit.cost CostModel.oneQubitCNOT circuit.erase = some cost) :
    n - 1 ≤ cost := by
  exact (circuit.fullyControlled_cnotCount_lowerBound target U hnonscalar heval).trans
    (circuit.cnotCount_le_of_erase_oneQubitCNOTCost_eq_some hcost)

end BasicCircuit

end

end Barenco.LowerBounds
