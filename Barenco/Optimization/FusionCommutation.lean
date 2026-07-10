import Barenco.Optimization.FusionLaws
import Barenco.ThreeQubit.Lemma61

/-!
# Exact commutation laws for fusion syntax

This proof-side leaf exposes only commutations backed by exact arbitrary-width
semantic theorems:

* one-qubit gates on distinct wires commute; and
* a one-qubit gate commutes with a CNOT when its wire is distinct from both CNOT
  endpoints.

The rules do not inspect or trust structural support metadata.  They invoke the
certified locality results from `Barenco.ThreeQubit.Lemma61` for the concrete
trusted constructors.  Generic evaluator lemmas then justify swapping a
certified commuting adjacent pair at the head, tail, or inside an arbitrary
chronological context.  Every equality is exact; no phase quotient is used.
-/

namespace Barenco.Optimization

open Barenco

/-- Exact semantic commutation of two visible fusion nodes. -/
def DenotationsCommute {n : ℕ}
    (first second : FusionPrimitive n) : Prop :=
  first.denotation * second.denotation =
    second.denotation * first.denotation

namespace DenotationsCommute

/-- Semantic commutation is symmetric. -/
theorem symm {n : ℕ} {first second : FusionPrimitive n}
    (hcommute : DenotationsCommute first second) :
    DenotationsCommute second first := by
  exact Eq.symm hcommute

end DenotationsCommute

/-! ## Constructor-backed local commutations -/

/-- One-qubit payloads on distinct ambient wires commute exactly. -/
theorem oneQubit_denotationsCommute_of_ne {n : ℕ}
    (firstWire secondWire : Fin n) (h : firstWire ≠ secondWire)
    (firstPayload secondPayload : QubitUnitary) :
    DenotationsCommute
      (.oneQubit firstWire firstPayload)
      (.oneQubit secondWire secondPayload) := by
  exact Barenco.ThreeQubit.localUnitary_commute_of_ne
    firstWire secondWire h firstPayload secondPayload

/--
A CNOT commutes exactly with a one-qubit payload on a wire disjoint from its
control and target.
-/
theorem cnot_oneQubit_denotationsCommute_of_disjoint {n : ℕ}
    (control cnotTarget localWire : Fin n)
    (hcontrolTarget : control ≠ cnotTarget)
    (hcontrolLocal : control ≠ localWire)
    (htargetLocal : cnotTarget ≠ localWire)
    (payload : QubitUnitary) :
    DenotationsCommute
      (.cnot control cnotTarget hcontrolTarget)
      (.oneQubit localWire payload) := by
  exact Barenco.ThreeQubit.cnotUnitary_commute_localUnitary
    control cnotTarget localWire hcontrolTarget hcontrolLocal htargetLocal payload

/-- Symmetric one-qubit/CNOT form of the exact disjoint-wire law. -/
theorem oneQubit_cnot_denotationsCommute_of_disjoint {n : ℕ}
    (localWire control cnotTarget : Fin n)
    (hcontrolTarget : control ≠ cnotTarget)
    (hcontrolLocal : control ≠ localWire)
    (htargetLocal : cnotTarget ≠ localWire)
    (payload : QubitUnitary) :
    DenotationsCommute
      (.oneQubit localWire payload)
      (.cnot control cnotTarget hcontrolTarget) :=
  (cnot_oneQubit_denotationsCommute_of_disjoint
    control cnotTarget localWire hcontrolTarget
      hcontrolLocal htargetLocal payload).symm

/-! ## Generic adjacent-swap evaluator laws -/

/-- Swap a certified commuting adjacent pair at the head of any tail. -/
theorem eval_swap_head {n : ℕ}
    (first second : FusionPrimitive n) (tail : FusionCircuit n)
    (hcommute : DenotationsCommute first second) :
    FusionCircuit.eval (first :: second :: tail) =
      FusionCircuit.eval (second :: first :: tail) := by
  simp only [FusionCircuit.eval_cons]
  calc
    (FusionCircuit.eval tail * second.denotation) * first.denotation =
        FusionCircuit.eval tail * (second.denotation * first.denotation) :=
      mul_assoc _ _ _
    _ = FusionCircuit.eval tail * (first.denotation * second.denotation) := by
      rw [hcommute]
    _ = (FusionCircuit.eval tail * first.denotation) * second.denotation :=
      (mul_assoc _ _ _).symm

/-- Swap a certified commuting pair at the chronological end of any prefix. -/
theorem eval_swap_tail {n : ℕ}
    (before : FusionCircuit n) (first second : FusionPrimitive n)
    (hcommute : DenotationsCommute first second) :
    FusionCircuit.eval
        (FusionCircuit.append before [first, second]) =
      FusionCircuit.eval
        (FusionCircuit.append before [second, first]) := by
  rw [FusionCircuit.eval_append, FusionCircuit.eval_append,
    eval_swap_head first second [] hcommute]

/-- Swap a certified commuting adjacent pair inside any chronological context. -/
theorem eval_swap_context {n : ℕ}
    (before tail : FusionCircuit n)
    (first second : FusionPrimitive n)
    (hcommute : DenotationsCommute first second) :
    FusionCircuit.eval
        (FusionCircuit.append before (first :: second :: tail)) =
      FusionCircuit.eval
        (FusionCircuit.append before (second :: first :: tail)) := by
  rw [FusionCircuit.eval_append, FusionCircuit.eval_append,
    eval_swap_head first second tail hcommute]

/-- The arbitrary-context swap remains exact after trusted lowering. -/
theorem eval_lower_swap_context {n : ℕ}
    (before tail : FusionCircuit n)
    (first second : FusionPrimitive n)
    (hcommute : DenotationsCommute first second) :
    Circuit.eval
        (FusionCircuit.lower
          (FusionCircuit.append before (first :: second :: tail))) =
      Circuit.eval
        (FusionCircuit.lower
          (FusionCircuit.append before (second :: first :: tail))) := by
  rw [FusionCircuit.eval_lower, FusionCircuit.eval_lower]
  exact eval_swap_context before tail first second hcommute

end Barenco.Optimization
