import Barenco.LowerBounds.BasicCircuit

/-!
# Exact zero-width obstruction

The proof-carrying one-qubit/CNOT syntax has no primitive at width zero because
every constructor requires an inhabitant of `Fin 0`.  Consequently every
`BasicCircuit 0` is the empty list and evaluates exactly to identity.

The semantic zero-qubit Hilbert space is nevertheless one-dimensional: its
unique computational-basis assignment supports arbitrary scalar phases.  The
certified scalar `-1` below is therefore a concrete unitary that the restricted
width-zero syntax cannot realize.  This is an exact matrix statement, not an
equivalence-up-to-global-phase claim.
-/

namespace Barenco.Universality

open Matrix
open Barenco.LowerBounds

/-- There is no allowed one-qubit/CNOT primitive on a zero-wire register. -/
theorem not_basicPrimitive_zero (primitive : BasicPrimitive 0) : False := by
  cases primitive with
  | oneQubit target _ => exact Fin.elim0 target
  | cnot control _ _ => exact Fin.elim0 control

/-- Every proof-carrying width-zero basic circuit is syntactically empty. -/
theorem basicCircuit_zero_eq_nil (circuit : BasicCircuit 0) : circuit = [] := by
  cases circuit with
  | nil => rfl
  | cons primitive _ => exact (not_basicPrimitive_zero primitive).elim

/-- Every accepted one-qubit/CNOT circuit at width zero evaluates to identity. -/
theorem basicCircuit_zero_eval (circuit : BasicCircuit 0) :
    circuit.eval = (1 : UnitaryGate 0) := by
  rw [basicCircuit_zero_eq_nil circuit]
  rfl

/-- Width-zero restricted circuits contain no primitive occurrences. -/
theorem basicCircuit_zero_gateCount (circuit : BasicCircuit 0) :
    circuit.gateCount = 0 := by
  rw [basicCircuit_zero_eq_nil circuit]
  rfl

/-- The unique computational-basis assignment of a zero-wire register. -/
def zeroWidthBasis : Basis 0 :=
  fun index => Fin.elim0 index

theorem zeroWidthBasis_unique (basis : Basis 0) : basis = zeroWidthBasis := by
  funext index
  exact Fin.elim0 index

/-- Raw scalar `-1` on the one-dimensional zero-qubit Hilbert space. -/
def zeroWidthNegRaw : Gate 0 :=
  fun _ _ => -1

/-- A certified nonidentity zero-qubit unitary: multiplication by `-1`. -/
def zeroWidthNegUnitary : UnitaryGate 0 :=
  ⟨zeroWidthNegRaw, by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    ext row col
    rw [Matrix.mul_apply]
    rw [Fintype.sum_eq_single zeroWidthBasis]
    · simp [zeroWidthNegRaw, Matrix.one_apply, zeroWidthBasis_unique row,
        zeroWidthBasis_unique col]
    · intro basis hbasis
      exact (hbasis (zeroWidthBasis_unique basis)).elim⟩

@[simp]
theorem zeroWidthNegUnitary_apply (row col : Basis 0) :
    zeroWidthNegUnitary row col = -1 := rfl

/-- The certified scalar `-1` is not the exact identity matrix. -/
theorem zeroWidthNegUnitary_ne_one :
    zeroWidthNegUnitary ≠ (1 : UnitaryGate 0) := by
  intro heq
  have hentry := congrArg
    (fun U : UnitaryGate 0 => U zeroWidthBasis zeroWidthBasis) heq
  norm_num [Matrix.one_apply] at hentry

/--
No proof-carrying width-zero circuit over arbitrary one-qubit gates and CNOTs
exactly realizes the scalar `-1` unitary.
-/
theorem no_basicCircuit_zero_realizes_neg (circuit : BasicCircuit 0) :
    circuit.eval ≠ zeroWidthNegUnitary := by
  rw [basicCircuit_zero_eval circuit]
  exact Ne.symm zeroWidthNegUnitary_ne_one

end Barenco.Universality
