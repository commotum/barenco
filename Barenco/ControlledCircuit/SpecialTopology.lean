import Barenco.ControlledCircuit.Block
import Barenco.OneQubit.CircuitBridge
import Barenco.Cost

/-!
# Three- and four-gate controlled-circuit topologies

This leaf defines the chronological circuit shapes used in Barenco et al.,
Lemmas 5.4 and 5.5, before classifying which one-qubit targets they realize.

* `twoCNOTCircuit` is `[A, CNOT, B, CNOT]`. Its inactive target block is
  `B * A`, and its active block is `X * B * X * A`.
* `oneCNOTCircuit` is `[A, CNOT, B]`. Its inactive target block is `B * A`,
  and its active block is `B * X * A`.

The builders are public runtime syntax. Evaluator, characterization, and resource
theorems are public proof-side API. No Pauli-conjugate or Euler classification is
proved here.
-/

namespace Barenco.ControlledCircuit

open Barenco.OneQubit

/-! ## Lemma 5.4 two-CNOT topology -/

/-- Chronological topology `[A(target), CNOT, B(target), CNOT]`. -/
def twoCNOTCircuit {n : ℕ} (control target : Fin n) (h : control ≠ target)
    (A B : QubitUnitary) : Circuit n :=
  [Primitive.oneQubit target A,
    Primitive.cnot control target h,
    Primitive.oneQubit target B,
    Primitive.cnot control target h]

/-- Direct full-register product produced by chronological evaluation. -/
theorem eval_twoCNOTCircuit_raw {n : ℕ}
    (control target : Fin n) (h : control ≠ target) (A B : QubitUnitary) :
    (Circuit.eval (twoCNOTCircuit control target h A B) : Gate n) =
      cnotRaw control target h * localRaw target B *
        cnotRaw control target h * localRaw target A := by
  simp [twoCNOTCircuit, Circuit.eval]

/-- Exact inactive and active target blocks of the two-CNOT topology. -/
theorem eval_twoCNOTCircuit_raw_blocks {n : ℕ}
    (control target : Fin n) (h : control ≠ target) (A B : QubitUnitary) :
    (Circuit.eval (twoCNOTCircuit control target h A B) : Gate n) =
      targetBlockRaw target (fun rest =>
        if rest ⟨control, h⟩ then
          sigmaX * (B : QubitMatrix) * sigmaX * (A : QubitMatrix)
        else
          (B : QubitMatrix) * (A : QubitMatrix)) := by
  rw [eval_twoCNOTCircuit_raw]
  simp_rw [localRaw_eq_targetBlockRaw, cnotRaw_eq_targetBlockRaw]
  rw [targetBlockRaw_mul, targetBlockRaw_mul, targetBlockRaw_mul]
  congr 1
  funext rest
  cases hcontrol : rest ⟨control, h⟩ <;>
    simp [sigmaX_eq_coe_pauliX]

/--
The two-CNOT topology implements a singleton positive control of `W` exactly iff
its inactive block is identity and its active block is `W`.
-/
theorem eval_twoCNOTCircuit_eq_iff {n : ℕ}
    (control target : Fin n) (h : control ≠ target) (A B W : QubitUnitary) :
    Circuit.eval (twoCNOTCircuit control target h A B) =
        positiveControlledUnitary target ({⟨control, h⟩} : ControlSet target) W ↔
      (B : QubitMatrix) * (A : QubitMatrix) = 1 ∧
        sigmaX * (B : QubitMatrix) * sigmaX * (A : QubitMatrix) =
          (W : QubitMatrix) := by
  constructor
  · intro heval
    have hraw := congrArg Subtype.val heval
    rw [eval_twoCNOTCircuit_raw_blocks, coe_positiveControlledUnitary,
      positiveControlledRaw_singleton_eq_targetBlockRaw] at hraw
    have hblocks := targetBlockRaw_injective target hraw
    constructor
    · simpa using congrFun hblocks (fun _ => false)
    · simpa using congrFun hblocks (fun _ => true)
  · rintro ⟨hinactive, hactive⟩
    apply Subtype.ext
    rw [eval_twoCNOTCircuit_raw_blocks, coe_positiveControlledUnitary,
      positiveControlledRaw_singleton_eq_targetBlockRaw]
    congr 1
    funext rest
    cases hcontrol : rest ⟨control, h⟩ <;>
      simp [hinactive, hactive]

/-! ### Syntax-derived resources -/

@[simp]
theorem twoCNOTCircuit_gateCount {n : ℕ}
    (control target : Fin n) (h : control ≠ target) (A B : QubitUnitary) :
    Circuit.gateCount (twoCNOTCircuit control target h A B) = 4 := by
  rfl

@[simp]
theorem twoCNOTCircuit_kindCounts {n : ℕ}
    (control target : Fin n) (h : control ≠ target) (A B : QubitUnitary) :
    Circuit.kindCount .oneQubit (twoCNOTCircuit control target h A B) = 2 ∧
      Circuit.kindCount .cnot (twoCNOTCircuit control target h A B) = 2 := by
  simp [twoCNOTCircuit, Circuit.kindCount]

@[simp]
theorem twoCNOTCircuit_oneQubitCNOTCost {n : ℕ}
    (control target : Fin n) (h : control ≠ target) (A B : QubitUnitary) :
    Circuit.cost CostModel.oneQubitCNOT (twoCNOTCircuit control target h A B) =
      some 4 := by
  rfl

/-! ## Lemma 5.5 one-CNOT topology -/

/-- Chronological topology `[A(target), CNOT, B(target)]`. -/
def oneCNOTCircuit {n : ℕ} (control target : Fin n) (h : control ≠ target)
    (A B : QubitUnitary) : Circuit n :=
  [Primitive.oneQubit target A,
    Primitive.cnot control target h,
    Primitive.oneQubit target B]

/-- Direct full-register product produced by chronological evaluation. -/
theorem eval_oneCNOTCircuit_raw {n : ℕ}
    (control target : Fin n) (h : control ≠ target) (A B : QubitUnitary) :
    (Circuit.eval (oneCNOTCircuit control target h A B) : Gate n) =
      localRaw target B * cnotRaw control target h * localRaw target A := by
  simp [oneCNOTCircuit, Circuit.eval]

/-- Exact inactive and active target blocks of the one-CNOT topology. -/
theorem eval_oneCNOTCircuit_raw_blocks {n : ℕ}
    (control target : Fin n) (h : control ≠ target) (A B : QubitUnitary) :
    (Circuit.eval (oneCNOTCircuit control target h A B) : Gate n) =
      targetBlockRaw target (fun rest =>
        if rest ⟨control, h⟩ then
          (B : QubitMatrix) * sigmaX * (A : QubitMatrix)
        else
          (B : QubitMatrix) * (A : QubitMatrix)) := by
  rw [eval_oneCNOTCircuit_raw]
  simp_rw [localRaw_eq_targetBlockRaw, cnotRaw_eq_targetBlockRaw]
  rw [targetBlockRaw_mul, targetBlockRaw_mul]
  congr 1
  funext rest
  cases hcontrol : rest ⟨control, h⟩ <;>
    simp [sigmaX_eq_coe_pauliX]

/--
The one-CNOT topology implements a singleton positive control of `V` exactly iff
its inactive block is identity and its active block is `V`.
-/
theorem eval_oneCNOTCircuit_eq_iff {n : ℕ}
    (control target : Fin n) (h : control ≠ target) (A B V : QubitUnitary) :
    Circuit.eval (oneCNOTCircuit control target h A B) =
        positiveControlledUnitary target ({⟨control, h⟩} : ControlSet target) V ↔
      (B : QubitMatrix) * (A : QubitMatrix) = 1 ∧
        (B : QubitMatrix) * sigmaX * (A : QubitMatrix) = (V : QubitMatrix) := by
  constructor
  · intro heval
    have hraw := congrArg Subtype.val heval
    rw [eval_oneCNOTCircuit_raw_blocks, coe_positiveControlledUnitary,
      positiveControlledRaw_singleton_eq_targetBlockRaw] at hraw
    have hblocks := targetBlockRaw_injective target hraw
    constructor
    · simpa using congrFun hblocks (fun _ => false)
    · simpa using congrFun hblocks (fun _ => true)
  · rintro ⟨hinactive, hactive⟩
    apply Subtype.ext
    rw [eval_oneCNOTCircuit_raw_blocks, coe_positiveControlledUnitary,
      positiveControlledRaw_singleton_eq_targetBlockRaw]
    congr 1
    funext rest
    cases hcontrol : rest ⟨control, h⟩ <;>
      simp [hinactive, hactive]

/-! ### Syntax-derived resources -/

@[simp]
theorem oneCNOTCircuit_gateCount {n : ℕ}
    (control target : Fin n) (h : control ≠ target) (A B : QubitUnitary) :
    Circuit.gateCount (oneCNOTCircuit control target h A B) = 3 := by
  rfl

@[simp]
theorem oneCNOTCircuit_kindCounts {n : ℕ}
    (control target : Fin n) (h : control ≠ target) (A B : QubitUnitary) :
    Circuit.kindCount .oneQubit (oneCNOTCircuit control target h A B) = 2 ∧
      Circuit.kindCount .cnot (oneCNOTCircuit control target h A B) = 1 := by
  simp [oneCNOTCircuit, Circuit.kindCount]

@[simp]
theorem oneCNOTCircuit_oneQubitCNOTCost {n : ℕ}
    (control target : Fin n) (h : control ≠ target) (A B : QubitUnitary) :
    Circuit.cost CostModel.oneQubitCNOT (oneCNOTCircuit control target h A B) =
      some 3 := by
  rfl

end Barenco.ControlledCircuit
