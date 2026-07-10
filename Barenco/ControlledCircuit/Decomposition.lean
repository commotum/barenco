import Barenco.ControlledCircuit.Block
import Barenco.OneQubit.Lemma43
import Barenco.OneQubit.CircuitBridge
import Barenco.Cost

/-!
# The five-gate controlled special-unitary decomposition

This file reconstructs the diagram in Barenco et al., Lemma 5.1 as actual
chronological circuit syntax. The circuit list is

`A(target); CNOT(control,target); B(target); CNOT(control,target); C(target)`.

Because the library uses column vectors, its active target block is
`C * X * B * X * A`, while its inactive block is `C * B * A`. The evaluator
theorems below hold on an arbitrary ambient register with distinct control and
target wires; they are not inferred from a two-qubit sample.
-/

namespace Barenco.ControlledCircuit

open Barenco.OneQubit

/-- The chronological five-gate topology displayed in Lemma 5.1. -/
def controlledABCCircuit {n : ℕ} (control target : Fin n) (h : control ≠ target)
    (A B C : QubitUnitary) : Circuit n :=
  [Primitive.oneQubit target A,
    Primitive.cnot control target h,
    Primitive.oneQubit target B,
    Primitive.cnot control target h,
    Primitive.oneQubit target C]

/-- Forget the determinant-one certificate while retaining certified unitarity. -/
def specialUnitaryAsUnitary (A : QubitSpecialUnitary) : QubitUnitary :=
  ⟨A, (Matrix.mem_specialUnitaryGroup_iff.mp A.prop).1⟩

@[simp]
theorem coe_specialUnitaryAsUnitary (A : QubitSpecialUnitary) :
    (specialUnitaryAsUnitary A : QubitMatrix) = (A : QubitMatrix) := rfl

/-- Direct full-register matrix product produced by chronological evaluation. -/
theorem eval_controlledABCCircuit_raw {n : ℕ}
    (control target : Fin n) (h : control ≠ target) (A B C : QubitUnitary) :
    (Circuit.eval (controlledABCCircuit control target h A B C) : Gate n) =
      localRaw target C * cnotRaw control target h * localRaw target B *
        cnotRaw control target h * localRaw target A := by
  simp [controlledABCCircuit, Circuit.eval]

/--
The five-gate evaluator exposes exactly its inactive and active target blocks.
-/
theorem eval_controlledABCCircuit_raw_blocks {n : ℕ}
    (control target : Fin n) (h : control ≠ target) (A B C : QubitUnitary) :
    (Circuit.eval (controlledABCCircuit control target h A B C) : Gate n) =
      targetBlockRaw target (fun rest =>
        if rest ⟨control, h⟩ then
          (C : QubitMatrix) * sigmaX * (B : QubitMatrix) * sigmaX *
            (A : QubitMatrix)
        else
          (C : QubitMatrix) * (B : QubitMatrix) * (A : QubitMatrix)) := by
  rw [eval_controlledABCCircuit_raw]
  simp_rw [localRaw_eq_targetBlockRaw, cnotRaw_eq_targetBlockRaw]
  rw [targetBlockRaw_mul, targetBlockRaw_mul, targetBlockRaw_mul,
    targetBlockRaw_mul]
  congr 1
  funext rest
  cases hcontrol : rest ⟨control, h⟩ <;>
    simp [sigmaX_eq_coe_pauliX]

/--
Exact semantic characterization of the five-gate topology. It implements the
single positive control of `W` iff the inactive target product is identity and
the active target product is `W`.
-/
theorem eval_controlledABCCircuit_eq_iff {n : ℕ}
    (control target : Fin n) (h : control ≠ target) (A B C W : QubitUnitary) :
    Circuit.eval (controlledABCCircuit control target h A B C) =
        positiveControlledUnitary target ({⟨control, h⟩} : ControlSet target) W ↔
      (C : QubitMatrix) * (B : QubitMatrix) * (A : QubitMatrix) = 1 ∧
        (C : QubitMatrix) * sigmaX * (B : QubitMatrix) * sigmaX *
          (A : QubitMatrix) = (W : QubitMatrix) := by
  constructor
  · intro heval
    have hraw := congrArg Subtype.val heval
    rw [eval_controlledABCCircuit_raw_blocks, coe_positiveControlledUnitary,
      positiveControlledRaw_singleton_eq_targetBlockRaw] at hraw
    have hblocks := targetBlockRaw_injective target hraw
    constructor
    · simpa using congrFun hblocks (fun _ => false)
    · simpa using congrFun hblocks (fun _ => true)
  · rintro ⟨hinactive, hactive⟩
    apply Subtype.ext
    rw [eval_controlledABCCircuit_raw_blocks, coe_positiveControlledUnitary,
      positiveControlledRaw_singleton_eq_targetBlockRaw]
    congr 1
    funext rest
    cases hcontrol : rest ⟨control, h⟩ <;>
      simp [hinactive, hactive]

/-- Existence of certified special-unitary factors in the Lemma 5.1 topology. -/
def HasControlledSU2Circuit {n : ℕ} (control target : Fin n)
    (h : control ≠ target) (W : QubitUnitary) : Prop :=
  ∃ A B C : QubitSpecialUnitary,
    Circuit.eval (controlledABCCircuit control target h
      (specialUnitaryAsUnitary A) (specialUnitaryAsUnitary B)
      (specialUnitaryAsUnitary C)) =
      positiveControlledUnitary target ({⟨control, h⟩} : ControlSet target) W

/--
Barenco et al., Lemma 5.1, including its converse: the displayed topology with
`SU(2)` factors implements controlled `W` exactly iff `det W = 1`.
-/
theorem controlledSU2Circuit_correct_iff {n : ℕ}
    (control target : Fin n) (h : control ≠ target) (W : QubitUnitary) :
    HasControlledSU2Circuit control target h W ↔
      Matrix.det (W : QubitMatrix) = 1 := by
  constructor
  · rintro ⟨A, B, C, heval⟩
    have hactive :=
      (eval_controlledABCCircuit_eq_iff control target h
        (specialUnitaryAsUnitary A) (specialUnitaryAsUnitary B)
        (specialUnitaryAsUnitary C) W).mp heval |>.2
    have hA := (Matrix.mem_specialUnitaryGroup_iff.mp A.prop).2
    have hB := (Matrix.mem_specialUnitaryGroup_iff.mp B.prop).2
    have hC := (Matrix.mem_specialUnitaryGroup_iff.mp C.prop).2
    have hdet := congrArg Matrix.det hactive
    simpa only [coe_specialUnitaryAsUnitary, Matrix.det_mul, hA, hB, hC,
      sigmaX_det, one_mul, mul_one, neg_mul, mul_neg, neg_neg] using hdet.symm
  · intro hdet
    let Wspecial : QubitSpecialUnitary :=
      ⟨W, Matrix.mem_specialUnitaryGroup_iff.mpr ⟨W.property, hdet⟩⟩
    obtain ⟨A, B, C, hinactive, hactive⟩ :=
      specialUnitary_exists_columnChronologicalABC Wspecial
    refine ⟨A, B, C, ?_⟩
    apply (eval_controlledABCCircuit_eq_iff control target h
      (specialUnitaryAsUnitary A) (specialUnitaryAsUnitary B)
      (specialUnitaryAsUnitary C) W).mpr
    exact ⟨hinactive, by simpa [Wspecial] using hactive⟩

/-! ## Syntax-derived resources for the displayed circuit -/

@[simp]
theorem controlledABCCircuit_gateCount {n : ℕ}
    (control target : Fin n) (h : control ≠ target) (A B C : QubitUnitary) :
    Circuit.gateCount (controlledABCCircuit control target h A B C) = 5 := by
  rfl

@[simp]
theorem controlledABCCircuit_kindCounts {n : ℕ}
    (control target : Fin n) (h : control ≠ target) (A B C : QubitUnitary) :
    Circuit.kindCount .oneQubit (controlledABCCircuit control target h A B C) = 3 ∧
      Circuit.kindCount .cnot (controlledABCCircuit control target h A B C) = 2 := by
  simp [controlledABCCircuit, Circuit.kindCount]

@[simp]
theorem controlledABCCircuit_oneQubitCNOTCost {n : ℕ}
    (control target : Fin n) (h : control ≠ target) (A B C : QubitUnitary) :
    Circuit.cost CostModel.oneQubitCNOT
      (controlledABCCircuit control target h A B C) = some 5 := by
  rfl

end Barenco.ControlledCircuit
