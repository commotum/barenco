import Barenco.ControlledCircuit.Alternative

/-!
# Primitive expansion of the controlled-V macro circuit

This leaf expands both controlled-`V` nodes in `controlledVMacroU2Circuit` by
the Lemma 5.5 topology `[D(target), CNOT(control,target), F(target)]`.  With the
library's standard-column convention, the unmerged chronological circuit is

`E; F*P; D; CNOT; F; F*Q*D; D; CNOT; F; R*D`,

where `E` is the phase gate on the control wire.  The hypothesis `D * F = I`
then justifies the three adjacent target-local merges, producing the existing
Corollary 5.3 circuit `E; P; CNOT; Q; CNOT; R`.

Evaluator equalities and structural resource theorems are deliberately kept
separate: the gate counts and costs below inspect circuit syntax only.
-/

namespace Barenco.ControlledCircuit

open Barenco.OneQubit

noncomputable section

/--
The target-only primitive expansion of `controlledVMacroCoreCircuit`.

The list is chronological.  Each three-node subsequence `D; CNOT; F` is the
Lemma 5.5 implementation of one controlled-`V` macro.
-/
def expandedVMacroCoreCircuit {n : ℕ} (control target : Fin n)
    (h : control ≠ target) (P Q R D F : QubitUnitary) : Circuit n :=
  [Primitive.oneQubit target (F * P),
    Primitive.oneQubit target D,
    Primitive.cnot control target h,
    Primitive.oneQubit target F,
    Primitive.oneQubit target (F * Q * D),
    Primitive.oneQubit target D,
    Primitive.cnot control target h,
    Primitive.oneQubit target F,
    Primitive.oneQubit target (R * D)]

/-- The full ten-primitive expansion, with the control-wire phase gate first. -/
def expandedVMacroU2Circuit {n : ℕ} (control target : Fin n)
    (h : control ≠ target) (delta : ℝ)
    (P Q R D F : QubitUnitary) : Circuit n :=
  Circuit.append (controlledPhaseCircuit control delta)
    (expandedVMacroCoreCircuit control target h P Q R D F)

/-- Explicit ten-node chronological syntax of the full expansion. -/
theorem expandedVMacroU2Circuit_eq_explicit {n : ℕ}
    (control target : Fin n) (h : control ≠ target) (delta : ℝ)
    (P Q R D F : QubitUnitary) :
    expandedVMacroU2Circuit control target h delta P Q R D F =
      [Primitive.oneQubit control (controlPhaseUnitary delta),
        Primitive.oneQubit target (F * P),
        Primitive.oneQubit target D,
        Primitive.cnot control target h,
        Primitive.oneQubit target F,
        Primitive.oneQubit target (F * Q * D),
        Primitive.oneQubit target D,
        Primitive.cnot control target h,
        Primitive.oneQubit target F,
        Primitive.oneQubit target (R * D)] := by
  rfl

/-- Explicit six-node syntax of the existing merged Corollary 5.3 circuit. -/
theorem controlledU2Circuit_eq_explicit {n : ℕ}
    (control target : Fin n) (h : control ≠ target) (delta : ℝ)
    (P Q R : QubitUnitary) :
    controlledU2Circuit control target h delta P Q R =
      [Primitive.oneQubit control (controlPhaseUnitary delta),
        Primitive.oneQubit target P,
        Primitive.cnot control target h,
        Primitive.oneQubit target Q,
        Primitive.cnot control target h,
        Primitive.oneQubit target R] := by
  rfl

/-! ## Evaluator identities -/

/-- Direct full-register product of the nine-node expanded target core. -/
theorem eval_expandedVMacroCoreCircuit_raw {n : ℕ}
    (control target : Fin n) (h : control ≠ target)
    (P Q R D F : QubitUnitary) :
    (Circuit.eval (expandedVMacroCoreCircuit control target h P Q R D F) : Gate n) =
      localRaw target (R * D) * localRaw target F * cnotRaw control target h *
        localRaw target D * localRaw target (F * Q * D) * localRaw target F *
        cnotRaw control target h * localRaw target D * localRaw target (F * P) := by
  simp [expandedVMacroCoreCircuit, Circuit.eval]

private theorem localRaw_mul_localRaw {n : ℕ} (target : Fin n)
    (U W : QubitMatrix) :
    localRaw target U * localRaw target W = localRaw target (U * W) := by
  rw [localRaw_eq_targetBlockRaw, localRaw_eq_targetBlockRaw,
    localRaw_eq_targetBlockRaw, targetBlockRaw_mul]

private theorem localUnitary_mul_localUnitary {n : ℕ} (target : Fin n)
    (U W : QubitUnitary) :
    localUnitary target U * localUnitary target W = localUnitary target (U * W) := by
  apply Subtype.ext
  simp only [Submonoid.coe_mul, coe_localUnitary]
  rw [localRaw_mul_localRaw, Submonoid.coe_mul]

/--
The three adjacent one-qubit merge groups reduce the expanded core to the
five-node A/B/C core.  This theorem uses only `D * F = I`; it does not use a
semantic identification of the controlled-`V` macro.
-/
theorem eval_expandedVMacroCoreCircuit_eq_controlledABCCircuit {n : ℕ}
    (control target : Fin n) (h : control ≠ target)
    (P Q R D F : QubitUnitary)
    (hDF : (D : QubitMatrix) * (F : QubitMatrix) = 1) :
    Circuit.eval (expandedVMacroCoreCircuit control target h P Q R D F) =
      Circuit.eval (controlledABCCircuit control target h P Q R) := by
  have hDFu : D * F = 1 := by
    apply Subtype.ext
    simpa only [Submonoid.coe_mul, Submonoid.coe_one] using hDF
  have hfirstProduct : D * (F * P) = P := by
    rw [← mul_assoc, hDFu, one_mul]
  have hmiddleProduct : D * (F * Q * D) * F = Q := by
    calc
      D * (F * Q * D) * F = (D * F) * Q * (D * F) := by
        simp only [mul_assoc]
      _ = Q := by rw [hDFu]; simp
  have hlastProduct : (R * D) * F = R := by
    rw [mul_assoc, hDFu, mul_one]
  have hfirst :
      Circuit.eval
          [Primitive.oneQubit target (F * P), Primitive.oneQubit target D] =
        localUnitary target P := by
    simpa [Circuit.eval, localUnitary_mul_localUnitary, hfirstProduct]
  have hmiddle :
      Circuit.eval
          [Primitive.oneQubit target F,
            Primitive.oneQubit target (F * Q * D),
            Primitive.oneQubit target D] =
        localUnitary target Q := by
    simpa [Circuit.eval, localUnitary_mul_localUnitary, hmiddleProduct]
  have hlast :
      Circuit.eval
          [Primitive.oneQubit target F, Primitive.oneQubit target (R * D)] =
        localUnitary target R := by
    simpa [Circuit.eval, localUnitary_mul_localUnitary, hlastProduct]
  change Circuit.eval (Circuit.append
      [Primitive.oneQubit target (F * P), Primitive.oneQubit target D]
      (Circuit.append [Primitive.cnot control target h]
        (Circuit.append
          [Primitive.oneQubit target F,
            Primitive.oneQubit target (F * Q * D),
            Primitive.oneQubit target D]
          (Circuit.append [Primitive.cnot control target h]
            [Primitive.oneQubit target F,
              Primitive.oneQubit target (R * D)])))) = _
  rw [Circuit.eval_append, Circuit.eval_append, Circuit.eval_append,
    Circuit.eval_append, hfirst, hmiddle, hlast]
  simp [controlledABCCircuit, Circuit.eval]

/--
Under the Lemma 5.5 equations, the five-node controlled-`V` macro core has the
same evaluator as the merged A/B/C core.
-/
theorem eval_controlledVMacroCoreCircuit_eq_controlledABCCircuit {n : ℕ}
    (control target : Fin n) (h : control ≠ target)
    (P Q R D F V : QubitUnitary)
    (hDF : (D : QubitMatrix) * (F : QubitMatrix) = 1)
    (hV : (V : QubitMatrix) = (F : QubitMatrix) * sigmaX * (D : QubitMatrix)) :
    Circuit.eval (controlledVMacroCoreCircuit control target h P Q R D F V) =
      Circuit.eval (controlledABCCircuit control target h P Q R) := by
  apply Subtype.ext
  rw [eval_controlledVMacroCoreCircuit_raw_blocks,
    eval_controlledABCCircuit_raw_blocks]
  congr 1
  funext rest
  cases rest ⟨control, h⟩
  · simp only [Bool.false_eq_true, if_false, Submonoid.coe_mul]
    calc
      ((R : QubitMatrix) * D) * (F * Q * D) * (F * P) =
        (R : QubitMatrix) * (D * F) * Q * (D * F) * P := by
          noncomm_ring
      _ = (R : QubitMatrix) * Q * P := by rw [hDF]; simp
  · simp only [if_true, Submonoid.coe_mul]
    rw [hV]
    calc
      ((R : QubitMatrix) * D) * (F * sigmaX * D) * (F * Q * D) *
          (F * sigmaX * D) * (F * P) =
        (R : QubitMatrix) * (D * F) * sigmaX * (D * F) * Q * (D * F) *
          sigmaX * (D * F) * P := by
          noncomm_ring
      _ = (R : QubitMatrix) * sigmaX * Q * sigmaX * P := by rw [hDF]; simp

/-- Exact evaluator preservation when both controlled-`V` macros are expanded. -/
theorem eval_expandedVMacroCoreCircuit_eq_macro {n : ℕ}
    (control target : Fin n) (h : control ≠ target)
    (P Q R D F V : QubitUnitary)
    (hDF : (D : QubitMatrix) * (F : QubitMatrix) = 1)
    (hV : (V : QubitMatrix) = (F : QubitMatrix) * sigmaX * (D : QubitMatrix)) :
    Circuit.eval (expandedVMacroCoreCircuit control target h P Q R D F) =
      Circuit.eval (controlledVMacroCoreCircuit control target h P Q R D F V) := by
  rw [eval_expandedVMacroCoreCircuit_eq_controlledABCCircuit control target h
      P Q R D F hDF,
    eval_controlledVMacroCoreCircuit_eq_controlledABCCircuit control target h
      P Q R D F V hDF hV]

/-- Exact evaluator preservation for the full phase-plus-core macro circuit. -/
theorem eval_expandedVMacroU2Circuit_eq_macro {n : ℕ}
    (control target : Fin n) (h : control ≠ target) (delta : ℝ)
    (P Q R D F V : QubitUnitary)
    (hDF : (D : QubitMatrix) * (F : QubitMatrix) = 1)
    (hV : (V : QubitMatrix) = (F : QubitMatrix) * sigmaX * (D : QubitMatrix)) :
    Circuit.eval (expandedVMacroU2Circuit control target h delta P Q R D F) =
      Circuit.eval (controlledVMacroU2Circuit control target h delta P Q R D F V) := by
  rw [expandedVMacroU2Circuit, controlledVMacroU2Circuit,
    Circuit.eval_append, Circuit.eval_append,
    eval_expandedVMacroCoreCircuit_eq_macro control target h P Q R D F V hDF hV]

/--
The ten-node expansion evaluates exactly as the six-node merged Corollary 5.3
circuit.  The proof is the three local merge groups, not a resource argument.
-/
theorem eval_expandedVMacroU2Circuit_eq_controlledU2Circuit {n : ℕ}
    (control target : Fin n) (h : control ≠ target) (delta : ℝ)
    (P Q R D F : QubitUnitary)
    (hDF : (D : QubitMatrix) * (F : QubitMatrix) = 1) :
    Circuit.eval (expandedVMacroU2Circuit control target h delta P Q R D F) =
      Circuit.eval (controlledU2Circuit control target h delta P Q R) := by
  rw [expandedVMacroU2Circuit, controlledU2Circuit,
    Circuit.eval_append, Circuit.eval_append,
    eval_expandedVMacroCoreCircuit_eq_controlledABCCircuit control target h
      P Q R D F hDF]

/-! ## Syntax-derived resources -/

@[simp]
theorem expandedVMacroU2Circuit_gateCount {n : ℕ}
    (control target : Fin n) (h : control ≠ target) (delta : ℝ)
    (P Q R D F : QubitUnitary) :
    Circuit.gateCount
      (expandedVMacroU2Circuit control target h delta P Q R D F) = 10 := by
  rfl

@[simp]
theorem expandedVMacroU2Circuit_kindCounts {n : ℕ}
    (control target : Fin n) (h : control ≠ target) (delta : ℝ)
    (P Q R D F : QubitUnitary) :
    Circuit.kindCount .oneQubit
        (expandedVMacroU2Circuit control target h delta P Q R D F) = 8 ∧
      Circuit.kindCount .cnot
        (expandedVMacroU2Circuit control target h delta P Q R D F) = 2 := by
  simp [expandedVMacroU2Circuit, expandedVMacroCoreCircuit,
    controlledPhaseCircuit, Circuit.append, Circuit.kindCount]

/-- Exact Sections 3–7 cost of the fully expanded ten-primitive circuit. -/
@[simp]
theorem expandedVMacroU2Circuit_oneQubitCNOTCost {n : ℕ}
    (control target : Fin n) (h : control ≠ target) (delta : ℝ)
    (P Q R D F : QubitUnitary) :
    Circuit.cost CostModel.oneQubitCNOT
      (expandedVMacroU2Circuit control target h delta P Q R D F) = some 10 := by
  rfl

/--
The syntax-derived expanded and merged costs are ten and six, respectively.
The second conjunct is the existing Corollary 5.3 cost theorem.
-/
theorem expanded_and_mergedVMacroU2Circuit_oneQubitCNOTCosts {n : ℕ}
    (control target : Fin n) (h : control ≠ target) (delta : ℝ)
    (P Q R D F : QubitUnitary) :
    Circuit.cost CostModel.oneQubitCNOT
        (expandedVMacroU2Circuit control target h delta P Q R D F) = some 10 ∧
      Circuit.cost CostModel.oneQubitCNOT
        (controlledU2Circuit control target h delta P Q R) = some 6 := by
  exact ⟨expandedVMacroU2Circuit_oneQubitCNOTCost control target h delta P Q R D F,
    controlledU2Circuit_oneQubitCNOTCost control target h delta P Q R⟩

end

end Barenco.ControlledCircuit
