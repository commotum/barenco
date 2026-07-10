import Barenco.ThreeQubit.Lemma61
import Barenco.ControlledCircuit.ControlledZ
import Barenco.Equivalence.Phase

/-!
# Section 6.2: exact relative-phase Toffoli constructions

This file reconstructs the two seven-node diagrams from Barenco et al., Section
6.2 on three named, pairwise distinct wires in an arbitrary ambient register.
The paper's row-action matrices are translated to the library's standard-column
semantics before they enter circuit syntax.

Both displayed circuits evaluate exactly to the same signed permutation.  Its
target blocks, indexed by the first and second control bits, are `I`, `I`, `Z`,
and `X`; equivalently, it has Toffoli's basis permutation and negates precisely
the input column with bits `first=true`, `second=false`, `target=true`.

The paper's separately discussed doubly controlled
`W = [[0,1],[-1,0]]` has a different sign witness: after translation it negates
the `first=second=target=true` input column.  Exact signed actions are primary;
`BasisPhaseEq`, `SameBasisBehavior`, and `BasisMeasurementEq` are derived from
them.  No global-phase or all-measurement equivalence is claimed.
-/

namespace Barenco.ThreeQubit

open Barenco.OneQubit
open Barenco.ControlledCircuit
open scoped Matrix

noncomputable section

/-! ## The paper's `W` in both matrix conventions -/

/-- The matrix `W` exactly as displayed under the paper's row-action convention. -/
def paperW : QubitMatrix := matrix2 0 1 (-1) 0

/-- Standard-column translation of the paper's displayed `W`. -/
def wMatrix : QubitMatrix := fromPaper paperW

/-- The translated `W` is the semantic Y rotation through `pi`. -/
theorem wMatrix_eq_ry_pi : wMatrix = ry Real.pi := by
  ext row col
  cases row <;> cases col <;>
    simp [wMatrix, paperW, ry, paperRy, fromPaper, Real.sin_pi_div_two,
      Real.cos_pi_div_two]

/-- Certified standard-column form of the paper's `W`. -/
def wUnitary : QubitUnitary := ryUnitary Real.pi

/-- The certificate `wUnitary` has exactly the translated paper matrix. -/
@[simp]
theorem coe_wUnitary : (wUnitary : QubitMatrix) = wMatrix := by
  rw [wMatrix_eq_ry_pi]
  rfl

/-! ## Shared target-block semantics -/

/-- The exact block family of both relative-phase Toffoli diagrams. -/
def relativeToffoliBlock {n : ℕ} (first second target : Fin n)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target)
    (rest : ComplementBasis target) : QubitUnitary :=
  if rest ⟨first, hfirstTarget⟩ then
    if rest ⟨second, hsecondTarget⟩ then sigmaXUnitary else sigmaZUnitary
  else 1

/-- Certified arbitrary-width signed permutation realized by both diagrams. -/
def relativeToffoliUnitary {n : ℕ} (first second target : Fin n)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    UnitaryGate n :=
  reindexUnitary (splitTarget target).symm
    (blockDiagonalUnitary
      (relativeToffoliBlock first second target hfirstTarget hsecondTarget))

@[simp]
theorem coe_relativeToffoliUnitary {n : ℕ} (first second target : Fin n)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    (relativeToffoliUnitary first second target hfirstTarget hsecondTarget : Gate n) =
      targetBlockRaw target (fun rest ↦
        if rest ⟨first, hfirstTarget⟩ then
          if rest ⟨second, hsecondTarget⟩ then sigmaX else sigmaZ
        else 1) := by
  change targetBlockRaw target (fun rest ↦
      ((relativeToffoliBlock first second target hfirstTarget hsecondTarget rest :
        QubitUnitary) : QubitMatrix)) = _
  congr 1
  funext rest
  cases hfirstBit : rest ⟨first, hfirstTarget⟩ <;>
    cases hsecondBit : rest ⟨second, hsecondTarget⟩ <;>
    simp [relativeToffoliBlock, hfirstBit, hsecondBit]

/-! ## The two chronological circuits -/

/--
The first seven-node diagram:
`A; CNOT(second,target); A; CNOT(first,target); A†; CNOT(second,target); A†`,
where the semantic translation of the paper's label is `A = ry (pi/4)`.
-/
def relativePhaseToffoliACircuit {n : ℕ} (first second target : Fin n)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) : Circuit n :=
  [Primitive.oneQubit target (ryUnitary (Real.pi / 4)),
    Primitive.cnot second target hsecondTarget,
    Primitive.oneQubit target (ryUnitary (Real.pi / 4)),
    Primitive.cnot first target hfirstTarget,
    Primitive.oneQubit target (ryUnitary (-(Real.pi / 4))),
    Primitive.cnot second target hsecondTarget,
    Primitive.oneQubit target (ryUnitary (-(Real.pi / 4)))]

/--
The second seven-node diagram:
`B; CZ(second,target); B†; CZ(first,target); B; CZ(second,target); B†`,
where the semantic translation is `B = ry (3*pi/4)`.

The controlled-Z nodes remain honest controlled-one-qubit macros in this syntax;
they are not mislabeled as CNOTs for resource accounting.
-/
def relativePhaseToffoliBCircuit {n : ℕ} (first second target : Fin n)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) : Circuit n :=
  [Primitive.oneQubit target (ryUnitary (3 * Real.pi / 4)),
    Primitive.positiveControlled target
      ({⟨second, hsecondTarget⟩} : ControlSet target) sigmaZUnitary,
    Primitive.oneQubit target (ryUnitary (-(3 * Real.pi / 4))),
    Primitive.positiveControlled target
      ({⟨first, hfirstTarget⟩} : ControlSet target) sigmaZUnitary,
    Primitive.oneQubit target (ryUnitary (3 * Real.pi / 4)),
    Primitive.positiveControlled target
      ({⟨second, hsecondTarget⟩} : ControlSet target) sigmaZUnitary,
    Primitive.oneQubit target (ryUnitary (-(3 * Real.pi / 4)))]

/-! ## Syntax-derived resources -/

@[simp]
theorem relativePhaseToffoliACircuit_gateCount {n : ℕ}
    (first second target : Fin n) (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target) :
    Circuit.gateCount
      (relativePhaseToffoliACircuit first second target hfirstTarget hsecondTarget) = 7 :=
  rfl

@[simp]
theorem relativePhaseToffoliACircuit_oneQubitCount {n : ℕ}
    (first second target : Fin n) (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target) :
    Circuit.kindCount .oneQubit
      (relativePhaseToffoliACircuit first second target hfirstTarget hsecondTarget) = 4 :=
  rfl

@[simp]
theorem relativePhaseToffoliACircuit_cnotCount {n : ℕ}
    (first second target : Fin n) (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target) :
    Circuit.kindCount .cnot
      (relativePhaseToffoliACircuit first second target hfirstTarget hsecondTarget) = 3 :=
  rfl

@[simp]
theorem relativePhaseToffoliACircuit_oneQubitCNOTCost {n : ℕ}
    (first second target : Fin n) (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target) :
    Circuit.cost CostModel.oneQubitCNOT
      (relativePhaseToffoliACircuit first second target hfirstTarget hsecondTarget) =
        some 7 :=
  rfl

@[simp]
theorem relativePhaseToffoliBCircuit_gateCount {n : ℕ}
    (first second target : Fin n) (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target) :
    Circuit.gateCount
      (relativePhaseToffoliBCircuit first second target hfirstTarget hsecondTarget) = 7 :=
  rfl

@[simp]
theorem relativePhaseToffoliBCircuit_oneQubitCount {n : ℕ}
    (first second target : Fin n) (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target) :
    Circuit.kindCount .oneQubit
      (relativePhaseToffoliBCircuit first second target hfirstTarget hsecondTarget) = 4 :=
  rfl

@[simp]
theorem relativePhaseToffoliBCircuit_controlledZMacroCount {n : ℕ}
    (first second target : Fin n) (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target) :
    Circuit.kindCount (.controlledOneQubit 1)
      (relativePhaseToffoliBCircuit first second target hfirstTarget hsecondTarget) = 3 := by
  simp [relativePhaseToffoliBCircuit, Circuit.kindCount]

/-- The unexpanded controlled-Z macros are unsupported by the one-qubit+CNOT model. -/
@[simp]
theorem relativePhaseToffoliBCircuit_oneQubitCNOTCost {n : ℕ}
    (first second target : Fin n) (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target) :
    Circuit.cost CostModel.oneQubitCNOT
      (relativePhaseToffoliBCircuit first second target hfirstTarget hsecondTarget) = none :=
  rfl

/-! ## Evaluator target blocks -/

theorem eval_relativePhaseToffoliACircuit_blocks {n : ℕ}
    (first second target : Fin n) (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target) :
    (Circuit.eval
        (relativePhaseToffoliACircuit first second target hfirstTarget hsecondTarget) :
      Gate n) =
      targetBlockRaw target (fun rest ↦
        ry (-(Real.pi / 4)) *
          (if rest ⟨second, hsecondTarget⟩ then sigmaX else 1) *
          ry (-(Real.pi / 4)) *
          (if rest ⟨first, hfirstTarget⟩ then sigmaX else 1) *
          ry (Real.pi / 4) *
          (if rest ⟨second, hsecondTarget⟩ then sigmaX else 1) *
          ry (Real.pi / 4)) := by
  simp [relativePhaseToffoliACircuit, Circuit.eval]
  simp_rw [localRaw_eq_targetBlockRaw, cnotRaw_eq_targetBlockRaw]
  rw [targetBlockRaw_mul, targetBlockRaw_mul, targetBlockRaw_mul,
    targetBlockRaw_mul, targetBlockRaw_mul, targetBlockRaw_mul]
  congr 1
  funext rest
  cases hfirstBit : rest ⟨first, hfirstTarget⟩ <;>
    cases hsecondBit : rest ⟨second, hsecondTarget⟩ <;>
    simp [sigmaX_eq_coe_pauliX]

theorem eval_relativePhaseToffoliBCircuit_blocks {n : ℕ}
    (first second target : Fin n) (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target) :
    (Circuit.eval
        (relativePhaseToffoliBCircuit first second target hfirstTarget hsecondTarget) :
      Gate n) =
      targetBlockRaw target (fun rest ↦
        ry (-(3 * Real.pi / 4)) *
          (if rest ⟨second, hsecondTarget⟩ then sigmaZ else 1) *
          ry (3 * Real.pi / 4) *
          (if rest ⟨first, hfirstTarget⟩ then sigmaZ else 1) *
          ry (-(3 * Real.pi / 4)) *
          (if rest ⟨second, hsecondTarget⟩ then sigmaZ else 1) *
          ry (3 * Real.pi / 4)) := by
  simp [relativePhaseToffoliBCircuit, Circuit.eval]
  simp_rw [localRaw_eq_targetBlockRaw,
    positiveControlledRaw_singleton_eq_targetBlockRaw]
  rw [targetBlockRaw_mul, targetBlockRaw_mul, targetBlockRaw_mul,
    targetBlockRaw_mul, targetBlockRaw_mul, targetBlockRaw_mul]
  congr 1
  funext rest
  cases hfirstBit : rest ⟨first, hfirstTarget⟩ <;>
    cases hsecondBit : rest ⟨second, hsecondTarget⟩ <;>
    simp

/-! ## One-qubit block identities -/

/-- Same-side Y rotations cancel across Pauli-X. -/
theorem ry_mul_sigmaX_mul_ry (theta : ℝ) :
    ry theta * sigmaX * ry theta = sigmaX := by
  calc
    ry theta * sigmaX * ry theta =
        (ry theta * sigmaX * ry theta) * (sigmaX * sigmaX) := by
          rw [sigmaX_sq, mul_one]
    _ = ry theta * (sigmaX * ry theta * sigmaX) * sigmaX := by
          noncomm_ring
    _ = ry theta * ry (-theta) * sigmaX := by
          rw [sigmaX_mul_ry_mul_sigmaX]
    _ = sigmaX := by
          rw [ry_mul]
          simp

/-- Pauli-Z is an involution. -/
theorem sigmaZ_sq : sigmaZ * sigmaZ = (1 : QubitMatrix) := by
  rw [sigmaZ_eq_matrix2, matrix2_mul]
  norm_num

/-- Pauli-Z conjugation negates a semantic Y-rotation angle. -/
theorem sigmaZ_mul_ry_mul_sigmaZ (theta : ℝ) :
    sigmaZ * ry theta * sigmaZ = ry (-theta) := by
  ext row col
  cases row <;> cases col <;>
    simp [Matrix.mul_apply, sigmaZ_eq_matrix2] <;>
    rw [show -(↑theta : ℂ) / 2 = -((↑theta : ℂ) / 2) by ring] <;>
    simp

/-- Commutation form of `sigmaZ_mul_ry_mul_sigmaZ`. -/
theorem sigmaZ_mul_ry (theta : ℝ) :
    sigmaZ * ry theta = ry (-theta) * sigmaZ := by
  calc
    sigmaZ * ry theta = (sigmaZ * ry theta * sigmaZ) * sigmaZ := by
      rw [mul_assoc, sigmaZ_sq, mul_one]
    _ = ry (-theta) * sigmaZ := by rw [sigmaZ_mul_ry_mul_sigmaZ]

/-- A semantic `pi` Y rotation followed by Pauli-Z is Pauli-X. -/
theorem ry_pi_mul_sigmaZ : ry Real.pi * sigmaZ = sigmaX := by
  ext row col
  cases row <;> cases col <;>
    simp [Matrix.mul_apply, sigmaZ_eq_matrix2, ry, paperRy, fromPaper]

/-- Semantic Y rotations have exact period `4*pi`, not merely period `2*pi`. -/
theorem ry_four_pi : ry (4 * Real.pi) = (1 : QubitMatrix) := by
  ext row col
  cases row <;> cases col <;>
    simp [ry, paperRy, fromPaper] <;>
    rw [show 4 * (↑Real.pi : ℂ) / 2 = 2 * (↑Real.pi : ℂ) by ring] <;>
    simp

theorem ry_neg_three_pi_eq_ry_pi : ry (-3 * Real.pi) = ry Real.pi := by
  have hmul : ry (-3 * Real.pi) * ry (4 * Real.pi) = ry Real.pi := by
    rw [ry_mul]
    congr 1
    ring
  simpa [ry_four_pi] using hmul

theorem ry_neg_three_pi_mul_sigmaZ :
    ry (-3 * Real.pi) * sigmaZ = sigmaX := by
  rw [ry_neg_three_pi_eq_ry_pi, ry_pi_mul_sigmaZ]

theorem ry_neg_pi_div_two_mul_sigmaX_mul_ry_pi_div_two :
    ry (-(Real.pi / 2)) * sigmaX * ry (Real.pi / 2) = sigmaZ := by
  calc
    ry (-(Real.pi / 2)) * sigmaX * ry (Real.pi / 2) =
        ry (-(Real.pi / 2)) * (ry Real.pi * sigmaZ) * ry (Real.pi / 2) := by
          rw [ry_pi_mul_sigmaZ]
    _ = ry (-(Real.pi / 2)) * ry Real.pi *
        (sigmaZ * ry (Real.pi / 2)) := by noncomm_ring
    _ = ry (-(Real.pi / 2)) * ry Real.pi *
        (ry (-(Real.pi / 2)) * sigmaZ) := by rw [sigmaZ_mul_ry]
    _ = sigmaZ := by
      rw [show ry (-(Real.pi / 2)) * ry Real.pi *
          (ry (-(Real.pi / 2)) * sigmaZ) =
          (ry (-(Real.pi / 2)) * ry Real.pi * ry (-(Real.pi / 2))) *
            sigmaZ by noncomm_ring]
      rw [ry_mul, ry_mul]
      have hsum : -(Real.pi / 2) + Real.pi + -(Real.pi / 2) = 0 := by ring
      rw [hsum, ry_zero, one_mul]

/-- Exact four-case target-block calculation for the first diagram. -/
theorem relativePhaseToffoliA_block_cases (firstBit secondBit : Bool) :
    ry (-(Real.pi / 4)) * (if secondBit then sigmaX else 1) *
          ry (-(Real.pi / 4)) * (if firstBit then sigmaX else 1) *
          ry (Real.pi / 4) * (if secondBit then sigmaX else 1) *
          ry (Real.pi / 4) =
      if firstBit then (if secondBit then sigmaX else sigmaZ) else 1 := by
  cases firstBit <;> cases secondBit
  · simp only [Bool.false_eq_true, ↓reduceIte, mul_one]
    calc
      ry (-(Real.pi / 4)) * ry (-(Real.pi / 4)) *
          ry (Real.pi / 4) * ry (Real.pi / 4) =
          (ry (-(Real.pi / 4)) * ry (-(Real.pi / 4))) *
            (ry (Real.pi / 4) * ry (Real.pi / 4)) := by noncomm_ring
      _ = ry (-(Real.pi / 4) + -(Real.pi / 4)) *
          ry (Real.pi / 4 + Real.pi / 4) := by rw [ry_mul, ry_mul]
      _ = 1 := by rw [ry_mul]; simp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    calc
      ry (-(Real.pi / 4)) * sigmaX * ry (-(Real.pi / 4)) * 1 *
          ry (Real.pi / 4) * sigmaX * ry (Real.pi / 4) =
          (ry (-(Real.pi / 4)) * sigmaX * ry (-(Real.pi / 4))) *
            (ry (Real.pi / 4) * sigmaX * ry (Real.pi / 4)) := by
              simp only [mul_one]
              noncomm_ring
      _ = sigmaX * sigmaX := by rw [ry_mul_sigmaX_mul_ry, ry_mul_sigmaX_mul_ry]
      _ = 1 := sigmaX_sq
  · simp only [Bool.false_eq_true, ↓reduceIte, mul_one]
    have hsumNeg : -(Real.pi / 4) + -(Real.pi / 4) = -(Real.pi / 2) := by ring
    have hsumPos : Real.pi / 4 + Real.pi / 4 = Real.pi / 2 := by ring
    rw [show ry (-(Real.pi / 4)) * ry (-(Real.pi / 4)) * sigmaX *
        ry (Real.pi / 4) * ry (Real.pi / 4) =
        (ry (-(Real.pi / 4)) * ry (-(Real.pi / 4))) * sigmaX *
          (ry (Real.pi / 4) * ry (Real.pi / 4)) by noncomm_ring]
    rw [ry_mul, ry_mul, hsumNeg, hsumPos]
    exact ry_neg_pi_div_two_mul_sigmaX_mul_ry_pi_div_two
  · simp only [↓reduceIte]
    calc
      ry (-(Real.pi / 4)) * sigmaX * ry (-(Real.pi / 4)) * sigmaX *
          ry (Real.pi / 4) * sigmaX * ry (Real.pi / 4) =
          (ry (-(Real.pi / 4)) * sigmaX * ry (-(Real.pi / 4))) * sigmaX *
            (ry (Real.pi / 4) * sigmaX * ry (Real.pi / 4)) := by noncomm_ring
      _ = sigmaX * sigmaX * sigmaX := by
            rw [ry_mul_sigmaX_mul_ry, ry_mul_sigmaX_mul_ry]
      _ = sigmaX := by rw [sigmaX_sq, one_mul]

/-- Exact four-case target-block calculation for the controlled-Z diagram. -/
theorem relativePhaseToffoliB_block_cases (firstBit secondBit : Bool) :
    ry (-(3 * Real.pi / 4)) * (if secondBit then sigmaZ else 1) *
          ry (3 * Real.pi / 4) * (if firstBit then sigmaZ else 1) *
          ry (-(3 * Real.pi / 4)) * (if secondBit then sigmaZ else 1) *
          ry (3 * Real.pi / 4) =
      if firstBit then (if secondBit then sigmaX else sigmaZ) else 1 := by
  cases firstBit <;> cases secondBit
  · simp only [Bool.false_eq_true, ↓reduceIte, mul_one]
    calc
      ry (-(3 * Real.pi / 4)) * ry (3 * Real.pi / 4) *
          ry (-(3 * Real.pi / 4)) * ry (3 * Real.pi / 4) =
          (ry (-(3 * Real.pi / 4)) * ry (3 * Real.pi / 4)) *
            (ry (-(3 * Real.pi / 4)) * ry (3 * Real.pi / 4)) := by noncomm_ring
      _ = ry (-(3 * Real.pi / 4) + 3 * Real.pi / 4) *
          ry (-(3 * Real.pi / 4) + 3 * Real.pi / 4) := by rw [ry_mul, ry_mul]
      _ = 1 := by simp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hInv : ry (3 * Real.pi / 4) * ry (-(3 * Real.pi / 4)) = 1 := by
      rw [ry_mul]
      simp
    have hOuter : ry (-(3 * Real.pi / 4)) * ry (3 * Real.pi / 4) = 1 := by
      rw [ry_mul]
      simp
    simp only [mul_one]
    calc
      ry (-(3 * Real.pi / 4)) * sigmaZ * ry (3 * Real.pi / 4) *
          ry (-(3 * Real.pi / 4)) * sigmaZ * ry (3 * Real.pi / 4) =
          ry (-(3 * Real.pi / 4)) * sigmaZ *
            (ry (3 * Real.pi / 4) * ry (-(3 * Real.pi / 4))) * sigmaZ *
            ry (3 * Real.pi / 4) := by noncomm_ring
      _ = ry (-(3 * Real.pi / 4)) * sigmaZ * 1 * sigmaZ *
            ry (3 * Real.pi / 4) := by rw [hInv]
      _ = ry (-(3 * Real.pi / 4)) * ry (3 * Real.pi / 4) := by
            rw [show ry (-(3 * Real.pi / 4)) * sigmaZ * 1 * sigmaZ *
                ry (3 * Real.pi / 4) =
                ry (-(3 * Real.pi / 4)) * (sigmaZ * sigmaZ) *
                  ry (3 * Real.pi / 4) by noncomm_ring]
            rw [sigmaZ_sq]
            noncomm_ring
      _ = 1 := hOuter
  · simp only [Bool.false_eq_true, ↓reduceIte, mul_one]
    have hInv : ry (-(3 * Real.pi / 4)) * ry (3 * Real.pi / 4) = 1 := by
      rw [ry_mul]
      simp
    calc
      ry (-(3 * Real.pi / 4)) * ry (3 * Real.pi / 4) * sigmaZ *
          ry (-(3 * Real.pi / 4)) * ry (3 * Real.pi / 4) =
          (ry (-(3 * Real.pi / 4)) * ry (3 * Real.pi / 4)) * sigmaZ *
            (ry (-(3 * Real.pi / 4)) * ry (3 * Real.pi / 4)) := by noncomm_ring
      _ = sigmaZ := by rw [hInv, one_mul, mul_one]
  · simp only [↓reduceIte]
    have hcomm : sigmaZ * ry (3 * Real.pi / 4) =
        ry (-(3 * Real.pi / 4)) * sigmaZ := by
      simpa using sigmaZ_mul_ry (3 * Real.pi / 4)
    calc
      ry (-(3 * Real.pi / 4)) * sigmaZ * ry (3 * Real.pi / 4) * sigmaZ *
          ry (-(3 * Real.pi / 4)) * sigmaZ * ry (3 * Real.pi / 4) =
          ry (-(3 * Real.pi / 4)) * (sigmaZ * ry (3 * Real.pi / 4)) * sigmaZ *
            ry (-(3 * Real.pi / 4)) * (sigmaZ * ry (3 * Real.pi / 4)) := by
              noncomm_ring
      _ = ry (-(3 * Real.pi / 4)) *
          (ry (-(3 * Real.pi / 4)) * sigmaZ) * sigmaZ *
          ry (-(3 * Real.pi / 4)) *
          (ry (-(3 * Real.pi / 4)) * sigmaZ) := by rw [hcomm]
      _ = ry (-(3 * Real.pi / 4)) * ry (-(3 * Real.pi / 4)) *
          ry (-(3 * Real.pi / 4)) * ry (-(3 * Real.pi / 4)) * sigmaZ := by
            rw [show ry (-(3 * Real.pi / 4)) *
                (ry (-(3 * Real.pi / 4)) * sigmaZ) * sigmaZ *
                ry (-(3 * Real.pi / 4)) *
                (ry (-(3 * Real.pi / 4)) * sigmaZ) =
                ry (-(3 * Real.pi / 4)) * ry (-(3 * Real.pi / 4)) *
                (sigmaZ * sigmaZ) * ry (-(3 * Real.pi / 4)) *
                ry (-(3 * Real.pi / 4)) * sigmaZ by noncomm_ring]
            rw [sigmaZ_sq]
            noncomm_ring
      _ = ry (-3 * Real.pi) * sigmaZ := by
            repeat rw [ry_mul]
            congr 1
            ring
      _ = sigmaX := ry_neg_three_pi_mul_sigmaZ

/-! ## Exact evaluator equality -/

theorem eval_relativePhaseToffoliACircuit {n : ℕ}
    (first second target : Fin n) (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target) :
    Circuit.eval
        (relativePhaseToffoliACircuit first second target hfirstTarget hsecondTarget) =
      relativeToffoliUnitary first second target hfirstTarget hsecondTarget := by
  apply Subtype.ext
  rw [eval_relativePhaseToffoliACircuit_blocks, coe_relativeToffoliUnitary]
  congr 1
  funext rest
  exact relativePhaseToffoliA_block_cases
    (rest ⟨first, hfirstTarget⟩) (rest ⟨second, hsecondTarget⟩)

theorem eval_relativePhaseToffoliBCircuit {n : ℕ}
    (first second target : Fin n) (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target) :
    Circuit.eval
        (relativePhaseToffoliBCircuit first second target hfirstTarget hsecondTarget) =
      relativeToffoliUnitary first second target hfirstTarget hsecondTarget := by
  apply Subtype.ext
  rw [eval_relativePhaseToffoliBCircuit_blocks, coe_relativeToffoliUnitary]
  congr 1
  funext rest
  exact relativePhaseToffoliB_block_cases
    (rest ⟨first, hfirstTarget⟩) (rest ⟨second, hsecondTarget⟩)

/-- The two source diagrams are exactly equal, not merely basis-phase equivalent. -/
theorem eval_relativePhaseToffoliACircuit_eq_BCircuit {n : ℕ}
    (first second target : Fin n) (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target) :
    Circuit.eval
        (relativePhaseToffoliACircuit first second target hfirstTarget hsecondTarget) =
      Circuit.eval
        (relativePhaseToffoliBCircuit first second target hfirstTarget hsecondTarget) := by
  rw [eval_relativePhaseToffoliACircuit, eval_relativePhaseToffoliBCircuit]
