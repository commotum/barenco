import Barenco.ThreeQubit.Lemma61
import Barenco.ControlledCircuit.ControlledZ
import Barenco.Equivalence.Phase
import Barenco.OneQubit.Pauli

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

/-- The source's displayed identity `W = Ph(pi/2) * sigma_y` in row convention. -/
theorem paperW_eq_paperPhase_mul_paperY :
    paperW = paperPhase (Real.pi / 2) * paperY := by
  have hcis : cis (Real.pi / 2) = Complex.I := by
    simpa only [cis, Complex.ofReal_div, Complex.ofReal_ofNat] using
      Complex.exp_pi_div_two_mul_I
  rw [paperW, paperPhase, paperY, matrix2_mul, hcis]
  norm_num

/-- Standard-column translation of the paper's displayed `W`. -/
def wMatrix : QubitMatrix := fromPaper paperW

/--
Transposing the source identity reverses its product: semantic Pauli-Y is
followed algebraically by the scalar phase.
-/
theorem wMatrix_eq_sigmaY_mul_phaseShift :
    wMatrix = sigmaY * phaseShift (Real.pi / 2) := by
  calc
    wMatrix = fromPaper (paperPhase (Real.pi / 2) * paperY) := by
      rw [wMatrix, paperW_eq_paperPhase_mul_paperY]
    _ = sigmaY * phaseShift (Real.pi / 2) := by
      rw [fromPaper_mul]
      rfl

/-- Scalarity restores the paper's displayed factor order in column convention. -/
theorem wMatrix_eq_phaseShift_mul_sigmaY :
    wMatrix = phaseShift (Real.pi / 2) * sigmaY := by
  rw [wMatrix_eq_sigmaY_mul_phaseShift,
    ← phaseShift_mul_comm (Real.pi / 2) sigmaY]

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

/-- Certified semantic form of the source identity `W = Ph(pi/2) * sigma_y`. -/
theorem wUnitary_eq_phaseShift_mul_sigmaY :
    wUnitary = phaseShiftUnitary (Real.pi / 2) * sigmaYUnitary := by
  apply Subtype.ext
  simpa using wMatrix_eq_phaseShift_mul_sigmaY

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
            congr 2
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

/-! ## Exact adjacent-pair cancellation -/

/-- The canonical `I/I/Z/X` signed permutation is an involution. -/
@[simp]
theorem relativeToffoliUnitary_sq {n : ℕ}
    (first second target : Fin n) (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target) :
    relativeToffoliUnitary first second target hfirstTarget hsecondTarget ^ 2 = 1 := by
  rw [pow_two]
  apply Subtype.ext
  simp only [Submonoid.coe_mul, coe_relativeToffoliUnitary, Submonoid.coe_one]
  rw [targetBlockRaw_mul]
  rw [← targetBlockRaw_one target]
  congr 1
  funext rest
  cases hfirstBit : rest ⟨first, hfirstTarget⟩ <;>
    cases hsecondBit : rest ⟨second, hsecondTarget⟩ <;>
    simp [sigmaX_sq, sigmaZ_sq]

/-- Two immediately adjacent copies of the first diagram evaluate to identity. -/
@[simp]
theorem eval_append_relativePhaseToffoliACircuit_self {n : ℕ}
    (first second target : Fin n) (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target) :
    Circuit.eval (Circuit.append
      (relativePhaseToffoliACircuit first second target hfirstTarget hsecondTarget)
      (relativePhaseToffoliACircuit first second target hfirstTarget hsecondTarget)) = 1 := by
  rw [Circuit.eval_append, eval_relativePhaseToffoliACircuit,
    ← pow_two, relativeToffoliUnitary_sq]

/-- Two immediately adjacent copies of the second diagram evaluate to identity. -/
@[simp]
theorem eval_append_relativePhaseToffoliBCircuit_self {n : ℕ}
    (first second target : Fin n) (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target) :
    Circuit.eval (Circuit.append
      (relativePhaseToffoliBCircuit first second target hfirstTarget hsecondTarget)
      (relativePhaseToffoliBCircuit first second target hfirstTarget hsecondTarget)) = 1 := by
  rw [Circuit.eval_append, eval_relativePhaseToffoliBCircuit,
    ← pow_two, relativeToffoliUnitary_sq]

/-! ## Two-control block bridge and exact phase witnesses -/

/-- Nested target block selected by both named controls. -/
def twoControlBlock {n : ℕ} (first second target : Fin n)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target)
    (U : QubitMatrix) (rest : ComplementBasis target) : QubitMatrix :=
  if rest ⟨first, hfirstTarget⟩ then
    if rest ⟨second, hsecondTarget⟩ then U else 1
  else 1

/-- The existing unordered `twoControlSet` has the expected nested target blocks. -/
theorem positiveControlledRaw_twoControlSet_eq_targetBlockRaw {n : ℕ}
    (first second target : Fin n) (_hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target)
    (U : QubitMatrix) :
    positiveControlledRaw target
        (twoControlSet first second target hfirstTarget hsecondTarget) U =
      targetBlockRaw target
        (twoControlBlock first second target hfirstTarget hsecondTarget U) := by
  rw [twoControlSet, positiveControlledRaw, controlledRaw_eq_targetBlockRaw]
  congr 1
  funext rest
  cases hfirstBit : rest ⟨first, hfirstTarget⟩ <;>
    cases hsecondBit : rest ⟨second, hsecondTarget⟩ <;>
    simp [twoControlBlock, positiveControlsEnabled, hfirstBit, hsecondBit]

/-- Exact doubly controlled Pauli-X (Toffoli) on three named wires. -/
def toffoliUnitary {n : ℕ} (first second target : Fin n)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    UnitaryGate n :=
  positiveControlledUnitary target
    (twoControlSet first second target hfirstTarget hsecondTarget) sigmaXUnitary

/-- Exact doubly controlled standard-column translation of the paper's `W`. -/
def controlledWUnitary {n : ℕ} (first second target : Fin n)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    UnitaryGate n :=
  positiveControlledUnitary target
    (twoControlSet first second target hfirstTarget hsecondTarget) wUnitary

/-- Input-column sign of the two displayed relative-phase diagrams. -/
def relativeToffoliPhase {n : ℕ} (first second target : Fin n)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target)
    (rest : ComplementBasis target) (input : Bool) : Circle :=
  if rest ⟨first, hfirstTarget⟩ = true ∧
      rest ⟨second, hsecondTarget⟩ = false ∧ input = true then
    (-1 : Circle)
  else 1

/-- The relative-phase witness is negative exactly on input bits `101`. -/
@[simp]
theorem relativeToffoliPhase_input {n : ℕ}
    (first second target : Fin n) (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target) (input : Basis n) :
    relativeToffoliPhase first second target hfirstTarget hsecondTarget
        (splitTarget target input).2 (input target) =
      if input first = true ∧ input second = false ∧ input target = true then
        (-1 : Circle)
      else 1 := by
  simp [relativeToffoliPhase]

/-- Input-column sign of doubly controlled paper `W`. -/
def controlledWPhase {n : ℕ} (first second target : Fin n)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target)
    (rest : ComplementBasis target) (input : Bool) : Circle :=
  if rest ⟨first, hfirstTarget⟩ = true ∧
      rest ⟨second, hsecondTarget⟩ = true ∧ input = true then
    (-1 : Circle)
  else 1

/-- The controlled-`W` witness is negative exactly on input bits `111`. -/
@[simp]
theorem controlledWPhase_input {n : ℕ}
    (first second target : Fin n) (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target) (input : Basis n) :
    controlledWPhase first second target hfirstTarget hsecondTarget
        (splitTarget target input).2 (input target) =
      if input first = true ∧ input second = true ∧ input target = true then
        (-1 : Circle)
      else 1 := by
  simp [controlledWPhase]

/-- Entrywise block sign of the canonical relative-phase unitary versus Toffoli. -/
theorem relativeToffoliBlock_phase {n : ℕ}
    (first second target : Fin n) (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target) (rest : ComplementBasis target)
    (row input : Bool) :
    (if rest ⟨first, hfirstTarget⟩ then
        if rest ⟨second, hsecondTarget⟩ then sigmaX else sigmaZ
      else 1) row input =
      (relativeToffoliPhase first second target hfirstTarget hsecondTarget
        rest input : ℂ) *
        twoControlBlock first second target hfirstTarget hsecondTarget sigmaX
          rest row input := by
  cases hfirstBit : rest ⟨first, hfirstTarget⟩ <;>
    cases hsecondBit : rest ⟨second, hsecondTarget⟩ <;>
    cases row <;> cases input <;>
    norm_num [relativeToffoliPhase, twoControlBlock, sigmaZ_eq_matrix2,
      sigmaX_eq_paperX, paperX, hfirstBit, hsecondBit]

/-- Entrywise block sign of controlled paper `W` versus Toffoli. -/
theorem controlledWBlock_phase {n : ℕ}
    (first second target : Fin n) (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target) (rest : ComplementBasis target)
    (row input : Bool) :
    twoControlBlock first second target hfirstTarget hsecondTarget wMatrix
        rest row input =
      (controlledWPhase first second target hfirstTarget hsecondTarget rest input :
        ℂ) *
        twoControlBlock first second target hfirstTarget hsecondTarget sigmaX
          rest row input := by
  cases hfirstBit : rest ⟨first, hfirstTarget⟩ <;>
    cases hsecondBit : rest ⟨second, hsecondTarget⟩ <;>
    cases row <;> cases input <;>
    norm_num [twoControlBlock, wMatrix, paperW, controlledWPhase, fromPaper,
      sigmaX_eq_paperX, paperX, hfirstBit, hsecondBit]

/-! ## Lifting block signs to full-register columns -/

/-- Pointwise target-block column phases lift to arbitrary-width basis-phase equality. -/
theorem targetBlockRaw_basisPhaseEq {n : ℕ} (target : Fin n)
    (F G : ComplementBasis target → QubitMatrix)
    (phase : ComplementBasis target → Bool → Circle)
    (hphase : ∀ rest row input,
      G rest row input = (phase rest input : ℂ) * F rest row input) :
    BasisPhaseEq (targetBlockRaw target F) (targetBlockRaw target G) := by
  refine ⟨fun input ↦ phase (splitTarget target input).2 (input target), ?_⟩
  intro row input
  rw [targetBlockRaw_apply, targetBlockRaw_apply]
  by_cases hrest : (splitTarget target row).2 = (splitTarget target input).2
  · rw [if_pos hrest, if_pos hrest, hphase, hrest]
  · rw [if_neg hrest, if_neg hrest, mul_zero]

/-- Pointwise block phases also give the corresponding exact basis-column action. -/
theorem targetBlockRaw_mulVec_basisKet_phase {n : ℕ} (target : Fin n)
    (F G : ComplementBasis target → QubitMatrix)
    (phase : ComplementBasis target → Bool → Circle)
    (hphase : ∀ rest row input,
      G rest row input = (phase rest input : ℂ) * F rest row input)
    (input : Basis n) :
    targetBlockRaw target G *ᵥ basisKet input =
      (phase (splitTarget target input).2 (input target) : ℂ) •
        (targetBlockRaw target F *ᵥ basisKet input) := by
  ext row
  simp only [mulVec_basisKet_apply, Pi.smul_apply, smul_eq_mul]
  rw [targetBlockRaw_apply, targetBlockRaw_apply]
  by_cases hrest : (splitTarget target row).2 = (splitTarget target input).2
  · rw [if_pos hrest, if_pos hrest, hphase, hrest]
  · rw [if_neg hrest, if_neg hrest, mul_zero]

/-- Classical basis assignment produced by exact Toffoli on the three named wires. -/
def toffoliOutput {n : ℕ} (first second target : Fin n)
    (input : Basis n) : Basis n :=
  if input first = true ∧ input second = true then
    setTarget target input (!input target)
  else input

/-- Exact arbitrary-width Toffoli basis action. -/
theorem toffoliUnitary_mulVec_basisKet {n : ℕ}
    (first second target : Fin n) (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target) (input : Basis n) :
    (toffoliUnitary first second target hfirstTarget hsecondTarget : Gate n) *ᵥ
        basisKet input =
      basisKet (toffoliOutput first second target input) := by
  rw [toffoliUnitary, coe_positiveControlledUnitary,
    positiveControlledRaw_truthTable]
  by_cases hactive : input first = true ∧ input second = true
  · rw [if_pos]
    · simpa [toffoliOutput, hactive, xRaw, sigmaX_eq_coe_pauliX] using
        xRaw_mulVec_basisKet target input
    · intro i hi
      rw [twoControlSet] at hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact hactive.1
      · exact hactive.2
  · rw [if_neg]
    · simp [toffoliOutput, hactive]
    · intro hall
      apply hactive
      constructor
      · exact hall ⟨first, hfirstTarget⟩ (by simp [twoControlSet])
      · exact hall ⟨second, hsecondTarget⟩ (by simp [twoControlSet])

/-! ## Basis-phase relations with exact witnesses -/

/-- The canonical relative-phase unitary differs from Toffoli by its `101` sign. -/
theorem relativeToffoliUnitary_basisPhaseEq_toffoli {n : ℕ}
    (first second target : Fin n) (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    BasisPhaseEq (toffoliUnitary first second target hfirstTarget hsecondTarget : Gate n)
      (relativeToffoliUnitary first second target hfirstTarget hsecondTarget : Gate n) := by
  simp only [toffoliUnitary, coe_positiveControlledUnitary, coe_sigmaXUnitary]
  rw [positiveControlledRaw_twoControlSet_eq_targetBlockRaw first second target
      hfirstSecond hfirstTarget hsecondTarget sigmaX,
    coe_relativeToffoliUnitary]
  exact targetBlockRaw_basisPhaseEq target
    (twoControlBlock first second target hfirstTarget hsecondTarget sigmaX)
    (fun rest ↦ if rest ⟨first, hfirstTarget⟩ then
      if rest ⟨second, hsecondTarget⟩ then sigmaX else sigmaZ else 1)
    (relativeToffoliPhase first second target hfirstTarget hsecondTarget)
    (relativeToffoliBlock_phase first second target hfirstTarget hsecondTarget)

/-- Doubly controlled paper `W` differs from Toffoli by its `111` sign. -/
theorem controlledWUnitary_basisPhaseEq_toffoli {n : ℕ}
    (first second target : Fin n) (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    BasisPhaseEq (toffoliUnitary first second target hfirstTarget hsecondTarget : Gate n)
      (controlledWUnitary first second target hfirstTarget hsecondTarget : Gate n) := by
  simp only [toffoliUnitary, controlledWUnitary, coe_positiveControlledUnitary,
    coe_sigmaXUnitary, coe_wUnitary]
  rw [positiveControlledRaw_twoControlSet_eq_targetBlockRaw first second target
      hfirstSecond hfirstTarget hsecondTarget sigmaX,
    positiveControlledRaw_twoControlSet_eq_targetBlockRaw first second target
      hfirstSecond hfirstTarget hsecondTarget wMatrix]
  exact targetBlockRaw_basisPhaseEq target
    (twoControlBlock first second target hfirstTarget hsecondTarget sigmaX)
    (twoControlBlock first second target hfirstTarget hsecondTarget wMatrix)
    (controlledWPhase first second target hfirstTarget hsecondTarget)
    (controlledWBlock_phase first second target hfirstTarget hsecondTarget)

/-! ## Exact signed-permutation basis actions -/

/-- Canonical exact signed action: Toffoli output with the `101` input sign. -/
theorem relativeToffoliUnitary_mulVec_basisKet {n : ℕ}
    (first second target : Fin n) (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target)
    (input : Basis n) :
    (relativeToffoliUnitary first second target hfirstTarget hsecondTarget : Gate n) *ᵥ
        basisKet input =
      (relativeToffoliPhase first second target hfirstTarget hsecondTarget
        (splitTarget target input).2 (input target) : ℂ) •
        basisKet (toffoliOutput first second target input) := by
  rw [coe_relativeToffoliUnitary]
  have hphase := targetBlockRaw_mulVec_basisKet_phase target
    (twoControlBlock first second target hfirstTarget hsecondTarget sigmaX)
    (fun rest ↦ if rest ⟨first, hfirstTarget⟩ then
      if rest ⟨second, hsecondTarget⟩ then sigmaX else sigmaZ else 1)
    (relativeToffoliPhase first second target hfirstTarget hsecondTarget)
    (relativeToffoliBlock_phase first second target hfirstTarget hsecondTarget) input
  rw [hphase]
  congr 1
  rw [← positiveControlledRaw_twoControlSet_eq_targetBlockRaw first second target
      hfirstSecond hfirstTarget hsecondTarget sigmaX]
  simpa [toffoliUnitary, coe_sigmaXUnitary] using
    toffoliUnitary_mulVec_basisKet first second target hfirstTarget hsecondTarget input

/-- Exact signed action of doubly controlled paper `W`, whose sign is on `111`. -/
theorem controlledWUnitary_mulVec_basisKet {n : ℕ}
    (first second target : Fin n) (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target)
    (input : Basis n) :
    (controlledWUnitary first second target hfirstTarget hsecondTarget : Gate n) *ᵥ
        basisKet input =
      (controlledWPhase first second target hfirstTarget hsecondTarget
        (splitTarget target input).2 (input target) : ℂ) •
        basisKet (toffoliOutput first second target input) := by
  simp only [controlledWUnitary, coe_positiveControlledUnitary, coe_wUnitary]
  rw [positiveControlledRaw_twoControlSet_eq_targetBlockRaw first second target
      hfirstSecond hfirstTarget hsecondTarget wMatrix]
  have hphase := targetBlockRaw_mulVec_basisKet_phase target
    (twoControlBlock first second target hfirstTarget hsecondTarget sigmaX)
    (twoControlBlock first second target hfirstTarget hsecondTarget wMatrix)
    (controlledWPhase first second target hfirstTarget hsecondTarget)
    (controlledWBlock_phase first second target hfirstTarget hsecondTarget) input
  rw [hphase]
  congr 1
  rw [← positiveControlledRaw_twoControlSet_eq_targetBlockRaw first second target
      hfirstSecond hfirstTarget hsecondTarget sigmaX]
  simpa [toffoliUnitary, coe_sigmaXUnitary] using
    toffoliUnitary_mulVec_basisKet first second target hfirstTarget hsecondTarget input

/-- Exact signed action of the first seven-node circuit. -/
theorem relativePhaseToffoliACircuit_mulVec_basisKet {n : ℕ}
    (first second target : Fin n) (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target)
    (input : Basis n) :
    (Circuit.eval
        (relativePhaseToffoliACircuit first second target hfirstTarget hsecondTarget) :
      Gate n) *ᵥ basisKet input =
      (relativeToffoliPhase first second target hfirstTarget hsecondTarget
        (splitTarget target input).2 (input target) : ℂ) •
        basisKet (toffoliOutput first second target input) := by
  rw [eval_relativePhaseToffoliACircuit]
  exact relativeToffoliUnitary_mulVec_basisKet first second target hfirstSecond
    hfirstTarget hsecondTarget input

/-- Exact signed action of the controlled-Z seven-node circuit. -/
theorem relativePhaseToffoliBCircuit_mulVec_basisKet {n : ℕ}
    (first second target : Fin n) (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target)
    (input : Basis n) :
    (Circuit.eval
        (relativePhaseToffoliBCircuit first second target hfirstTarget hsecondTarget) :
      Gate n) *ᵥ basisKet input =
      (relativeToffoliPhase first second target hfirstTarget hsecondTarget
        (splitTarget target input).2 (input target) : ℂ) •
        basisKet (toffoliOutput first second target input) := by
  rw [eval_relativePhaseToffoliBCircuit]
  exact relativeToffoliUnitary_mulVec_basisKet first second target hfirstSecond
    hfirstTarget hsecondTarget input

/-! ## Derived phase, reversible-basis, and basis-measurement relations -/

theorem relativePhaseToffoliACircuit_basisPhaseEq_toffoli {n : ℕ}
    (first second target : Fin n) (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    BasisPhaseEq (toffoliUnitary first second target hfirstTarget hsecondTarget : Gate n)
      (Circuit.eval
        (relativePhaseToffoliACircuit first second target hfirstTarget hsecondTarget) :
          Gate n) := by
  rw [eval_relativePhaseToffoliACircuit]
  exact relativeToffoliUnitary_basisPhaseEq_toffoli first second target
    hfirstSecond hfirstTarget hsecondTarget

theorem relativePhaseToffoliBCircuit_basisPhaseEq_toffoli {n : ℕ}
    (first second target : Fin n) (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    BasisPhaseEq (toffoliUnitary first second target hfirstTarget hsecondTarget : Gate n)
      (Circuit.eval
        (relativePhaseToffoliBCircuit first second target hfirstTarget hsecondTarget) :
          Gate n) := by
  rw [eval_relativePhaseToffoliBCircuit]
  exact relativeToffoliUnitary_basisPhaseEq_toffoli first second target
    hfirstSecond hfirstTarget hsecondTarget

theorem relativePhaseToffoliACircuit_sameBasisBehavior {n : ℕ}
    (first second target : Fin n) (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    SameBasisBehavior
      (toffoliUnitary first second target hfirstTarget hsecondTarget : Gate n)
      (Circuit.eval
        (relativePhaseToffoliACircuit first second target hfirstTarget hsecondTarget) :
          Gate n) :=
  BasisPhaseEq.toSameBasisBehavior
    (relativePhaseToffoliACircuit_basisPhaseEq_toffoli first second target
      hfirstSecond hfirstTarget hsecondTarget)

theorem relativePhaseToffoliACircuit_basisMeasurementEq {n : ℕ}
    (first second target : Fin n) (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    BasisMeasurementEq
      (toffoliUnitary first second target hfirstTarget hsecondTarget : Gate n)
      (Circuit.eval
        (relativePhaseToffoliACircuit first second target hfirstTarget hsecondTarget) :
          Gate n) :=
  BasisPhaseEq.toBasisMeasurementEq
    (relativePhaseToffoliACircuit_basisPhaseEq_toffoli first second target
      hfirstSecond hfirstTarget hsecondTarget)

theorem relativePhaseToffoliBCircuit_sameBasisBehavior {n : ℕ}
    (first second target : Fin n) (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    SameBasisBehavior
      (toffoliUnitary first second target hfirstTarget hsecondTarget : Gate n)
      (Circuit.eval
        (relativePhaseToffoliBCircuit first second target hfirstTarget hsecondTarget) :
          Gate n) :=
  BasisPhaseEq.toSameBasisBehavior
    (relativePhaseToffoliBCircuit_basisPhaseEq_toffoli first second target
      hfirstSecond hfirstTarget hsecondTarget)

theorem relativePhaseToffoliBCircuit_basisMeasurementEq {n : ℕ}
    (first second target : Fin n) (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    BasisMeasurementEq
      (toffoliUnitary first second target hfirstTarget hsecondTarget : Gate n)
      (Circuit.eval
        (relativePhaseToffoliBCircuit first second target hfirstTarget hsecondTarget) :
          Gate n) :=
  BasisPhaseEq.toBasisMeasurementEq
    (relativePhaseToffoliBCircuit_basisPhaseEq_toffoli first second target
      hfirstSecond hfirstTarget hsecondTarget)

theorem controlledWUnitary_sameBasisBehavior {n : ℕ}
    (first second target : Fin n) (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    SameBasisBehavior
      (toffoliUnitary first second target hfirstTarget hsecondTarget : Gate n)
      (controlledWUnitary first second target hfirstTarget hsecondTarget : Gate n) :=
  BasisPhaseEq.toSameBasisBehavior
    (controlledWUnitary_basisPhaseEq_toffoli first second target
      hfirstSecond hfirstTarget hsecondTarget)

theorem controlledWUnitary_basisMeasurementEq {n : ℕ}
    (first second target : Fin n) (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target) (hsecondTarget : second ≠ target) :
    BasisMeasurementEq
      (toffoliUnitary first second target hfirstTarget hsecondTarget : Gate n)
      (controlledWUnitary first second target hfirstTarget hsecondTarget : Gate n) :=
  BasisPhaseEq.toBasisMeasurementEq
    (controlledWUnitary_basisPhaseEq_toffoli first second target
      hfirstSecond hfirstTarget hsecondTarget)

end

end Barenco.ThreeQubit
