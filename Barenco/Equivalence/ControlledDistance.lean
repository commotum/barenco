import Barenco.ControlledCircuit.Block
import Barenco.Equivalence.OperatorNorm
import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Exact operator distances for target-controlled blocks

Target-local and target-controlled matrices are reindexed homogeneous block
diagonals.  For the scoped L² induced operator norm, both reindexing and
block-diagonal assembly are isometric.  Consequently the norm of a target-block
matrix is exactly the finite supremum of its one-qubit block norms.

The principal application is the exact identity-distance formula for a
controlled one-qubit matrix.  The enabled predicate carries an explicit witness:
without an active block, the controlled matrix is the full identity and its
distance need not equal the target-matrix distance.

The C-star-algebra instances and homomorphisms below are local proof machinery.
This module adds no circuit syntax and makes no resource claim.
-/

namespace Barenco.ControlledCircuit

open scoped Matrix.Norms.L2Operator

noncomputable section

/-!
Mathlib's L² matrix norm already has the required C-star identity, but the
bundled `CStarAlgebra` instance is intentionally kept local so importing this
leaf cannot alter norm inference in algebraic circuit modules.
-/

noncomputable local instance matrixCStarAlgebra (n : Type*)
    [Fintype n] [DecidableEq n] : CStarAlgebra (Matrix n n ℂ) where
  norm_mul_self_le M := CStarRing.norm_star_mul_self (x := M) |>.symm.le

private noncomputable def blockDiagonalStarAlgHom (m o : Type*)
    [Fintype m] [DecidableEq m] [Fintype o] [DecidableEq o] :
    (o → Matrix m m ℂ) →⋆ₐ[ℂ] Matrix (m × o) (m × o) ℂ :=
  { Matrix.blockDiagonalRingHom m o ℂ with
    commutes' := fun c => by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
      change Matrix.blockDiagonal (c • (1 : o → Matrix m m ℂ)) =
        c • (1 : Matrix (m × o) (m × o) ℂ)
      rw [Matrix.blockDiagonal_smul, Matrix.blockDiagonal_one]
    map_star' := fun M => by
      exact (Matrix.blockDiagonal_conjTranspose M).symm }

private noncomputable def reindexStarAlgEquiv (m n : Type*)
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (e : m ≃ n) : Matrix m m ℂ ≃⋆ₐ[ℂ] Matrix n n ℂ :=
  StarAlgEquiv.ofAlgEquiv (Matrix.reindexAlgEquiv ℂ ℂ e) (by
    intro M
    exact (Matrix.conjTranspose_reindex e e M).symm)

private theorem norm_blockDiagonal (m o : Type*)
    [Fintype m] [DecidableEq m] [Fintype o] [DecidableEq o]
    (F : o → Matrix m m ℂ) :
    ‖Matrix.blockDiagonal F‖ = ‖F‖ := by
  exact NonUnitalStarAlgHom.norm_map (blockDiagonalStarAlgHom m o)
    Matrix.blockDiagonal_injective F

private theorem norm_reindex (m n : Type*)
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (e : m ≃ n) (M : Matrix m m ℂ) :
    ‖Matrix.reindexAlgEquiv ℂ ℂ e M‖ = ‖M‖ := by
  exact StarAlgEquiv.norm_map (reindexStarAlgEquiv m n e) M

/-! ## Exact target-block norms and distances -/

/--
The L² operator norm of a target-block matrix is exactly the finite supremum
norm of its one-qubit block family.
-/
@[simp]
theorem norm_targetBlockRaw {n : ℕ} (target : Fin n)
    (blocks : ComplementBasis target → QubitMatrix) :
    ‖targetBlockRaw target blocks‖ = ‖blocks‖ := by
  rw [targetBlockRaw, norm_reindex, norm_blockDiagonal]

/-- Operator distance between target-block matrices is the block-family norm. -/
theorem operatorDistance_targetBlockRaw {n : ℕ} (target : Fin n)
    (F G : ComplementBasis target → QubitMatrix) :
    operatorDistance (targetBlockRaw target F) (targetBlockRaw target G) =
      ‖F - G‖ := by
  rw [operatorDistance]
  have hsub :
      targetBlockRaw target F - targetBlockRaw target G =
        targetBlockRaw target (F - G) := by
    rw [targetBlockRaw, targetBlockRaw, targetBlockRaw]
    rw [← map_sub, ← Matrix.blockDiagonal_sub]
  rw [hsub, norm_targetBlockRaw]

private theorem norm_ite_eq_of_exists_true {index : Type*} [Fintype index]
    (enabled : index → Bool) (A : QubitMatrix)
    (henabled : ∃ rest, enabled rest = true) :
    ‖fun rest => if enabled rest then A else 0‖ = ‖A‖ := by
  classical
  obtain ⟨witness, hwitness⟩ := henabled
  apply le_antisymm
  · rw [Pi.norm_def]
    change
      (↑(Finset.univ.sup fun rest =>
          ‖if enabled rest then A else 0‖₊) : ℝ) ≤
        (↑‖A‖₊ : ℝ)
    rw [NNReal.coe_le_coe]
    apply Finset.sup_le
    intro rest _
    by_cases hrest : enabled rest = true <;> simp [hrest]
  · rw [Pi.norm_def]
    change
      (↑‖A‖₊ : ℝ) ≤
        (↑(Finset.univ.sup fun rest =>
          ‖if enabled rest then A else 0‖₊) : ℝ)
    rw [NNReal.coe_le_coe]
    calc
      ‖A‖₊ = ‖if enabled witness then A else 0‖₊ := by
        simp [hwitness]
      _ ≤ Finset.univ.sup (fun rest =>
          ‖if enabled rest then A else 0‖₊) :=
        Finset.le_sup
          (f := fun rest => ‖if enabled rest then A else 0‖₊)
          (Finset.mem_univ witness)

/-! ## Controlled identity-distance formulas -/

/--
If at least one complementary assignment enables the control predicate, the
full-register identity-to-controlled distance is exactly the one-qubit
identity-to-target distance.
-/
theorem operatorDistance_one_controlledRaw_eq {n : ℕ} (target : Fin n)
    (enabled : ComplementBasis target → Bool) (U : QubitMatrix)
    (henabled : ∃ rest, enabled rest = true) :
    operatorDistance (1 : Gate n) (controlledRaw target enabled U) =
      operatorDistance (1 : QubitMatrix) U := by
  rw [← targetBlockRaw_one target,
    controlledRaw_eq_targetBlockRaw,
    operatorDistance_targetBlockRaw,
    operatorDistance]
  have hfamily :
      (fun _ : ComplementBasis target => (1 : QubitMatrix)) -
          (fun rest => if enabled rest then U else 1) =
        fun rest => if enabled rest then (1 : QubitMatrix) - U else 0 := by
    funext rest
    by_cases hrest : enabled rest = true <;> simp [hrest]
  rw [hfamily, norm_ite_eq_of_exists_true enabled ((1 : QubitMatrix) - U)
    henabled]

/-- The same exact formula with the two distance arguments reversed. -/
theorem operatorDistance_controlledRaw_one_eq {n : ℕ} (target : Fin n)
    (enabled : ComplementBasis target → Bool) (U : QubitMatrix)
    (henabled : ∃ rest, enabled rest = true) :
    operatorDistance (controlledRaw target enabled U) (1 : Gate n) =
      operatorDistance U (1 : QubitMatrix) := by
  rw [operatorDistance_comm, operatorDistance_comm U]
  exact operatorDistance_one_controlledRaw_eq target enabled U henabled

private theorem exists_positiveControlsEnabled_true {n : ℕ}
    {target : Fin n} (controls : ControlSet target) :
    ∃ rest, positiveControlsEnabled controls rest = true := by
  let rest : ComplementBasis target := fun _ => true
  refine ⟨rest, (positiveControlsEnabled_eq_true_iff controls rest).2 ?_⟩
  intro control _
  rfl

/-- Positive controls always have an all-true active complementary block. -/
theorem operatorDistance_one_positiveControlledRaw_eq {n : ℕ}
    (target : Fin n) (controls : ControlSet target) (U : QubitMatrix) :
    operatorDistance (1 : Gate n)
        (positiveControlledRaw target controls U) =
      operatorDistance (1 : QubitMatrix) U := by
  exact operatorDistance_one_controlledRaw_eq target
    (positiveControlsEnabled controls) U
    (exists_positiveControlsEnabled_true controls)

/-- Reversed positive-control identity-distance formula. -/
theorem operatorDistance_positiveControlledRaw_one_eq {n : ℕ}
    (target : Fin n) (controls : ControlSet target) (U : QubitMatrix) :
    operatorDistance (positiveControlledRaw target controls U)
        (1 : Gate n) =
      operatorDistance U (1 : QubitMatrix) := by
  exact operatorDistance_controlledRaw_one_eq target
    (positiveControlsEnabled controls) U
    (exists_positiveControlsEnabled_true controls)

/-- Certified-unitary specialization of the positive-control formula. -/
theorem operatorDistance_one_positiveControlledUnitary_eq {n : ℕ}
    (target : Fin n) (controls : ControlSet target) (U : QubitUnitary) :
    operatorDistance (1 : Gate n)
        (positiveControlledUnitary target controls U : Gate n) =
      operatorDistance (1 : QubitMatrix) (U : QubitMatrix) := by
  rw [coe_positiveControlledUnitary]
  exact operatorDistance_one_positiveControlledRaw_eq target controls U

/-- Reversed certified-unitary positive-control formula. -/
theorem operatorDistance_positiveControlledUnitary_one_eq {n : ℕ}
    (target : Fin n) (controls : ControlSet target) (U : QubitUnitary) :
    operatorDistance
        (positiveControlledUnitary target controls U : Gate n)
        (1 : Gate n) =
      operatorDistance (U : QubitMatrix) (1 : QubitMatrix) := by
  rw [coe_positiveControlledUnitary]
  exact operatorDistance_positiveControlledRaw_one_eq target controls U

end

end Barenco.ControlledCircuit
