import Barenco.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Certified matrix semantics

This module supplies small, reusable constructors for semantic quantum gates.  It
uses mathlib's standard column-vector convention: for a matrix `U`, the action on
the computational basis ket `|j⟩` is the `j`th column of `U`.

Two index conventions are worth making explicit.

* `Matrix.reindex e e U` is indexed by the *target* of `e`; its entry at `(i, j)`
  is the old entry at `(e.symm i, e.symm j)`.
* `Matrix.blockDiagonal blocks` is indexed by `(localIndex, blockIndex)`, in that
  order.  Distinct block indices give a zero entry.

The constructors below return elements of `Matrix.unitaryGroup`, so later circuit
code cannot use reindexing, block-diagonal assembly, or tensor products without
also carrying their unitarity certificates.
-/

namespace Barenco

open Matrix
open scoped Kronecker

section BasisKets

variable {ι ρ : Type*}

/-- The standard basis vector `|i⟩`, represented as an amplitude function. -/
def basisKet [DecidableEq ι] (i : ι) : ι → ℂ :=
  Pi.single i 1

@[simp]
theorem basisKet_apply [DecidableEq ι] (i j : ι) :
    basisKet i j = if j = i then 1 else 0 := by
  simp [basisKet, Pi.single_apply]

@[simp]
theorem basisKet_apply_self [DecidableEq ι] (i : ι) : basisKet i i = 1 := by
  simp

@[simp]
theorem basisKet_apply_of_ne [DecidableEq ι] {i j : ι} (h : i ≠ j) :
    basisKet i j = 0 := by
  rw [basisKet_apply, if_neg h.symm]

/-- Left multiplication by a matrix sends `|j⟩` to the `j`th column. -/
@[simp]
theorem mulVec_basisKet [Fintype ι] [DecidableEq ι]
    (U : Matrix ρ ι ℂ) (j : ι) :
    U *ᵥ basisKet j = U.col j := by
  unfold basisKet
  exact Matrix.mulVec_single_one U j

/-- Entrywise form of `mulVec_basisKet`. -/
@[simp]
theorem mulVec_basisKet_apply [Fintype ι] [DecidableEq ι]
    (U : Matrix ρ ι ℂ) (i : ρ) (j : ι) :
    (U *ᵥ basisKet j) i = U i j := by
  simp

/-- Two matrices are equal exactly when they agree on every standard basis ket. -/
theorem matrix_eq_iff_mulVec_basisKet_eq [Fintype ι] [DecidableEq ι]
    (U V : Matrix ρ ι ℂ) :
    U = V ↔ ∀ j, U *ᵥ basisKet j = V *ᵥ basisKet j := by
  constructor
  · rintro rfl
    exact fun _ ↦ rfl
  · intro h
    ext i j
    simpa using congrFun (h j) i

end BasisKets

section Reindex

variable {ι κ : Type*}
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/--
Simultaneously reindexing the rows and columns of a square complex matrix
preserves and reflects unitarity.
-/
theorem reindex_mem_unitaryGroup_iff (e : ι ≃ κ) (U : Matrix ι ι ℂ) :
    Matrix.reindex e e U ∈ Matrix.unitaryGroup κ ℂ ↔
      U ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.mem_unitaryGroup_iff']
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_reindex]
  let r := Matrix.reindexAlgEquiv ℂ ℂ e
  change r Uᴴ * r U = 1 ↔ Uᴴ * U = 1
  constructor
  · intro h
    apply r.injective
    simpa only [map_mul, map_one] using h
  · intro h
    simpa only [map_mul, map_one] using congrArg r h

/-- A certified unitary obtained by transporting both matrix indices along `e`. -/
def reindexUnitary (e : ι ≃ κ) (U : Matrix.unitaryGroup ι ℂ) :
    Matrix.unitaryGroup κ ℂ :=
  ⟨Matrix.reindex e e (U : Matrix ι ι ℂ),
    (reindex_mem_unitaryGroup_iff e U).2 U.property⟩

@[simp]
theorem coe_reindexUnitary (e : ι ≃ κ) (U : Matrix.unitaryGroup ι ℂ) :
    (reindexUnitary e U : Matrix κ κ ℂ) = Matrix.reindex e e (U : Matrix ι ι ℂ) :=
  rfl

/--
Orientation of certified reindexing: a target entry is read at the inverse images
of its row and column indices.
-/
@[simp]
theorem reindexUnitary_apply (e : ι ≃ κ) (U : Matrix.unitaryGroup ι ℂ) (i j : κ) :
    reindexUnitary e U i j = U (e.symm i) (e.symm j) :=
  rfl

@[simp]
theorem reindexUnitary_one (e : ι ≃ κ) :
    reindexUnitary e (1 : Matrix.unitaryGroup ι ℂ) = 1 := by
  apply Subtype.ext
  change Matrix.reindex e e (1 : Matrix ι ι ℂ) = (1 : Matrix κ κ ℂ)
  exact (Matrix.reindexAlgEquiv ℂ ℂ e).map_one

@[simp]
theorem reindexUnitary_mul (e : ι ≃ κ)
    (U V : Matrix.unitaryGroup ι ℂ) :
    reindexUnitary e (U * V) = reindexUnitary e U * reindexUnitary e V := by
  apply Subtype.ext
  change Matrix.reindex e e ((U : Matrix ι ι ℂ) * (V : Matrix ι ι ℂ)) =
    Matrix.reindex e e (U : Matrix ι ι ℂ) * Matrix.reindex e e (V : Matrix ι ι ℂ)
  exact (Matrix.reindexAlgEquiv ℂ ℂ e).map_mul
    (U : Matrix ι ι ℂ) (V : Matrix ι ι ℂ)

@[simp]
theorem reindexUnitary_symm_reindexUnitary (e : ι ≃ κ)
    (U : Matrix.unitaryGroup ι ℂ) :
    reindexUnitary e.symm (reindexUnitary e U) = U := by
  apply Subtype.ext
  ext i j
  simp

/-- Reindexing gives a multiplicative equivalence of unitary groups. -/
def reindexUnitaryEquiv (e : ι ≃ κ) :
    Matrix.unitaryGroup ι ℂ ≃* Matrix.unitaryGroup κ ℂ where
  toFun := reindexUnitary e
  invFun := reindexUnitary e.symm
  left_inv := reindexUnitary_symm_reindexUnitary e
  right_inv := reindexUnitary_symm_reindexUnitary e.symm
  map_mul' := reindexUnitary_mul e

@[simp]
theorem reindexUnitaryEquiv_apply (e : ι ≃ κ) (U : Matrix.unitaryGroup ι ℂ) :
    reindexUnitaryEquiv e U = reindexUnitary e U :=
  rfl

end Reindex

section BlockDiagonal

variable {ι κ : Type*}
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/--
A homogeneous block-diagonal complex matrix is unitary exactly when every block
is unitary.
-/
theorem blockDiagonal_mem_unitaryGroup_iff (U : κ → Matrix ι ι ℂ) :
    Matrix.blockDiagonal U ∈ Matrix.unitaryGroup (ι × κ) ℂ ↔
      ∀ k, U k ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul,
    ← Matrix.blockDiagonal_one, Matrix.blockDiagonal_inj]
  constructor
  · intro h k
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    exact congrFun h k
  · intro h
    funext k
    change (U k)ᴴ * U k = (1 : Matrix ι ι ℂ)
    have hk : star (U k) * U k = (1 : Matrix ι ι ℂ) :=
      (Matrix.mem_unitaryGroup_iff').1 (h k)
    simpa only [Matrix.star_eq_conjTranspose] using hk

/-- Pointwise unitarity is sufficient for block-diagonal unitarity. -/
theorem blockDiagonal_mem_unitaryGroup (U : κ → Matrix ι ι ℂ)
    (hU : ∀ k, U k ∈ Matrix.unitaryGroup ι ℂ) :
    Matrix.blockDiagonal U ∈ Matrix.unitaryGroup (ι × κ) ℂ :=
  (blockDiagonal_mem_unitaryGroup_iff U).2 hU

/-- Assemble a family of certified unitaries into a certified block diagonal. -/
def blockDiagonalUnitary (U : κ → Matrix.unitaryGroup ι ℂ) :
    Matrix.unitaryGroup (ι × κ) ℂ :=
  ⟨Matrix.blockDiagonal fun k ↦ (U k : Matrix ι ι ℂ),
    blockDiagonal_mem_unitaryGroup _ fun k ↦ (U k).property⟩

@[simp]
theorem coe_blockDiagonalUnitary (U : κ → Matrix.unitaryGroup ι ℂ) :
    (blockDiagonalUnitary U : Matrix (ι × κ) (ι × κ) ℂ) =
      Matrix.blockDiagonal fun k ↦ (U k : Matrix ι ι ℂ) :=
  rfl

/--
Entry orientation for the certified block diagonal: local indices come first and
the block selector comes second.
-/
@[simp]
theorem blockDiagonalUnitary_apply (U : κ → Matrix.unitaryGroup ι ℂ)
    (ik jk : ι × κ) :
    blockDiagonalUnitary U ik jk =
      if ik.2 = jk.2 then U ik.2 ik.1 jk.1 else 0 :=
  rfl

end BlockDiagonal

section Kronecker

variable {ι κ : Type*}
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The Kronecker product of two certified complex unitaries. -/
def kroneckerUnitary (U : Matrix.unitaryGroup ι ℂ)
    (V : Matrix.unitaryGroup κ ℂ) : Matrix.unitaryGroup (ι × κ) ℂ :=
  ⟨(U : Matrix ι ι ℂ) ⊗ₖ (V : Matrix κ κ ℂ),
    Matrix.kronecker_mem_unitary U.property V.property⟩

@[simp]
theorem coe_kroneckerUnitary (U : Matrix.unitaryGroup ι ℂ)
    (V : Matrix.unitaryGroup κ ℂ) :
    (kroneckerUnitary U V : Matrix (ι × κ) (ι × κ) ℂ) =
      (U : Matrix ι ι ℂ) ⊗ₖ (V : Matrix κ κ ℂ) :=
  rfl

@[simp]
theorem kroneckerUnitary_apply (U : Matrix.unitaryGroup ι ℂ)
    (V : Matrix.unitaryGroup κ ℂ) (i j : ι × κ) :
    kroneckerUnitary U V i j = U i.1 j.1 * V i.2 j.2 :=
  rfl

end Kronecker

end Barenco
