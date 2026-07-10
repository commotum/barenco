import Barenco.Universality.TwoLevel
import Mathlib.Algebra.BigOperators.Fin

/-!
# Algebraic data for finite two-level elimination

This module contains the low-dependency data carried by the constructive
elimination theorem.  A factor records its two ordered indices and certified
`U(2)` block.  `factorProduct` uses ordinary left-associated mathematical
product order: the head is the leftmost factor, so the rightmost factor acts
first on column vectors.

The successor-dimension lemmas embed factors from `Fin n` into the first `n`
indices of `Fin (n+1)` and prove all four blocks of their product explicitly.
-/

namespace Barenco.Universality

open Matrix

noncomputable section

/-- A certified two-level factor over `Fin dimension`. -/
structure FinTwoLevelFactor (dimension : ℕ) where
  /-- The `false` coordinate of the ordered block. -/
  first : Fin dimension
  /-- The `true` coordinate of the ordered block. -/
  second : Fin dimension
  /-- Two-level factors always use distinct coordinates. -/
  distinct : first ≠ second
  /-- The certified `U(2)` block in `false,true` order. -/
  block : QubitUnitary

namespace FinTwoLevelFactor

/-- Full finite-dimensional denotation of a recorded two-level factor. -/
def eval {dimension : ℕ} (factor : FinTwoLevelFactor dimension) :
    Matrix.unitaryGroup (Fin dimension) ℂ :=
  twoLevelUnitary factor.first factor.second factor.distinct factor.block

/-- The inverse of a two-level factor has the same ordered support. -/
def inverse {dimension : ℕ} (factor : FinTwoLevelFactor dimension) :
    FinTwoLevelFactor dimension where
  first := factor.first
  second := factor.second
  distinct := factor.distinct
  block := factor.block⁻¹

@[simp]
theorem eval_inverse {dimension : ℕ} (factor : FinTwoLevelFactor dimension) :
    factor.inverse.eval = factor.eval⁻¹ := by
  exact twoLevelUnitary_inv factor.first factor.second factor.distinct factor.block

/-- Embed a factor into the first `dimension` coordinates of `Fin (dimension+1)`. -/
def castSucc {dimension : ℕ} (factor : FinTwoLevelFactor dimension) :
    FinTwoLevelFactor (dimension + 1) where
  first := factor.first.castSucc
  second := factor.second.castSucc
  distinct := (Fin.castSucc_injective dimension) factor.distinct
  block := factor.block

@[simp]
theorem eval_castSucc_apply_castSucc {dimension : ℕ}
    (factor : FinTwoLevelFactor dimension) (row col : Fin dimension) :
    factor.castSucc.eval row.castSucc col.castSucc = factor.eval row col := by
  simp only [eval, castSucc, twoLevelUnitary_apply, twoLevelCoordinate]
  split_ifs with hrowFirst hrowSecond hcolFirst hcolSecond <;>
    simp_all only [Fin.castSucc_inj]

@[simp]
theorem eval_castSucc_apply_castSucc_last {dimension : ℕ}
    (factor : FinTwoLevelFactor dimension) (row : Fin dimension) :
    factor.castSucc.eval row.castSucc (Fin.last dimension) = 0 := by
  simp [eval, castSucc, twoLevelUnitary_apply, twoLevelCoordinate,
    Fin.castSucc_ne_last]

@[simp]
theorem eval_castSucc_apply_last_castSucc {dimension : ℕ}
    (factor : FinTwoLevelFactor dimension) (col : Fin dimension) :
    factor.castSucc.eval (Fin.last dimension) col.castSucc = 0 := by
  simp [eval, castSucc, twoLevelUnitary_apply, twoLevelCoordinate,
    Fin.castSucc_ne_last]

@[simp]
theorem eval_castSucc_apply_last_last {dimension : ℕ}
    (factor : FinTwoLevelFactor dimension) :
    factor.castSucc.eval (Fin.last dimension) (Fin.last dimension) = 1 := by
  simp [eval, castSucc, twoLevelUnitary_apply, twoLevelCoordinate,
    Fin.castSucc_ne_last]

end FinTwoLevelFactor

/-- Conventional left-to-right product of an explicit factor list. -/
def factorProduct {dimension : ℕ} (factors : List (FinTwoLevelFactor dimension)) :
    Matrix.unitaryGroup (Fin dimension) ℂ :=
  (factors.map FinTwoLevelFactor.eval).prod

@[simp]
theorem factorProduct_nil {dimension : ℕ} :
    factorProduct ([] : List (FinTwoLevelFactor dimension)) = 1 := rfl

@[simp]
theorem factorProduct_cons {dimension : ℕ} (factor : FinTwoLevelFactor dimension)
    (factors : List (FinTwoLevelFactor dimension)) :
    factorProduct (factor :: factors) = factor.eval * factorProduct factors := by
  simp [factorProduct]

@[simp]
theorem factorProduct_append {dimension : ℕ}
    (first second : List (FinTwoLevelFactor dimension)) :
    factorProduct (first ++ second) = factorProduct first * factorProduct second := by
  simp [factorProduct]

/-- Reverse a product and invert every factor, retaining explicit two-level data. -/
def inverseFactors {dimension : ℕ} :
    List (FinTwoLevelFactor dimension) → List (FinTwoLevelFactor dimension)
  | [] => []
  | factor :: factors => inverseFactors factors ++ [factor.inverse]

@[simp]
theorem factorProduct_inverseFactors {dimension : ℕ}
    (factors : List (FinTwoLevelFactor dimension)) :
    factorProduct (inverseFactors factors) = (factorProduct factors)⁻¹ := by
  induction factors with
  | nil => simp [inverseFactors]
  | cons factor factors ih =>
      simp [inverseFactors, ih]

/-- Embed every factor into the first coordinates of the successor dimension. -/
def castSuccFactors {dimension : ℕ} (factors : List (FinTwoLevelFactor dimension)) :
    List (FinTwoLevelFactor (dimension + 1)) :=
  factors.map FinTwoLevelFactor.castSucc

@[simp]
theorem factorProduct_castSuccFactors_apply_castSucc {dimension : ℕ}
    (factors : List (FinTwoLevelFactor dimension)) (row col : Fin dimension) :
    factorProduct (castSuccFactors factors) row.castSucc col.castSucc =
      factorProduct factors row col := by
  induction factors generalizing row col with
  | nil => simp [castSuccFactors, Matrix.one_apply]
  | cons factor factors ih =>
      rw [castSuccFactors, List.map_cons, factorProduct_cons, factorProduct_cons]
      change (∑ middle : Fin (dimension + 1),
          factor.castSucc.eval row.castSucc middle *
            factorProduct (castSuccFactors factors) middle col.castSucc) =
        ∑ middle : Fin dimension,
          factor.eval row middle * factorProduct factors middle col
      rw [Fin.sum_univ_castSucc]
      simp only [FinTwoLevelFactor.eval_castSucc_apply_castSucc,
        FinTwoLevelFactor.eval_castSucc_apply_castSucc_last, zero_mul, add_zero]
      simp_rw [ih]

@[simp]
theorem factorProduct_castSuccFactors_apply_last_last {dimension : ℕ}
    (factors : List (FinTwoLevelFactor dimension)) :
    factorProduct (castSuccFactors factors) (Fin.last dimension) (Fin.last dimension) = 1 := by
  induction factors with
  | nil => simp [castSuccFactors]
  | cons factor factors ih =>
      rw [castSuccFactors, List.map_cons, factorProduct_cons]
      change (∑ middle : Fin (dimension + 1),
          factor.castSucc.eval (Fin.last dimension) middle *
            factorProduct (castSuccFactors factors) middle (Fin.last dimension)) = 1
      rw [Fin.sum_univ_castSucc]
      simp only [FinTwoLevelFactor.eval_castSucc_apply_last_castSucc, zero_mul,
        Finset.sum_const_zero, FinTwoLevelFactor.eval_castSucc_apply_last_last,
        ih, one_mul, zero_add]

@[simp]
theorem factorProduct_castSuccFactors_apply_castSucc_last {dimension : ℕ}
    (factors : List (FinTwoLevelFactor dimension)) (row : Fin dimension) :
    factorProduct (castSuccFactors factors) row.castSucc (Fin.last dimension) = 0 := by
  induction factors generalizing row with
  | nil => simp [castSuccFactors]
  | cons factor factors ih =>
      rw [castSuccFactors, List.map_cons, factorProduct_cons]
      change (∑ middle : Fin (dimension + 1),
          factor.castSucc.eval row.castSucc middle *
            factorProduct (castSuccFactors factors) middle (Fin.last dimension)) = 0
      rw [Fin.sum_univ_castSucc]
      simp only [FinTwoLevelFactor.eval_castSucc_apply_castSucc,
        FinTwoLevelFactor.eval_castSucc_apply_castSucc_last,
        factorProduct_castSuccFactors_apply_last_last, zero_mul, add_zero]
      simp_rw [ih]
      simp

@[simp]
theorem factorProduct_castSuccFactors_apply_last_castSucc {dimension : ℕ}
    (factors : List (FinTwoLevelFactor dimension)) (col : Fin dimension) :
    factorProduct (castSuccFactors factors) (Fin.last dimension) col.castSucc = 0 := by
  induction factors with
  | nil => simp [castSuccFactors, Matrix.one_apply, Fin.castSucc_ne_last]
  | cons factor factors ih =>
      rw [castSuccFactors, List.map_cons, factorProduct_cons]
      change (∑ middle : Fin (dimension + 1),
          factor.castSucc.eval (Fin.last dimension) middle *
            factorProduct (castSuccFactors factors) middle col.castSucc) = 0
      rw [Fin.sum_univ_castSucc]
      simp only [FinTwoLevelFactor.eval_castSucc_apply_last_castSucc,
        FinTwoLevelFactor.eval_castSucc_apply_last_last, zero_mul, Finset.sum_const_zero,
        one_mul, ih, zero_add]

/-- A certified unitary is diagonal when all unequal-index entries vanish. -/
def IsDiagonalUnitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) : Prop :=
  ∀ row col, row ≠ col → U row col = 0

/-- Explicit factors, an exact diagonal residual, and their proved product. -/
structure FinTwoLevelDecomposition {dimension : ℕ}
    (U : Matrix.unitaryGroup (Fin dimension) ℂ) where
  /-- Left-to-right mathematical factors. -/
  factors : List (FinTwoLevelFactor dimension)
  /-- Exact certified diagonal residual. -/
  residual : Matrix.unitaryGroup (Fin dimension) ℂ
  /-- The residual has no off-diagonal entries. -/
  residual_diagonal : IsDiagonalUnitary residual
  /-- Exact product equation; no phase is discarded. -/
  product_eq : U = factorProduct factors * residual

/-- A certified block sum of two possibly different finite dimensions. -/
def sumUnitary {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (U : Matrix.unitaryGroup ι ℂ)
    (V : Matrix.unitaryGroup κ ℂ) : Matrix.unitaryGroup (ι ⊕ κ) ℂ :=
  ⟨Matrix.fromBlocks (U : Matrix ι ι ℂ) 0 0 (V : Matrix κ κ ℂ), by
    have hU : (U : Matrix ι ι ℂ)ᴴ * (U : Matrix ι ι ℂ) = 1 := by
      have h := (Matrix.mem_unitaryGroup_iff').1 U.property
      simpa only [Matrix.star_eq_conjTranspose] using h
    have hV : (V : Matrix κ κ ℂ)ᴴ * (V : Matrix κ κ ℂ) = 1 := by
      have h := (Matrix.mem_unitaryGroup_iff').1 V.property
      simpa only [Matrix.star_eq_conjTranspose] using h
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
      Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
    simp [hU, hV]⟩

/-- A certified one-dimensional unitary from its scalar norm equation. -/
def scalarFinOneUnitary (z : ℂ) (hz : star z * z = 1) :
    Matrix.unitaryGroup (Fin 1) ℂ :=
  ⟨fun _ _ => z, by
    rw [Matrix.mem_unitaryGroup_iff']
    ext row col
    have hrow : row = 0 := Subsingleton.elim _ _
    have hcol : col = 0 := Subsingleton.elim _ _
    subst row
    subst col
    simpa [Matrix.mul_apply] using hz⟩

/-- Extend a diagonal block by one final scalar coordinate. -/
def finSuccBlockUnitary {dimension : ℕ}
    (U : Matrix.unitaryGroup (Fin dimension) ℂ)
    (z : ℂ) (hz : star z * z = 1) :
    Matrix.unitaryGroup (Fin (dimension + 1)) ℂ :=
  reindexUnitary finSumFinEquiv (sumUnitary U (scalarFinOneUnitary z hz))

@[simp]
theorem finSuccBlockUnitary_apply_castSucc {dimension : ℕ}
    (U : Matrix.unitaryGroup (Fin dimension) ℂ) (z : ℂ)
    (hz : star z * z = 1) (row col : Fin dimension) :
    finSuccBlockUnitary U z hz row.castSucc col.castSucc = U row col := by
  simp [finSuccBlockUnitary, sumUnitary]

@[simp]
theorem finSuccBlockUnitary_apply_castSucc_last {dimension : ℕ}
    (U : Matrix.unitaryGroup (Fin dimension) ℂ) (z : ℂ)
    (hz : star z * z = 1) (row : Fin dimension) :
    finSuccBlockUnitary U z hz row.castSucc (Fin.last dimension) = 0 := by
  simp [finSuccBlockUnitary, sumUnitary]

@[simp]
theorem finSuccBlockUnitary_apply_last_castSucc {dimension : ℕ}
    (U : Matrix.unitaryGroup (Fin dimension) ℂ) (z : ℂ)
    (hz : star z * z = 1) (col : Fin dimension) :
    finSuccBlockUnitary U z hz (Fin.last dimension) col.castSucc = 0 := by
  simp [finSuccBlockUnitary, sumUnitary]

@[simp]
theorem finSuccBlockUnitary_apply_last_last {dimension : ℕ}
    (U : Matrix.unitaryGroup (Fin dimension) ℂ) (z : ℂ)
    (hz : star z * z = 1) :
    finSuccBlockUnitary U z hz (Fin.last dimension) (Fin.last dimension) = z := by
  simp [finSuccBlockUnitary, sumUnitary, scalarFinOneUnitary]

theorem isDiagonal_finSuccBlockUnitary {dimension : ℕ}
    (U : Matrix.unitaryGroup (Fin dimension) ℂ) (hU : IsDiagonalUnitary U)
    (z : ℂ) (hz : star z * z = 1) :
    IsDiagonalUnitary (finSuccBlockUnitary U z hz) := by
  intro row col hrowCol
  revert col
  refine Fin.lastCases ?_ (fun row' => ?_) row
  · intro col hrowCol
    refine Fin.lastCases ?_ (fun col' => ?_) col
    · exact (hrowCol rfl).elim
    · exact finSuccBlockUnitary_apply_last_castSucc U z hz col'
  · intro col hrowCol
    refine Fin.lastCases ?_ (fun col' => ?_) col
    · exact finSuccBlockUnitary_apply_castSucc_last U z hz row'
    · rw [finSuccBlockUnitary_apply_castSucc]
      apply hU
      intro h
      apply hrowCol
      exact congrArg Fin.castSucc h

end

end Barenco.Universality
