import Barenco.Universality.Elimination

/-!
# Transporting finite two-level decompositions

The elimination algorithm is canonical over `Fin d`.  This module transports
its explicit factors and diagonal residual to an arbitrary finite decidable
index type.  The transport is algebraic simultaneous matrix reindexing; it does
not claim that the chosen equivalence is a zero-cost circuit operation.
-/

namespace Barenco.Universality

open Matrix

noncomputable section

/-- Ordered-pair coordinates commute with an index equivalence. -/
theorem twoLevelCoordinate_equiv {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (first second : ι) (index : κ) :
    twoLevelCoordinate (e first) (e second) index =
      twoLevelCoordinate first second (e.symm index) := by
  by_cases hfirst : index = e first
  · subst index
    simp [twoLevelCoordinate]
  · by_cases hsecond : index = e second
    · subst index
      by_cases h : first = second
      · subst second
        simp at hfirst
      · simp [twoLevelCoordinate]
    · have hfirst' : e.symm index ≠ first := by
        intro h
        apply hfirst
        exact e.symm_apply_eq.mp h
      have hsecond' : e.symm index ≠ second := by
        intro h
        apply hsecond
        exact e.symm_apply_eq.mp h
      simp [twoLevelCoordinate, hfirst, hsecond, hfirst', hsecond']

/-- Reindexing an embedded block maps exactly its two ordered endpoints. -/
theorem reindexUnitary_twoLevelUnitary {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (first second : ι) (hfirstSecond : first ≠ second)
    (U : QubitUnitary) :
    reindexUnitary e (twoLevelUnitary first second hfirstSecond U) =
      twoLevelUnitary (e first) (e second) (e.injective.ne hfirstSecond) U := by
  apply Subtype.ext
  ext row col
  rw [reindexUnitary_apply, twoLevelUnitary_apply, twoLevelUnitary_apply]
  rw [twoLevelCoordinate_equiv, twoLevelCoordinate_equiv]
  simp

/-- A certified two-level factor on an arbitrary finite index type. -/
structure FiniteTwoLevelFactor (ι : Type*) [Fintype ι] [DecidableEq ι] where
  /-- The `false` coordinate of the ordered block. -/
  first : ι
  /-- The `true` coordinate of the ordered block. -/
  second : ι
  /-- The two coordinates are distinct. -/
  distinct : first ≠ second
  /-- Certified local block. -/
  block : QubitUnitary

namespace FiniteTwoLevelFactor

/-- Full matrix denotation of a generic finite-index factor. -/
def eval {ι : Type*} [Fintype ι] [DecidableEq ι]
    (factor : FiniteTwoLevelFactor ι) : Matrix.unitaryGroup ι ℂ :=
  twoLevelUnitary factor.first factor.second factor.distinct factor.block

/-- Transport a canonical `Fin` factor through an explicit equivalence. -/
def reindex {dimension : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Fin dimension ≃ ι) (factor : FinTwoLevelFactor dimension) :
    FiniteTwoLevelFactor ι where
  first := e factor.first
  second := e factor.second
  distinct := e.injective.ne factor.distinct
  block := factor.block

@[simp]
theorem eval_reindex {dimension : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Fin dimension ≃ ι) (factor : FinTwoLevelFactor dimension) :
    (factor.reindex e).eval = reindexUnitary e factor.eval := by
  rw [eval, FinTwoLevelFactor.eval, reindexUnitary_twoLevelUnitary]

end FiniteTwoLevelFactor

/-- Conventional product of generic finite-index factors. -/
def finiteFactorProduct {ι : Type*} [Fintype ι] [DecidableEq ι]
    (factors : List (FiniteTwoLevelFactor ι)) : Matrix.unitaryGroup ι ℂ :=
  (factors.map FiniteTwoLevelFactor.eval).prod

@[simp]
theorem finiteFactorProduct_reindex {dimension : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (e : Fin dimension ≃ ι)
    (factors : List (FinTwoLevelFactor dimension)) :
    finiteFactorProduct (factors.map (FiniteTwoLevelFactor.reindex e)) =
      reindexUnitary e (factorProduct factors) := by
  induction factors with
  | nil => simp [finiteFactorProduct]
  | cons factor factors ih =>
      simp [finiteFactorProduct, factorProduct, ih, reindexUnitary_mul]

/-- Explicit transported decomposition on an arbitrary finite index type. -/
structure FiniteTwoLevelDecomposition {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) where
  /-- Actual ordered two-level factors on `ι`. -/
  factors : List (FiniteTwoLevelFactor ι)
  /-- Exact certified diagonal residual. -/
  residual : Matrix.unitaryGroup ι ℂ
  /-- The transported residual is diagonal in the chosen `ι` basis. -/
  residual_diagonal : IsDiagonalUnitary residual
  /-- Exact product equation. -/
  product_eq : U = finiteFactorProduct factors * residual

/--
Decompose a unitary over any finite decidable index type by transporting the
canonical `Fin (card ι)` construction through `Fintype.equivFin`.
-/
def decomposeFiniteUnitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) : FiniteTwoLevelDecomposition U :=
  let toFin := Fintype.equivFin ι
  let Ufin := reindexUnitary toFin U
  let decomposition := decomposeFinUnitary (Fintype.card ι) Ufin
  let fromFin := toFin.symm
  { factors := decomposition.factors.map (FiniteTwoLevelFactor.reindex fromFin)
    residual := reindexUnitary fromFin decomposition.residual
    residual_diagonal := by
      intro row col hrowCol
      rw [reindexUnitary_apply]
      apply decomposition.residual_diagonal
      exact fromFin.symm.injective.ne hrowCol
    product_eq := by
      calc
        U = reindexUnitary fromFin Ufin := by
          simp [Ufin, fromFin, toFin]
        _ = reindexUnitary fromFin
            (factorProduct decomposition.factors * decomposition.residual) := by
          rw [← decomposition.product_eq]
        _ = reindexUnitary fromFin (factorProduct decomposition.factors) *
            reindexUnitary fromFin decomposition.residual := by
          rw [reindexUnitary_mul]
        _ = finiteFactorProduct
              (decomposition.factors.map (FiniteTwoLevelFactor.reindex fromFin)) *
            reindexUnitary fromFin decomposition.residual := by
          rw [finiteFactorProduct_reindex] }

theorem decomposeFiniteUnitary_product_eq {ι : Type*}
    [Fintype ι] [DecidableEq ι] (U : Matrix.unitaryGroup ι ℂ) :
    U = finiteFactorProduct (decomposeFiniteUnitary U).factors *
      (decomposeFiniteUnitary U).residual :=
  (decomposeFiniteUnitary U).product_eq

theorem decomposeFiniteUnitary_residual_diagonal {ι : Type*}
    [Fintype ι] [DecidableEq ι] (U : Matrix.unitaryGroup ι ℂ) :
    IsDiagonalUnitary (decomposeFiniteUnitary U).residual :=
  (decomposeFiniteUnitary U).residual_diagonal

end


end Barenco.Universality
