import Barenco.Universality.EliminationCore
import Barenco.Universality.Givens

/-!
# Constructive finite-unitary two-level elimination

This module performs exact left Givens elimination on certified complex
unitaries over `Fin dimension`.  At a successor dimension, every earlier row is
paired once with `Fin.last`; each step clears that row in the last column and
later steps leave it untouched.  Unitarity then forces the rest of the last row
to vanish, exposing a smaller certified unitary for recursion.
-/

namespace Barenco.Universality

open Matrix

noncomputable section

section TwoLevelRows

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Left multiplication by a two-level unitary: its first output row. -/
theorem twoLevelUnitary_mul_apply_first (first second : ι)
    (hfirstSecond : first ≠ second) (U : QubitUnitary)
    (M : Matrix ι ι ℂ) (col : ι) :
    ((twoLevelUnitary first second hfirstSecond U : Matrix ι ι ℂ) * M) first col =
      U false false * M first col + U false true * M second col := by
  rw [Matrix.mul_apply]
  rw [Fintype.sum_eq_add_sum_subtype_ne _ first]
  rw [Fintype.sum_eq_add_sum_subtype_ne _ ⟨second, hfirstSecond.symm⟩]
  simp only [twoLevelUnitary_first_first, twoLevelUnitary_first_second]
  have hrest : (∑ index : {index : {index : ι // index ≠ first} //
      index ≠ ⟨second, hfirstSecond.symm⟩},
      (twoLevelUnitary first second hfirstSecond U : Matrix ι ι ℂ) first index.1.1 *
        M index.1.1 col) = 0 := by
    apply Finset.sum_eq_zero
    intro index _
    rw [twoLevelUnitary_pair_outside]
    · simp
    · exact Or.inl rfl
    · exact index.1.2
    · intro hindexSecond
      apply index.2
      exact Subtype.ext hindexSecond
  rw [hrest, add_zero]

/-- Left multiplication by a two-level unitary: its second output row. -/
theorem twoLevelUnitary_mul_apply_second (first second : ι)
    (hfirstSecond : first ≠ second) (U : QubitUnitary)
    (M : Matrix ι ι ℂ) (col : ι) :
    ((twoLevelUnitary first second hfirstSecond U : Matrix ι ι ℂ) * M) second col =
      U true false * M first col + U true true * M second col := by
  rw [Matrix.mul_apply]
  rw [Fintype.sum_eq_add_sum_subtype_ne _ second]
  rw [Fintype.sum_eq_add_sum_subtype_ne _ ⟨first, hfirstSecond⟩]
  simp only [twoLevelUnitary_second_second, twoLevelUnitary_second_first]
  have hrest : (∑ index : {index : {index : ι // index ≠ second} //
      index ≠ ⟨first, hfirstSecond⟩},
      (twoLevelUnitary first second hfirstSecond U : Matrix ι ι ℂ) second index.1.1 *
        M index.1.1 col) = 0 := by
    apply Finset.sum_eq_zero
    intro index _
    rw [twoLevelUnitary_pair_outside]
    · simp
    · exact Or.inr rfl
    · intro hindexFirst
      apply index.2
      exact Subtype.ext hindexFirst
    · exact index.1.2
  rw [hrest, add_zero, add_comm]

/-- Every row outside the selected pair is unchanged by left multiplication. -/
theorem twoLevelUnitary_mul_apply_outside (first second row : ι)
    (hfirstSecond : first ≠ second) (U : QubitUnitary)
    (M : Matrix ι ι ℂ) (hrowFirst : row ≠ first) (hrowSecond : row ≠ second)
    (col : ι) :
    ((twoLevelUnitary first second hfirstSecond U : Matrix ι ι ℂ) * M) row col =
      M row col := by
  rw [Matrix.mul_apply]
  rw [Fintype.sum_eq_add_sum_subtype_ne _ row]
  rw [twoLevelUnitary_outside_outside]
  · simp only [if_pos, one_mul]
    have hrest : (∑ index : {index : ι // index ≠ row},
        (twoLevelUnitary first second hfirstSecond U : Matrix ι ι ℂ) row index.1 *
          M index.1 col) = 0 := by
      apply Finset.sum_eq_zero
      intro index _
      rw [twoLevelUnitary_apply]
      simp only [twoLevelCoordinate_outside _ _ _ hrowFirst hrowSecond]
      cases hcoordinate : twoLevelCoordinate first second index.1 <;>
        simp [(index.2).symm]
    rw [hrest, add_zero]
  · exact hrowFirst
  · exact hrowSecond
  · exact hrowFirst
  · exact hrowSecond

end TwoLevelRows

/-- A Givens factor that clears `index` against the chosen `pivot`. -/
def givensFactor {dimension : ℕ} (pivot : Fin dimension)
    (index : {index : Fin dimension // index ≠ pivot})
    (U : Matrix.unitaryGroup (Fin dimension) ℂ) : FinTwoLevelFactor dimension where
  first := index
  second := pivot
  distinct := index.property
  block := givensUnitary (U index pivot) (U pivot pivot)

/-- One exact left Givens step. -/
def applyGivensFactor {dimension : ℕ} (pivot : Fin dimension)
    (index : {index : Fin dimension // index ≠ pivot})
    (U : Matrix.unitaryGroup (Fin dimension) ℂ) :
    Matrix.unitaryGroup (Fin dimension) ℂ :=
  (givensFactor pivot index U).eval * U

@[simp]
theorem applyGivensFactor_clears {dimension : ℕ} (pivot : Fin dimension)
    (index : {index : Fin dimension // index ≠ pivot})
    (U : Matrix.unitaryGroup (Fin dimension) ℂ) :
    applyGivensFactor pivot index U index pivot = 0 := by
  change ((twoLevelUnitary (index : Fin dimension) pivot index.property
      (givensUnitary (U index pivot) (U pivot pivot)) :
        Matrix (Fin dimension) (Fin dimension) ℂ) * U) index pivot = 0
  rw [twoLevelUnitary_mul_apply_first]
  exact givensUnitary_eliminates (U index pivot) (U pivot pivot)

theorem applyGivensFactor_row_eq {dimension : ℕ} (pivot : Fin dimension)
    (index : {index : Fin dimension // index ≠ pivot})
    (U : Matrix.unitaryGroup (Fin dimension) ℂ) (row : Fin dimension)
    (hrowIndex : row ≠ index) (hrowPivot : row ≠ pivot) (col : Fin dimension) :
    applyGivensFactor pivot index U row col = U row col := by
  exact twoLevelUnitary_mul_apply_outside (index : Fin dimension) pivot row index.property _ _
    hrowIndex hrowPivot col

/-- Output of a left-pivot sweep, including its exact multiplier equation. -/
structure PivotElimination {dimension : ℕ} (U : Matrix.unitaryGroup (Fin dimension) ℂ) where
  /-- Factors in conventional mathematical product order. -/
  factors : List (FinTwoLevelFactor dimension)
  /-- Matrix after all listed left multiplications. -/
  residual : Matrix.unitaryGroup (Fin dimension) ℂ
  /-- Exact accumulated left-multiplication equation. -/
  residual_eq : residual = factorProduct factors * U

/-- Sweep a duplicate-free list of non-pivot coordinates against `pivot`. -/
def pivotEliminate {dimension : ℕ} (pivot : Fin dimension) :
    (indices : List {index : Fin dimension // index ≠ pivot}) →
      (U : Matrix.unitaryGroup (Fin dimension) ℂ) → PivotElimination U
  | [], U =>
      { factors := []
        residual := U
        residual_eq := by simp }
  | index :: indices, U =>
      let factor := givensFactor pivot index U
      let next := pivotEliminate pivot indices (factor.eval * U)
      { factors := next.factors ++ [factor]
        residual := next.residual
        residual_eq := by
          rw [next.residual_eq, factorProduct_append]
          simp only [factorProduct_cons, factorProduct_nil, mul_one]
          rw [mul_assoc] }

theorem pivotEliminate_row_eq_of_forall_ne {dimension : ℕ}
    (pivot : Fin dimension) (indices : List {index : Fin dimension // index ≠ pivot})
    (U : Matrix.unitaryGroup (Fin dimension) ℂ) (row : Fin dimension)
    (hrowPivot : row ≠ pivot)
    (hrowIndices : ∀ index ∈ indices, row ≠ index.1) (col : Fin dimension) :
    (pivotEliminate pivot indices U).residual row col = U row col := by
  induction indices generalizing U with
  | nil => rfl
  | cons index indices ih =>
      change (pivotEliminate pivot indices (applyGivensFactor pivot index U)).residual row col =
        U row col
      rw [ih]
      · exact applyGivensFactor_row_eq pivot index U row
          (hrowIndices index (List.mem_cons_self)) hrowPivot col
      · intro later hlater
        exact hrowIndices later (List.mem_cons_of_mem index hlater)

theorem pivotEliminate_zero_of_mem {dimension : ℕ}
    (pivot : Fin dimension) (indices : List {index : Fin dimension // index ≠ pivot})
    (hnodup : indices.Nodup) (U : Matrix.unitaryGroup (Fin dimension) ℂ)
    (index : {index : Fin dimension // index ≠ pivot}) (hindex : index ∈ indices) :
    (pivotEliminate pivot indices U).residual index pivot = 0 := by
  induction indices generalizing U with
  | nil => simp at hindex
  | cons current indices ih =>
      rw [List.nodup_cons] at hnodup
      rcases List.mem_cons.mp hindex with hcurrent | hrest
      · subst index
        change (pivotEliminate pivot indices
          (applyGivensFactor pivot current U)).residual current pivot = 0
        rw [pivotEliminate_row_eq_of_forall_ne]
        · exact applyGivensFactor_clears pivot current U
        · exact current.property
        · intro later hlater heq
          apply hnodup.1
          have : current = later := Subtype.ext heq
          simpa [this] using hlater
      · change (pivotEliminate pivot indices
          (applyGivensFactor pivot current U)).residual index pivot = 0
        exact ih hnodup.2 (applyGivensFactor pivot current U) hrest

/-- The complete successor-dimension pivot schedule. -/
def successorPivotSchedule (dimension : ℕ) :
    List {index : Fin (dimension + 1) // index ≠ Fin.last dimension} :=
  List.ofFn fun index : Fin dimension =>
    ⟨index.castSucc, Fin.castSucc_ne_last index⟩

theorem successorPivotSchedule_nodup (dimension : ℕ) :
    (successorPivotSchedule dimension).Nodup := by
  rw [successorPivotSchedule, List.nodup_ofFn]
  intro first second h
  apply (Fin.castSucc_injective dimension)
  exact congrArg Subtype.val h

theorem mem_successorPivotSchedule (index : Fin dimension) :
    (⟨index.castSucc, Fin.castSucc_ne_last index⟩ :
      {index : Fin (dimension + 1) // index ≠ Fin.last dimension}) ∈
        successorPivotSchedule dimension := by
  rw [successorPivotSchedule, List.mem_ofFn]
  exact ⟨index, rfl⟩

/-- Eliminate the final column above its last entry. -/
def eliminateLastColumn {dimension : ℕ}
    (U : Matrix.unitaryGroup (Fin (dimension + 1)) ℂ) : PivotElimination U :=
  pivotEliminate (Fin.last dimension) (successorPivotSchedule dimension) U

@[simp]
theorem eliminateLastColumn_apply_castSucc_last {dimension : ℕ}
    (U : Matrix.unitaryGroup (Fin (dimension + 1)) ℂ) (row : Fin dimension) :
    (eliminateLastColumn U).residual row.castSucc (Fin.last dimension) = 0 := by
  exact pivotEliminate_zero_of_mem (Fin.last dimension)
    (successorPivotSchedule dimension) (successorPivotSchedule_nodup dimension) U
    ⟨row.castSucc, Fin.castSucc_ne_last row⟩ (mem_successorPivotSchedule row)

theorem eliminateLastColumn_last_norm {dimension : ℕ}
    (U : Matrix.unitaryGroup (Fin (dimension + 1)) ℂ) :
    star ((eliminateLastColumn U).residual (Fin.last dimension) (Fin.last dimension)) *
      (eliminateLastColumn U).residual (Fin.last dimension) (Fin.last dimension) = 1 := by
  let R := (eliminateLastColumn U).residual
  have hunitary : (R : Matrix (Fin (dimension + 1)) (Fin (dimension + 1)) ℂ)ᴴ * R = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff').1 R.property
    simpa only [Matrix.star_eq_conjTranspose] using h
  have hentry := congrFun (congrFun hunitary (Fin.last dimension)) (Fin.last dimension)
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
    if_pos] at hentry
  rw [Fin.sum_univ_castSucc] at hentry
  simpa [R, eliminateLastColumn_apply_castSucc_last] using hentry

@[simp]
theorem eliminateLastColumn_apply_last_castSucc {dimension : ℕ}
    (U : Matrix.unitaryGroup (Fin (dimension + 1)) ℂ) (col : Fin dimension) :
    (eliminateLastColumn U).residual (Fin.last dimension) col.castSucc = 0 := by
  let R := (eliminateLastColumn U).residual
  let z := R (Fin.last dimension) (Fin.last dimension)
  have hz : star z * z = 1 := eliminateLastColumn_last_norm U
  have hzstar : star z ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hz
    exact zero_ne_one hz
  have hunitary : (R : Matrix (Fin (dimension + 1)) (Fin (dimension + 1)) ℂ)ᴴ * R = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff').1 R.property
    simpa only [Matrix.star_eq_conjTranspose] using h
  have hentry := congrFun (congrFun hunitary (Fin.last dimension)) col.castSucc
  have hlastCol : Fin.last dimension ≠ col.castSucc :=
    (Fin.castSucc_ne_last col).symm
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
    if_neg hlastCol] at hentry
  rw [Fin.sum_univ_castSucc] at hentry
  simp only [R, eliminateLastColumn_apply_castSucc_last, star_zero, zero_mul,
    Finset.sum_const_zero, zero_add] at hentry
  exact (mul_eq_zero.mp hentry).resolve_left hzstar

/-- Certified upper-left block exposed after final-column elimination. -/
def eliminatedUpperUnitary {dimension : ℕ}
    (U : Matrix.unitaryGroup (Fin (dimension + 1)) ℂ) :
    Matrix.unitaryGroup (Fin dimension) ℂ :=
  let R := (eliminateLastColumn U).residual
  ⟨fun row col => R row.castSucc col.castSucc, by
    rw [Matrix.mem_unitaryGroup_iff']
    ext row col
    have hunitary :
        (R : Matrix (Fin (dimension + 1)) (Fin (dimension + 1)) ℂ)ᴴ * R = 1 := by
      have h := (Matrix.mem_unitaryGroup_iff').1 R.property
      simpa only [Matrix.star_eq_conjTranspose] using h
    have hentry := congrFun (congrFun hunitary row.castSucc) col.castSucc
    change (∑ middle : Fin (dimension + 1),
        star (R middle row.castSucc) * R middle col.castSucc) =
      if row.castSucc = col.castSucc then 1 else 0 at hentry
    rw [Fin.sum_univ_castSucc] at hentry
    simp only [eliminateLastColumn_apply_last_castSucc, R, star_zero, zero_mul,
      add_zero, Fin.castSucc_inj] at hentry
    simpa [Matrix.mul_apply, Matrix.one_apply] using hentry⟩

@[simp]
theorem eliminatedUpperUnitary_apply {dimension : ℕ}
    (U : Matrix.unitaryGroup (Fin (dimension + 1)) ℂ) (row col : Fin dimension) :
    eliminatedUpperUnitary U row col =
      (eliminateLastColumn U).residual row.castSucc col.castSucc := rfl

/--
Lift a decomposition of the exposed upper block and recover the complete
post-elimination residual as its lifted factor product times a diagonal block.
-/
theorem eliminateLastColumn_residual_factorization {dimension : ℕ}
    (U : Matrix.unitaryGroup (Fin (dimension + 1)) ℂ)
    (smaller : FinTwoLevelDecomposition (eliminatedUpperUnitary U)) :
    (eliminateLastColumn U).residual =
      factorProduct (castSuccFactors smaller.factors) *
        finSuccBlockUnitary smaller.residual
          ((eliminateLastColumn U).residual (Fin.last dimension) (Fin.last dimension))
          (eliminateLastColumn_last_norm U) := by
  apply Subtype.ext
  ext row col
  induction row using Fin.lastCases with
  | last =>
      induction col using Fin.lastCases with
      | last =>
          change (eliminateLastColumn U).residual (Fin.last dimension) (Fin.last dimension) =
            ∑ middle : Fin (dimension + 1),
              factorProduct (castSuccFactors smaller.factors) (Fin.last dimension) middle *
                finSuccBlockUnitary smaller.residual
                  ((eliminateLastColumn U).residual (Fin.last dimension) (Fin.last dimension))
                  (eliminateLastColumn_last_norm U) middle (Fin.last dimension)
          rw [Fin.sum_univ_castSucc]
          simp
      | cast col' =>
          change (eliminateLastColumn U).residual (Fin.last dimension) col'.castSucc =
            ∑ middle : Fin (dimension + 1),
              factorProduct (castSuccFactors smaller.factors) (Fin.last dimension) middle *
                finSuccBlockUnitary smaller.residual
                  ((eliminateLastColumn U).residual (Fin.last dimension) (Fin.last dimension))
                  (eliminateLastColumn_last_norm U) middle col'.castSucc
          rw [Fin.sum_univ_castSucc]
          simp
  | cast row' =>
      induction col using Fin.lastCases with
      | last =>
          change (eliminateLastColumn U).residual row'.castSucc (Fin.last dimension) =
            ∑ middle : Fin (dimension + 1),
              factorProduct (castSuccFactors smaller.factors) row'.castSucc middle *
                finSuccBlockUnitary smaller.residual
                  ((eliminateLastColumn U).residual (Fin.last dimension) (Fin.last dimension))
                  (eliminateLastColumn_last_norm U) middle (Fin.last dimension)
          rw [Fin.sum_univ_castSucc]
          simp
      | cast col' =>
          have hsmall := congrArg
            (fun V : Matrix.unitaryGroup (Fin dimension) ℂ => V row' col')
            smaller.product_eq
          change (eliminateLastColumn U).residual row'.castSucc col'.castSucc =
            ∑ middle : Fin (dimension + 1),
              factorProduct (castSuccFactors smaller.factors) row'.castSucc middle *
                finSuccBlockUnitary smaller.residual
                  ((eliminateLastColumn U).residual (Fin.last dimension) (Fin.last dimension))
                  (eliminateLastColumn_last_norm U) middle col'.castSucc
          rw [Fin.sum_univ_castSucc]
          simp only [factorProduct_castSuccFactors_apply_castSucc,
            factorProduct_castSuccFactors_apply_castSucc_last,
            finSuccBlockUnitary_apply_castSucc,
            finSuccBlockUnitary_apply_last_castSucc, mul_zero, add_zero]
          simpa [eliminatedUpperUnitary_apply, Matrix.mul_apply] using hsmall

/--
One recursive successor step: invert the left-elimination factors, then append
the lifted factors for the smaller upper block.
-/
def successorFinTwoLevelDecomposition {dimension : ℕ}
    (U : Matrix.unitaryGroup (Fin (dimension + 1)) ℂ)
    (smaller : FinTwoLevelDecomposition (eliminatedUpperUnitary U)) :
    FinTwoLevelDecomposition U where
  factors := inverseFactors (eliminateLastColumn U).factors ++
    castSuccFactors smaller.factors
  residual := finSuccBlockUnitary smaller.residual
    ((eliminateLastColumn U).residual (Fin.last dimension) (Fin.last dimension))
    (eliminateLastColumn_last_norm U)
  residual_diagonal := isDiagonal_finSuccBlockUnitary smaller.residual
    smaller.residual_diagonal _ _
  product_eq := by
    let E := factorProduct (eliminateLastColumn U).factors
    let P := factorProduct (castSuccFactors smaller.factors)
    let D := finSuccBlockUnitary smaller.residual
      ((eliminateLastColumn U).residual (Fin.last dimension) (Fin.last dimension))
      (eliminateLastColumn_last_norm U)
    have hrecover : U = E⁻¹ * (eliminateLastColumn U).residual := by
      rw [(eliminateLastColumn U).residual_eq]
      simp [E]
    have hblock : (eliminateLastColumn U).residual = P * D := by
      exact eliminateLastColumn_residual_factorization U smaller
    calc
      U = E⁻¹ * (eliminateLastColumn U).residual := hrecover
      _ = E⁻¹ * (P * D) := by rw [hblock]
      _ = (E⁻¹ * P) * D := by rw [mul_assoc]
      _ = factorProduct
          (inverseFactors (eliminateLastColumn U).factors ++
            castSuccFactors smaller.factors) * D := by
        rw [factorProduct_append, factorProduct_inverseFactors]

/--
Constructive exact decomposition of every finite complex unitary into explicit
two-level factors and one certified diagonal residual.

The equation uses conventional mathematical product order.  It includes the
empty and singleton dimensions without additional assumptions.
-/
def decomposeFinUnitary : (dimension : ℕ) →
    (U : Matrix.unitaryGroup (Fin dimension) ℂ) → FinTwoLevelDecomposition U
  | 0, U =>
      { factors := []
        residual := U
        residual_diagonal := by
          intro row
          exact Fin.elim0 row
        product_eq := by simp }
  | dimension + 1, U =>
      successorFinTwoLevelDecomposition U
        (decomposeFinUnitary dimension (eliminatedUpperUnitary U))

theorem decomposeFinUnitary_product_eq {dimension : ℕ}
    (U : Matrix.unitaryGroup (Fin dimension) ℂ) :
    U = factorProduct (decomposeFinUnitary dimension U).factors *
      (decomposeFinUnitary dimension U).residual :=
  (decomposeFinUnitary dimension U).product_eq

theorem decomposeFinUnitary_residual_diagonal {dimension : ℕ}
    (U : Matrix.unitaryGroup (Fin dimension) ℂ) :
    IsDiagonalUnitary (decomposeFinUnitary dimension U).residual :=
  (decomposeFinUnitary dimension U).residual_diagonal

end

end Barenco.Universality
