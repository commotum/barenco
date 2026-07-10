import Barenco.Universality.TwoLevel

/-!
# Transporting two-level unitaries by a certified unitary

A unitary that sends two named basis kets to two other named basis kets conjugates
the corresponding ordered two-level block. No hypothesis about its action on the
remaining basis is needed: unitarity forces the orthogonal complement of the pair
to map to the orthogonal complement of the image pair.

This algebraic lemma lets the Section 8 path proof track only its two endpoints;
the intermediate path permutation does not have to be normalized into a global
closed-form permutation.
-/

namespace Barenco.Universality

open scoped Matrix

noncomputable section

/-- A two-level unitary fixes every vector whose two selected coordinates vanish. -/
theorem twoLevelUnitary_mulVec_eq_self_of_pair_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (first second : ι) (hfirstSecond : first ≠ second) (U : QubitUnitary)
    (state : ι → ℂ) (hfirst : state first = 0) (hsecond : state second = 0) :
    (twoLevelUnitary first second hfirstSecond U : Matrix ι ι ℂ) *ᵥ state = state := by
  funext row
  rw [Matrix.mulVec]
  simp only [dotProduct]
  by_cases hrowFirst : row = first
  · subst row
    rw [hfirst]
    apply Finset.sum_eq_zero
    intro col _
    by_cases hcolFirst : col = first
    · subst col
      simp [hfirst]
    · by_cases hcolSecond : col = second
      · subst col
        simp [hsecond]
      · simp [twoLevelUnitary_pair_outside, hcolFirst, hcolSecond]
  · by_cases hrowSecond : row = second
    · subst row
      rw [hsecond]
      apply Finset.sum_eq_zero
      intro col _
      by_cases hcolFirst : col = first
      · subst col
        simp [hfirst]
      · by_cases hcolSecond : col = second
        · subst col
          simp [hsecond]
        · simp [twoLevelUnitary_pair_outside, hcolFirst, hcolSecond]
    · rw [Finset.sum_eq_single row]
      · simp [twoLevelUnitary_outside_outside, hrowFirst, hrowSecond]
      · intro col _ hcol
        by_cases hcolFirst : col = first
        · subst col
          simp [twoLevelUnitary_outside_pair, hrowFirst, hrowSecond]
        · by_cases hcolSecond : col = second
          · subst col
            simp [twoLevelUnitary_outside_pair, hrowFirst, hrowSecond]
          · have hrowCol : row ≠ col := Ne.symm hcol
            simp [twoLevelUnitary_outside_outside, hrowFirst, hrowSecond,
              hcolFirst, hcolSecond, hrowCol]
      · simp

/-- Applying a certified inverse undoes an exact vector action. -/
theorem unitary_inv_mulVec_of_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix.unitaryGroup ι ℂ) (input output : ι → ℂ)
    (hP : (P : Matrix ι ι ℂ) *ᵥ input = output) :
    ((P⁻¹ : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) *ᵥ output = input := by
  rw [← hP, Matrix.mulVec_mulVec]
  change (((P⁻¹ * P : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) *ᵥ input) = input
  simp

/-- A known basis-column image makes every other column zero in that image row. -/
theorem unitary_basisImage_row_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix.unitaryGroup ι ℂ) (source target other : ι)
    (hP : (P : Matrix ι ι ℂ) *ᵥ basisKet source = basisKet target)
    (hother : other ≠ source) :
    ((P : Matrix ι ι ℂ) *ᵥ basisKet other) target = 0 := by
  have hinv := unitary_inv_mulVec_of_eq P (basisKet source) (basisKet target) hP
  have hentry := congrFun hinv other
  rw [mulVec_basisKet_apply] at hentry
  have hzero : ((P⁻¹ : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) other target = 0 := by
    simpa [basisKet_apply, hother] using hentry
  change star (P : Matrix ι ι ℂ) other target = 0 at hzero
  change star ((P : Matrix ι ι ℂ) target other) = 0 at hzero
  rw [mulVec_basisKet_apply]
  exact star_eq_zero.mp hzero

/--
Conjugation transports an ordered two-level unitary along the two named basis
images of any certified unitary.
-/
theorem unitary_conjugate_twoLevelUnitary
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix.unitaryGroup ι ℂ)
    (first second imageFirst imageSecond : ι)
    (hfirstSecond : first ≠ second) (himage : imageFirst ≠ imageSecond)
    (hPFirst : (P : Matrix ι ι ℂ) *ᵥ basisKet first = basisKet imageFirst)
    (hPSecond : (P : Matrix ι ι ℂ) *ᵥ basisKet second = basisKet imageSecond)
    (U : QubitUnitary) :
    P⁻¹ * twoLevelUnitary imageFirst imageSecond himage U * P =
      twoLevelUnitary first second hfirstSecond U := by
  apply Subtype.ext
  rw [matrix_eq_iff_mulVec_basisKet_eq]
  intro input
  change (((((P⁻¹ : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) *
      (twoLevelUnitary imageFirst imageSecond himage U : Matrix ι ι ℂ) *
      (P : Matrix ι ι ℂ)) *ᵥ basisKet input)) = _
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  by_cases hinputFirst : input = first
  · subst input
    rw [hPFirst, twoLevelUnitary_mulVec_basisKet_first,
      Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      unitary_inv_mulVec_of_eq P (basisKet first) (basisKet imageFirst) hPFirst,
      unitary_inv_mulVec_of_eq P (basisKet second) (basisKet imageSecond) hPSecond,
      twoLevelUnitary_mulVec_basisKet_first]
  · by_cases hinputSecond : input = second
    · subst input
      rw [hPSecond, twoLevelUnitary_mulVec_basisKet_second,
        Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
        unitary_inv_mulVec_of_eq P (basisKet first) (basisKet imageFirst) hPFirst,
        unitary_inv_mulVec_of_eq P (basisKet second) (basisKet imageSecond) hPSecond,
        twoLevelUnitary_mulVec_basisKet_second]
    · have hzeroFirst :
          ((P : Matrix ι ι ℂ) *ᵥ basisKet input) imageFirst = 0 :=
        unitary_basisImage_row_eq_zero P first imageFirst input hPFirst hinputFirst
      have hzeroSecond :
          ((P : Matrix ι ι ℂ) *ᵥ basisKet input) imageSecond = 0 :=
        unitary_basisImage_row_eq_zero P second imageSecond input hPSecond hinputSecond
      rw [twoLevelUnitary_mulVec_eq_self_of_pair_zero imageFirst imageSecond himage U
        ((P : Matrix ι ι ℂ) *ᵥ basisKet input) hzeroFirst hzeroSecond]
      rw [unitary_inv_mulVec_of_eq P (basisKet input)
        ((P : Matrix ι ι ℂ) *ᵥ basisKet input) rfl]
      rw [twoLevelUnitary_mulVec_basisKet_outside first second input hfirstSecond U
        hinputFirst hinputSecond]

end

end Barenco.Universality
