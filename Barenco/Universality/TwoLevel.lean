import Barenco.Semantics

/-!
# Certified two-level unitaries

A two-level unitary acts by an ordered `U(2)` block on two distinct indices and
by the identity on every other index.  The order matters: `first` is the
`false` row and column of the one-qubit block, while `second` is the `true` row
and column.

The construction is genuinely finite-dimensional and independent of circuit
syntax.  It first forms `U ⊕ I` on the explicit sum of the ordered pair and
its complement, then transports both matrix indices along an equivalence with
the ambient finite type.  Entry and basis-ket theorems below expose the exact
orientation needed by later synthesis proofs.
-/

namespace Barenco.Universality

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The indices outside an ordered pair. -/
abbrev TwoLevelComplement (first second : ι) :=
  {index : ι // index ≠ first ∧ index ≠ second}

/--
Split an ambient index type into the ordered pair `first, second` and its
complement.  `false` names `first` and `true` names `second`.
-/
def twoLevelIndexEquiv (first second : ι) (hfirstSecond : first ≠ second) :
    Bool ⊕ TwoLevelComplement first second ≃ ι where
  toFun
    | Sum.inl false => first
    | Sum.inl true => second
    | Sum.inr index => index
  invFun index :=
    if hfirst : index = first then Sum.inl false
    else if hsecond : index = second then Sum.inl true
    else Sum.inr ⟨index, hfirst, hsecond⟩
  left_inv := by
    rintro (bit | ⟨index, hfirst, hsecond⟩)
    · cases bit <;> simp [hfirstSecond.symm]
    · simp [hfirst, hsecond]
  right_inv := by
    intro index
    by_cases hfirst : index = first
    · simp [hfirst]
    · by_cases hsecond : index = second
      · simp [hsecond, hfirstSecond.symm]
      · simp [hfirst, hsecond]

omit [Fintype ι] in
@[simp]
theorem twoLevelIndexEquiv_inl_false (first second : ι)
    (hfirstSecond : first ≠ second) :
    twoLevelIndexEquiv first second hfirstSecond (Sum.inl false) = first :=
  rfl

omit [Fintype ι] in
@[simp]
theorem twoLevelIndexEquiv_inl_true (first second : ι)
    (hfirstSecond : first ≠ second) :
    twoLevelIndexEquiv first second hfirstSecond (Sum.inl true) = second :=
  rfl

omit [Fintype ι] in
@[simp]
theorem twoLevelIndexEquiv_inr (first second : ι)
    (hfirstSecond : first ≠ second) (index : TwoLevelComplement first second) :
    twoLevelIndexEquiv first second hfirstSecond (Sum.inr index) = index :=
  rfl

omit [Fintype ι] in
@[simp]
theorem twoLevelIndexEquiv_symm_first (first second : ι)
    (hfirstSecond : first ≠ second) :
    (twoLevelIndexEquiv first second hfirstSecond).symm first = Sum.inl false := by
  simp [twoLevelIndexEquiv]

omit [Fintype ι] in
@[simp]
theorem twoLevelIndexEquiv_symm_second (first second : ι)
    (hfirstSecond : first ≠ second) :
    (twoLevelIndexEquiv first second hfirstSecond).symm second = Sum.inl true := by
  simp [twoLevelIndexEquiv, hfirstSecond.symm]

omit [Fintype ι] in
@[simp]
theorem twoLevelIndexEquiv_symm_outside (first second index : ι)
    (hfirstSecond : first ≠ second) (hindexFirst : index ≠ first)
    (hindexSecond : index ≠ second) :
    (twoLevelIndexEquiv first second hfirstSecond).symm index =
      Sum.inr ⟨index, hindexFirst, hindexSecond⟩ := by
  simp [twoLevelIndexEquiv, hindexFirst, hindexSecond]

/-- The certified block sum `U ⊕ I` before ambient-index transport. -/
def twoLevelBlockUnitary (U : QubitUnitary)
    (κ : Type*) [Fintype κ] [DecidableEq κ] :
    Matrix.unitaryGroup (Bool ⊕ κ) ℂ :=
  ⟨Matrix.fromBlocks (U : QubitMatrix) 0 0 (1 : Matrix κ κ ℂ), by
    have hU : (U : QubitMatrix)ᴴ * (U : QubitMatrix) = 1 := by
      have hUnitary : star (U : QubitMatrix) * (U : QubitMatrix) = 1 :=
        (Matrix.mem_unitaryGroup_iff').1 U.property
      simpa only [Matrix.star_eq_conjTranspose] using hUnitary
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
      Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
    simp [hU]⟩

@[simp]
theorem coe_twoLevelBlockUnitary (U : QubitUnitary)
    (κ : Type*) [Fintype κ] [DecidableEq κ] :
    (twoLevelBlockUnitary U κ : Matrix (Bool ⊕ κ) (Bool ⊕ κ) ℂ) =
      Matrix.fromBlocks (U : QubitMatrix) 0 0 1 :=
  rfl

@[simp]
theorem twoLevelBlockUnitary_one (κ : Type*) [Fintype κ] [DecidableEq κ] :
    twoLevelBlockUnitary (1 : QubitUnitary) κ = 1 := by
  apply Subtype.ext
  exact Matrix.fromBlocks_one

@[simp]
theorem twoLevelBlockUnitary_mul (U V : QubitUnitary)
    (κ : Type*) [Fintype κ] [DecidableEq κ] :
    twoLevelBlockUnitary (U * V) κ =
      twoLevelBlockUnitary U κ * twoLevelBlockUnitary V κ := by
  apply Subtype.ext
  change Matrix.fromBlocks
      ((U : QubitMatrix) * (V : QubitMatrix)) 0 0 1 =
    Matrix.fromBlocks (U : QubitMatrix) 0 0 1 *
      Matrix.fromBlocks (V : QubitMatrix) 0 0 1
  rw [Matrix.fromBlocks_multiply]
  simp

/-- The multiplicative embedding `U ↦ U ⊕ I`. -/
def twoLevelBlockEmbedding (κ : Type*) [Fintype κ] [DecidableEq κ] :
    QubitUnitary →* Matrix.unitaryGroup (Bool ⊕ κ) ℂ where
  toFun U := twoLevelBlockUnitary U κ
  map_one' := twoLevelBlockUnitary_one κ
  map_mul' U V := twoLevelBlockUnitary_mul U V κ

/-- Transporting `U ⊕ I` gives a multiplicative embedding into the ambient type. -/
def twoLevelEmbedding (first second : ι) (hfirstSecond : first ≠ second) :
    QubitUnitary →* Matrix.unitaryGroup ι ℂ :=
  (reindexUnitaryEquiv (twoLevelIndexEquiv first second hfirstSecond)).toMonoidHom.comp
    (twoLevelBlockEmbedding (TwoLevelComplement first second))

/--
Embed an ordered one-qubit block into two distinct indices of an arbitrary
finite type, acting as identity on the complement.
-/
def twoLevelUnitary (first second : ι) (hfirstSecond : first ≠ second)
    (U : QubitUnitary) : Matrix.unitaryGroup ι ℂ :=
  reindexUnitary (twoLevelIndexEquiv first second hfirstSecond)
    (twoLevelBlockUnitary U (TwoLevelComplement first second))

@[simp]
theorem twoLevelUnitary_one (first second : ι) (hfirstSecond : first ≠ second) :
    twoLevelUnitary first second hfirstSecond (1 : QubitUnitary) = 1 := by
  simp [twoLevelUnitary]

@[simp]
theorem twoLevelUnitary_mul (first second : ι) (hfirstSecond : first ≠ second)
    (U V : QubitUnitary) :
    twoLevelUnitary first second hfirstSecond (U * V) =
      twoLevelUnitary first second hfirstSecond U *
        twoLevelUnitary first second hfirstSecond V := by
  simp [twoLevelUnitary]

@[simp]
theorem twoLevelUnitary_inv (first second : ι) (hfirstSecond : first ≠ second)
    (U : QubitUnitary) :
    twoLevelUnitary first second hfirstSecond U⁻¹ =
      (twoLevelUnitary first second hfirstSecond U)⁻¹ := by
  exact map_inv (twoLevelEmbedding first second hfirstSecond) U

/-- Which ordered-pair coordinate an ambient index occupies, if any. -/
def twoLevelCoordinate (first second index : ι) : Option Bool :=
  if index = first then some false
  else if index = second then some true
  else none

omit [Fintype ι] in
@[simp]
theorem twoLevelCoordinate_first (first second : ι) :
    twoLevelCoordinate first second first = some false := by
  simp [twoLevelCoordinate]

omit [Fintype ι] in
@[simp]
theorem twoLevelCoordinate_second (first second : ι) (hfirstSecond : first ≠ second) :
    twoLevelCoordinate first second second = some true := by
  simp [twoLevelCoordinate, hfirstSecond.symm]

omit [Fintype ι] in
@[simp]
theorem twoLevelCoordinate_outside (first second index : ι)
    (hindexFirst : index ≠ first) (hindexSecond : index ≠ second) :
    twoLevelCoordinate first second index = none := by
  simp [twoLevelCoordinate, hindexFirst, hindexSecond]

/-- Exact entry formula, including all off-pair identity entries. -/
theorem twoLevelUnitary_apply (first second : ι) (hfirstSecond : first ≠ second)
    (U : QubitUnitary) (row col : ι) :
    twoLevelUnitary first second hfirstSecond U row col =
      match twoLevelCoordinate first second row,
          twoLevelCoordinate first second col with
      | some localRow, some localCol => U localRow localCol
      | none, none => if row = col then 1 else 0
      | _, _ => 0 := by
  by_cases hrowFirst : row = first
  · subst row
    by_cases hcolFirst : col = first
    · subst col
      simp [twoLevelUnitary, twoLevelCoordinate]
    · by_cases hcolSecond : col = second
      · subst col
        simp [twoLevelUnitary, twoLevelCoordinate, hfirstSecond.symm]
      · simp [twoLevelUnitary, twoLevelCoordinate, hcolFirst,
          hcolSecond]
  · by_cases hrowSecond : row = second
    · subst row
      by_cases hcolFirst : col = first
      · subst col
        simp [twoLevelUnitary, twoLevelCoordinate, hfirstSecond.symm]
      · by_cases hcolSecond : col = second
        · subst col
          simp [twoLevelUnitary, twoLevelCoordinate, hfirstSecond.symm]
        · simp [twoLevelUnitary, twoLevelCoordinate,
            hfirstSecond.symm, hcolFirst, hcolSecond]
    · by_cases hcolFirst : col = first
      · subst col
        simp [twoLevelUnitary, twoLevelCoordinate, hrowFirst,
          hrowSecond]
      · by_cases hcolSecond : col = second
        · subst col
          simp [twoLevelUnitary, twoLevelCoordinate, hrowFirst,
            hrowSecond, hfirstSecond.symm]
        · simp [twoLevelUnitary, twoLevelCoordinate, hrowFirst,
            hrowSecond, hcolFirst, hcolSecond, Matrix.one_apply]

@[simp]
theorem twoLevelUnitary_first_first (first second : ι)
    (hfirstSecond : first ≠ second) (U : QubitUnitary) :
    twoLevelUnitary first second hfirstSecond U first first = U false false := by
  rw [twoLevelUnitary_apply]
  simp

@[simp]
theorem twoLevelUnitary_first_second (first second : ι)
    (hfirstSecond : first ≠ second) (U : QubitUnitary) :
    twoLevelUnitary first second hfirstSecond U first second = U false true := by
  rw [twoLevelUnitary_apply]
  simp [hfirstSecond]

@[simp]
theorem twoLevelUnitary_second_first (first second : ι)
    (hfirstSecond : first ≠ second) (U : QubitUnitary) :
    twoLevelUnitary first second hfirstSecond U second first = U true false := by
  rw [twoLevelUnitary_apply]
  simp [hfirstSecond]

@[simp]
theorem twoLevelUnitary_second_second (first second : ι)
    (hfirstSecond : first ≠ second) (U : QubitUnitary) :
    twoLevelUnitary first second hfirstSecond U second second = U true true := by
  rw [twoLevelUnitary_apply]
  simp [hfirstSecond]

@[simp]
theorem twoLevelUnitary_outside_outside (first second row col : ι)
    (hfirstSecond : first ≠ second) (U : QubitUnitary)
    (hrowFirst : row ≠ first) (hrowSecond : row ≠ second)
    (hcolFirst : col ≠ first) (hcolSecond : col ≠ second) :
    twoLevelUnitary first second hfirstSecond U row col =
      if row = col then 1 else 0 := by
  rw [twoLevelUnitary_apply]
  simp [hrowFirst, hrowSecond, hcolFirst, hcolSecond]

@[simp]
theorem twoLevelUnitary_pair_outside (first second row col : ι)
    (hfirstSecond : first ≠ second) (U : QubitUnitary)
    (hrow : row = first ∨ row = second)
    (hcolFirst : col ≠ first) (hcolSecond : col ≠ second) :
    twoLevelUnitary first second hfirstSecond U row col = 0 := by
  rw [twoLevelUnitary_apply]
  rcases hrow with rfl | rfl <;>
    simp [hfirstSecond, hcolFirst, hcolSecond]

@[simp]
theorem twoLevelUnitary_outside_pair (first second row col : ι)
    (hfirstSecond : first ≠ second) (U : QubitUnitary)
    (hrowFirst : row ≠ first) (hrowSecond : row ≠ second)
    (hcol : col = first ∨ col = second) :
    twoLevelUnitary first second hfirstSecond U row col = 0 := by
  rw [twoLevelUnitary_apply]
  rcases hcol with rfl | rfl <;>
    simp [hfirstSecond, hrowFirst, hrowSecond]

/-- Exact action on the first ordered basis ket (the `false` block column). -/
theorem twoLevelUnitary_mulVec_basisKet_first (first second : ι)
    (hfirstSecond : first ≠ second) (U : QubitUnitary) :
    (twoLevelUnitary first second hfirstSecond U : Matrix ι ι ℂ) *ᵥ basisKet first =
      U false false • basisKet first + U true false • basisKet second := by
  ext row
  rw [mulVec_basisKet_apply]
  by_cases hrowFirst : row = first
  · subst row
    simp [hfirstSecond]
  · by_cases hrowSecond : row = second
    · subst row
      simp [hfirstSecond.symm]
    · simp [twoLevelUnitary_outside_pair, hrowFirst, hrowSecond]

/-- Exact action on the second ordered basis ket (the `true` block column). -/
theorem twoLevelUnitary_mulVec_basisKet_second (first second : ι)
    (hfirstSecond : first ≠ second) (U : QubitUnitary) :
    (twoLevelUnitary first second hfirstSecond U : Matrix ι ι ℂ) *ᵥ basisKet second =
      U false true • basisKet first + U true true • basisKet second := by
  ext row
  rw [mulVec_basisKet_apply]
  by_cases hrowFirst : row = first
  · subst row
    simp [hfirstSecond]
  · by_cases hrowSecond : row = second
    · subst row
      simp [hfirstSecond.symm]
    · simp [twoLevelUnitary_outside_pair, hrowFirst, hrowSecond]

/-- Every basis ket outside the ordered pair is fixed exactly. -/
theorem twoLevelUnitary_mulVec_basisKet_outside (first second index : ι)
    (hfirstSecond : first ≠ second) (U : QubitUnitary)
    (hindexFirst : index ≠ first) (hindexSecond : index ≠ second) :
    (twoLevelUnitary first second hfirstSecond U : Matrix ι ι ℂ) *ᵥ basisKet index =
      basisKet index := by
  ext row
  rw [mulVec_basisKet_apply]
  by_cases hrowFirst : row = first
  · subst row
    simp [twoLevelUnitary_pair_outside, hindexFirst, hindexFirst.symm,
      hindexSecond]
  · by_cases hrowSecond : row = second
    · subst row
      simp [twoLevelUnitary_pair_outside, hindexFirst, hindexSecond,
        hindexSecond.symm]
    · rw [twoLevelUnitary_outside_outside first second row index hfirstSecond U
        hrowFirst hrowSecond hindexFirst hindexSecond]
      simp [basisKet_apply]

end Barenco.Universality
