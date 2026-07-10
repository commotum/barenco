import Barenco.OneQubit.Lemma43

/-!
# Selected column-chronological A/B/C factors

Barenco Lemma 4.3 supplies three special-unitary factors existentially.  This
leaf packages one fixed choice for later circuit constructors while retaining
the exact standard-column equations.  The selected factors are noncomputable
only because the underlying Euler decomposition is selected classically.
-/

namespace Barenco.OneQubit

noncomputable section

/--
Certified column-chronological Lemma 4.3 factors for a special unitary `W`.

Applying `A` first and `C` last gives the inactive product `C * B * A` and the
active product `C * X * B * X * A`.
-/
structure ColumnABCFactors (W : QubitSpecialUnitary) where
  A : QubitSpecialUnitary
  B : QubitSpecialUnitary
  C : QubitSpecialUnitary
  inactive :
    (C : QubitMatrix) * (B : QubitMatrix) * (A : QubitMatrix) = 1
  active :
    (C : QubitMatrix) * sigmaX * (B : QubitMatrix) * sigmaX *
      (A : QubitMatrix) = (W : QubitMatrix)

private theorem nonempty_columnABCFactors (W : QubitSpecialUnitary) :
    Nonempty (ColumnABCFactors W) := by
  obtain ⟨A, B, C, hinactive, hactive⟩ :=
    specialUnitary_exists_columnChronologicalABC W
  exact ⟨⟨A, B, C, hinactive, hactive⟩⟩

/-- One fixed checked choice of the column-chronological Lemma 4.3 factors. -/
def selectedColumnABCFactors (W : QubitSpecialUnitary) : ColumnABCFactors W :=
  Classical.choice (nonempty_columnABCFactors W)

/-- The selected factors have exact identity product on the inactive branch. -/
@[simp]
theorem selectedColumnABCFactors_inactive (W : QubitSpecialUnitary) :
    ((selectedColumnABCFactors W).C : QubitMatrix) *
        ((selectedColumnABCFactors W).B : QubitMatrix) *
        ((selectedColumnABCFactors W).A : QubitMatrix) = 1 :=
  (selectedColumnABCFactors W).inactive

/-- The selected factors have exact `W` product on the active branch. -/
@[simp]
theorem selectedColumnABCFactors_active (W : QubitSpecialUnitary) :
    ((selectedColumnABCFactors W).C : QubitMatrix) * sigmaX *
        ((selectedColumnABCFactors W).B : QubitMatrix) * sigmaX *
        ((selectedColumnABCFactors W).A : QubitMatrix) = (W : QubitMatrix) :=
  (selectedColumnABCFactors W).active

end


end Barenco.OneQubit
