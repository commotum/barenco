import Barenco.OneQubit.Euler

/-!
# Existential A/B/C decomposition (Barenco et al., Lemma 4.3)

`Decomposition.lean` proves the parameterized identities.  This leaf supplies the
existential consequence using the independently proved Euler theorem.

Two statements are kept distinct.  The first is the paper's raw row-action matrix
identity `A B C = I` and `A X B X C = W`.  The second translates the same factors
to standard-column gates and states the reversed products that a chronological
list of column-vector matrices evaluates. Both declarations are public proof-side
API. They quantify over certified special-unitary matrices but do not construct a
`Circuit`, count primitives, or establish any other resource claim.
-/

namespace Barenco.OneQubit

noncomputable section

/-- The paper-row algebraic statement of Lemma 4.3. -/
theorem specialUnitary_exists_paperABC (W : QubitSpecialUnitary) :
    ∃ A B C : QubitSpecialUnitary,
      (A : QubitMatrix) * (B : QubitMatrix) * (C : QubitMatrix) = 1 ∧
        (A : QubitMatrix) * paperX * (B : QubitMatrix) * paperX *
          (C : QubitMatrix) = (W : QubitMatrix) := by
  obtain ⟨alpha, theta, beta, _htheta, hEuler⟩ :=
    specialUnitary_exists_paperEuler W
  refine ⟨paperASpecialUnitary alpha theta,
    paperBSpecialUnitary alpha theta beta,
    paperCSpecialUnitary alpha beta, ?_, ?_⟩
  · exact paperA_mul_paperB_mul_paperC alpha theta beta
  · exact (paperA_mul_X_mul_paperB_mul_X_mul_paperC alpha theta beta).trans
      hEuler.symm

/--
Standard-column chronological form of Lemma 4.3.  Here `A` is applied first and
`C` last, so the semantic matrix products are `C B A` and `C X B X A`. This is an
existential matrix equality, not a syntactic circuit construction.
-/
theorem specialUnitary_exists_columnChronologicalABC (W : QubitSpecialUnitary) :
    ∃ A B C : QubitSpecialUnitary,
      (C : QubitMatrix) * (B : QubitMatrix) * (A : QubitMatrix) = 1 ∧
        (C : QubitMatrix) * sigmaX * (B : QubitMatrix) * sigmaX *
          (A : QubitMatrix) = (W : QubitMatrix) := by
  obtain ⟨alpha, theta, beta, _htheta, hEuler⟩ :=
    specialUnitary_exists_columnEuler W
  refine ⟨columnASpecialUnitary alpha theta,
    columnBSpecialUnitary alpha theta beta,
    columnCSpecialUnitary alpha beta, ?_, ?_⟩
  · simpa only [coe_columnASpecialUnitary, coe_columnBSpecialUnitary,
      coe_columnCSpecialUnitary] using
        columnC_mul_columnB_mul_columnA alpha theta beta
  · have hactive :=
      (columnC_mul_X_mul_columnB_mul_X_mul_columnA alpha theta beta).trans
        hEuler.symm
    simpa only [coe_columnASpecialUnitary, coe_columnBSpecialUnitary,
      coe_columnCSpecialUnitary] using hactive

end

end Barenco.OneQubit
