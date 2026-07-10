import Barenco.OneQubit.Certified
import Barenco.Controlled

/-!
# Bridge from Section 4's semantic Pauli-X to the controlled-gate core

The foundational controlled-gate layer already constructs Pauli-X as the
permutation matrix of Boolean negation.  Section 4 constructs the same matrix by
translating the paper's explicit display.  This narrow leaf proves that the two
certificates coincide without making the low-dependency one-qubit matrix module
import controlled-gate infrastructure.

All declarations in this leaf are public proof-side equalities of certified
matrices or their semantic register embeddings. No declaration constructs a
`Primitive` or `Circuit`, and no resource conclusion is drawn.
-/

namespace Barenco.OneQubit

/-- The explicit standard-column Pauli-X matrix equals the permutation matrix. -/
theorem sigmaX_eq_coe_pauliX : sigmaX = (Barenco.pauliX : QubitMatrix) := by
  ext row col
  cases row <;> cases col <;> rfl

/-- The two independently certified one-qubit Pauli-X gates are identical. -/
theorem sigmaXUnitary_eq_pauliX : sigmaXUnitary = Barenco.pauliX := by
  apply Subtype.ext
  exact sigmaX_eq_coe_pauliX

/-- Embedding either Pauli-X certificate gives the same semantic register gate. -/
theorem localUnitary_sigmaX_eq_xUnitary {n : ℕ} (target : Fin n) :
    localUnitary target sigmaXUnitary = xUnitary target := by
  rw [sigmaXUnitary_eq_pauliX]
  rfl

end Barenco.OneQubit
