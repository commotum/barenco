import Barenco.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Checked mathlib API probes

These examples pin the exact declarations and orientations selected during
`1-GUARDRAILS`. They are deliberately generic and contain no project axioms.
-/

namespace Barenco.ApiSmoke

open Matrix
open scoped Kronecker

universe u v

variable {ι : Type u} {κ : Type v}
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The identity matrix packages directly as a certified unitary. -/
example : Matrix.unitaryGroup ι ℂ := 1

/-- The Kronecker product API preserves certified matrix unitarity. -/
example (U : Matrix.unitaryGroup ι ℂ) (V : Matrix.unitaryGroup κ ℂ) :
    ((U : Matrix ι ι ℂ) ⊗ₖ (V : Matrix κ κ ℂ)) ∈
      Matrix.unitaryGroup (ι × κ) ℂ := by
  exact Matrix.kronecker_mem_unitary U.property V.property

/-- Reindexing through one equivalence preserves matrix multiplication. -/
example (e : ι ≃ κ) (A B : Matrix ι ι ℂ) :
    Matrix.reindexAlgEquiv ℂ ℂ e (A * B) =
      Matrix.reindexAlgEquiv ℂ ℂ e A * Matrix.reindexAlgEquiv ℂ ℂ e B := by
  exact map_mul (Matrix.reindexAlgEquiv ℂ ℂ e) A B

/-- `permMatrix` acts by composing a vector with the permutation itself. -/
example (σ : Equiv.Perm ι) (v : ι → ℂ) : σ.permMatrix ℂ *ᵥ v = v ∘ σ := by
  exact Matrix.permMatrix_mulVec (σ := σ) (v := v)

/-- Existing API splits selected wires from their complement. -/
example (p : ι → Prop) [DecidablePred p] :
    (ι → Bool) ≃
      ({i : ι // p i} → Bool) × ({i : ι // ¬p i} → Bool) :=
  Equiv.piEquivPiSubtypeProd p (fun _ => Bool)

section L2OperatorNorm

open scoped Matrix.Norms.L2Operator

/-- The selected L² operator norm is submultiplicative. -/
example (A B : Matrix ι ι ℂ) : ‖A * B‖ ≤ ‖A‖ * ‖B‖ := by
  exact Matrix.l2_opNorm_mul A B

end L2OperatorNorm

end Barenco.ApiSmoke
