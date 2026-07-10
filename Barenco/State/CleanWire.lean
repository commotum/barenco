import Barenco.Controlled

/-!
# States with one fixed computational-basis wire

An auxiliary wire initialized to a basis bit does not range over the whole
register state space.  Its valid inputs form the subspace of amplitude functions
supported on basis assignments carrying that bit.  This file packages that
subspace, identifies it linearly with the state space on the complementary wires,
and proves that a controlled gate targeting another wire preserves it.

The factorization equivalence is exact linear algebra.  It does not assume state
normalization and does not identify states up to phase.  In particular, membership
in `cleanZeroSubspace wire` literally says that the fixed wire factors as `|0⟩`
from an otherwise arbitrary state on all complementary wires.
-/

namespace Barenco

open Matrix

/-! ## Extending basis-column equalities to supported states -/

/--
Two matrices act equally on a vector when their basis columns agree everywhere
that the vector can have nonzero amplitude.

The row type is deliberately independent of the finite column type, so this is
usable for rectangular matrices as well as full-register gates.
-/
theorem mulVec_eq_of_basisKet_eq_on_support
    {ι ρ : Type*} [Fintype ι] [DecidableEq ι]
    (U V : Matrix ρ ι ℂ) (ψ : ι → ℂ) (supported : ι → Prop)
    (hψ : ∀ i, ¬supported i → ψ i = 0)
    (hbasis : ∀ i, supported i → U *ᵥ basisKet i = V *ᵥ basisKet i) :
    U *ᵥ ψ = V *ᵥ ψ := by
  funext row
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : supported i
  · have hentry := congrFun (hbasis i hi) row
    simp only [mulVec_basisKet_apply] at hentry
    rw [hentry]
  · rw [hψ i hi, mul_zero, mul_zero]

/-! ## Fixed-wire subspaces -/

/--
States supported only on computational-basis assignments where `wire` equals
`bit`.
-/
def fixedWireSubspace {n : ℕ} (wire : Fin n) (bit : Bool) :
    Submodule ℂ (State n) where
  carrier := {ψ | ∀ x, x wire ≠ bit → ψ x = 0}
  zero_mem' := by
    intro x _
    rfl
  add_mem' := by
    intro ψ φ hψ hφ x hx
    simp [hψ x hx, hφ x hx]
  smul_mem' := by
    intro c ψ hψ x hx
    simp [hψ x hx]

@[simp]
theorem mem_fixedWireSubspace_iff {n : ℕ} (wire : Fin n) (bit : Bool)
    (ψ : State n) :
    ψ ∈ fixedWireSubspace wire bit ↔
      ∀ x, x wire ≠ bit → ψ x = 0 :=
  Iff.rfl

/-- States whose designated wire is cleanly initialized to zero. -/
def cleanZeroSubspace {n : ℕ} (wire : Fin n) : Submodule ℂ (State n) :=
  fixedWireSubspace wire false

@[simp]
theorem mem_cleanZeroSubspace_iff {n : ℕ} (wire : Fin n) (ψ : State n) :
    ψ ∈ cleanZeroSubspace wire ↔
      ∀ x, x wire = true → ψ x = 0 := by
  constructor
  · intro h x hx
    exact h x (by simp [hx])
  · intro h x hx
    cases hbit : x wire
    · exact (hx hbit).elim
    · exact h x hbit

/-! ## Removing and reinserting the fixed wire -/

/--
Insert a complementary-wire amplitude function into the full register while
fixing `wire` to `bit`.
-/
def fixedWireEmbed {n : ℕ} (wire : Fin n) (bit : Bool) :
    (ComplementBasis wire → ℂ) →ₗ[ℂ] State n where
  toFun ψ x :=
    if (splitTarget wire x).1 = bit then
      ψ (splitTarget wire x).2
    else 0
  map_add' := by
    intro ψ φ
    funext x
    change (if x wire = bit then
        ψ (splitTarget wire x).2 + φ (splitTarget wire x).2 else 0) =
      (if x wire = bit then ψ (splitTarget wire x).2 else 0) +
        if x wire = bit then φ (splitTarget wire x).2 else 0
    by_cases hx : x wire = bit <;> simp [hx]
  map_smul' := by
    intro c ψ
    funext x
    change (if x wire = bit then c * ψ (splitTarget wire x).2 else 0) =
      c * if x wire = bit then ψ (splitTarget wire x).2 else 0
    by_cases hx : x wire = bit <;> simp [hx]

@[simp]
theorem fixedWireEmbed_apply {n : ℕ} (wire : Fin n) (bit : Bool)
    (ψ : ComplementBasis wire → ℂ) (x : Basis n) :
    fixedWireEmbed wire bit ψ x =
      if x wire = bit then ψ (splitTarget wire x).2 else 0 :=
  rfl

/-- Read a full-register state only on assignments where `wire` equals `bit`. -/
def fixedWireRestrict {n : ℕ} (wire : Fin n) (bit : Bool) :
    State n →ₗ[ℂ] (ComplementBasis wire → ℂ) where
  toFun ψ rest := ψ ((splitTarget wire).symm (bit, rest))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem fixedWireRestrict_apply {n : ℕ} (wire : Fin n) (bit : Bool)
    (ψ : State n) (rest : ComplementBasis wire) :
    fixedWireRestrict wire bit ψ rest =
      ψ ((splitTarget wire).symm (bit, rest)) :=
  rfl

/-- Reinserting a reduced state always lands in the fixed-wire subspace. -/
theorem fixedWireEmbed_mem {n : ℕ} (wire : Fin n) (bit : Bool)
    (ψ : ComplementBasis wire → ℂ) :
    fixedWireEmbed wire bit ψ ∈ fixedWireSubspace wire bit := by
  rw [mem_fixedWireSubspace_iff]
  intro x hx
  simp [fixedWireEmbed_apply, hx]

/-- Restriction after fixed-wire embedding is literally the original state. -/
@[simp]
theorem fixedWireRestrict_embed {n : ℕ} (wire : Fin n) (bit : Bool)
    (ψ : ComplementBasis wire → ℂ) :
    fixedWireRestrict wire bit (fixedWireEmbed wire bit ψ) = ψ := by
  funext rest
  change (if
      (splitTarget wire ((splitTarget wire).symm (bit, rest))).1 = bit then
        ψ (splitTarget wire ((splitTarget wire).symm (bit, rest))).2
      else 0) = ψ rest
  rw [Equiv.apply_symm_apply]
  simp

/--
Embedding the restriction of a supported state literally reconstructs the full
state.  This is the fixed-wire factorization statement used for clean ancillas.
-/
theorem fixedWireEmbed_restrict {n : ℕ} (wire : Fin n) (bit : Bool)
    (ψ : State n) (hψ : ψ ∈ fixedWireSubspace wire bit) :
    fixedWireEmbed wire bit (fixedWireRestrict wire bit ψ) = ψ := by
  funext x
  by_cases hx : x wire = bit
  · have hrebuild :
        (splitTarget wire).symm (bit, (splitTarget wire x).2) = x := by
      apply (splitTarget wire).injective
      rw [Equiv.apply_symm_apply]
      apply Prod.ext
      · exact hx.symm
      · rfl
    simp [fixedWireEmbed_apply, fixedWireRestrict_apply, hx, hrebuild]
  · have hzero := (mem_fixedWireSubspace_iff wire bit ψ).mp hψ x hx
    simp [fixedWireEmbed_apply, hx, hzero]

/--
Removing a fixed wire is a linear equivalence from complementary-wire states to
the corresponding supported full-register states.
-/
def fixedWireLinearEquiv {n : ℕ} (wire : Fin n) (bit : Bool) :
    (ComplementBasis wire → ℂ) ≃ₗ[ℂ] fixedWireSubspace wire bit where
  toFun ψ := ⟨fixedWireEmbed wire bit ψ, fixedWireEmbed_mem wire bit ψ⟩
  invFun ψ := fixedWireRestrict wire bit ψ
  left_inv := fixedWireRestrict_embed wire bit
  right_inv := by
    intro ψ
    apply Subtype.ext
    exact fixedWireEmbed_restrict wire bit ψ ψ.property
  map_add' := by
    intro ψ φ
    apply Subtype.ext
    exact (fixedWireEmbed wire bit).map_add ψ φ
  map_smul' := by
    intro c ψ
    apply Subtype.ext
    exact (fixedWireEmbed wire bit).map_smul c ψ

@[simp]
theorem coe_fixedWireLinearEquiv_apply {n : ℕ} (wire : Fin n) (bit : Bool)
    (ψ : ComplementBasis wire → ℂ) :
    ((fixedWireLinearEquiv wire bit ψ : fixedWireSubspace wire bit) : State n) =
      fixedWireEmbed wire bit ψ :=
  rfl

@[simp]
theorem fixedWireLinearEquiv_symm_apply {n : ℕ} (wire : Fin n) (bit : Bool)
    (ψ : fixedWireSubspace wire bit) :
    (fixedWireLinearEquiv wire bit).symm ψ = fixedWireRestrict wire bit ψ :=
  rfl

/-- Literal factorization of every fixed-wire state through the linear equivalence. -/
theorem fixedWireSubspace_factorization {n : ℕ} (wire : Fin n) (bit : Bool)
    (ψ : fixedWireSubspace wire bit) :
    (ψ : State n) =
      fixedWireEmbed wire bit ((fixedWireLinearEquiv wire bit).symm ψ) := by
  rw [fixedWireLinearEquiv_symm_apply]
  exact (fixedWireEmbed_restrict wire bit ψ ψ.property).symm

/-- The fixed-wire equivalence specialized to a clean-zero auxiliary wire. -/
def cleanZeroLinearEquiv {n : ℕ} (wire : Fin n) :
    (ComplementBasis wire → ℂ) ≃ₗ[ℂ] cleanZeroSubspace wire :=
  fixedWireLinearEquiv wire false

/-! ## Preservation by controlled gates targeting another wire -/

/-- A raw controlled one-qubit matrix preserves every fixed non-target wire. -/
theorem controlledRaw_mulVec_mem_fixedWireSubspace {n : ℕ}
    (wire target : Fin n) (hwireTarget : wire ≠ target) (bit : Bool)
    (enabled : ComplementBasis target → Bool) (U : QubitMatrix)
    (ψ : State n) (hψ : ψ ∈ fixedWireSubspace wire bit) :
    controlledRaw target enabled U *ᵥ ψ ∈ fixedWireSubspace wire bit := by
  rw [mem_fixedWireSubspace_iff] at hψ ⊢
  intro row hrow
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro x _
  by_cases hx : x wire = bit
  · have hchanged : row wire ≠ x wire := by
      intro heq
      exact hrow (heq.trans hx)
    have hzero := controlledRaw_mulVec_basisKet_eq_zero_of_changed
      target enabled U wire hwireTarget hchanged
    have hentry : controlledRaw target enabled U row x = 0 := by
      simpa only [mulVec_basisKet_apply] using hzero
    rw [hentry, zero_mul]
  · rw [hψ x hx, mul_zero]

/-- A raw positive-controlled one-qubit matrix preserves every fixed non-target wire. -/
theorem positiveControlledRaw_mulVec_mem_fixedWireSubspace {n : ℕ}
    (wire target : Fin n) (hwireTarget : wire ≠ target) (bit : Bool)
    (controls : ControlSet target) (U : QubitMatrix)
    (ψ : State n) (hψ : ψ ∈ fixedWireSubspace wire bit) :
    positiveControlledRaw target controls U *ᵥ ψ ∈
      fixedWireSubspace wire bit := by
  exact controlledRaw_mulVec_mem_fixedWireSubspace wire target hwireTarget bit
    (positiveControlsEnabled controls) U ψ hψ

/-- A certified positive-controlled gate preserves every fixed non-target wire. -/
theorem positiveControlledUnitary_mulVec_mem_fixedWireSubspace {n : ℕ}
    (wire target : Fin n) (hwireTarget : wire ≠ target) (bit : Bool)
    (controls : ControlSet target) (U : QubitUnitary)
    (ψ : State n) (hψ : ψ ∈ fixedWireSubspace wire bit) :
    (positiveControlledUnitary target controls U : Gate n) *ᵥ ψ ∈
      fixedWireSubspace wire bit := by
  rw [coe_positiveControlledUnitary]
  exact positiveControlledRaw_mulVec_mem_fixedWireSubspace wire target
    hwireTarget bit controls U ψ hψ

/-- Raw positive-controlled gates preserve a clean-zero non-target wire. -/
theorem positiveControlledRaw_mulVec_mem_cleanZeroSubspace {n : ℕ}
    (wire target : Fin n) (hwireTarget : wire ≠ target)
    (controls : ControlSet target) (U : QubitMatrix)
    (ψ : State n) (hψ : ψ ∈ cleanZeroSubspace wire) :
    positiveControlledRaw target controls U *ᵥ ψ ∈ cleanZeroSubspace wire := by
  exact positiveControlledRaw_mulVec_mem_fixedWireSubspace wire target
    hwireTarget false controls U ψ hψ

/-- Certified positive-controlled gates preserve a clean-zero non-target wire. -/
theorem positiveControlledUnitary_mulVec_mem_cleanZeroSubspace {n : ℕ}
    (wire target : Fin n) (hwireTarget : wire ≠ target)
    (controls : ControlSet target) (U : QubitUnitary)
    (ψ : State n) (hψ : ψ ∈ cleanZeroSubspace wire) :
    (positiveControlledUnitary target controls U : Gate n) *ᵥ ψ ∈
      cleanZeroSubspace wire := by
  exact positiveControlledUnitary_mulVec_mem_fixedWireSubspace wire target
    hwireTarget false controls U ψ hψ

end Barenco
