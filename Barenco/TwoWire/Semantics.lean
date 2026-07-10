import Barenco.TwoWire.Layout
import Barenco.Semantics

/-!
# Certified two-wire gate semantics

This module embeds a raw or certified two-qubit matrix on any ordered pair of
distinct wires in an ambient register.  The embedding splits the selected pair
from its spectators, applies `U ⊗ I`, and reindexes back to the ambient basis.
Consequently every locality statement below is derived from the embedding rather
than asserted as support metadata.

For `pair`, local bit `0` is `pair.first` and local bit `1` is
`pair.second`; the local basis order is therefore `00, 01, 10, 11`.
Reversing the ordered pair reindexes the local matrix by the explicit two-bit
swap.  All equalities are exact: no scalar phase is discarded.
-/

namespace Barenco

open Matrix
open scoped Kronecker

/-- Raw two-qubit matrix in local basis order `00,01,10,11`. -/
abbrev TwoQubitMatrix := Gate 2

/-- Certified two-qubit unitary in local basis order `00,01,10,11`. -/
abbrev TwoQubitUnitary := UnitaryGate 2

/-- Embed a raw two-qubit matrix on an ordered ambient wire pair. -/
def twoWireRaw {n : ℕ} (pair : OrderedWirePair n)
    (U : TwoQubitMatrix) : Gate n :=
  Matrix.reindexAlgEquiv ℂ ℂ (splitTwoWire pair).symm
    (U ⊗ₖ (1 : Matrix (PairComplementBasis pair)
      (PairComplementBasis pair) ℂ))

/-- Embed a certified two-qubit unitary on an ordered ambient wire pair. -/
def twoWireUnitary {n : ℕ} (pair : OrderedWirePair n)
    (U : TwoQubitUnitary) : UnitaryGate n :=
  reindexUnitary (splitTwoWire pair).symm
    (kroneckerUnitary U (1 : Matrix.unitaryGroup
      (PairComplementBasis pair) ℂ))

@[simp]
theorem coe_twoWireUnitary {n : ℕ} (pair : OrderedWirePair n)
    (U : TwoQubitUnitary) :
    (twoWireUnitary pair U : Gate n) = twoWireRaw pair U := rfl

/-- Exact full-register entry formula. -/
@[simp]
theorem twoWireRaw_apply {n : ℕ} (pair : OrderedWirePair n)
    (U : TwoQubitMatrix) (row col : Basis n) :
    twoWireRaw pair U row col =
      if AgreeOffTwoWire pair row col then
        U (twoWireLocalBits pair row) (twoWireLocalBits pair col)
      else 0 := by
  change U (twoWireLocalBits pair row) (twoWireLocalBits pair col) *
      (1 : Matrix (PairComplementBasis pair) (PairComplementBasis pair) ℂ)
        (splitTwoWire pair row).2 (splitTwoWire pair col).2 = _
  rw [Matrix.one_apply]
  simp only [splitTwoWire_snd_eq_iff]
  by_cases hagree : AgreeOffTwoWire pair row col <;> simp [hagree]

/-- Exact full-register entry formula for the certified embedding. -/
@[simp]
theorem twoWireUnitary_apply {n : ℕ} (pair : OrderedWirePair n)
    (U : TwoQubitUnitary) (row col : Basis n) :
    twoWireUnitary pair U row col =
      if AgreeOffTwoWire pair row col then
        U (twoWireLocalBits pair row) (twoWireLocalBits pair col)
      else 0 := by
  change twoWireRaw pair U row col = _
  exact twoWireRaw_apply pair U row col

/-- A basis column has support only on rows with unchanged spectators. -/
theorem twoWireRaw_mulVec_basisKet {n : ℕ} (pair : OrderedWirePair n)
    (U : TwoQubitMatrix) (input : Basis n) :
    twoWireRaw pair U *ᵥ basisKet input = fun row =>
      if AgreeOffTwoWire pair row input then
        U (twoWireLocalBits pair row) (twoWireLocalBits pair input)
      else 0 := by
  funext row
  rw [mulVec_basisKet_apply, twoWireRaw_apply]

/-- Selected output-pair amplitude of a basis column. -/
@[simp]
theorem twoWireRaw_mulVec_basisKet_setTwoWire {n : ℕ}
    (pair : OrderedWirePair n) (U : TwoQubitMatrix)
    (input : Basis n) (output : Basis 2) :
    (twoWireRaw pair U *ᵥ basisKet input)
        (setTwoWire pair input output) =
      U output (twoWireLocalBits pair input) := by
  rw [twoWireRaw_mulVec_basisKet]
  change (if AgreeOffTwoWire pair (setTwoWire pair input output) input then
      U (twoWireLocalBits pair (setTwoWire pair input output))
        (twoWireLocalBits pair input) else 0) = _
  rw [if_pos (agreeOffTwoWire_setTwoWire pair input output)]
  simp

/-- Changing any spectator makes the corresponding basis-column amplitude zero. -/
theorem twoWireRaw_mulVec_basisKet_eq_zero_of_changed {n : ℕ}
    (pair : OrderedWirePair n) (U : TwoQubitMatrix)
    (input row : Basis n) (wire : Fin n)
    (hfirst : wire ≠ pair.first) (hsecond : wire ≠ pair.second)
    (hchanged : row wire ≠ input wire) :
    (twoWireRaw pair U *ᵥ basisKet input) row = 0 := by
  rw [twoWireRaw_mulVec_basisKet]
  change (if AgreeOffTwoWire pair row input then
      U (twoWireLocalBits pair row) (twoWireLocalBits pair input) else 0) = 0
  rw [if_neg (fun hagree => hchanged (hagree wire hfirst hsecond))]

/-- Basis action as an explicit four-term superposition on the selected pair. -/
theorem twoWireRaw_mulVec_basisKet_eq_sum {n : ℕ}
    (pair : OrderedWirePair n) (U : TwoQubitMatrix) (input : Basis n) :
    twoWireRaw pair U *ᵥ basisKet input =
      ∑ output : Basis 2,
        U output (twoWireLocalBits pair input) •
          basisKet (setTwoWire pair input output) := by
  funext row
  rw [twoWireRaw_mulVec_basisKet]
  change (if AgreeOffTwoWire pair row input then
      U (twoWireLocalBits pair row) (twoWireLocalBits pair input) else 0) =
    ∑ output : Basis 2,
      (U output (twoWireLocalBits pair input) •
        basisKet (setTwoWire pair input output)) row
  by_cases hagree : AgreeOffTwoWire pair row input
  · rw [if_pos hagree]
    have heq :
        row = setTwoWire pair input (twoWireLocalBits pair row) :=
      (eq_setTwoWire_iff pair row input (twoWireLocalBits pair row)).2
        ⟨rfl, hagree⟩
    rw [Finset.sum_eq_single (twoWireLocalBits pair row)]
    · rw [Pi.smul_apply, basisKet_apply, if_pos heq]
      simp only [smul_eq_mul, mul_one]
    · intro output _ houtput
      rw [Pi.smul_apply, basisKet_apply]
      have hne : row ≠ setTwoWire pair input output := by
        intro hrow
        apply houtput
        rw [hrow, twoWireLocalBits_setTwoWire]
      simp [hne]
    · simp
  · rw [if_neg hagree]
    symm
    apply Finset.sum_eq_zero
    intro output _
    rw [Pi.smul_apply, basisKet_apply]
    have hne : row ≠ setTwoWire pair input output := by
      intro hrow
      apply hagree
      rw [hrow]
      exact agreeOffTwoWire_setTwoWire pair input output
    simp [hne]

/-- Arbitrary-state action depends only on the input amplitudes with the same spectators. -/
theorem twoWireRaw_mulVec {n : ℕ} (pair : OrderedWirePair n)
    (U : TwoQubitMatrix) (state : State n) (row : Basis n) :
    (twoWireRaw pair U *ᵥ state) row =
      ∑ inputLocal : Basis 2,
        U (twoWireLocalBits pair row) inputLocal *
          state (setTwoWire pair row inputLocal) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [← (splitTwoWire pair).symm.sum_comp
    (fun input => twoWireRaw pair U row input * state input)]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro inputLocal _
  rw [Finset.sum_eq_single (twoWireSpectatorBits pair row)]
  · simp only [splitTwoWire_symm_apply, twoWireRaw_apply,
      twoWireLocalBits_reconstructTwoWire]
    rw [if_pos]
    · rfl
    · rw [agreeOffTwoWire_iff_spectatorBits_eq,
        twoWireSpectatorBits_reconstructTwoWire]
  · intro spectators _ hspectators
    simp only [splitTwoWire_symm_apply, twoWireRaw_apply,
      twoWireLocalBits_reconstructTwoWire]
    rw [if_neg]
    · simp
    · rw [agreeOffTwoWire_iff_spectatorBits_eq,
        twoWireSpectatorBits_reconstructTwoWire]
      exact Ne.symm hspectators
  · simp

/-- Fixed-right-identity Kronecker preserves identity. -/
private theorem kroneckerUnitary_one_one (ι κ : Type*)
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] :
    kroneckerUnitary (1 : Matrix.unitaryGroup ι ℂ)
      (1 : Matrix.unitaryGroup κ ℂ) = 1 := by
  apply Subtype.ext
  exact Matrix.one_kronecker_one

/-- Fixed-right-identity Kronecker preserves multiplication. -/
private theorem kroneckerUnitary_mul_right_one {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (U V : Matrix.unitaryGroup ι ℂ) :
    kroneckerUnitary (U * V) (1 : Matrix.unitaryGroup κ ℂ) =
      kroneckerUnitary U 1 * kroneckerUnitary V 1 := by
  apply Subtype.ext
  change ((U : Matrix ι ι ℂ) * (V : Matrix ι ι ℂ)) ⊗ₖ
      (1 : Matrix κ κ ℂ) =
    ((U : Matrix ι ι ℂ) ⊗ₖ (1 : Matrix κ κ ℂ)) *
      ((V : Matrix ι ι ℂ) ⊗ₖ (1 : Matrix κ κ ℂ))
  rw [← Matrix.mul_kronecker_mul]
  simp

@[simp]
theorem twoWireUnitary_one {n : ℕ} (pair : OrderedWirePair n) :
    twoWireUnitary pair (1 : TwoQubitUnitary) = 1 := by
  rw [twoWireUnitary, kroneckerUnitary_one_one, reindexUnitary_one]

@[simp]
theorem twoWireUnitary_mul {n : ℕ} (pair : OrderedWirePair n)
    (U V : TwoQubitUnitary) :
    twoWireUnitary pair (U * V) =
      twoWireUnitary pair U * twoWireUnitary pair V := by
  rw [twoWireUnitary, kroneckerUnitary_mul_right_one, reindexUnitary_mul]
  rfl

/-- Embedding on a fixed ordered pair is a monoid homomorphism. -/
def twoWireEmbedding {n : ℕ} (pair : OrderedWirePair n) :
    TwoQubitUnitary →* UnitaryGate n where
  toFun := twoWireUnitary pair
  map_one' := twoWireUnitary_one pair
  map_mul' := twoWireUnitary_mul pair

@[simp]
theorem twoWireEmbedding_apply {n : ℕ} (pair : OrderedWirePair n)
    (U : TwoQubitUnitary) :
    twoWireEmbedding pair U = twoWireUnitary pair U := rfl

@[simp]
theorem twoWireUnitary_inv {n : ℕ} (pair : OrderedWirePair n)
    (U : TwoQubitUnitary) :
    twoWireUnitary pair U⁻¹ = (twoWireUnitary pair U)⁻¹ := by
  exact map_inv (twoWireEmbedding pair) U

/-- Raw identity law (derived from the certified identity theorem). -/
@[simp]
theorem twoWireRaw_one {n : ℕ} (pair : OrderedWirePair n) :
    twoWireRaw pair (1 : TwoQubitMatrix) = 1 := by
  change (twoWireUnitary pair (1 : TwoQubitUnitary) : Gate n) = 1
  rw [twoWireUnitary_one]
  rfl

/-- Raw multiplication law, valid without unitarity assumptions. -/
theorem twoWireRaw_mul {n : ℕ} (pair : OrderedWirePair n)
    (U V : TwoQubitMatrix) :
    twoWireRaw pair (U * V) = twoWireRaw pair U * twoWireRaw pair V := by
  let r := Matrix.reindexAlgEquiv ℂ ℂ (splitTwoWire pair).symm
  change r ((U * V) ⊗ₖ (1 : Matrix (PairComplementBasis pair)
      (PairComplementBasis pair) ℂ)) =
    r (U ⊗ₖ (1 : Matrix (PairComplementBasis pair)
      (PairComplementBasis pair) ℂ)) *
    r (V ⊗ₖ (1 : Matrix (PairComplementBasis pair)
      (PairComplementBasis pair) ℂ))
  rw [← map_mul]
  apply congrArg r
  rw [← Matrix.mul_kronecker_mul]
  simp

/-- Raw embedding commutes with matrix adjoints. -/
@[simp]
theorem twoWireRaw_star {n : ℕ} (pair : OrderedWirePair n)
    (U : TwoQubitMatrix) :
    twoWireRaw pair (star U) = star (twoWireRaw pair U) := by
  ext row col
  change twoWireRaw pair (star U) row col = star (twoWireRaw pair U col row)
  rw [twoWireRaw_apply, twoWireRaw_apply, Matrix.star_apply]
  by_cases hagree : AgreeOffTwoWire pair row col
  · have hreverse : AgreeOffTwoWire pair col row :=
      agreeOffTwoWire_symm hagree
    rw [if_pos hagree, if_pos hreverse]
  · have hreverse : ¬AgreeOffTwoWire pair col row :=
      fun h => hagree (agreeOffTwoWire_symm h)
    rw [if_neg hagree, if_neg hreverse]
    simp

/-- Explicit head-first chronology: `first` executes before `second`. -/
theorem twoWireUnitary_chronological {n : ℕ} (pair : OrderedWirePair n)
    (first second : TwoQubitUnitary) :
    twoWireUnitary pair second * twoWireUnitary pair first =
      twoWireUnitary pair (second * first) := by
  rw [twoWireUnitary_mul]

/-- The distinctness proof carried by the pair cannot affect raw semantics. -/
theorem twoWireRaw_mk_proof_irrel {n : ℕ} (first second : Fin n)
    (h h' : first ≠ second) (U : TwoQubitMatrix) :
    twoWireRaw (⟨first, second, h⟩ : OrderedWirePair n) U =
      twoWireRaw (⟨first, second, h'⟩ : OrderedWirePair n) U := by
  have hp : (⟨first, second, h⟩ : OrderedWirePair n) =
      ⟨first, second, h'⟩ := by
    ext <;> rfl
  rw [hp]

/-- Reversing ambient pair orientation reindexes the local matrix by the local swap. -/
theorem twoWireRaw_swap {n : ℕ} (pair : OrderedWirePair n)
    (U : TwoQubitMatrix) :
    twoWireRaw pair.swap U =
      twoWireRaw pair (Matrix.reindex reverseTwoQubitBasis
        reverseTwoQubitBasis U) := by
  ext row col
  simp only [twoWireRaw_apply]
  by_cases hagree : AgreeOffTwoWire pair row col
  · have hswap : AgreeOffTwoWire pair.swap row col :=
      (agreeOffTwoWire_swap_iff pair row col).2 hagree
    rw [if_pos hswap, if_pos hagree]
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
      reverseTwoQubitBasis_symm_apply, twoWireLocalBits_swap]
  · have hswap : ¬AgreeOffTwoWire pair.swap row col :=
      fun h => hagree ((agreeOffTwoWire_swap_iff pair row col).1 h)
    rw [if_neg hswap, if_neg hagree]

/-- Certified orientation law. -/
theorem twoWireUnitary_swap {n : ℕ} (pair : OrderedWirePair n)
    (U : TwoQubitUnitary) :
    twoWireUnitary pair.swap U =
      twoWireUnitary pair (reindexUnitary reverseTwoQubitBasis U) := by
  apply Subtype.ext
  ext row col
  simp only [coe_twoWireUnitary, twoWireRaw_apply, reindexUnitary_apply]
  by_cases hagree : AgreeOffTwoWire pair row col
  · have hswap : AgreeOffTwoWire pair.swap row col :=
      (agreeOffTwoWire_swap_iff pair row col).2 hagree
    rw [if_pos hswap, if_pos hagree]
    simp only [reverseTwoQubitBasis_symm_apply, twoWireLocalBits_swap]
  · have hswap : ¬AgreeOffTwoWire pair.swap row col :=
      fun h => hagree ((agreeOffTwoWire_swap_iff pair row col).1 h)
    rw [if_neg hswap, if_neg hagree]

end Barenco

