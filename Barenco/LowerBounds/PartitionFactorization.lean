import Barenco.LowerBounds.BasicCircuit
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Tensor factorization across a wire partition

This module makes the informal phrase "the register splits into two independent
parts" precise for arbitrary, possibly noncontiguous, sets of wires.  The two
factors are raw complex matrices: requiring them to be certified unitaries is
unnecessary for the lower-bound obstruction, and the raw formulation is
strictly stronger.

The proof-carrying `BasicCircuit` syntax is essential here.  Locality is proved
from its two constructors, rather than inferred from the metadata of an
arbitrary `Primitive`.
-/

namespace Barenco.LowerBounds

open Matrix
open scoped Kronecker

noncomputable section

/-! ## Splitting an arbitrary finite set of wires -/

/-- Computational-basis assignments on the wires selected by `cut`. -/
abbrev CutBasis {n : ℕ} (cut : Finset (Fin n)) :=
  {wire : Fin n // wire ∈ cut} → Bool

/-- Computational-basis assignments on the wires outside `cut`. -/
abbrev CutComplementBasis {n : ℕ} (cut : Finset (Fin n)) :=
  {wire : Fin n // wire ∉ cut} → Bool

/-- Split a register assignment into its restrictions to `cut` and its complement. -/
def wireSplit {n : ℕ} (cut : Finset (Fin n)) :
    Basis n ≃ CutBasis cut × CutComplementBasis cut :=
  Equiv.piEquivPiSubtypeProd (fun wire => wire ∈ cut) (fun _ => Bool)

@[simp]
theorem wireSplit_fst_apply {n : ℕ} (cut : Finset (Fin n))
    (input : Basis n) (wire : {wire : Fin n // wire ∈ cut}) :
    (wireSplit cut input).1 wire = input wire := rfl

@[simp]
theorem wireSplit_snd_apply {n : ℕ} (cut : Finset (Fin n))
    (input : Basis n) (wire : {wire : Fin n // wire ∉ cut}) :
    (wireSplit cut input).2 wire = input wire := rfl

/-- Reindex a full-register matrix by the selected/complementary wire split. -/
def partitionReindex {n : ℕ} (cut : Finset (Fin n)) :
    Gate n ≃ₐ[ℂ]
      Matrix (CutBasis cut × CutComplementBasis cut)
        (CutBasis cut × CutComplementBasis cut) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ (wireSplit cut)

@[simp]
theorem partitionReindex_apply {n : ℕ} (cut : Finset (Fin n))
    (G : Gate n)
    (row col : CutBasis cut × CutComplementBasis cut) :
    partitionReindex cut G row col =
      G ((wireSplit cut).symm row) ((wireSplit cut).symm col) := rfl

/-! ## Raw tensor-factor relations -/

/-- `G` is a tensor product after grouping the wires in `cut` first. -/
def TensorFactorsAcross {n : ℕ} (cut : Finset (Fin n)) (G : Gate n) : Prop :=
  ∃ left : Matrix (CutBasis cut) (CutBasis cut) ℂ,
    ∃ right : Matrix (CutComplementBasis cut) (CutComplementBasis cut) ℂ,
      partitionReindex cut G = left ⊗ₖ right

/-- `G` acts only on the selected side of the partition. -/
def TensorLocalOnCut {n : ℕ} (cut : Finset (Fin n)) (G : Gate n) : Prop :=
  ∃ left : Matrix (CutBasis cut) (CutBasis cut) ℂ,
    partitionReindex cut G = left ⊗ₖ (1 :
      Matrix (CutComplementBasis cut) (CutComplementBasis cut) ℂ)

/-- `G` acts only on the complementary side of the partition. -/
def TensorLocalOffCut {n : ℕ} (cut : Finset (Fin n)) (G : Gate n) : Prop :=
  ∃ right : Matrix (CutComplementBasis cut) (CutComplementBasis cut) ℂ,
    partitionReindex cut G =
      (1 : Matrix (CutBasis cut) (CutBasis cut) ℂ) ⊗ₖ right

theorem TensorLocalOnCut.tensorFactorsAcross {n : ℕ} {cut : Finset (Fin n)}
    {G : Gate n} (hG : TensorLocalOnCut cut G) : TensorFactorsAcross cut G := by
  rcases hG with ⟨left, hleft⟩
  exact ⟨left, 1, hleft⟩

theorem TensorLocalOffCut.tensorFactorsAcross {n : ℕ} {cut : Finset (Fin n)}
    {G : Gate n} (hG : TensorLocalOffCut cut G) : TensorFactorsAcross cut G := by
  rcases hG with ⟨right, hright⟩
  exact ⟨1, right, hright⟩

/-- The identity factors across every wire partition. -/
theorem TensorFactorsAcross.one {n : ℕ} (cut : Finset (Fin n)) :
    TensorFactorsAcross cut (1 : Gate n) := by
  refine ⟨1, 1, ?_⟩
  rw [partitionReindex]
  simp

/-- Tensor factorization across a fixed cut is closed under matrix multiplication. -/
theorem TensorFactorsAcross.mul {n : ℕ} {cut : Finset (Fin n)} {G H : Gate n}
    (hG : TensorFactorsAcross cut G) (hH : TensorFactorsAcross cut H) :
    TensorFactorsAcross cut (G * H) := by
  rcases hG with ⟨leftG, rightG, hG⟩
  rcases hH with ⟨leftH, rightH, hH⟩
  refine ⟨leftG * leftH, rightG * rightH, ?_⟩
  rw [map_mul, hG, hH, Matrix.mul_kronecker_mul]

/-! ## Local one-qubit factors -/

/-- Agreement away from one selected wire inside `cut`. -/
abbrev AgreeOffCut {n : ℕ} {cut : Finset (Fin n)}
    (target : {wire : Fin n // wire ∈ cut})
    (row col : CutBasis cut) : Prop :=
  ∀ wire, wire ≠ target → row wire = col wire

/-- Agreement away from one selected wire outside `cut`. -/
abbrev AgreeOffCutComplement {n : ℕ} {cut : Finset (Fin n)}
    (target : {wire : Fin n // wire ∉ cut})
    (row col : CutComplementBasis cut) : Prop :=
  ∀ wire, wire ≠ target → row wire = col wire

/-- Raw one-qubit matrix on the selected side of a wire partition. -/
def cutLocalRaw {n : ℕ} (cut : Finset (Fin n))
    (target : {wire : Fin n // wire ∈ cut}) (U : QubitMatrix) :
    Matrix (CutBasis cut) (CutBasis cut) ℂ := fun row col =>
  if AgreeOffCut target row col then U (row target) (col target) else 0

/-- Raw one-qubit matrix on the complementary side of a wire partition. -/
def cutComplementLocalRaw {n : ℕ} (cut : Finset (Fin n))
    (target : {wire : Fin n // wire ∉ cut}) (U : QubitMatrix) :
    Matrix (CutComplementBasis cut) (CutComplementBasis cut) ℂ := fun row col =>
  if AgreeOffCutComplement target row col then U (row target) (col target) else 0

private theorem agreeOff_wireSplit_symm_iff_of_mem {n : ℕ}
    (cut : Finset (Fin n)) (target : Fin n) (htarget : target ∈ cut)
    (row col : CutBasis cut × CutComplementBasis cut) :
    AgreeOff target ((wireSplit cut).symm row) ((wireSplit cut).symm col) ↔
      AgreeOffCut ⟨target, htarget⟩ row.1 col.1 ∧ row.2 = col.2 := by
  constructor
  · intro hagree
    constructor
    · intro wire hwire
      have hne : (wire : Fin n) ≠ target := by
        intro heq
        apply hwire
        exact Subtype.ext heq
      simpa [wireSplit, Equiv.piEquivPiSubtypeProd_symm_apply, wire.property] using
        hagree wire hne
    · funext wire
      have hne : (wire : Fin n) ≠ target := by
        intro heq
        subst target
        exact wire.property htarget
      simpa [wireSplit, Equiv.piEquivPiSubtypeProd_symm_apply, wire.property] using
        hagree wire hne
  · rintro ⟨hleft, hright⟩ wire hwire
    by_cases hmem : wire ∈ cut
    · have hne : (⟨wire, hmem⟩ : {wire : Fin n // wire ∈ cut}) ≠
          ⟨target, htarget⟩ := by
        intro heq
        exact hwire (congrArg Subtype.val heq)
      have hvalue := hleft ⟨wire, hmem⟩ hne
      simpa [wireSplit, Equiv.piEquivPiSubtypeProd_symm_apply, hmem] using hvalue
    · have hvalue := congrFun hright
          (⟨wire, hmem⟩ : {wire : Fin n // wire ∉ cut})
      simpa [wireSplit, Equiv.piEquivPiSubtypeProd_symm_apply, hmem] using hvalue

private theorem agreeOff_wireSplit_symm_iff_of_notMem {n : ℕ}
    (cut : Finset (Fin n)) (target : Fin n) (htarget : target ∉ cut)
    (row col : CutBasis cut × CutComplementBasis cut) :
    AgreeOff target ((wireSplit cut).symm row) ((wireSplit cut).symm col) ↔
      row.1 = col.1 ∧
        AgreeOffCutComplement ⟨target, htarget⟩ row.2 col.2 := by
  constructor
  · intro hagree
    constructor
    · funext wire
      have hne : (wire : Fin n) ≠ target := by
        intro heq
        subst target
        exact htarget wire.property
      simpa [wireSplit, Equiv.piEquivPiSubtypeProd_symm_apply, wire.property] using
        hagree wire hne
    · intro wire hwire
      have hne : (wire : Fin n) ≠ target := by
        intro heq
        apply hwire
        exact Subtype.ext heq
      simpa [wireSplit, Equiv.piEquivPiSubtypeProd_symm_apply, wire.property] using
        hagree wire hne
  · rintro ⟨hleft, hright⟩ wire hwire
    by_cases hmem : wire ∈ cut
    · have hvalue := congrFun hleft
          (⟨wire, hmem⟩ : {wire : Fin n // wire ∈ cut})
      simpa [wireSplit, Equiv.piEquivPiSubtypeProd_symm_apply, hmem] using hvalue
    · have hne : (⟨wire, hmem⟩ : {wire : Fin n // wire ∉ cut}) ≠
          ⟨target, htarget⟩ := by
        intro heq
        exact hwire (congrArg Subtype.val heq)
      have hvalue := hright ⟨wire, hmem⟩ hne
      simpa [wireSplit, Equiv.piEquivPiSubtypeProd_symm_apply, hmem] using hvalue

/-- A local one-qubit matrix whose target lies in `cut` acts only on that side. -/
theorem localRaw_tensorLocalOnCut_of_mem {n : ℕ} (cut : Finset (Fin n))
    (target : Fin n) (htarget : target ∈ cut) (U : QubitMatrix) :
    TensorLocalOnCut cut (localRaw target U) := by
  refine ⟨cutLocalRaw cut ⟨target, htarget⟩ U, ?_⟩
  ext row col
  rw [partitionReindex_apply, Matrix.kronecker_apply,
    localRaw_apply_eq_if_agreeOff,
    agreeOff_wireSplit_symm_iff_of_mem cut target htarget]
  simp only [cutLocalRaw, Matrix.one_apply]
  have hrowTarget :
      (wireSplit cut).symm row target = row.1 ⟨target, htarget⟩ := by
    simp [wireSplit, Equiv.piEquivPiSubtypeProd_symm_apply, htarget]
  have hcolTarget :
      (wireSplit cut).symm col target = col.1 ⟨target, htarget⟩ := by
    simp [wireSplit, Equiv.piEquivPiSubtypeProd_symm_apply, htarget]
  rw [hrowTarget, hcolTarget]
  by_cases hleft : AgreeOffCut ⟨target, htarget⟩ row.1 col.1 <;>
    by_cases hright : row.2 = col.2 <;> simp [hleft, hright]

/-- A local one-qubit matrix whose target lies outside `cut` acts only there. -/
theorem localRaw_tensorLocalOffCut_of_notMem {n : ℕ} (cut : Finset (Fin n))
    (target : Fin n) (htarget : target ∉ cut) (U : QubitMatrix) :
    TensorLocalOffCut cut (localRaw target U) := by
  refine ⟨cutComplementLocalRaw cut ⟨target, htarget⟩ U, ?_⟩
  ext row col
  rw [partitionReindex_apply, Matrix.kronecker_apply,
    localRaw_apply_eq_if_agreeOff,
    agreeOff_wireSplit_symm_iff_of_notMem cut target htarget]
  simp only [cutComplementLocalRaw, Matrix.one_apply]
  have hrowTarget :
      (wireSplit cut).symm row target = row.2 ⟨target, htarget⟩ := by
    simp [wireSplit, Equiv.piEquivPiSubtypeProd_symm_apply, htarget]
  have hcolTarget :
      (wireSplit cut).symm col target = col.2 ⟨target, htarget⟩ := by
    simp [wireSplit, Equiv.piEquivPiSubtypeProd_symm_apply, htarget]
  rw [hrowTarget, hcolTarget]
  by_cases hleft : row.1 = col.1 <;>
    by_cases hright : AgreeOffCutComplement ⟨target, htarget⟩ row.2 col.2 <;>
      simp [hleft, hright]

end

end Barenco.LowerBounds
