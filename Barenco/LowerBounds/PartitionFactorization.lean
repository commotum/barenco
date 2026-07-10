import Barenco.LowerBounds.InteractionGraph
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Tensor factorization across a wire partition

This module makes the informal phrase "the register splits into two independent
parts" precise for arbitrary, possibly noncontiguous, sets of wires.  The two
factors are raw complex matrices: requiring them to be certified unitaries is
unnecessary for the lower-bound obstruction.  This makes factorability a weaker
predicate and therefore makes a proof of nonfactorability stronger.

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
    localRaw_apply_eq_if_agreeOff]
  simp only [cutLocalRaw, Matrix.one_apply]
  have hrowTarget :
      (wireSplit cut).symm row target = row.1 ⟨target, htarget⟩ := by
    simp [wireSplit, Equiv.piEquivPiSubtypeProd_symm_apply, htarget]
  have hcolTarget :
      (wireSplit cut).symm col target = col.1 ⟨target, htarget⟩ := by
    simp [wireSplit, Equiv.piEquivPiSubtypeProd_symm_apply, htarget]
  by_cases hleft : AgreeOffCut ⟨target, htarget⟩ row.1 col.1 <;>
    by_cases hright : row.2 = col.2 <;>
      simp [agreeOff_wireSplit_symm_iff_of_mem cut target htarget,
        hrowTarget, hcolTarget, hright]

/-- A local one-qubit matrix whose target lies outside `cut` acts only there. -/
theorem localRaw_tensorLocalOffCut_of_notMem {n : ℕ} (cut : Finset (Fin n))
    (target : Fin n) (htarget : target ∉ cut) (U : QubitMatrix) :
    TensorLocalOffCut cut (localRaw target U) := by
  refine ⟨cutComplementLocalRaw cut ⟨target, htarget⟩ U, ?_⟩
  ext row col
  rw [partitionReindex_apply, Matrix.kronecker_apply,
    localRaw_apply_eq_if_agreeOff]
  simp only [cutComplementLocalRaw, Matrix.one_apply]
  have hrowTarget :
      (wireSplit cut).symm row target = row.2 ⟨target, htarget⟩ := by
    simp [wireSplit, Equiv.piEquivPiSubtypeProd_symm_apply, htarget]
  have hcolTarget :
      (wireSplit cut).symm col target = col.2 ⟨target, htarget⟩ := by
    simp [wireSplit, Equiv.piEquivPiSubtypeProd_symm_apply, htarget]
  by_cases hleft : row.1 = col.1 <;>
    by_cases hright : AgreeOffCutComplement ⟨target, htarget⟩ row.2 col.2 <;>
      simp [agreeOff_wireSplit_symm_iff_of_notMem cut target htarget,
        hrowTarget, hcolTarget, hleft]

/-! ## CNOT factors -/

/-- The basis update underlying a CNOT, on an arbitrary wire index type. -/
def xorBasisUpdate {ι : Type*} [DecidableEq ι] (control target : ι)
    (input : ι → Bool) : ι → Bool :=
  if input control then Function.update input target (!input target) else input

private theorem setTarget_eq_update {n : ℕ} (target : Fin n)
    (input : Basis n) (bit : Bool) :
    setTarget target input bit = Function.update input target bit := by
  funext wire
  by_cases hwire : wire = target
  · subst wire
    simp
  · rw [setTarget_apply_of_ne target input bit wire hwire]
    simp [hwire]

/-- Raw CNOT permutation matrix on the selected side of a partition. -/
def cutCNOTRaw {n : ℕ} (cut : Finset (Fin n))
    (control target : {wire : Fin n // wire ∈ cut}) :
    Matrix (CutBasis cut) (CutBasis cut) ℂ := fun row col =>
  if row = xorBasisUpdate control target col then 1 else 0

/-- Raw CNOT permutation matrix on the complementary side of a partition. -/
def cutComplementCNOTRaw {n : ℕ} (cut : Finset (Fin n))
    (control target : {wire : Fin n // wire ∉ cut}) :
    Matrix (CutComplementBasis cut) (CutComplementBasis cut) ℂ := fun row col =>
  if row = xorBasisUpdate control target col then 1 else 0

private theorem cnotRaw_apply_eq_xorBasisUpdate {n : ℕ}
    (control target : Fin n) (hcontrolTarget : control ≠ target)
    (row col : Basis n) :
    cnotRaw control target hcontrolTarget row col =
      if row = xorBasisUpdate control target col then 1 else 0 := by
  calc
    cnotRaw control target hcontrolTarget row col =
        (cnotRaw control target hcontrolTarget *ᵥ basisKet col) row := by simp
    _ = basisKet
        (if col control then setTarget target col (!col target) else col) row := by
      rw [cnotRaw_mulVec_basisKet]
    _ = if row = xorBasisUpdate control target col then 1 else 0 := by
      rw [setTarget_eq_update]
      simp only [basisKet_apply]
      rfl

private theorem wireSplit_xorBasisUpdate_of_mem {n : ℕ}
    (cut : Finset (Fin n)) (control target : Fin n)
    (hcontrol : control ∈ cut) (htarget : target ∈ cut)
    (input : CutBasis cut × CutComplementBasis cut) :
    wireSplit cut
        (xorBasisUpdate control target ((wireSplit cut).symm input)) =
      (xorBasisUpdate ⟨control, hcontrol⟩ ⟨target, htarget⟩ input.1, input.2) := by
  apply Prod.ext
  · funext wire
    cases hbit : input.1 ⟨control, hcontrol⟩
    · simp [xorBasisUpdate, wireSplit,
        Equiv.piEquivPiSubtypeProd_symm_apply, hcontrol, hbit]
    · by_cases hwire : wire = ⟨target, htarget⟩
      · subst wire
        simp [xorBasisUpdate, wireSplit,
          Equiv.piEquivPiSubtypeProd_symm_apply, hcontrol, htarget, hbit]
      · have hwireValue : (wire : Fin n) ≠ target := by
          intro heq
          apply hwire
          exact Subtype.ext heq
        simp [xorBasisUpdate, wireSplit,
          Equiv.piEquivPiSubtypeProd_symm_apply, hcontrol, htarget,
          hbit, Function.update_apply, hwire, hwireValue]
  · funext wire
    cases hbit : input.1 ⟨control, hcontrol⟩
    · simp [xorBasisUpdate, wireSplit,
        Equiv.piEquivPiSubtypeProd_symm_apply, hcontrol, hbit]
    · have hwireTarget : (wire : Fin n) ≠ target := by
        intro heq
        subst target
        exact wire.property htarget
      simp [xorBasisUpdate, wireSplit,
        Equiv.piEquivPiSubtypeProd_symm_apply, hcontrol, htarget,
        wire.property, hbit, Function.update_apply, hwireTarget]

private theorem wireSplit_xorBasisUpdate_of_notMem {n : ℕ}
    (cut : Finset (Fin n)) (control target : Fin n)
    (hcontrol : control ∉ cut) (htarget : target ∉ cut)
    (input : CutBasis cut × CutComplementBasis cut) :
    wireSplit cut
        (xorBasisUpdate control target ((wireSplit cut).symm input)) =
      (input.1,
        xorBasisUpdate ⟨control, hcontrol⟩ ⟨target, htarget⟩ input.2) := by
  apply Prod.ext
  · funext wire
    cases hbit : input.2 ⟨control, hcontrol⟩
    · simp [xorBasisUpdate, wireSplit,
        Equiv.piEquivPiSubtypeProd_symm_apply, hcontrol, hbit]
    · have hwireTarget : (wire : Fin n) ≠ target := by
        intro heq
        subst target
        exact htarget wire.property
      simp [xorBasisUpdate, wireSplit,
        Equiv.piEquivPiSubtypeProd_symm_apply, hcontrol, htarget,
        hbit, Function.update_apply, hwireTarget]
  · funext wire
    cases hbit : input.2 ⟨control, hcontrol⟩
    · simp [xorBasisUpdate, wireSplit,
        Equiv.piEquivPiSubtypeProd_symm_apply, hcontrol, hbit]
    · by_cases hwire : wire = ⟨target, htarget⟩
      · subst wire
        simp [xorBasisUpdate, wireSplit,
          Equiv.piEquivPiSubtypeProd_symm_apply, hcontrol, htarget, hbit]
      · have hwireValue : (wire : Fin n) ≠ target := by
          intro heq
          apply hwire
          exact Subtype.ext heq
        simp [xorBasisUpdate, wireSplit,
          Equiv.piEquivPiSubtypeProd_symm_apply, hcontrol, htarget,
          wire.property, hbit, Function.update_apply, hwire, hwireValue]

/-- A CNOT whose two endpoints lie in `cut` acts only on that side. -/
theorem cnotRaw_tensorLocalOnCut_of_mem {n : ℕ} (cut : Finset (Fin n))
    (control target : Fin n) (hcontrolTarget : control ≠ target)
    (hcontrol : control ∈ cut) (htarget : target ∈ cut) :
    TensorLocalOnCut cut (cnotRaw control target hcontrolTarget) := by
  refine ⟨cutCNOTRaw cut ⟨control, hcontrol⟩ ⟨target, htarget⟩, ?_⟩
  ext row col
  rw [partitionReindex_apply, Matrix.kronecker_apply,
    cnotRaw_apply_eq_xorBasisUpdate, Matrix.one_apply]
  have heq :
      (wireSplit cut).symm row =
          xorBasisUpdate control target ((wireSplit cut).symm col) ↔
        row.1 = xorBasisUpdate ⟨control, hcontrol⟩ ⟨target, htarget⟩ col.1 ∧
          row.2 = col.2 := by
    constructor
    · intro h
      have hsplit := congrArg (wireSplit cut) h
      rw [(wireSplit cut).apply_symm_apply,
        wireSplit_xorBasisUpdate_of_mem cut control target hcontrol htarget] at hsplit
      have hleft := congrArg Prod.fst hsplit
      have hright :=
        congrArg (fun pair : CutBasis cut × CutComplementBasis cut => pair.2) hsplit
      exact ⟨hleft, hright⟩
    · rintro ⟨hleft, hright⟩
      apply (wireSplit cut).injective
      rw [(wireSplit cut).apply_symm_apply,
        wireSplit_xorBasisUpdate_of_mem cut control target hcontrol htarget]
      exact Prod.ext hleft hright
  by_cases hleft :
      row.1 = xorBasisUpdate ⟨control, hcontrol⟩ ⟨target, htarget⟩ col.1 <;>
    by_cases hright : row.2 = col.2 <;>
      simp [cutCNOTRaw, heq, hleft, hright]

/-- A CNOT whose two endpoints lie outside `cut` acts only there. -/
theorem cnotRaw_tensorLocalOffCut_of_notMem {n : ℕ} (cut : Finset (Fin n))
    (control target : Fin n) (hcontrolTarget : control ≠ target)
    (hcontrol : control ∉ cut) (htarget : target ∉ cut) :
    TensorLocalOffCut cut (cnotRaw control target hcontrolTarget) := by
  refine ⟨cutComplementCNOTRaw cut ⟨control, hcontrol⟩ ⟨target, htarget⟩, ?_⟩
  ext row col
  rw [partitionReindex_apply, Matrix.kronecker_apply,
    cnotRaw_apply_eq_xorBasisUpdate, Matrix.one_apply]
  have heq :
      (wireSplit cut).symm row =
          xorBasisUpdate control target ((wireSplit cut).symm col) ↔
        row.1 = col.1 ∧
          row.2 =
            xorBasisUpdate ⟨control, hcontrol⟩ ⟨target, htarget⟩ col.2 := by
    constructor
    · intro h
      have hsplit := congrArg (wireSplit cut) h
      rw [(wireSplit cut).apply_symm_apply,
        wireSplit_xorBasisUpdate_of_notMem cut control target hcontrol htarget] at hsplit
      have hleft :=
        congrArg (fun pair : CutBasis cut × CutComplementBasis cut => pair.1) hsplit
      have hright := congrArg Prod.snd hsplit
      exact ⟨hleft, hright⟩
    · rintro ⟨hleft, hright⟩
      apply (wireSplit cut).injective
      rw [(wireSplit cut).apply_symm_apply,
        wireSplit_xorBasisUpdate_of_notMem cut control target hcontrol htarget]
      exact Prod.ext hleft hright
  by_cases hleft : row.1 = col.1 <;>
    by_cases hright :
        row.2 = xorBasisUpdate ⟨control, hcontrol⟩ ⟨target, htarget⟩ col.2 <;>
      simp [cutComplementCNOTRaw, heq, hleft, hright]

/-! ## Proof-carrying basic primitives and circuits -/

namespace BasicPrimitive

/-- A basic primitive supported inside `cut` is tensor-local on that side. -/
theorem tensorLocalOnCut_of_wires_subset {n : ℕ} (cut : Finset (Fin n))
    (primitive : BasicPrimitive n) (hsupport : primitive.wires ⊆ cut) :
    TensorLocalOnCut cut (primitive.denotation : Gate n) := by
  cases primitive with
  | oneQubit target U =>
      have htarget : target ∈ cut := hsupport (by simp [wires])
      change TensorLocalOnCut cut (localRaw target U)
      exact localRaw_tensorLocalOnCut_of_mem cut target htarget U
  | cnot control target hcontrolTarget =>
      have hcontrol : control ∈ cut := hsupport (by simp [wires])
      have htarget : target ∈ cut := hsupport (by simp [wires])
      simpa only [denotation_cnot, coe_cnotUnitary] using
        cnotRaw_tensorLocalOnCut_of_mem cut control target hcontrolTarget
          hcontrol htarget

/-- A basic primitive disjoint from `cut` is tensor-local on its complement. -/
theorem tensorLocalOffCut_of_disjoint {n : ℕ} (cut : Finset (Fin n))
    (primitive : BasicPrimitive n) (hsupport : Disjoint primitive.wires cut) :
    TensorLocalOffCut cut (primitive.denotation : Gate n) := by
  rw [Finset.disjoint_left] at hsupport
  cases primitive with
  | oneQubit target U =>
      have htarget : target ∉ cut := fun hmem => hsupport (by simp [wires]) hmem
      change TensorLocalOffCut cut (localRaw target U)
      exact localRaw_tensorLocalOffCut_of_notMem cut target htarget U
  | cnot control target hcontrolTarget =>
      have hcontrol : control ∉ cut := fun hmem => hsupport (by simp [wires]) hmem
      have htarget : target ∉ cut := fun hmem => hsupport (by simp [wires]) hmem
      simpa only [denotation_cnot, coe_cnotUnitary] using
        cnotRaw_tensorLocalOffCut_of_notMem cut control target hcontrolTarget
          hcontrol htarget

/-- Every basic primitive that does not cross `cut` factors across it. -/
theorem tensorFactorsAcross_of_doesNotCross {n : ℕ} (cut : Finset (Fin n))
    (primitive : BasicPrimitive n) (hcross : primitive.DoesNotCross cut) :
    TensorFactorsAcross cut (primitive.denotation : Gate n) := by
  rcases hcross with hinside | houtside
  · exact (primitive.tensorLocalOnCut_of_wires_subset cut hinside).tensorFactorsAcross
  · exact (primitive.tensorLocalOffCut_of_disjoint cut houtside).tensorFactorsAcross

end BasicPrimitive

namespace BasicCircuit

/--
If no primitive crosses a fixed wire cut, the complete evaluator factors across
that cut.  The proof follows the chronological evaluator and uses the exact
Kronecker multiplication law at every cons node.
-/
theorem eval_tensorFactorsAcross_of_all_doesNotCross {n : ℕ}
    (cut : Finset (Fin n)) (circuit : BasicCircuit n)
    (hcross : ∀ primitive ∈ circuit, primitive.DoesNotCross cut) :
    TensorFactorsAcross cut (circuit.eval : Gate n) := by
  induction circuit with
  | nil =>
      change TensorFactorsAcross cut (1 : Gate n)
      exact TensorFactorsAcross.one cut
  | cons primitive circuit ih =>
      change TensorFactorsAcross cut
        ((BasicCircuit.eval circuit : Gate n) * (primitive.denotation : Gate n))
      apply TensorFactorsAcross.mul
      · apply ih
        intro tailPrimitive htail
        exact hcross tailPrimitive (List.mem_cons_of_mem primitive htail)
      · exact primitive.tensorFactorsAcross_of_doesNotCross cut
          (hcross primitive (List.mem_cons_self))

/--
The evaluator of every basic circuit factors across the CNOT-interaction
component containing any selected target wire.
-/
theorem eval_tensorFactorsAcross_targetComponent {n : ℕ}
    (circuit : BasicCircuit n) (target : Fin n) :
    TensorFactorsAcross (circuit.targetComponent target) (circuit.eval : Gate n) := by
  exact circuit.eval_tensorFactorsAcross_of_all_doesNotCross
    (circuit.targetComponent target)
    (circuit.all_primitives_doNotCross_targetComponent target)

end BasicCircuit

end

end Barenco.LowerBounds
