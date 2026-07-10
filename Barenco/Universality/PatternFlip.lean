import Barenco.ThreeQubit.Lemma61

/-!
# Exact control-pattern flips

Section 8 turns mixed positive/negative controls into positive controls by
temporarily applying Pauli-X on every wire whose required control value is
`false`. This module makes that conjugating permutation explicit.

`patternFlipCircuit target pattern` never touches `target`. Its exact basis action
is `patternFlipBasis`; the latter is an involution and sends all complementary
wires to `true` exactly when the original complementary assignment equals
`pattern`.
-/

namespace Barenco.Universality

open Barenco.ThreeQubit
open scoped Matrix

noncomputable section

/-! ## A reusable list of local Pauli-X gates -/

/-- Chronological local-X circuit on the listed wires. -/
def xCircuit {n : ℕ} (wires : List (Fin n)) : Circuit n :=
  wires.map fun wire => Primitive.oneQubit wire pauliX

/-- Basis update performed by `xCircuit`, in chronological list order. -/
def toggleBasis {n : ℕ} : List (Fin n) → Basis n → Basis n
  | [], input => input
  | wire :: wires, input =>
      toggleBasis wires (setTarget wire input (!input wire))

@[simp]
theorem xCircuit_nil {n : ℕ} : xCircuit ([] : List (Fin n)) = [] := rfl

@[simp]
theorem xCircuit_cons {n : ℕ} (wire : Fin n) (wires : List (Fin n)) :
    xCircuit (wire :: wires) =
      Primitive.oneQubit wire pauliX :: xCircuit wires := rfl

@[simp]
theorem toggleBasis_nil {n : ℕ} (input : Basis n) :
    toggleBasis [] input = input := rfl

@[simp]
theorem toggleBasis_cons {n : ℕ} (wire : Fin n) (wires : List (Fin n))
    (input : Basis n) :
    toggleBasis (wire :: wires) input =
      toggleBasis wires (setTarget wire input (!input wire)) := rfl

/-- Exact full-register basis action of a chronological local-X list. -/
@[simp]
theorem eval_xCircuit_mulVec_basisKet {n : ℕ} :
    ∀ (wires : List (Fin n)) (input : Basis n),
      (Circuit.eval (xCircuit wires) : Gate n) *ᵥ basisKet input =
        basisKet (toggleBasis wires input)
  | [], input => by simp [xCircuit, toggleBasis]
  | wire :: wires, input => by
      rw [xCircuit_cons, Circuit.eval_cons]
      change (((Circuit.eval (xCircuit wires) : UnitaryGate n) : Gate n) *
          localRaw wire pauliX) *ᵥ basisKet input = _
      rw [← Matrix.mulVec_mulVec, show localRaw wire (pauliX : QubitMatrix) =
        xRaw wire from rfl, xRaw_mulVec_basisKet,
        eval_xCircuit_mulVec_basisKet wires]
      rfl

/-- A duplicate-free toggle list flips exactly its listed coordinates once. -/
theorem toggleBasis_apply_of_nodup {n : ℕ} {wires : List (Fin n)}
    (hnodup : wires.Nodup) (input : Basis n) (index : Fin n) :
    toggleBasis wires input index =
      if index ∈ wires then !input index else input index := by
  induction wires generalizing input with
  | nil => simp
  | cons wire wires ih =>
      have hwire : wire ∉ wires := (List.nodup_cons.mp hnodup).1
      have hwires : wires.Nodup := (List.nodup_cons.mp hnodup).2
      rw [toggleBasis_cons, ih hwires]
      by_cases hindex : index = wire
      · subst index
        simp [hwire]
      · by_cases hmem : index ∈ wires
        · simp [hindex, hmem, setTarget_apply_of_ne]
        · simp [hindex, hmem, setTarget_apply_of_ne]

/-- Local-X lists on wires disjoint from `target` commute with every target gate. -/
theorem eval_xCircuit_commute_localUnitary {n : ℕ} (target : Fin n)
    (U : QubitUnitary) :
    ∀ (wires : List (Fin n)),
      (∀ wire ∈ wires, wire ≠ target) →
      Commute (Circuit.eval (xCircuit wires)) (localUnitary target U)
  | [], _ => by simp [xCircuit]
  | wire :: wires, hdisjoint => by
      have hwire : wire ≠ target := hdisjoint wire (by simp)
      have htail : ∀ tailWire ∈ wires, tailWire ≠ target := by
        intro tailWire hmem
        exact hdisjoint tailWire (by simp [hmem])
      have ih := eval_xCircuit_commute_localUnitary target U wires htail
      have hlocal : Commute (localUnitary wire pauliX) (localUnitary target U) :=
        localUnitary_commute_of_ne wire target hwire pauliX U
      change Commute
        (Circuit.eval (xCircuit wires) * localUnitary wire pauliX)
        (localUnitary target U)
      exact ih.mul_left hlocal

/-! ## Flipping exactly the negative controls -/

/-- Complementary wires whose required pattern value is `false`. -/
def falsePatternControls {n : ℕ} {target : Fin n}
    (pattern : ComplementBasis target) : List (TargetComplement target) :=
  (Finset.univ.filter fun wire => pattern wire = false).toList

/-- Ambient wire list used by the negative-control conjugation. -/
def falsePatternWires {n : ℕ} {target : Fin n}
    (pattern : ComplementBasis target) : List (Fin n) :=
  (falsePatternControls pattern).map Subtype.val

/-- Literal local-X prefix that converts `pattern` into the all-true pattern. -/
def patternFlipCircuit {n : ℕ} (target : Fin n)
    (pattern : ComplementBasis target) : Circuit n :=
  xCircuit (falsePatternWires pattern)

/-- Named certified semantic permutation of the literal pattern-flip circuit. -/
def patternFlipUnitary {n : ℕ} (target : Fin n)
    (pattern : ComplementBasis target) : UnitaryGate n :=
  Circuit.eval (patternFlipCircuit target pattern)

@[simp]
theorem eval_patternFlipCircuit_eq {n : ℕ} (target : Fin n)
    (pattern : ComplementBasis target) :
    Circuit.eval (patternFlipCircuit target pattern) =
      patternFlipUnitary target pattern := rfl

/-- Pointwise basis permutation performed by `patternFlipCircuit`. -/
def patternFlipBasis {n : ℕ} (target : Fin n)
    (pattern : ComplementBasis target) (input : Basis n) : Basis n :=
  fun wire => if hwire : wire = target then input wire
    else if pattern ⟨wire, hwire⟩ then input wire else !input wire

theorem nodup_falsePatternWires {n : ℕ} {target : Fin n}
    (pattern : ComplementBasis target) :
    (falsePatternWires pattern).Nodup := by
  exact (Finset.nodup_toList _).map Subtype.val_injective

@[simp]
theorem mem_falsePatternWires_iff {n : ℕ} {target wire : Fin n}
    (pattern : ComplementBasis target) :
    wire ∈ falsePatternWires pattern ↔
      ∃ hwire : wire ≠ target, pattern ⟨wire, hwire⟩ = false := by
  constructor
  · intro hmem
    rw [falsePatternWires, List.mem_map] at hmem
    rcases hmem with ⟨control, hcontrol, rfl⟩
    exact ⟨control.property, by
      simpa [falsePatternControls] using hcontrol⟩
  · rintro ⟨hwire, hpattern⟩
    rw [falsePatternWires, List.mem_map]
    exact ⟨⟨wire, hwire⟩, by simp [falsePatternControls, hpattern], rfl⟩

@[simp]
theorem toggleBasis_falsePatternWires {n : ℕ} (target : Fin n)
    (pattern : ComplementBasis target) (input : Basis n) :
    toggleBasis (falsePatternWires pattern) input =
      patternFlipBasis target pattern input := by
  funext wire
  rw [toggleBasis_apply_of_nodup (nodup_falsePatternWires pattern)]
  by_cases hwire : wire = target
  · subst wire
    simp [patternFlipBasis, mem_falsePatternWires_iff]
  · cases hpattern : pattern ⟨wire, hwire⟩ <;>
      simp [patternFlipBasis, hwire, mem_falsePatternWires_iff, hpattern]

/-- Exact basis action of the literal negative-control flip prefix. -/
@[simp]
theorem eval_patternFlipCircuit_mulVec_basisKet {n : ℕ} (target : Fin n)
    (pattern : ComplementBasis target) (input : Basis n) :
    (Circuit.eval (patternFlipCircuit target pattern) : Gate n) *ᵥ basisKet input =
      basisKet (patternFlipBasis target pattern input) := by
  rw [patternFlipCircuit, eval_xCircuit_mulVec_basisKet,
    toggleBasis_falsePatternWires]

/-- Basis action through the named semantic pattern-flip unitary. -/
@[simp]
theorem patternFlipUnitary_mulVec_basisKet {n : ℕ} (target : Fin n)
    (pattern : ComplementBasis target) (input : Basis n) :
    (patternFlipUnitary target pattern : Gate n) *ᵥ basisKet input =
      basisKet (patternFlipBasis target pattern input) := by
  exact eval_patternFlipCircuit_mulVec_basisKet target pattern input

@[simp]
theorem patternFlipBasis_target {n : ℕ} (target : Fin n)
    (pattern : ComplementBasis target) (input : Basis n) :
    patternFlipBasis target pattern input target = input target := by
  simp [patternFlipBasis]

@[simp]
theorem patternFlipBasis_complement {n : ℕ} (target : Fin n)
    (pattern : ComplementBasis target) (input : Basis n)
    (wire : TargetComplement target) :
    patternFlipBasis target pattern input wire =
      if pattern wire then input wire else !input wire := by
  simp [patternFlipBasis, wire.property]

/-- Pattern flipping is an exact involution on basis assignments. -/
@[simp]
theorem patternFlipBasis_involutive {n : ℕ} (target : Fin n)
    (pattern : ComplementBasis target) (input : Basis n) :
    patternFlipBasis target pattern (patternFlipBasis target pattern input) = input := by
  funext wire
  by_cases hwire : wire = target
  · subst wire
    simp
  · cases hpattern : pattern ⟨wire, hwire⟩ <;>
      simp [patternFlipBasis, hwire, hpattern]

/--
After the flip prefix, all complementary wires are true exactly for the desired
mixed-polarity control pattern.
-/
theorem patternFlipBasis_all_true_iff {n : ℕ} (target : Fin n)
    (pattern : ComplementBasis target) (input : Basis n) :
    (∀ wire : TargetComplement target,
        patternFlipBasis target pattern input wire = true) ↔
      (splitTarget target input).2 = pattern := by
  constructor
  · intro hall
    funext wire
    have hwire := hall wire
    cases hpattern : pattern wire <;> cases hinput : input wire <;>
      simp [patternFlipBasis_complement, hpattern, hinput] at hwire ⊢
  · intro hmatch wire
    have hwire := congrFun hmatch wire
    cases hpattern : pattern wire <;> cases hinput : input wire <;>
      simp [patternFlipBasis_complement, hpattern, hinput] at hwire ⊢

/-- The literal flip prefix is disjoint from, and commutes with, the target gate. -/
theorem eval_patternFlipCircuit_commute_localUnitary {n : ℕ}
    (target : Fin n) (pattern : ComplementBasis target) (U : QubitUnitary) :
    Commute (Circuit.eval (patternFlipCircuit target pattern))
      (localUnitary target U) := by
  apply eval_xCircuit_commute_localUnitary target U
  intro wire hwire
  rw [falsePatternWires, List.mem_map] at hwire
  rcases hwire with ⟨control, _, rfl⟩
  exact control.property

/-- Named semantic pattern flip commutes with every target-local unitary. -/
theorem patternFlipUnitary_commute_localUnitary {n : ℕ}
    (target : Fin n) (pattern : ComplementBasis target) (U : QubitUnitary) :
    Commute (patternFlipUnitary target pattern) (localUnitary target U) := by
  exact eval_patternFlipCircuit_commute_localUnitary target pattern U

/-! ## Small unitary-action cancellation lemmas -/

/-- Applying a certified inverse undoes any known vector action. -/
theorem unitary_inv_mulVec_of_mulVec_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix.unitaryGroup ι ℂ) (input output : ι → ℂ)
    (hP : (P : Matrix ι ι ℂ) *ᵥ input = output) :
    ((P⁻¹ : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) *ᵥ output = input := by
  rw [← hP, Matrix.mulVec_mulVec]
  change (((P⁻¹ * P : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) *ᵥ input) = input
  simp

/-- A commuting unitary conjugation leaves the other unitary's vector action unchanged. -/
theorem unitary_inv_mulVec_commuting_of_mulVec_eq {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (P L : Matrix.unitaryGroup ι ℂ) (hcomm : Commute P L)
    (input output : ι → ℂ)
    (hP : (P : Matrix ι ι ℂ) *ᵥ input = output) :
    ((P⁻¹ : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) *ᵥ
      ((L : Matrix ι ι ℂ) *ᵥ output) =
      (L : Matrix ι ι ℂ) *ᵥ input := by
  rw [← hP, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have hconjugate : P⁻¹ * L * P = L := by
    calc
      P⁻¹ * L * P = P⁻¹ * (L * P) := by rw [mul_assoc]
      _ = P⁻¹ * (P * L) := by rw [← hcomm.eq]
      _ = L := by simp
  change (((P⁻¹ * L * P : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) *ᵥ input) = _
  rw [hconjugate]

end

end Barenco.Universality
