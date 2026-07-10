import Barenco.Cost
import Barenco.Universality.BasisPath
import Barenco.Universality.PatternFlip

/-!
# Affine normalization of an ordered computational-basis pair

For two distinct assignments on a positive-width register, this module builds a
literal one-qubit/CNOT circuit that sends the ordered pair to a canonical pair.
It first flips every wire which is true in the first assignment, sending that
assignment to zero and the second to their bitwise difference.  A canonical
differing pivot then controls CNOTs which clear every other true difference bit.

The resulting circuit sends the first endpoint to the all-zero assignment and
the second to the assignment supported only at the pivot.  All action theorems
are full-register basis-ket equalities; all resource theorems are derived from
the literal syntax.
-/

namespace Barenco.Universality

open scoped Matrix

noncomputable section

/-! ## Canonical assignments and the chosen pivot -/

/-- The all-zero computational-basis assignment. -/
def allZeroBasis {n : ℕ} : Basis n := fun _ => false

/-- The assignment which is true exactly at `pivot`. -/
def singletonBasis {n : ℕ} (pivot : Fin n) : Basis n := fun wire =>
  if wire = pivot then true else false

@[simp]
theorem allZeroBasis_apply {n : ℕ} (wire : Fin n) :
    allZeroBasis wire = false := rfl

@[simp]
theorem singletonBasis_apply_self {n : ℕ} (pivot : Fin n) :
    singletonBasis pivot pivot = true := by
  simp [singletonBasis]

@[simp]
theorem singletonBasis_apply_of_ne {n : ℕ} (pivot wire : Fin n)
    (hwire : wire ≠ pivot) :
    singletonBasis pivot wire = false := by
  simp [singletonBasis, hwire]

theorem allZeroBasis_ne_singletonBasis {n : ℕ} (pivot : Fin n) :
    (allZeroBasis : Basis n) ≠ singletonBasis pivot := by
  intro h
  have := congrFun h pivot
  simp at this

/-- Pointwise Boolean difference of two assignments. -/
def basisDifference {n : ℕ} (first second : Basis n) : Basis n := fun wire =>
  if first wire = second wire then false else true

@[simp]
theorem basisDifference_eq_true_iff {n : ℕ} (first second : Basis n)
    (wire : Fin n) :
    basisDifference first second wire = true ↔ first wire ≠ second wire := by
  simp [basisDifference]

@[simp]
theorem basisDifference_eq_false_iff {n : ℕ} (first second : Basis n)
    (wire : Fin n) :
    basisDifference first second wire = false ↔ first wire = second wire := by
  simp [basisDifference]

theorem differingWires_nonempty_of_ne {n : ℕ} {first second : Basis n}
    (hfirstSecond : first ≠ second) :
    (differingWires first second).Nonempty := by
  by_contra hempty
  apply hfirstSecond
  funext wire
  have hnotMem : wire ∉ differingWires first second := by
    simp [Finset.not_nonempty_iff_eq_empty.mp hempty]
  exact not_ne_iff.mp ((mem_differingWires first second wire).not.mp hnotMem)

/-- The least wire on which the two endpoints differ. -/
def differingPivot {n : ℕ} (first second : Basis n)
    (hfirstSecond : first ≠ second) : Fin n :=
  (differingWires first second).min'
    (differingWires_nonempty_of_ne hfirstSecond)

@[simp]
theorem differingPivot_mem {n : ℕ} (first second : Basis n)
    (hfirstSecond : first ≠ second) :
    differingPivot first second hfirstSecond ∈ differingWires first second := by
  exact Finset.min'_mem _ _

theorem differingPivot_bit_ne {n : ℕ} (first second : Basis n)
    (hfirstSecond : first ≠ second) :
    first (differingPivot first second hfirstSecond) ≠
      second (differingPivot first second hfirstSecond) := by
  exact (mem_differingWires first second _).mp
    (differingPivot_mem first second hfirstSecond)

@[simp]
theorem basisDifference_differingPivot {n : ℕ} (first second : Basis n)
    (hfirstSecond : first ≠ second) :
    basisDifference first second (differingPivot first second hfirstSecond) = true := by
  exact (basisDifference_eq_true_iff first second _).2
    (differingPivot_bit_ne first second hfirstSecond)

/-! ## The local-X translation -/

/-- True wires of an assignment, in increasing register order. -/
def trueWireList {n : ℕ} (input : Basis n) : List (Fin n) :=
  (Finset.univ.filter fun wire => input wire = true).sort

@[simp]
theorem mem_trueWireList {n : ℕ} (input : Basis n) (wire : Fin n) :
    wire ∈ trueWireList input ↔ input wire = true := by
  simp [trueWireList]

theorem trueWireList_nodup {n : ℕ} (input : Basis n) :
    (trueWireList input).Nodup := by
  exact Finset.sort_nodup _ _

/-- Number of local-X gates in the translation prefix. -/
def trueBitCount {n : ℕ} (input : Basis n) : ℕ :=
  (trueWireList input).length

theorem toggleBasis_trueWireList_self {n : ℕ} (input : Basis n) :
    toggleBasis (trueWireList input) input = allZeroBasis := by
  funext wire
  rw [toggleBasis_apply_of_nodup (trueWireList_nodup input)]
  cases hbit : input wire <;> simp [hbit]

theorem toggleBasis_trueWireList_second {n : ℕ}
    (first second : Basis n) :
    toggleBasis (trueWireList first) second = basisDifference first second := by
  funext wire
  rw [toggleBasis_apply_of_nodup (trueWireList_nodup first)]
  cases hfirst : first wire <;> cases hsecond : second wire <;>
    simp [hfirst, hsecond, basisDifference]

/-! ## Clearing all non-pivot difference wires -/

/-- Ambient wires other than a fixed pivot. -/
abbrev PivotComplement {n : ℕ} (pivot : Fin n) :=
  {wire : Fin n // wire ≠ pivot}

/-- Other differing wires, listed in increasing order. -/
def otherDifferenceTargets {n : ℕ} (first second : Basis n)
    (hfirstSecond : first ≠ second) :
    List (PivotComplement (differingPivot first second hfirstSecond)) :=
  (Finset.univ.filter fun wire :
      PivotComplement (differingPivot first second hfirstSecond) =>
        first wire ≠ second wire).sort

@[simp]
theorem mem_otherDifferenceTargets {n : ℕ} (first second : Basis n)
    (hfirstSecond : first ≠ second)
    (wire : PivotComplement (differingPivot first second hfirstSecond)) :
    wire ∈ otherDifferenceTargets first second hfirstSecond ↔
      first wire ≠ second wire := by
  simp [otherDifferenceTargets]

theorem otherDifferenceTargets_nodup {n : ℕ} (first second : Basis n)
    (hfirstSecond : first ≠ second) :
    (otherDifferenceTargets first second hfirstSecond).Nodup := by
  exact Finset.sort_nodup _ _

/-- There is one clearing CNOT for every differing wire except the pivot. -/
@[simp]
theorem length_otherDifferenceTargets {n : ℕ} (first second : Basis n)
    (hfirstSecond : first ≠ second) :
    (otherDifferenceTargets first second hfirstSecond).length =
      hammingDist first second - 1 := by
  rw [otherDifferenceTargets, Finset.length_sort]
  let pivot := differingPivot first second hfirstSecond
  let source : Finset (PivotComplement pivot) :=
    Finset.univ.filter fun wire => first wire ≠ second wire
  let image : Finset (Fin n) := (differingWires first second).erase pivot
  change source.card = hammingDist first second - 1
  have hcard : source.card = image.card := by
    apply Finset.card_bij (s := source) (t := image)
      (fun (wire : PivotComplement pivot) _ => (wire : Fin n))
    · intro wire hwire
      have hdiff : first (wire : Fin n) ≠ second wire := by
        simpa [source] using hwire
      exact Finset.mem_erase.mpr ⟨wire.property,
        (mem_differingWires first second wire).2 hdiff⟩
    · intro firstWire _ secondWire _ heq
      exact Subtype.ext heq
    · intro wire hwire
      have herase := Finset.mem_erase.mp hwire
      refine ⟨⟨wire, herase.1⟩, ?_, rfl⟩
      have hdiff : first wire ≠ second wire :=
        (mem_differingWires first second wire).1 herase.2
      simp [source, hdiff]
  rw [hcard]
  have hpivot : pivot ∈ differingWires first second := by
    exact differingPivot_mem first second hfirstSecond
  rw [show image.card = (differingWires first second).card - 1 by
    simpa [image] using Finset.card_erase_of_mem hpivot]
  simp [differingWires, hammingDist]

/-- Forget the proof that every clearing target differs from the pivot. -/
def pivotTargetWires {n : ℕ} {pivot : Fin n}
    (targets : List (PivotComplement pivot)) : List (Fin n) :=
  targets.map Subtype.val

theorem pivotTargetWires_nodup {n : ℕ} {pivot : Fin n}
    {targets : List (PivotComplement pivot)} (hnodup : targets.Nodup) :
    (pivotTargetWires targets).Nodup := by
  exact hnodup.map Subtype.val_injective

@[simp]
theorem mem_pivotTargetWires_otherDifferenceTargets {n : ℕ}
    (first second : Basis n) (hfirstSecond : first ≠ second)
    (wire : Fin n) :
    wire ∈ pivotTargetWires (otherDifferenceTargets first second hfirstSecond) ↔
      wire ≠ differingPivot first second hfirstSecond ∧
        first wire ≠ second wire := by
  constructor
  · intro hmem
    rw [pivotTargetWires, List.mem_map] at hmem
    rcases hmem with ⟨target, htarget, rfl⟩
    exact ⟨target.property,
      (mem_otherDifferenceTargets first second hfirstSecond target).mp htarget⟩
  · rintro ⟨hwire, hdiff⟩
    rw [pivotTargetWires, List.mem_map]
    exact ⟨⟨wire, hwire⟩,
      (mem_otherDifferenceTargets first second hfirstSecond ⟨wire, hwire⟩).2 hdiff,
      rfl⟩

/-- Literal chronological CNOT list with the common control `pivot`. -/
def pivotClearCircuit {n : ℕ} (pivot : Fin n)
    (targets : List (PivotComplement pivot)) : Circuit n :=
  targets.map fun (target : PivotComplement pivot) =>
    Primitive.cnot pivot (target : Fin n) (Ne.symm target.property)

/-- Basis update performed by `pivotClearCircuit`. -/
def pivotClearBasis {n : ℕ} (pivot : Fin n) :
    List (PivotComplement pivot) → Basis n → Basis n
  | [], input => input
  | target :: targets, input =>
      pivotClearBasis pivot targets
        (if input pivot then setTarget target input (!input target) else input)

@[simp]
theorem pivotClearCircuit_nil {n : ℕ} (pivot : Fin n) :
    pivotClearCircuit pivot [] = [] := rfl

@[simp]
theorem pivotClearCircuit_cons {n : ℕ} (pivot : Fin n)
    (target : PivotComplement pivot) (targets : List (PivotComplement pivot)) :
    pivotClearCircuit pivot (target :: targets) =
      Primitive.cnot pivot target (Ne.symm target.property) ::
        pivotClearCircuit pivot targets := rfl

@[simp]
theorem pivotClearBasis_nil {n : ℕ} (pivot : Fin n) (input : Basis n) :
    pivotClearBasis pivot [] input = input := rfl

@[simp]
theorem pivotClearBasis_cons {n : ℕ} (pivot : Fin n)
    (target : PivotComplement pivot) (targets : List (PivotComplement pivot))
    (input : Basis n) :
    pivotClearBasis pivot (target :: targets) input =
      pivotClearBasis pivot targets
        (if input pivot then setTarget target input (!input target) else input) := rfl

/-- Exact full-register basis action of the common-control CNOT list. -/
@[simp]
theorem eval_pivotClearCircuit_mulVec_basisKet {n : ℕ} (pivot : Fin n) :
    ∀ (targets : List (PivotComplement pivot)) (input : Basis n),
      (Circuit.eval (pivotClearCircuit pivot targets) : Gate n) *ᵥ basisKet input =
        basisKet (pivotClearBasis pivot targets input)
  | [], input => by simp [pivotClearCircuit, pivotClearBasis]
  | target :: targets, input => by
      rw [pivotClearCircuit_cons, Circuit.eval_cons]
      change (((Circuit.eval (pivotClearCircuit pivot targets) : UnitaryGate n) : Gate n) *
          (((Primitive.cnot pivot (target : Fin n) (Ne.symm target.property)).denotation :
            UnitaryGate n) : Gate n)) *ᵥ basisKet input = _
      rw [← Matrix.mulVec_mulVec, Primitive.cnot_denotation_val,
        cnotRaw_mulVec_basisKet,
        eval_pivotClearCircuit_mulVec_basisKet]
      rfl

/-- A common-control CNOT list is either a target-toggle list or the identity. -/
theorem pivotClearBasis_eq_if {n : ℕ} (pivot : Fin n) :
    ∀ (targets : List (PivotComplement pivot)) (input : Basis n),
      pivotClearBasis pivot targets input =
        if input pivot then toggleBasis (pivotTargetWires targets) input else input
  | [], input => by simp [pivotClearBasis, pivotTargetWires]
  | target :: targets, input => by
      rw [pivotClearBasis_cons]
      by_cases hcontrol : input pivot
      · rw [if_pos hcontrol, pivotClearBasis_eq_if]
        have hupdated :
            setTarget (target : Fin n) input (!input target) pivot = true := by
          rw [setTarget_apply_of_ne]
          · exact hcontrol
          · exact Ne.symm target.property
        rw [if_pos hupdated]
        rw [if_pos hcontrol]
        rfl
      · rw [if_neg hcontrol, pivotClearBasis_eq_if, if_neg hcontrol]
        rw [if_neg hcontrol]

theorem pivotClearBasis_apply_of_nodup {n : ℕ} (pivot : Fin n)
    {targets : List (PivotComplement pivot)} (hnodup : targets.Nodup)
    (input : Basis n) (wire : Fin n) :
    pivotClearBasis pivot targets input wire =
      if input pivot then
        if wire ∈ pivotTargetWires targets then !input wire else input wire
      else input wire := by
  rw [pivotClearBasis_eq_if]
  by_cases hcontrol : input pivot
  · simpa [hcontrol] using
      toggleBasis_apply_of_nodup (pivotTargetWires_nodup hnodup) input wire
  · simp [hcontrol]

theorem pivotClearBasis_basisDifference {n : ℕ}
    (first second : Basis n) (hfirstSecond : first ≠ second) :
    pivotClearBasis (differingPivot first second hfirstSecond)
        (otherDifferenceTargets first second hfirstSecond)
        (basisDifference first second) =
      singletonBasis (differingPivot first second hfirstSecond) := by
  let pivot := differingPivot first second hfirstSecond
  funext wire
  rw [pivotClearBasis_apply_of_nodup _
    (otherDifferenceTargets_nodup first second hfirstSecond)]
  rw [if_pos (basisDifference_differingPivot first second hfirstSecond)]
  by_cases hwire : wire = pivot
  · subst wire
    simp [singletonBasis, pivot,
      mem_pivotTargetWires_otherDifferenceTargets]
  · by_cases hdiff : first wire ≠ second wire
    · simp [singletonBasis, pivot, hwire, hdiff,
        basisDifference, mem_pivotTargetWires_otherDifferenceTargets]
    · simp [singletonBasis, pivot, hwire,
        basisDifference, not_ne_iff.mp hdiff,
        mem_pivotTargetWires_otherDifferenceTargets]

/-! ## The complete affine pair transport -/

/-- Pointwise action of the affine pair transport. -/
def affinePairBasis {controlCount : ℕ}
    (first second : Basis (controlCount + 1))
    (hfirstSecond : first ≠ second) (input : Basis (controlCount + 1)) :
    Basis (controlCount + 1) :=
  pivotClearBasis (differingPivot first second hfirstSecond)
    (otherDifferenceTargets first second hfirstSecond)
    (toggleBasis (trueWireList first) input)

/--
Literal one-qubit/CNOT circuit normalizing an arbitrary distinct ordered pair.
-/
def affinePairCircuit {controlCount : ℕ}
    (first second : Basis (controlCount + 1))
    (hfirstSecond : first ≠ second) : Circuit (controlCount + 1) :=
  Circuit.append
    (xCircuit (trueWireList first))
    (pivotClearCircuit (differingPivot first second hfirstSecond)
      (otherDifferenceTargets first second hfirstSecond))

@[simp]
theorem eval_affinePairCircuit_mulVec_basisKet {controlCount : ℕ}
    (first second : Basis (controlCount + 1))
    (hfirstSecond : first ≠ second) (input : Basis (controlCount + 1)) :
    (Circuit.eval (affinePairCircuit first second hfirstSecond) :
        Gate (controlCount + 1)) *ᵥ basisKet input =
      basisKet (affinePairBasis first second hfirstSecond input) := by
  rw [affinePairCircuit, Circuit.eval_append]
  change (((Circuit.eval
      (pivotClearCircuit (differingPivot first second hfirstSecond)
        (otherDifferenceTargets first second hfirstSecond)) :
          UnitaryGate (controlCount + 1)) : Gate (controlCount + 1)) *
      ((Circuit.eval (xCircuit (trueWireList first)) :
          UnitaryGate (controlCount + 1)) : Gate (controlCount + 1))) *ᵥ
        basisKet input = _
  rw [← Matrix.mulVec_mulVec, eval_xCircuit_mulVec_basisKet,
    eval_pivotClearCircuit_mulVec_basisKet]
  rfl

@[simp]
theorem affinePairBasis_first {controlCount : ℕ}
    (first second : Basis (controlCount + 1))
    (hfirstSecond : first ≠ second) :
    affinePairBasis first second hfirstSecond first = allZeroBasis := by
  rw [affinePairBasis, toggleBasis_trueWireList_self]
  rw [pivotClearBasis_eq_if]
  simp

@[simp]
theorem affinePairBasis_second {controlCount : ℕ}
    (first second : Basis (controlCount + 1))
    (hfirstSecond : first ≠ second) :
    affinePairBasis first second hfirstSecond second =
      singletonBasis (differingPivot first second hfirstSecond) := by
  rw [affinePairBasis, toggleBasis_trueWireList_second]
  exact pivotClearBasis_basisDifference first second hfirstSecond

/-- Exact full-register action on the first ordered endpoint. -/
@[simp]
theorem eval_affinePairCircuit_first {controlCount : ℕ}
    (first second : Basis (controlCount + 1))
    (hfirstSecond : first ≠ second) :
    (Circuit.eval (affinePairCircuit first second hfirstSecond) :
        Gate (controlCount + 1)) *ᵥ basisKet first =
      basisKet allZeroBasis := by
  rw [eval_affinePairCircuit_mulVec_basisKet, affinePairBasis_first]

/-- Exact full-register action on the second ordered endpoint. -/
@[simp]
theorem eval_affinePairCircuit_second {controlCount : ℕ}
    (first second : Basis (controlCount + 1))
    (hfirstSecond : first ≠ second) :
    (Circuit.eval (affinePairCircuit first second hfirstSecond) :
        Gate (controlCount + 1)) *ᵥ basisKet second =
      basisKet (singletonBasis (differingPivot first second hfirstSecond)) := by
  rw [eval_affinePairCircuit_mulVec_basisKet, affinePairBasis_second]

/-! ## Exact literal-syntax resources -/

/-- Number of CNOTs in the clearing suffix. -/
def affinePairCNOTCount {controlCount : ℕ}
    (first second : Basis (controlCount + 1))
    (hfirstSecond : first ≠ second) : ℕ :=
  (otherDifferenceTargets first second hfirstSecond).length

/-- Total number of primitive occurrences in the affine transport. -/
def affinePairGateCount {controlCount : ℕ}
    (first second : Basis (controlCount + 1))
    (hfirstSecond : first ≠ second) : ℕ :=
  trueBitCount first + affinePairCNOTCount first second hfirstSecond

@[simp]
theorem affinePairCNOTCount_eq {controlCount : ℕ}
    (first second : Basis (controlCount + 1))
    (hfirstSecond : first ≠ second) :
    affinePairCNOTCount first second hfirstSecond =
      hammingDist first second - 1 := by
  exact length_otherDifferenceTargets first second hfirstSecond

@[simp]
theorem affinePairGateCount_eq {controlCount : ℕ}
    (first second : Basis (controlCount + 1))
    (hfirstSecond : first ≠ second) :
    affinePairGateCount first second hfirstSecond =
      trueBitCount first + (hammingDist first second - 1) := by
  simp [affinePairGateCount]

@[simp]
theorem affinePairCircuit_gateCount {controlCount : ℕ}
    (first second : Basis (controlCount + 1))
    (hfirstSecond : first ≠ second) :
    Circuit.gateCount (affinePairCircuit first second hfirstSecond) =
      affinePairGateCount first second hfirstSecond := by
  rw [affinePairCircuit, Circuit.gateCount_append]
  simp [affinePairGateCount, affinePairCNOTCount,
    trueBitCount, xCircuit, pivotClearCircuit, Circuit.gateCount]

private theorem xCircuit_oneQubitKindCount {n : ℕ} :
    ∀ wires : List (Fin n),
      Circuit.kindCount PrimitiveKind.oneQubit (xCircuit wires) = wires.length
  | [] => rfl
  | wire :: wires => by
      have ih : List.countP (fun primitive =>
          decide (primitive.kind = PrimitiveKind.oneQubit)) (xCircuit wires) =
          wires.length := by
        simpa only [Circuit.kindCount] using xCircuit_oneQubitKindCount wires
      rw [xCircuit_cons]
      change List.countP (fun primitive =>
        decide (primitive.kind = PrimitiveKind.oneQubit))
          (Primitive.oneQubit wire pauliX :: xCircuit wires) = _
      rw [List.countP_cons]
      simp [ih]

private theorem xCircuit_cnotKindCount {n : ℕ} :
    ∀ wires : List (Fin n),
      Circuit.kindCount PrimitiveKind.cnot (xCircuit wires) = 0
  | [] => rfl
  | wire :: wires => by
      have ih : List.countP (fun primitive =>
          decide (primitive.kind = PrimitiveKind.cnot)) (xCircuit wires) = 0 := by
        simpa only [Circuit.kindCount] using xCircuit_cnotKindCount wires
      rw [xCircuit_cons]
      change List.countP (fun primitive =>
        decide (primitive.kind = PrimitiveKind.cnot))
          (Primitive.oneQubit wire pauliX :: xCircuit wires) = 0
      rw [List.countP_cons]
      simp [ih]

private theorem pivotClearCircuit_oneQubitKindCount {n : ℕ} (pivot : Fin n) :
    ∀ targets : List (PivotComplement pivot),
      Circuit.kindCount PrimitiveKind.oneQubit
        (pivotClearCircuit pivot targets) = 0
  | [] => rfl
  | target :: targets => by
      have ih : List.countP (fun primitive =>
          decide (primitive.kind = PrimitiveKind.oneQubit))
          (pivotClearCircuit pivot targets) = 0 := by
        simpa only [Circuit.kindCount] using
          pivotClearCircuit_oneQubitKindCount pivot targets
      rw [pivotClearCircuit_cons]
      change List.countP (fun primitive =>
        decide (primitive.kind = PrimitiveKind.oneQubit))
          (Primitive.cnot pivot target (Ne.symm target.property) ::
            pivotClearCircuit pivot targets) = 0
      rw [List.countP_cons]
      simp [ih]

private theorem pivotClearCircuit_cnotKindCount {n : ℕ} (pivot : Fin n) :
    ∀ targets : List (PivotComplement pivot),
      Circuit.kindCount PrimitiveKind.cnot (pivotClearCircuit pivot targets) =
        targets.length
  | [] => rfl
  | target :: targets => by
      have ih : List.countP (fun primitive =>
          decide (primitive.kind = PrimitiveKind.cnot))
          (pivotClearCircuit pivot targets) = targets.length := by
        simpa only [Circuit.kindCount] using
          pivotClearCircuit_cnotKindCount pivot targets
      rw [pivotClearCircuit_cons]
      change List.countP (fun primitive =>
        decide (primitive.kind = PrimitiveKind.cnot))
          (Primitive.cnot pivot target (Ne.symm target.property) ::
            pivotClearCircuit pivot targets) = _
      rw [List.countP_cons]
      simp [ih]

/-- Exact number of one-qubit primitive occurrences in the literal transport. -/
@[simp]
theorem affinePairCircuit_oneQubitCount {controlCount : ℕ}
    (first second : Basis (controlCount + 1))
    (hfirstSecond : first ≠ second) :
    Circuit.kindCount .oneQubit (affinePairCircuit first second hfirstSecond) =
      trueBitCount first := by
  rw [affinePairCircuit, Circuit.kindCount_append,
    xCircuit_oneQubitKindCount,
    pivotClearCircuit_oneQubitKindCount
      (differingPivot first second hfirstSecond)
      (otherDifferenceTargets first second hfirstSecond)]
  simp [trueBitCount]

/-- Exact number of CNOT primitive occurrences in the literal transport. -/
@[simp]
theorem affinePairCircuit_cnotCount {controlCount : ℕ}
    (first second : Basis (controlCount + 1))
    (hfirstSecond : first ≠ second) :
    Circuit.kindCount .cnot (affinePairCircuit first second hfirstSecond) =
      hammingDist first second - 1 := by
  rw [affinePairCircuit, Circuit.kindCount_append,
    xCircuit_cnotKindCount,
    pivotClearCircuit_cnotKindCount
      (differingPivot first second hfirstSecond)
      (otherDifferenceTargets first second hfirstSecond),
    length_otherDifferenceTargets]
  simp

private theorem xCircuit_oneQubitCNOTCost {n : ℕ} (wires : List (Fin n)) :
    Circuit.cost CostModel.oneQubitCNOT (xCircuit wires) = some wires.length := by
  induction wires with
  | nil => rfl
  | cons wire wires ih =>
      rw [xCircuit_cons, Circuit.cost_cons, Primitive.oneQubit_kind,
        CostModel.oneQubitCNOT_oneQubit, ih]
      simp [Circuit.addCost]
      omega

private theorem pivotClearCircuit_oneQubitCNOTCost {n : ℕ} (pivot : Fin n)
    (targets : List (PivotComplement pivot)) :
    Circuit.cost CostModel.oneQubitCNOT (pivotClearCircuit pivot targets) =
      some targets.length := by
  induction targets with
  | nil => rfl
  | cons target targets ih =>
      rw [pivotClearCircuit_cons, Circuit.cost_cons, Primitive.cnot_kind,
        CostModel.oneQubitCNOT_cnot, ih]
      simp [Circuit.addCost]
      omega

/-- The one-qubit/CNOT model accepts the literal affine transport exactly. -/
@[simp]
theorem affinePairCircuit_oneQubitCNOTCost {controlCount : ℕ}
    (first second : Basis (controlCount + 1))
    (hfirstSecond : first ≠ second) :
    Circuit.cost CostModel.oneQubitCNOT
        (affinePairCircuit first second hfirstSecond) =
      some (affinePairGateCount first second hfirstSecond) := by
  rw [affinePairCircuit, Circuit.cost_append,
    xCircuit_oneQubitCNOTCost, pivotClearCircuit_oneQubitCNOTCost]
  simp [Circuit.addCost, affinePairGateCount, affinePairCNOTCount,
    trueBitCount]

end

end Barenco.Universality
