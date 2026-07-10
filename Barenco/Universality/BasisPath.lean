import Barenco.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Chain
import Mathlib.InformationTheory.Hamming
import Mathlib.Tactic

/-!
# Canonical shortest paths through the computational basis

Two computational-basis assignments are joined by changing their differing
wires once each, in increasing `Fin` order.  The path includes both endpoints.
Its edge labels are exposed separately, so later circuit constructions can use
the precise wire changed at every step without recovering it from an existence
proof.

This module is purely finite combinatorics: it imports no gate or circuit
semantics.
-/

namespace Barenco.Universality

/-- The wires on which two basis assignments differ. -/
def differingWires {n : ℕ} (first last : Basis n) : Finset (Fin n) :=
  Finset.univ.filter fun wire => first wire ≠ last wire

@[simp]
theorem mem_differingWires {n : ℕ} (first last : Basis n) (wire : Fin n) :
    wire ∈ differingWires first last ↔ first wire ≠ last wire := by
  simp [differingWires]

/-- The differing wires in the canonical, increasing register order. -/
def differingWireList {n : ℕ} (first last : Basis n) : List (Fin n) :=
  (differingWires first last).sort

@[simp]
theorem mem_differingWireList {n : ℕ} (first last : Basis n) (wire : Fin n) :
    wire ∈ differingWireList first last ↔ first wire ≠ last wire := by
  simp [differingWireList]

theorem differingWireList_nodup {n : ℕ} (first last : Basis n) :
    (differingWireList first last).Nodup := by
  exact Finset.sort_nodup _ _

theorem differingWireList_sorted {n : ℕ} (first last : Basis n) :
    (differingWireList first last).Pairwise (· ≤ ·) := by
  exact Finset.pairwise_sort _ _

@[simp]
theorem length_differingWireList {n : ℕ} (first last : Basis n) :
    (differingWireList first last).length = hammingDist first last := by
  simp [differingWireList, differingWires, hammingDist]

theorem length_differingWireList_le {n : ℕ} (first last : Basis n) :
    (differingWireList first last).length ≤ n := by
  rw [length_differingWireList]
  simpa using hammingDist_le_card_fintype (x := first) (y := last)

/-- Set one named wire to its value in the destination assignment. -/
private def setDestinationWire {n : ℕ} (last : Basis n)
    (state : Basis n) (wire : Fin n) : Basis n :=
  Function.update state wire (last wire)

/--
The canonical path from `first` to `last`, including both endpoints.

`List.scanl` makes the labels in `differingWireList first last` align exactly
with consecutive pairs in this list.
-/
def basisPath {n : ℕ} (first last : Basis n) : List (Basis n) :=
  List.scanl (setDestinationWire last) first (differingWireList first last)

/-- Two assignments differ at exactly the named wire. -/
def BasisStepAt {n : ℕ} (wire : Fin n) (first last : Basis n) : Prop :=
  first wire ≠ last wire ∧ ∀ other, other ≠ wire → first other = last other

/-- Two assignments are adjacent in the Boolean hypercube. -/
def BasisAdjacent {n : ℕ} (first last : Basis n) : Prop :=
  ∃ wire, BasisStepAt wire first last

private theorem foldl_setDestinationWire_apply {n : ℕ} (first last : Basis n)
    (wires : List (Fin n)) (query : Fin n) :
    (wires.foldl (setDestinationWire last) first) query =
      if query ∈ wires then last query else first query := by
  induction wires generalizing first with
  | nil => simp
  | cons wire wires ih =>
      rw [List.foldl_cons, ih]
      by_cases htail : query ∈ wires
      · simp [htail]
      · by_cases hquery : query = wire
        · subst query
          simp [htail, setDestinationWire]
        · simp [htail, hquery, setDestinationWire]

private theorem getElem_not_mem_take_of_nodup {X : Type*} {items : List X}
    (hnodup : items.Nodup) (index : ℕ) (hindex : index < items.length) :
    items[index] ∉ items.take index := by
  intro hmem
  obtain ⟨prior, hprior, heq⟩ := List.mem_iff_getElem.mp hmem
  have hpriorIndex : prior < index := by
    simpa [List.length_take, Nat.min_eq_left (Nat.le_of_lt hindex)] using hprior
  have hpriorItems : prior < items.length := lt_trans hpriorIndex hindex
  have heq' : items[prior] = items[index] := by
    simpa using heq
  have : prior = index :=
    (hnodup.getElem_inj_iff (hi := hpriorItems) (hj := hindex)).mp heq'
  omega

private theorem getElem_mem_take_of_lt {X : Type*} {items : List X}
    (firstIndex laterIndex : ℕ) (hlater : laterIndex ≤ items.length)
    (hindex : firstIndex < laterIndex) :
    items[firstIndex]'(lt_of_lt_of_le hindex hlater) ∈ items.take laterIndex := by
  have hlength : firstIndex < (items.take laterIndex).length := by
    simp [List.length_take, Nat.min_eq_left hlater, hindex]
  have hmem := List.getElem_mem (l := items.take laterIndex) hlength
  simpa using hmem

theorem basisPath_getElem_apply {n : ℕ} (first last : Basis n)
    (index : ℕ) (hindex : index < (basisPath first last).length) (wire : Fin n) :
    (basisPath first last)[index] wire =
      if wire ∈ (differingWireList first last).take index
      then last wire else first wire := by
  change (List.scanl (setDestinationWire last) first
    (differingWireList first last))[index] wire = _
  rw [List.getElem_scanl]
  exact foldl_setDestinationWire_apply first last _ wire

@[simp]
theorem length_basisPath {n : ℕ} (first last : Basis n) :
    (basisPath first last).length = hammingDist first last + 1 := by
  simp [basisPath]

theorem length_basisPath_le {n : ℕ} (first last : Basis n) :
    (basisPath first last).length ≤ n + 1 := by
  rw [length_basisPath]
  exact Nat.add_le_add_right
    (by simpa using hammingDist_le_card_fintype (x := first) (y := last)) 1

@[simp]
theorem head?_basisPath {n : ℕ} (first last : Basis n) :
    (basisPath first last).head? = some first := by
  exact List.head?_scanl

theorem basisPath_ne_nil {n : ℕ} (first last : Basis n) :
    basisPath first last ≠ [] := by
  intro h
  have := congrArg List.head? h
  simp at this

theorem getLast?_basisPath {n : ℕ} (first last : Basis n) :
    (basisPath first last).getLast? = some last := by
  rw [basisPath, List.getLast?_scanl]
  congr 1
  funext wire
  rw [foldl_setDestinationWire_apply]
  by_cases hdiff : first wire ≠ last wire
  · simp [hdiff]
  · simp [not_ne_iff.mp hdiff]

theorem basisPath_getLast {n : ℕ} (first last : Basis n) :
    (basisPath first last).getLast (basisPath_ne_nil first last) = last := by
  have hlast := List.getLast?_eq_some_getLast (basisPath_ne_nil first last)
  exact Option.some.inj ((getLast?_basisPath first last).symm.trans hlast)

private theorem basisPath_getElem_succ_eq_update {n : ℕ}
    (first last : Basis n) (index : ℕ)
    (hindex : index < (differingWireList first last).length) :
    (basisPath first last)[index + 1]'(by
        rw [length_basisPath, ← length_differingWireList]
        omega) =
      Function.update
        ((basisPath first last)[index]'(by
          rw [length_basisPath, ← length_differingWireList]
          omega))
        ((differingWireList first last)[index])
        (last ((differingWireList first last)[index])) := by
  simp only [basisPath, List.getElem_scanl]
  rw [List.take_succ, List.getElem?_eq_getElem hindex, List.foldl_append]
  simp [setDestinationWire]

/-- The edge at `index` changes exactly the correspondingly indexed wire label. -/
theorem basisPath_stepAt_getElem {n : ℕ} (first last : Basis n)
    (index : ℕ) (hindex : index < (differingWireList first last).length) :
    BasisStepAt
      ((differingWireList first last)[index])
      ((basisPath first last)[index]'(by simp; omega))
      ((basisPath first last)[index + 1]'(by
        rw [length_basisPath, ← length_differingWireList]
        omega)) := by
  let wire := (differingWireList first last)[index]
  have hupdate := basisPath_getElem_succ_eq_update first last index hindex
  have hnotMem : wire ∉ (differingWireList first last).take index := by
    exact getElem_not_mem_take_of_nodup
      (differingWireList_nodup first last) index hindex
  have hcurrent :
      ((basisPath first last)[index]'(by
        rw [length_basisPath, ← length_differingWireList]
        omega)) wire = first wire := by
    rw [basisPath_getElem_apply]
    simp [hnotMem]
  have hdiff : first wire ≠ last wire := by
    exact (mem_differingWireList first last wire).mp
      (List.getElem_mem hindex)
  constructor
  · rw [hupdate, Function.update_apply, if_pos rfl, hcurrent]
    exact hdiff
  · intro other hother
    rw [hupdate, Function.update_apply, if_neg hother]

theorem basisPath_edge_hammingDist {n : ℕ} (first last : Basis n)
    (index : ℕ) (hindex : index < (differingWireList first last).length) :
    hammingDist
      ((basisPath first last)[index]'(by
        rw [length_basisPath, ← length_differingWireList]
        omega))
      ((basisPath first last)[index + 1]'(by
        rw [length_basisPath, ← length_differingWireList]
        omega)) = 1 := by
  let wire := (differingWireList first last)[index]
  have hstep := basisPath_stepAt_getElem first last index hindex
  rw [hammingDist]
  have hfilter :
      Finset.univ.filter (fun query =>
        ((basisPath first last)[index]'(by
          rw [length_basisPath, ← length_differingWireList]
          omega)) query ≠
          ((basisPath first last)[index + 1]'(by
            rw [length_basisPath, ← length_differingWireList]
            omega)) query) = {wire} := by
    ext query
    by_cases hquery : query = wire
    · subst query
      simp [hstep.1]
    · simp [hquery, hstep.2 query hquery]
  rw [hfilter]
  simp

/-- Every consecutive pair in the canonical path is hypercube-adjacent. -/
theorem basisPath_isChain {n : ℕ} (first last : Basis n) :
    (basisPath first last).IsChain BasisAdjacent := by
  rw [List.isChain_iff_getElem]
  intro index hindex
  have hlabel : index < (differingWireList first last).length := by
    simpa [basisPath] using hindex
  exact ⟨(differingWireList first last)[index],
    basisPath_stepAt_getElem first last index hlabel⟩

/-- The canonical path never revisits a basis assignment. -/
theorem basisPath_nodup {n : ℕ} (first last : Basis n) :
    (basisPath first last).Nodup := by
  rw [List.nodup_iff_pairwise_ne]
  rw [List.pairwise_iff_getElem]
  intro firstIndex laterIndex hfirstPath hlaterPath hindices
  have hfirstLabel : firstIndex < (differingWireList first last).length := by
    simp only [length_basisPath] at hlaterPath
    rw [← length_differingWireList] at hlaterPath
    omega
  have hlaterLe : laterIndex ≤ (differingWireList first last).length := by
    simp only [length_basisPath] at hlaterPath
    rw [← length_differingWireList] at hlaterPath
    omega
  let wire := (differingWireList first last)[firstIndex]
  have hnotMem :
      wire ∉ (differingWireList first last).take firstIndex := by
    exact getElem_not_mem_take_of_nodup
      (differingWireList_nodup first last) firstIndex hfirstLabel
  have hmem : wire ∈ (differingWireList first last).take laterIndex := by
    exact getElem_mem_take_of_lt firstIndex laterIndex hlaterLe hindices
  have hdiff : first wire ≠ last wire := by
    exact (mem_differingWireList first last wire).mp
      (List.getElem_mem hfirstLabel)
  intro heq
  have happly := congrFun heq wire
  rw [basisPath_getElem_apply, if_neg hnotMem,
    basisPath_getElem_apply, if_pos hmem] at happly
  exact hdiff happly

@[simp]
theorem differingWireList_self {n : ℕ} (first : Basis n) :
    differingWireList first first = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro wire
  simp

@[simp]
theorem basisPath_self {n : ℕ} (first : Basis n) :
    basisPath first first = [first] := by
  simp [basisPath]

/-- Equal endpoints give the unique zero-edge boundary case. -/
theorem basisPath_eq_singleton_iff {n : ℕ} (first last : Basis n) :
    basisPath first last = [first] ↔ first = last := by
  constructor
  · intro h
    have hlength := congrArg List.length h
    simp only [length_basisPath, List.length_singleton] at hlength
    have : hammingDist first last = 0 := by omega
    exact hammingDist_eq_zero.mp this
  · rintro rfl
    exact basisPath_self first

theorem one_lt_length_basisPath_iff {n : ℕ} (first last : Basis n) :
    1 < (basisPath first last).length ↔ first ≠ last := by
  rw [length_basisPath]
  calc
    1 < hammingDist first last + 1 ↔ 0 < hammingDist first last := by omega
    _ ↔ first ≠ last := hammingDist_pos

end Barenco.Universality
