import Barenco.Basic
import Mathlib.Logic.Equiv.Prod

/-!
# Ordered two-wire register layouts

This module separates two selected wires from the remaining wires of a finite
qubit register.  The pair is ordered: local bit `0` is the pair's `first` wire
and local bit `1` is its `second` wire.  Consequently `Basis 2` uses the local
basis order `00, 01, 10, 11` for `(first, second)`.

Only basis layout is defined here.  In particular, this leaf contains no gate,
circuit, support, or cost semantics.
-/

namespace Barenco

/-- Two distinct ambient wires, with semantically significant orientation. -/
structure OrderedWirePair (n : ℕ) where
  first : Fin n
  second : Fin n
  ne : first ≠ second
deriving DecidableEq

namespace OrderedWirePair

@[ext]
theorem ext {n : ℕ} {pair other : OrderedWirePair n}
    (hfirst : pair.first = other.first)
    (hsecond : pair.second = other.second) : pair = other := by
  cases pair
  cases other
  simp_all

theorem eq_iff {n : ℕ} {pair other : OrderedWirePair n} :
    pair = other ↔ pair.first = other.first ∧ pair.second = other.second := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨hfirst, hsecond⟩
    exact ext hfirst hsecond

/-- Reverse the orientation of an ordered wire pair. -/
def swap {n : ℕ} (pair : OrderedWirePair n) : OrderedWirePair n :=
  ⟨pair.second, pair.first, pair.ne.symm⟩

@[simp]
theorem swap_first {n : ℕ} (pair : OrderedWirePair n) :
    pair.swap.first = pair.second := rfl

@[simp]
theorem swap_second {n : ℕ} (pair : OrderedWirePair n) :
    pair.swap.second = pair.first := rfl

@[simp]
theorem swap_ne {n : ℕ} (pair : OrderedWirePair n) :
    pair.swap.ne = pair.ne.symm := rfl

@[simp]
theorem swap_swap {n : ℕ} (pair : OrderedWirePair n) :
    pair.swap.swap = pair := by
  ext <;> rfl

theorem swap_injective {n : ℕ} :
    Function.Injective (@swap n) := by
  intro pair other h
  simpa using congrArg swap h

end OrderedWirePair

/-- Ambient wire indices other than either member of `pair`. -/
abbrev PairComplement {n : ℕ} (pair : OrderedWirePair n) :=
  {wire : Fin n // wire ≠ pair.first ∧ wire ≠ pair.second}

/-- Computational-basis assignments on all wires outside `pair`. -/
abbrev PairComplementBasis {n : ℕ} (pair : OrderedWirePair n) :=
  PairComplement pair → Bool

/--
Read the two selected bits in pair order.  Local bit `0` is `pair.first` and
local bit `1` is `pair.second`.
-/
def twoWireLocalBits {n : ℕ} (pair : OrderedWirePair n)
    (input : Basis n) : Basis 2 :=
  (finTwoArrowEquiv Bool).symm (input pair.first, input pair.second)

@[simp]
theorem twoWireLocalBits_zero {n : ℕ} (pair : OrderedWirePair n)
    (input : Basis n) :
    twoWireLocalBits pair input 0 = input pair.first := by
  simp [twoWireLocalBits, finTwoArrowEquiv_symm_apply]

@[simp]
theorem twoWireLocalBits_one {n : ℕ} (pair : OrderedWirePair n)
    (input : Basis n) :
    twoWireLocalBits pair input 1 = input pair.second := by
  simp [twoWireLocalBits, finTwoArrowEquiv_symm_apply]

/-- Restrict an ambient assignment to the spectator wires outside `pair`. -/
def twoWireSpectatorBits {n : ℕ} (pair : OrderedWirePair n)
    (input : Basis n) : PairComplementBasis pair :=
  fun wire ↦ input wire

@[simp]
theorem twoWireSpectatorBits_apply {n : ℕ} (pair : OrderedWirePair n)
    (input : Basis n) (wire : PairComplement pair) :
    twoWireSpectatorBits pair input wire = input wire := rfl

/-- Reconstruct an ambient assignment from pair-local and spectator bits. -/
def reconstructTwoWire {n : ℕ} (pair : OrderedWirePair n)
    (bits : Basis 2) (spectators : PairComplementBasis pair) : Basis n :=
  fun wire ↦
    if hfirst : wire = pair.first then bits 0
    else if hsecond : wire = pair.second then bits 1
    else spectators ⟨wire, hfirst, hsecond⟩

@[simp]
theorem reconstructTwoWire_apply_first {n : ℕ} (pair : OrderedWirePair n)
    (bits : Basis 2) (spectators : PairComplementBasis pair) :
    reconstructTwoWire pair bits spectators pair.first = bits 0 := by
  simp [reconstructTwoWire]

@[simp]
theorem reconstructTwoWire_apply_second {n : ℕ} (pair : OrderedWirePair n)
    (bits : Basis 2) (spectators : PairComplementBasis pair) :
    reconstructTwoWire pair bits spectators pair.second = bits 1 := by
  simp [reconstructTwoWire, pair.ne.symm]

@[simp]
theorem reconstructTwoWire_apply_complement {n : ℕ} (pair : OrderedWirePair n)
    (bits : Basis 2) (spectators : PairComplementBasis pair)
    (wire : PairComplement pair) :
    reconstructTwoWire pair bits spectators wire = spectators wire := by
  simp [reconstructTwoWire, wire.property.1, wire.property.2]

/--
Split an ambient assignment into its ordered two-bit local assignment and all
spectator bits.  The inverse is `reconstructTwoWire`.
-/
def splitTwoWire {n : ℕ} (pair : OrderedWirePair n) :
    Basis n ≃ Basis 2 × PairComplementBasis pair where
  toFun input :=
    (twoWireLocalBits pair input, twoWireSpectatorBits pair input)
  invFun data := reconstructTwoWire pair data.1 data.2
  left_inv input := by
    funext wire
    by_cases hfirst : wire = pair.first
    · subst wire
      simp
    · by_cases hsecond : wire = pair.second
      · subst wire
        simp
      · simp [reconstructTwoWire, hfirst, hsecond]
  right_inv data := by
    apply Prod.ext
    · apply (finTwoArrowEquiv Bool).injective
      apply Prod.ext <;> simp
    · funext wire
      simp

@[simp]
theorem splitTwoWire_fst {n : ℕ} (pair : OrderedWirePair n)
    (input : Basis n) :
    (splitTwoWire pair input).1 = twoWireLocalBits pair input := rfl

@[simp]
theorem splitTwoWire_snd {n : ℕ} (pair : OrderedWirePair n)
    (input : Basis n) :
    (splitTwoWire pair input).2 = twoWireSpectatorBits pair input := rfl

@[simp]
theorem splitTwoWire_snd_apply {n : ℕ} (pair : OrderedWirePair n)
    (input : Basis n) (wire : PairComplement pair) :
    (splitTwoWire pair input).2 wire = input wire := rfl

@[simp]
theorem splitTwoWire_symm_apply {n : ℕ} (pair : OrderedWirePair n)
    (data : Basis 2 × PairComplementBasis pair) :
    (splitTwoWire pair).symm data = reconstructTwoWire pair data.1 data.2 := rfl

@[simp]
theorem twoWireLocalBits_reconstructTwoWire {n : ℕ}
    (pair : OrderedWirePair n) (bits : Basis 2)
    (spectators : PairComplementBasis pair) :
    twoWireLocalBits pair (reconstructTwoWire pair bits spectators) = bits := by
  have h := congrArg Prod.fst ((splitTwoWire pair).apply_symm_apply (bits, spectators))
  simpa using h

@[simp]
theorem twoWireSpectatorBits_reconstructTwoWire {n : ℕ}
    (pair : OrderedWirePair n) (bits : Basis 2)
    (spectators : PairComplementBasis pair) :
    twoWireSpectatorBits pair (reconstructTwoWire pair bits spectators) = spectators := by
  have h := congrArg Prod.snd ((splitTwoWire pair).apply_symm_apply (bits, spectators))
  simpa using h

/-- Replace both selected bits at once and retain every spectator bit. -/
def setTwoWire {n : ℕ} (pair : OrderedWirePair n) (input : Basis n)
    (bits : Basis 2) : Basis n :=
  reconstructTwoWire pair bits (twoWireSpectatorBits pair input)

@[simp]
theorem setTwoWire_apply_first {n : ℕ} (pair : OrderedWirePair n)
    (input : Basis n) (bits : Basis 2) :
    setTwoWire pair input bits pair.first = bits 0 := by
  simp [setTwoWire]

@[simp]
theorem setTwoWire_apply_second {n : ℕ} (pair : OrderedWirePair n)
    (input : Basis n) (bits : Basis 2) :
    setTwoWire pair input bits pair.second = bits 1 := by
  simp [setTwoWire]

@[simp]
theorem setTwoWire_apply_of_ne {n : ℕ} (pair : OrderedWirePair n)
    (input : Basis n) (bits : Basis 2) (wire : Fin n)
    (hfirst : wire ≠ pair.first) (hsecond : wire ≠ pair.second) :
    setTwoWire pair input bits wire = input wire := by
  simp [setTwoWire, reconstructTwoWire, hfirst, hsecond]

@[simp]
theorem setTwoWire_apply_complement {n : ℕ} (pair : OrderedWirePair n)
    (input : Basis n) (bits : Basis 2) (wire : PairComplement pair) :
    setTwoWire pair input bits wire = input wire := by
  exact setTwoWire_apply_of_ne pair input bits wire wire.property.1 wire.property.2

@[simp]
theorem twoWireLocalBits_setTwoWire {n : ℕ} (pair : OrderedWirePair n)
    (input : Basis n) (bits : Basis 2) :
    twoWireLocalBits pair (setTwoWire pair input bits) = bits := by
  simp [setTwoWire]

@[simp]
theorem twoWireSpectatorBits_setTwoWire {n : ℕ} (pair : OrderedWirePair n)
    (input : Basis n) (bits : Basis 2) :
    twoWireSpectatorBits pair (setTwoWire pair input bits) =
      twoWireSpectatorBits pair input := by
  simp [setTwoWire]

@[simp]
theorem setTwoWire_self {n : ℕ} (pair : OrderedWirePair n)
    (input : Basis n) :
    setTwoWire pair input (twoWireLocalBits pair input) = input := by
  exact (splitTwoWire pair).symm_apply_apply input

@[simp]
theorem setTwoWire_setTwoWire {n : ℕ} (pair : OrderedWirePair n)
    (input : Basis n) (firstLocal secondLocal : Basis 2) :
    setTwoWire pair (setTwoWire pair input firstLocal) secondLocal =
      setTwoWire pair input secondLocal := by
  apply (splitTwoWire pair).injective
  apply Prod.ext <;> simp

/-- Two assignments agree on every spectator wire outside `pair`. -/
abbrev AgreeOffTwoWire {n : ℕ} (pair : OrderedWirePair n)
    (left right : Basis n) : Prop :=
  ∀ wire, wire ≠ pair.first → wire ≠ pair.second → left wire = right wire

theorem agreeOffTwoWire_refl {n : ℕ} (pair : OrderedWirePair n)
    (input : Basis n) : AgreeOffTwoWire pair input input := by
  intro wire hfirst hsecond
  rfl

theorem agreeOffTwoWire_symm {n : ℕ} {pair : OrderedWirePair n}
    {left right : Basis n} (h : AgreeOffTwoWire pair left right) :
    AgreeOffTwoWire pair right left := by
  intro wire hfirst hsecond
  exact (h wire hfirst hsecond).symm

theorem agreeOffTwoWire_trans {n : ℕ} {pair : OrderedWirePair n}
    {left middle right : Basis n}
    (hlm : AgreeOffTwoWire pair left middle)
    (hmr : AgreeOffTwoWire pair middle right) :
    AgreeOffTwoWire pair left right := by
  intro wire hfirst hsecond
  exact (hlm wire hfirst hsecond).trans (hmr wire hfirst hsecond)

theorem agreeOffTwoWire_iff_spectatorBits_eq {n : ℕ}
    (pair : OrderedWirePair n) (left right : Basis n) :
    AgreeOffTwoWire pair left right ↔
      twoWireSpectatorBits pair left = twoWireSpectatorBits pair right := by
  constructor
  · intro hagree
    funext wire
    exact hagree wire wire.property.1 wire.property.2
  · intro heq wire hfirst hsecond
    exact congrFun heq ⟨wire, hfirst, hsecond⟩

theorem splitTwoWire_snd_eq_iff {n : ℕ} (pair : OrderedWirePair n)
    (left right : Basis n) :
    (splitTwoWire pair left).2 = (splitTwoWire pair right).2 ↔
      AgreeOffTwoWire pair left right := by
  rw [splitTwoWire_snd, splitTwoWire_snd,
    agreeOffTwoWire_iff_spectatorBits_eq]

theorem agreeOffTwoWire_setTwoWire {n : ℕ} (pair : OrderedWirePair n)
    (input : Basis n) (bits : Basis 2) :
    AgreeOffTwoWire pair (setTwoWire pair input bits) input := by
  intro wire hfirst hsecond
  exact setTwoWire_apply_of_ne pair input bits wire hfirst hsecond

theorem agreeOffTwoWire_setTwoWire_right {n : ℕ}
    (pair : OrderedWirePair n) (input : Basis n) (bits : Basis 2) :
    AgreeOffTwoWire pair input (setTwoWire pair input bits) :=
  agreeOffTwoWire_symm (agreeOffTwoWire_setTwoWire pair input bits)

theorem eq_iff_localBits_eq_of_agreeOffTwoWire {n : ℕ}
    {pair : OrderedWirePair n} {left right : Basis n}
    (hagree : AgreeOffTwoWire pair left right) :
    left = right ↔
      twoWireLocalBits pair left = twoWireLocalBits pair right := by
  constructor
  · rintro rfl
    rfl
  · intro hlocal
    apply (splitTwoWire pair).injective
    apply Prod.ext
    · exact hlocal
    · exact (splitTwoWire_snd_eq_iff pair left right).2 hagree

theorem eq_iff_first_second_eq_of_agreeOffTwoWire {n : ℕ}
    {pair : OrderedWirePair n} {left right : Basis n}
    (hagree : AgreeOffTwoWire pair left right) :
    left = right ↔
      left pair.first = right pair.first ∧
      left pair.second = right pair.second := by
  rw [eq_iff_localBits_eq_of_agreeOffTwoWire hagree]
  constructor
  · intro h
    exact ⟨congrFun h 0, congrFun h 1⟩
  · rintro ⟨hfirst, hsecond⟩
    apply (finTwoArrowEquiv Bool).injective
    apply Prod.ext
    · simpa using hfirst
    · simpa using hsecond

theorem eq_setTwoWire_iff {n : ℕ} (pair : OrderedWirePair n)
    (left input : Basis n) (bits : Basis 2) :
    left = setTwoWire pair input bits ↔
      twoWireLocalBits pair left = bits ∧ AgreeOffTwoWire pair left input := by
  constructor
  · rintro rfl
    exact ⟨twoWireLocalBits_setTwoWire pair input bits,
      agreeOffTwoWire_setTwoWire pair input bits⟩
  · rintro ⟨hlocal, hagree⟩
    apply (splitTwoWire pair).injective
    apply Prod.ext
    · simpa using hlocal
    · simpa using (splitTwoWire_snd_eq_iff pair left input).2 hagree

theorem setTwoWire_eq_iff {n : ℕ} (pair : OrderedWirePair n)
    (input right : Basis n) (bits : Basis 2) :
    setTwoWire pair input bits = right ↔
      bits = twoWireLocalBits pair right ∧ AgreeOffTwoWire pair input right := by
  rw [eq_comm, eq_setTwoWire_iff]
  constructor
  · rintro ⟨hlocal, hagree⟩
    exact ⟨hlocal.symm, agreeOffTwoWire_symm hagree⟩
  · rintro ⟨hlocal, hagree⟩
    exact ⟨hlocal.symm, agreeOffTwoWire_symm hagree⟩

/-! ## Reversing local wire orientation -/

/-- Swap local bits `0` and `1` of a two-qubit basis assignment. -/
def reverseTwoQubitBasis : Basis 2 ≃ Basis 2 :=
  Equiv.piCongrLeft (fun _ : Fin 2 ↦ Bool) (Equiv.swap 0 1)

@[simp]
theorem reverseTwoQubitBasis_zero (input : Basis 2) :
    reverseTwoQubitBasis input 0 = input 1 := by
  rw [reverseTwoQubitBasis]
  have h := Equiv.piCongrLeft_apply_apply (fun _ : Fin 2 ↦ Bool)
    (Equiv.swap 0 1) input 1
  simpa using h

@[simp]
theorem reverseTwoQubitBasis_one (input : Basis 2) :
    reverseTwoQubitBasis input 1 = input 0 := by
  rw [reverseTwoQubitBasis]
  have h := Equiv.piCongrLeft_apply_apply (fun _ : Fin 2 ↦ Bool)
    (Equiv.swap 0 1) input 0
  simpa using h

@[simp]
theorem reverseTwoQubitBasis_apply_apply (input : Basis 2) :
    reverseTwoQubitBasis (reverseTwoQubitBasis input) = input := by
  apply (finTwoArrowEquiv Bool).injective
  apply Prod.ext <;> simp

@[simp]
theorem reverseTwoQubitBasis_symm :
    reverseTwoQubitBasis.symm = reverseTwoQubitBasis := by
  apply Equiv.ext
  intro input
  apply reverseTwoQubitBasis.injective
  simp

@[simp]
theorem reverseTwoQubitBasis_symm_apply (input : Basis 2) :
    reverseTwoQubitBasis.symm input = reverseTwoQubitBasis input := by
  rw [reverseTwoQubitBasis_symm]

theorem reverseTwoQubitBasis_involutive :
    Function.Involutive reverseTwoQubitBasis :=
  reverseTwoQubitBasis_apply_apply

@[simp]
theorem twoWireLocalBits_swap {n : ℕ} (pair : OrderedWirePair n)
    (input : Basis n) :
    twoWireLocalBits pair.swap input =
      reverseTwoQubitBasis (twoWireLocalBits pair input) := by
  apply (finTwoArrowEquiv Bool).injective
  apply Prod.ext <;> simp

theorem agreeOffTwoWire_swap_iff {n : ℕ} (pair : OrderedWirePair n)
    (left right : Basis n) :
    AgreeOffTwoWire pair.swap left right ↔ AgreeOffTwoWire pair left right := by
  constructor
  · intro hagree wire hfirst hsecond
    exact hagree wire hsecond hfirst
  · intro hagree wire hsecond hfirst
    exact hagree wire hfirst hsecond

@[simp]
theorem setTwoWire_swap {n : ℕ} (pair : OrderedWirePair n)
    (input : Basis n) (bits : Basis 2) :
    setTwoWire pair.swap input bits =
      setTwoWire pair input (reverseTwoQubitBasis bits) := by
  funext wire
  by_cases hfirst : wire = pair.first
  · subst wire
    calc
      setTwoWire pair.swap input bits pair.first = bits 1 := by
        simpa using setTwoWire_apply_second pair.swap input bits
      _ = setTwoWire pair input (reverseTwoQubitBasis bits) pair.first := by simp
  · by_cases hsecond : wire = pair.second
    · subst wire
      calc
        setTwoWire pair.swap input bits pair.second = bits 0 := by
          simpa using setTwoWire_apply_first pair.swap input bits
        _ = setTwoWire pair input (reverseTwoQubitBasis bits) pair.second := by simp
    · rw [setTwoWire_apply_of_ne pair.swap input bits wire hsecond hfirst,
        setTwoWire_apply_of_ne pair input (reverseTwoQubitBasis bits) wire hfirst hsecond]

end Barenco
