import Barenco.TwoWire.ControlledBridges

/-!
# Ordered two-wire semantic diagnostics

These root-excluded checks exercise the ordered-pair semantics at width two and
on a padded, nonadjacent width-five register.  They use ordinary theorem proofs
and kernel reduction only.
-/

namespace Barenco.TwoWireExamples

open Matrix

/-! ## The canonical width-two layout -/

/-- The canonical local orientation: ambient wire `0`, then ambient wire `1`. -/
def widthTwoPair : OrderedWirePair 2 :=
  ⟨(0 : Fin 2), (1 : Fin 2), by decide⟩

@[simp]
theorem widthTwoPair_localBits (input : Basis 2) :
    twoWireLocalBits widthTwoPair input = input := by
  funext wire
  fin_cases wire <;> simp [widthTwoPair]

theorem widthTwoPair_agreeOff (row col : Basis 2) :
    AgreeOffTwoWire widthTwoPair row col := by
  intro wire hzero hone
  fin_cases wire
  · exact (hzero rfl).elim
  · exact (hone rfl).elim

/--
On the canonical width-two pair there are no spectators, so embedding any
certified `U(4)` matrix recovers that matrix exactly.
-/
@[simp]
theorem widthTwoCanonicalEmbedding (U : TwoQubitUnitary) :
    twoWireUnitary widthTwoPair U = U := by
  apply Subtype.ext
  ext row col
  rw [twoWireUnitary_apply, if_pos (widthTwoPair_agreeOff row col)]
  simp

/-! ## Pair orientation is operational -/

/-- The canonical local CNOT has local wire `0` controlling local wire `1`. -/
def localCNOT : TwoQubitUnitary :=
  cnotUnitary (0 : Fin 2) (1 : Fin 2) (by decide)

/--
Reversing the ordered pair embeds that same local matrix as ambient CNOT
`1 → 0`, not as ambient CNOT `0 → 1`.
-/
theorem reversedPairCNOT_eq_ambient_one_zero :
    twoWireUnitary widthTwoPair.swap localCNOT =
      cnotUnitary (1 : Fin 2) (0 : Fin 2) (by decide) := by
  simpa [widthTwoPair, localCNOT] using
    twoWireUnitary_cnotUnitary_zero_one widthTwoPair.swap

/-- The reversed CNOT visibly flips ambient wire `0` when ambient wire `1` is set. -/
theorem reversedPairCNOT_action :
    (twoWireUnitary widthTwoPair.swap localCNOT : Gate 2) *ᵥ
        basisKet (twoBit false true) =
      basisKet (twoBit true true) := by
  rw [reversedPairCNOT_eq_ambient_one_zero, coe_cnotUnitary,
    cnotRaw_mulVec_basisKet]
  apply congrArg basisKet
  funext wire
  fin_cases wire <;> simp [twoBit]

/-! ## A padded nonadjacent pair -/

/-- A concrete five-wire assignment in ambient wire order `0,1,2,3,4`. -/
def fiveBit (b0 b1 b2 b3 b4 : Bool) : Basis 5 :=
  fun wire ↦
    if wire = 0 then b0
    else if wire = 1 then b1
    else if wire = 2 then b2
    else if wire = 3 then b3
    else b4

/-- The nonadjacent ordered pair with local wire order `(4,1)`. -/
def nonAdjacentPair : OrderedWirePair 5 :=
  ⟨(4 : Fin 5), (1 : Fin 5), by decide⟩

/-- The input used by the width-five diagnostic, with every bit left symbolic. -/
def nonAdjacentInput (b0 b1 b2 b3 b4 : Bool) : Basis 5 :=
  fiveBit b0 b1 b2 b3 b4

/--
Expected output of local CNOT `0 → 1` on pair `(4,1)`: ambient wire `4`
controls ambient wire `1`; all other wires are unchanged.
-/
def nonAdjacentOutput (b0 b1 b2 b3 b4 : Bool) : Basis 5 :=
  fiveBit b0 (if b4 then !b1 else b1) b2 b3 b4

@[simp]
theorem nonAdjacentOutput_preserves_zero (b0 b1 b2 b3 b4 : Bool) :
    nonAdjacentOutput b0 b1 b2 b3 b4 0 =
      nonAdjacentInput b0 b1 b2 b3 b4 0 := by
  simp [nonAdjacentOutput, nonAdjacentInput, fiveBit]

@[simp]
theorem nonAdjacentOutput_preserves_two (b0 b1 b2 b3 b4 : Bool) :
    nonAdjacentOutput b0 b1 b2 b3 b4 2 =
      nonAdjacentInput b0 b1 b2 b3 b4 2 := by
  simp [nonAdjacentOutput, nonAdjacentInput, fiveBit]

@[simp]
theorem nonAdjacentOutput_preserves_three (b0 b1 b2 b3 b4 : Bool) :
    nonAdjacentOutput b0 b1 b2 b3 b4 3 =
      nonAdjacentInput b0 b1 b2 b3 b4 3 := by
  simp [nonAdjacentOutput, nonAdjacentInput, fiveBit]

/--
The nonadjacent `(4,1)` embedding has the exact CNOT basis-ket action while
retaining the arbitrary spectator bits on ambient wires `0`, `2`, and `3`.
-/
theorem nonAdjacentCNOT_action
    (b0 b1 b2 b3 b4 : Bool) :
    (twoWireUnitary nonAdjacentPair localCNOT : Gate 5) *ᵥ
        basisKet (nonAdjacentInput b0 b1 b2 b3 b4) =
      basisKet (nonAdjacentOutput b0 b1 b2 b3 b4) := by
  unfold localCNOT
  rw [twoWireUnitary_cnotUnitary_zero_one, coe_cnotUnitary,
    cnotRaw_mulVec_basisKet]
  apply congrArg basisKet
  funext wire
  fin_cases wire <;> cases b4 <;>
    simp [nonAdjacentPair, nonAdjacentInput, nonAdjacentOutput, fiveBit]

end Barenco.TwoWireExamples
