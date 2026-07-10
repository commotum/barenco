import Barenco.TwoWire.Semantics
import Barenco.Controlled

/-!
# Bridges from local two-wire matrices to ambient controlled gates

This proof-side leaf identifies the established arbitrary-register one-qubit and
controlled-gate semantics with their local two-qubit embeddings.  For an ordered
pair, local bit `0` is the ambient first wire and local bit `1` is the ambient
second wire.  Every result is exact equality of certified full-register
unitaries; no phase is discarded.
-/

namespace Barenco

/--
Agreement away from the ambient first wire splits into spectator agreement and
agreement away from local wire `0`.  The latter condition retains equality of
the ambient second wire, which `AgreeOffTwoWire` deliberately omits.
-/
theorem agreeOff_pairFirst_iff {n : ℕ} (pair : OrderedWirePair n)
    (row col : Basis n) :
    AgreeOff pair.first row col ↔
      AgreeOffTwoWire pair row col ∧
        AgreeOff (0 : Fin 2) (twoWireLocalBits pair row)
          (twoWireLocalBits pair col) := by
  constructor
  · intro hagree
    constructor
    · intro wire hfirst _
      exact hagree wire hfirst
    · intro localWire hlocal
      fin_cases localWire
      · exact (hlocal rfl).elim
      · simpa using hagree pair.second pair.ne.symm
  · rintro ⟨hpair, hlocal⟩ wire hfirst
    by_cases hsecond : wire = pair.second
    · subst wire
      simpa using hlocal (1 : Fin 2) (by decide)
    · exact hpair wire hfirst hsecond

/--
Agreement away from the ambient second wire splits into spectator agreement and
agreement away from local wire `1`.
-/
theorem agreeOff_pairSecond_iff {n : ℕ} (pair : OrderedWirePair n)
    (row col : Basis n) :
    AgreeOff pair.second row col ↔
      AgreeOffTwoWire pair row col ∧
        AgreeOff (1 : Fin 2) (twoWireLocalBits pair row)
          (twoWireLocalBits pair col) := by
  constructor
  · intro hagree
    constructor
    · intro wire _ hsecond
      exact hagree wire hsecond
    · intro localWire hlocal
      fin_cases localWire
      · simpa using hagree pair.first pair.ne
      · exact (hlocal rfl).elim
  · rintro ⟨hpair, hlocal⟩ wire hsecond
    by_cases hfirst : wire = pair.first
    · subst wire
      simpa using hlocal (0 : Fin 2) (by decide)
    · exact hpair wire hfirst hsecond

/-- Embedding a local gate on wire `0` is exactly the ambient first-wire gate. -/
theorem twoWireUnitary_localUnitary_zero {n : ℕ}
    (pair : OrderedWirePair n) (U : QubitUnitary) :
    twoWireUnitary pair (localUnitary (0 : Fin 2) U) =
      localUnitary pair.first U := by
  apply Subtype.ext
  ext row col
  simp only [coe_twoWireUnitary, coe_localUnitary, twoWireRaw_apply,
    localRaw_apply_eq_if_agreeOff]
  by_cases hpair : AgreeOffTwoWire pair row col <;>
    by_cases hlocal : AgreeOff (0 : Fin 2) (twoWireLocalBits pair row)
      (twoWireLocalBits pair col) <;>
    simp [hpair, hlocal, agreeOff_pairFirst_iff, twoWireLocalBits_zero]

/-- Embedding a local gate on wire `1` is exactly the ambient second-wire gate. -/
theorem twoWireUnitary_localUnitary_one {n : ℕ}
    (pair : OrderedWirePair n) (U : QubitUnitary) :
    twoWireUnitary pair (localUnitary (1 : Fin 2) U) =
      localUnitary pair.second U := by
  apply Subtype.ext
  ext row col
  simp only [coe_twoWireUnitary, coe_localUnitary, twoWireRaw_apply,
    localRaw_apply_eq_if_agreeOff]
  by_cases hpair : AgreeOffTwoWire pair row col <;>
    by_cases hlocal : AgreeOff (1 : Fin 2) (twoWireLocalBits pair row)
      (twoWireLocalBits pair col) <;>
    simp [hpair, hlocal, agreeOff_pairSecond_iff, twoWireLocalBits_one]

/--
The canonical local singleton control `0 → 1` embeds as the ambient singleton
control `pair.first → pair.second` for every one-qubit unitary payload.
-/
theorem twoWireUnitary_positiveControlledUnitary_zero_one {n : ℕ}
    (pair : OrderedWirePair n) (U : QubitUnitary) :
    twoWireUnitary pair
        (positiveControlledUnitary (1 : Fin 2)
          ({⟨(0 : Fin 2), by decide⟩} : ControlSet (1 : Fin 2)) U) =
      positiveControlledUnitary pair.second
        ({⟨pair.first, pair.ne⟩} : ControlSet pair.second) U := by
  apply Subtype.ext
  ext row col
  simp only [coe_twoWireUnitary, coe_positiveControlledUnitary,
    twoWireRaw_apply]
  rw [positiveControlledRaw, controlledRaw_apply_eq_if_agreeOff]
  rw [positiveControlledRaw, controlledRaw_apply_eq_if_agreeOff]
  by_cases hpair : AgreeOffTwoWire pair row col
  · by_cases hlocal : AgreeOff (1 : Fin 2) (twoWireLocalBits pair row)
        (twoWireLocalBits pair col)
    · have hcontrol : row pair.first = col pair.first := by
        simpa using hlocal (0 : Fin 2) (by decide)
      simp [hlocal, agreeOff_pairSecond_iff, positiveControlsEnabled,
        twoWireLocalBits_zero, twoWireLocalBits_one, hcontrol]
    · simp [hlocal, agreeOff_pairSecond_iff]
  · simp [hpair, agreeOff_pairSecond_iff]

/--
The canonical local CNOT `0 → 1` embeds as the ambient CNOT from the first wire
of the ordered pair to its second wire.
-/
theorem twoWireUnitary_cnotUnitary_zero_one {n : ℕ}
    (pair : OrderedWirePair n) :
    twoWireUnitary pair
        (cnotUnitary (0 : Fin 2) (1 : Fin 2) (by decide)) =
      cnotUnitary pair.first pair.second pair.ne := by
  rw [cnotUnitary, cnotUnitary]
  exact twoWireUnitary_positiveControlledUnitary_zero_one pair pauliX

end Barenco
