import Barenco.TwoWire.Circuit
import Barenco.TwoWireExamples

/-!
# Trusted two-wire circuit diagnostics

These root-excluded checks connect the ordered-pair semantics exercised in
`Barenco.TwoWireExamples` to literal trusted circuit syntax.  They cover the
canonical width-two register, reversed orientation, a nonadjacent width-five
pair, adjoints, structural resources, and both named paper cost models.
-/

namespace Barenco.TwoWireCircuitExamples

open scoped Matrix

/-! ## Canonical width-two singleton -/

/-- One trusted arbitrary-two-qubit node on the canonical pair `(0, 1)`. -/
def widthTwoSingleton (U : TwoQubitUnitary) : Circuit 2 :=
  [Primitive.twoQubit TwoWireExamples.widthTwoPair U]

/-- At width two, evaluating the singleton recovers its local `U(4)` payload. -/
@[simp]
theorem widthTwoSingleton_eval (U : TwoQubitUnitary) :
    Circuit.eval (widthTwoSingleton U) = U := by
  rw [widthTwoSingleton, Circuit.eval_singleton_twoQubit,
    TwoWireExamples.widthTwoCanonicalEmbedding]

/-! ## Reversed orientation -/

/-- The same local CNOT payload placed on the reversed ordered pair. -/
def reversedCNOTSingleton : Circuit 2 :=
  [Primitive.twoQubit TwoWireExamples.widthTwoPair.swap
    TwoWireExamples.localCNOT]

/--
Keeping the local CNOT `0 → 1` while reversing the pair gives ambient CNOT
`1 → 0`; orientation is not erased by the unordered support finset.
-/
theorem reversedCNOTSingleton_eval :
    Circuit.eval reversedCNOTSingleton =
      cnotUnitary (1 : Fin 2) (0 : Fin 2) (by decide) := by
  rw [reversedCNOTSingleton, Circuit.eval_singleton_twoQubit]
  exact TwoWireExamples.reversedPairCNOT_eq_ambient_one_zero

/-- The reversed singleton visibly flips wire `0` when wire `1` is set. -/
theorem reversedCNOTSingleton_action :
    (Circuit.eval reversedCNOTSingleton : Gate 2) *ᵥ
        basisKet (twoBit false true) =
      basisKet (twoBit true true) := by
  rw [reversedCNOTSingleton, Circuit.eval_singleton_twoQubit]
  exact TwoWireExamples.reversedPairCNOT_action

/-- Pair reversal is exact only with the corresponding local-basis reindexing. -/
theorem reversedPrimitive_eq_reindexed :
    Primitive.twoQubit TwoWireExamples.widthTwoPair.swap
        TwoWireExamples.localCNOT =
      Primitive.twoQubit TwoWireExamples.widthTwoPair
        (reindexUnitary reverseTwoQubitBasis TwoWireExamples.localCNOT) := by
  exact Primitive.twoQubit_swap _ _

/-! ## Nonadjacent width-five pair -/

/-- One literal CNOT payload on the nonadjacent ordered pair `(4, 1)`. -/
def nonAdjacentSingleton : Circuit 5 :=
  [Primitive.twoQubit TwoWireExamples.nonAdjacentPair
    TwoWireExamples.localCNOT]

/-- Arbitrary local payloads give the exact four-term selected-pair superposition. -/
theorem nonAdjacentPrimitive_basisSuperposition
    (U : TwoQubitUnitary) (input : Basis 5) :
    ((Primitive.twoQubit TwoWireExamples.nonAdjacentPair U).denotation :
        Gate 5) *ᵥ basisKet input =
      ∑ output : Basis 2,
        U output (twoWireLocalBits TwoWireExamples.nonAdjacentPair input) •
          basisKet
            (setTwoWire TwoWireExamples.nonAdjacentPair input output) := by
  exact Primitive.twoQubit_denotation_mulVec_basisKet_eq_sum _ _ _

/--
The trusted primitive has the checked nonadjacent CNOT action: ambient wire `4`
controls wire `1`, while the other three symbolic bits pass through unchanged.
-/
theorem nonAdjacentPrimitive_action (b0 b1 b2 b3 b4 : Bool) :
    ((Primitive.twoQubit TwoWireExamples.nonAdjacentPair
        TwoWireExamples.localCNOT).denotation : Gate 5) *ᵥ
        basisKet (TwoWireExamples.nonAdjacentInput b0 b1 b2 b3 b4) =
      basisKet (TwoWireExamples.nonAdjacentOutput b0 b1 b2 b3 b4) := by
  rw [Primitive.twoQubit_denotation]
  exact TwoWireExamples.nonAdjacentCNOT_action b0 b1 b2 b3 b4

/-- The evaluated singleton has the same exact nonadjacent basis action. -/
theorem nonAdjacentSingleton_action (b0 b1 b2 b3 b4 : Bool) :
    (Circuit.eval nonAdjacentSingleton : Gate 5) *ᵥ
        basisKet (TwoWireExamples.nonAdjacentInput b0 b1 b2 b3 b4) =
      basisKet (TwoWireExamples.nonAdjacentOutput b0 b1 b2 b3 b4) := by
  rw [nonAdjacentSingleton, Circuit.eval_singleton_twoQubit]
  exact TwoWireExamples.nonAdjacentCNOT_action b0 b1 b2 b3 b4

/-- The concrete output retains all three spectator wires `0`, `2`, and `3`. -/
theorem nonAdjacentOutput_preserves_spectators
    (b0 b1 b2 b3 b4 : Bool) :
    TwoWireExamples.nonAdjacentOutput b0 b1 b2 b3 b4 0 =
        TwoWireExamples.nonAdjacentInput b0 b1 b2 b3 b4 0 ∧
      TwoWireExamples.nonAdjacentOutput b0 b1 b2 b3 b4 2 =
        TwoWireExamples.nonAdjacentInput b0 b1 b2 b3 b4 2 ∧
      TwoWireExamples.nonAdjacentOutput b0 b1 b2 b3 b4 3 =
        TwoWireExamples.nonAdjacentInput b0 b1 b2 b3 b4 3 := by
  simp

/-- Any attempted change to a spectator has zero output amplitude. -/
theorem nonAdjacentPrimitive_changed_spectator_zero
    (U : TwoQubitUnitary) (input row : Basis 5) (wire : Fin 5)
    (hfirst : wire ≠ TwoWireExamples.nonAdjacentPair.first)
    (hsecond : wire ≠ TwoWireExamples.nonAdjacentPair.second)
    (hchanged : row wire ≠ input wire) :
    (((Primitive.twoQubit TwoWireExamples.nonAdjacentPair U).denotation :
        Gate 5) *ᵥ basisKet input) row = 0 := by
  exact Primitive.twoQubit_denotation_mulVec_basisKet_eq_zero_of_changed
    TwoWireExamples.nonAdjacentPair U input row wire hfirst hsecond hchanged

/-! ## Adjoint and literal resources -/

/-- Adjointing the explicit primitive gives the same pair with inverse payload. -/
@[simp]
theorem nonAdjacentPrimitive_adjoint (U : TwoQubitUnitary) :
    (Primitive.twoQubit TwoWireExamples.nonAdjacentPair U).adjoint =
      Primitive.twoQubit TwoWireExamples.nonAdjacentPair U⁻¹ := by
  exact Primitive.adjoint_twoQubit _ _

/-- The circuit adjoint is the literal singleton containing the inverse payload. -/
@[simp]
theorem nonAdjacentSingleton_adjoint (U : TwoQubitUnitary) :
    Circuit.adjoint
        [Primitive.twoQubit TwoWireExamples.nonAdjacentPair U] =
      [Primitive.twoQubit TwoWireExamples.nonAdjacentPair U⁻¹] := by
  rw [Circuit.adjoint_singleton, Primitive.adjoint_twoQubit]

/-- The primitive declares exactly the nonadjacent endpoint support. -/
@[simp]
theorem nonAdjacentPrimitive_support (U : TwoQubitUnitary) :
    (Primitive.twoQubit TwoWireExamples.nonAdjacentPair U).support =
      {(4 : Fin 5), (1 : Fin 5)} := by
  rfl

/-- The declared structural support has cardinality two, even for special payloads. -/
@[simp]
theorem nonAdjacentPrimitive_support_card (U : TwoQubitUnitary) :
    (Primitive.twoQubit TwoWireExamples.nonAdjacentPair U).support.card = 2 := by
  exact Primitive.twoQubit_support_card _ _

/-- The singleton contributes exactly one literal gate node. -/
@[simp]
theorem nonAdjacentSingleton_gateCount (U : TwoQubitUnitary) :
    Circuit.gateCount
        [Primitive.twoQubit TwoWireExamples.nonAdjacentPair U] = 1 := by
  exact Primitive.twoQubit_singleton_gateCount _ _

/-- Its only structural class is `arbitraryTwoQubit`. -/
@[simp]
theorem nonAdjacentSingleton_kindCount (U : TwoQubitUnitary) :
    Circuit.kindCount .arbitraryTwoQubit
        [Primitive.twoQubit TwoWireExamples.nonAdjacentPair U] = 1 := by
  exact Primitive.twoQubit_singleton_kindCount _ _

/-- Singleton touched support is computed from the actual endpoint syntax. -/
@[simp]
theorem nonAdjacentSingleton_touchedSupport (U : TwoQubitUnitary) :
    Circuit.touchedSupport
        [Primitive.twoQubit TwoWireExamples.nonAdjacentPair U] =
      {(4 : Fin 5), (1 : Fin 5)} := by
  exact Primitive.twoQubit_singleton_touchedSupport _ _

/-- Sections 3--7 do not price an undecomposed arbitrary `U(4)` node. -/
@[simp]
theorem nonAdjacentSingleton_oneQubitCNOT_cost (U : TwoQubitUnitary) :
    Circuit.cost CostModel.oneQubitCNOT
        [Primitive.twoQubit TwoWireExamples.nonAdjacentPair U] = none := by
  exact Primitive.oneQubitCNOT_cost_twoQubit _ _

/-- Section 8 prices the same literal arbitrary-two-qubit node as one operation. -/
@[simp]
theorem nonAdjacentSingleton_section8_cost (U : TwoQubitUnitary) :
    Circuit.cost CostModel.arbitraryTwoQubit
        [Primitive.twoQubit TwoWireExamples.nonAdjacentPair U] = some 1 := by
  exact Primitive.arbitraryTwoQubit_cost_twoQubit _ _

end Barenco.TwoWireCircuitExamples
