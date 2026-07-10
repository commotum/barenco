import Barenco.Optimization.EarlyNormalize
import Barenco.Optimization.Section8Normalize
import Barenco.Optimization.SymbolicCancellation
import Barenco.ThreeQubit.RelativePhaseFusion

/-!
# Normalization regression examples

This root-excluded module exercises the exact normalization policies at their
structural boundaries.  The examples deliberately inspect literal optimizer
syntax and resource folds in addition to evaluator preservation.  In
particular, they do not infer a gate count from a matrix equality and do not use
any phase-relaxed equivalence.
-/

namespace Barenco.NormalizeExamples

open Barenco.OneQubit
open Barenco.Optimization
open Barenco.ThreeQubit

noncomputable section

private def widthTwoPair : OrderedWirePair 2 := ⟨0, 1, by decide⟩

private def nonadjacentPair : OrderedWirePair 5 := ⟨4, 1, by decide⟩

private theorem pair_ne_swap {n : ℕ} (pair : OrderedWirePair n) :
    pair ≠ pair.swap := by
  intro heq
  exact pair.ne (congrArg OrderedWirePair.first heq)

/-! ## Ordered-pair and ambient-width boundaries -/

/-- The smallest register supporting a two-wire node uses reverse chronology. -/
example (first second : TwoQubitUnitary) :
    section8Normalize
        [FusionPrimitive.twoQubit widthTwoPair first,
          FusionPrimitive.twoQubit widthTwoPair second] =
      [FusionPrimitive.twoQubit widthTwoPair (second * first)] := by
  simp [section8Normalize, promoteCNOTCircuit, NormalizeCore.normalize,
    promoteCNOT, NormalizeCore.insert, section8IsIdentity, section8Combine]

/-- A nonadjacent endpoint in a width-five register is absorbed locally. -/
example (localGate : QubitUnitary) (payload : TwoQubitUnitary) :
    section8Normalize
        [FusionPrimitive.oneQubit nonadjacentPair.second localGate,
          FusionPrimitive.twoQubit nonadjacentPair payload] =
      [FusionPrimitive.twoQubit nonadjacentPair
        (payload * localOnePayload localGate)] := by
  have hne : nonadjacentPair.second ≠ nonadjacentPair.first := by decide
  simp [section8Normalize, promoteCNOTCircuit, NormalizeCore.normalize,
    promoteCNOT, NormalizeCore.insert, section8IsIdentity, section8Combine,
    hne]

/-- Reversed pair orientation is reindexed through the local bit swap. -/
example {n : ℕ} (pair : OrderedWirePair n)
    (first second : TwoQubitUnitary) :
    section8Normalize
        [FusionPrimitive.twoQubit pair first,
          FusionPrimitive.twoQubit pair.swap second] =
      [FusionPrimitive.twoQubit pair
        (reindexUnitary reverseTwoQubitBasis second * first)] := by
  have hne : pair ≠ pair.swap := pair_ne_swap pair
  simp [section8Normalize, promoteCNOTCircuit, promoteCNOT,
    NormalizeCore.normalize, NormalizeCore.insert, section8IsIdentity,
    section8Combine, hne]

/-! ## Sequence and exact-phase boundaries -/

/-- Normalization sees and fuses the pair straddling an append boundary. -/
example {n : ℕ} (target : Fin n) (first second : QubitUnitary) :
    normalizeEarly
        (FusionCircuit.append
          [FusionPrimitive.oneQubit target first]
          [FusionPrimitive.oneQubit target second]) =
      [FusionPrimitive.oneQubit target (second * first)] := by
  simp [FusionCircuit.append, normalizeEarly, earlyExpose,
    earlyExposeInsert, earlyAdjacentNormalize, NormalizeCore.normalize,
    NormalizeCore.insert, earlyIsIdentity, earlyCombine]

/-- A scalar-phase payload is retained exactly; the concrete pass never drops it. -/
example {n : ℕ} (target : Fin n) (delta : ℝ) :
    normalizeEarly
        [FusionPrimitive.oneQubit target (phaseShiftUnitary delta)] =
      [FusionPrimitive.oneQubit target (phaseShiftUnitary delta)] := by
  rfl

/-- Two scalar phases fuse in chronological order without quotienting phase. -/
example {n : ℕ} (target : Fin n) (first second : ℝ) :
    normalizeEarly
        [FusionPrimitive.oneQubit target (phaseShiftUnitary first),
          FusionPrimitive.oneQubit target (phaseShiftUnitary second)] =
      [FusionPrimitive.oneQubit target
        (phaseShiftUnitary second * phaseShiftUnitary first)] := by
  simp [normalizeEarly, earlyExpose, earlyExposeInsert,
    earlyAdjacentNormalize, NormalizeCore.normalize, NormalizeCore.insert,
    earlyIsIdentity, earlyCombine]

/-! ## Honest symbolic inverse provenance -/

/-- A recorded atom followed by its recorded inverse cancels syntactically. -/
example {Atom : Type*} [DecidableEq Atom] {n : ℕ}
    (target : Fin n) (name : Atom) :
    SymbolicCircuit.normalize
        [SymbolicPrimitive.atom target name,
          SymbolicPrimitive.inverseAtom target name] = [] := by
  simp

/-- Provenance cancellation is exact under every certified atom valuation. -/
example {Atom : Type*} [DecidableEq Atom] {n : ℕ}
    (valuation : Atom → QubitUnitary) (target : Fin n) (name : Atom) :
    FusionCircuit.eval
        (SymbolicCircuit.erase valuation
          [SymbolicPrimitive.atom target name,
            SymbolicPrimitive.inverseAtom target name]) = 1 := by
  simpa using
    (SymbolicCircuit.eval_erase_normalize valuation
      [SymbolicPrimitive.atom target name,
        SymbolicPrimitive.inverseAtom target name]).symm

/-! ## Deliberately different cost-model policies -/

/-- A touching CNOT is a hard stop for the early-model concrete pass. -/
example {n : ℕ} (control target : Fin n) (h : control ≠ target)
    (first second : QubitUnitary) :
    normalizeEarly
        [FusionPrimitive.oneQubit target first,
          FusionPrimitive.cnot control target h,
          FusionPrimitive.oneQubit target second] =
      [FusionPrimitive.oneQubit target first,
        FusionPrimitive.cnot control target h,
        FusionPrimitive.oneQubit target second] := by
  simp [normalizeEarly, earlyExpose, earlyExposeInsert,
    earlyAdjacentNormalize, NormalizeCore.normalize, NormalizeCore.insert,
    earlyIsIdentity, earlyCombine, h.symm]

/-- Section 8 instead absorbs the same three nodes into one certified `U(4)`. -/
example {n : ℕ} (control target : Fin n) (h : control ≠ target)
    (first second : QubitUnitary) :
    section8Normalize
        [FusionPrimitive.oneQubit target first,
          FusionPrimitive.cnot control target h,
          FusionPrimitive.oneQubit target second] =
      [FusionPrimitive.twoQubit ⟨control, target, h⟩
        ((localOnePayload second * localCNOTPayload) *
          localOnePayload first)] := by
  simp [section8Normalize, promoteCNOTCircuit, promoteCNOT, cnotAsTwoQubit,
    NormalizeCore.normalize, NormalizeCore.insert, section8IsIdentity,
    section8Combine, h.symm]

/-- The two policies therefore expose different literal resource profiles. -/
example {n : ℕ} (control target : Fin n) (h : control ≠ target)
    (first second : QubitUnitary) :
    let circuit : FusionCircuit n :=
      [FusionPrimitive.oneQubit target first,
        FusionPrimitive.cnot control target h,
        FusionPrimitive.oneQubit target second]
    FusionCircuit.gateCount (normalizeEarly circuit) = 3 ∧
      FusionCircuit.cnotCount (normalizeEarly circuit) = 1 ∧
      FusionCircuit.twoQubitCount (normalizeEarly circuit) = 0 ∧
      FusionCircuit.cost CostModel.oneQubitCNOT
          (normalizeEarly circuit) = some 3 ∧
      FusionCircuit.gateCount (section8Normalize circuit) = 1 ∧
      FusionCircuit.cnotCount (section8Normalize circuit) = 0 ∧
      FusionCircuit.twoQubitCount (section8Normalize circuit) = 1 ∧
      FusionCircuit.cost CostModel.oneQubitCNOT
          (section8Normalize circuit) = none ∧
      FusionCircuit.cost CostModel.arbitraryTwoQubit
          (section8Normalize circuit) = some 1 := by
  dsimp
  simp [normalizeEarly, earlyExpose, earlyExposeInsert,
    earlyAdjacentNormalize, section8Normalize, promoteCNOTCircuit, promoteCNOT,
    cnotAsTwoQubit, NormalizeCore.normalize, NormalizeCore.insert,
    earlyIsIdentity, earlyCombine, section8IsIdentity, section8Combine,
    FusionCircuit.gateCount, FusionCircuit.cnotCount,
    FusionCircuit.twoQubitCount, FusionCircuit.kindCount, FusionCircuit.cost,
    FusionPrimitive.cost, FusionPrimitive.kind, Circuit.addCost, h.symm]

/-- Both policies remain exactly semantic despite their distinct output syntax. -/
example {n : ℕ} (control target : Fin n) (h : control ≠ target)
    (first second : QubitUnitary) :
    let circuit : FusionCircuit n :=
      [FusionPrimitive.oneQubit target first,
        FusionPrimitive.cnot control target h,
        FusionPrimitive.oneQubit target second]
    FusionCircuit.eval (normalizeEarly circuit) =
      FusionCircuit.eval (section8Normalize circuit) := by
  dsimp
  rw [eval_normalizeEarly, eval_section8Normalize]

/-! ## Generic relative-A regression input -/

/--
On three pairwise-distinct wires, generic Section 8 normalization emits exactly
three literal arbitrary-two-qubit nodes.  This is only an optimizer regression:
it deliberately makes no paper-facing Toffoli or phase classification.
-/
example {n : ℕ} (first second target : Fin n)
    (hfirstSecond : first ≠ second)
    (hfirstTarget : first ≠ target)
    (hsecondTarget : second ≠ target) :
    let normalized := section8Normalize
      (relativePhaseToffoliAFusionCircuit first second target
        hfirstTarget hsecondTarget)
    FusionCircuit.gateCount normalized = 3 ∧
      FusionCircuit.oneQubitCount normalized = 0 ∧
      FusionCircuit.cnotCount normalized = 0 ∧
      FusionCircuit.twoQubitCount normalized = 3 ∧
      FusionCircuit.cost CostModel.arbitraryTwoQubit normalized = some 3 ∧
      FusionCircuit.cost CostModel.oneQubitCNOT normalized = none := by
  have hsecondFirst : second ≠ first := hfirstSecond.symm
  have htargetFirst : target ≠ first := hfirstTarget.symm
  have htargetSecond : target ≠ second := hsecondTarget.symm
  dsimp
  simp [relativePhaseToffoliAFusionCircuit, section8Normalize,
    promoteCNOTCircuit, promoteCNOT, cnotAsTwoQubit,
    NormalizeCore.normalize, NormalizeCore.insert, section8IsIdentity,
    section8Combine, FusionCircuit.gateCount, FusionCircuit.oneQubitCount,
    FusionCircuit.cnotCount, FusionCircuit.twoQubitCount,
    FusionCircuit.kindCount, FusionCircuit.cost, FusionPrimitive.cost,
    FusionPrimitive.kind, Circuit.addCost, OrderedWirePair.eq_iff, *]

/-! ## Barrier boundaries -/

/-- An opaque barrier is copied exactly and blocks fusion across it. -/
example {n : ℕ} (target : Fin n) (first second : QubitUnitary) :
    let barrierGate := Primitive.unclassified "normalization barrier"
      (1 : UnitaryGate n)
    section8NormalizeProgram
        [FusionStep.gate (FusionPrimitive.oneQubit target first),
          FusionStep.barrier barrierGate,
          FusionStep.gate (FusionPrimitive.oneQubit target second)] =
      [FusionStep.gate (FusionPrimitive.oneQubit target first),
        FusionStep.barrier barrierGate,
        FusionStep.gate (FusionPrimitive.oneQubit target second)] := by
  rfl

/-- A program consisting entirely of barriers is an exact fixed path. -/
example {n : ℕ} (circuit : Circuit n) :
    section8NormalizeProgram (FusionProgram.barriers circuit) =
      FusionProgram.barriers circuit := by
  induction circuit with
  | nil => rfl
  | cons primitive circuit ih =>
      change
        FusionStep.barrier primitive ::
            section8NormalizeProgram (FusionProgram.barriers circuit) =
          FusionStep.barrier primitive :: FusionProgram.barriers circuit
      rw [ih]

end

end Barenco.NormalizeExamples
