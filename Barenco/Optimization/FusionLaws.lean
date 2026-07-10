import Barenco.Optimization.FusionIR
import Barenco.TwoWire.ControlledBridges

/-!
# Exact local laws for payload-preserving fusion

This module contains the algebraic rules consumed by circuit normalization.  A
chronological fusion of `first; second` must carry local payload
`second * first`, matching the library's head-first circuit convention.  Every
law below is exact on an arbitrary ambient register; no scalar phase or
measurement-only equivalence is used.

The local payload constructors use the ordered two-wire convention from
`Barenco.TwoWire`: local bit `0` is the first ambient wire and local bit `1` is
the second.  The CNOT promotion constructs a genuine certified `U(4)` payload
and changes structural kind only after proving denotational equality.
-/

namespace Barenco.Optimization

open Barenco

/-! ## Canonical local payloads -/

/-- A one-qubit payload acting on local bit `0` of an ordered pair. -/
def localZeroPayload (U : QubitUnitary) : TwoQubitUnitary :=
  localUnitary (0 : Fin 2) U

/-- A one-qubit payload acting on local bit `1` of an ordered pair. -/
def localOnePayload (U : QubitUnitary) : TwoQubitUnitary :=
  localUnitary (1 : Fin 2) U

/-- Canonical local CNOT with local control `0` and local target `1`. -/
def localCNOTPayload : TwoQubitUnitary :=
  cnotUnitary (0 : Fin 2) (1 : Fin 2) (by decide)

@[simp]
theorem twoWireUnitary_localZeroPayload {n : ℕ}
    (pair : OrderedWirePair n) (U : QubitUnitary) :
    twoWireUnitary pair (localZeroPayload U) =
      localUnitary pair.first U := by
  exact twoWireUnitary_localUnitary_zero pair U

@[simp]
theorem twoWireUnitary_localOnePayload {n : ℕ}
    (pair : OrderedWirePair n) (U : QubitUnitary) :
    twoWireUnitary pair (localOnePayload U) =
      localUnitary pair.second U := by
  exact twoWireUnitary_localUnitary_one pair U

@[simp]
theorem twoWireUnitary_localCNOTPayload {n : ℕ}
    (pair : OrderedWirePair n) :
    twoWireUnitary pair localCNOTPayload =
      cnotUnitary pair.first pair.second pair.ne := by
  exact twoWireUnitary_cnotUnitary_zero_one pair

/-! ## One-wire algebra -/

/-- Embedding on one fixed wire preserves multiplication exactly. -/
theorem localUnitary_mul_same {n : ℕ} (target : Fin n)
    (U V : QubitUnitary) :
    localUnitary target (U * V) =
      localUnitary target U * localUnitary target V := by
  apply Subtype.ext
  change Matrix.reindexAlgEquiv ℂ ℂ (splitTarget target).symm
      (Matrix.blockDiagonal (fun _ : ComplementBasis target =>
        ((U : QubitMatrix) * (V : QubitMatrix)))) =
    Matrix.reindexAlgEquiv ℂ ℂ (splitTarget target).symm
        (Matrix.blockDiagonal (fun _ : ComplementBasis target =>
          (U : QubitMatrix))) *
      Matrix.reindexAlgEquiv ℂ ℂ (splitTarget target).symm
        (Matrix.blockDiagonal (fun _ : ComplementBasis target =>
          (V : QubitMatrix)))
  rw [← map_mul, ← Matrix.blockDiagonal_mul]

/-- Same-wire chronological fusion uses the reversed local product `second * first`. -/
theorem oneQubit_chronological {n : ℕ} (target : Fin n)
    (first second : QubitUnitary) :
    (FusionPrimitive.oneQubit target (second * first)).denotation =
      (FusionPrimitive.oneQubit target second).denotation *
        (FusionPrimitive.oneQubit target first).denotation := by
  exact localUnitary_mul_same target second first

/-! ## Trusted CNOT promotion -/

/--
Represent a visible CNOT as a certified arbitrary two-qubit payload on the same
ordered control/target pair.  This is a semantic conversion for the Section 8
policy, not an equality of structural kinds.
-/
def cnotAsTwoQubit {n : ℕ} (control target : Fin n)
    (h : control ≠ target) : FusionPrimitive n :=
  .twoQubit ⟨control, target, h⟩ localCNOTPayload

@[simp]
theorem cnotAsTwoQubit_denotation {n : ℕ} (control target : Fin n)
    (h : control ≠ target) :
    (cnotAsTwoQubit control target h).denotation =
      (FusionPrimitive.cnot control target h).denotation := by
  exact twoWireUnitary_localCNOTPayload ⟨control, target, h⟩

@[simp]
theorem cnotAsTwoQubit_support {n : ℕ} (control target : Fin n)
    (h : control ≠ target) :
    (cnotAsTwoQubit control target h).support =
      (FusionPrimitive.cnot control target h).support := rfl

/-- Promote every visible CNOT node and leave explicit payload nodes unchanged. -/
def promoteCNOT {n : ℕ} : FusionPrimitive n → FusionPrimitive n
  | .cnot control target h => cnotAsTwoQubit control target h
  | primitive => primitive

@[simp]
theorem promoteCNOT_denotation {n : ℕ} (primitive : FusionPrimitive n) :
    (promoteCNOT primitive).denotation = primitive.denotation := by
  cases primitive <;> simp [promoteCNOT]

@[simp]
theorem promoteCNOT_support {n : ℕ} (primitive : FusionPrimitive n) :
    (promoteCNOT primitive).support = primitive.support := by
  cases primitive <;> rfl

@[simp]
theorem promoteCNOT_idempotent {n : ℕ} (primitive : FusionPrimitive n) :
    promoteCNOT (promoteCNOT primitive) = promoteCNOT primitive := by
  cases primitive <;> rfl

/-! ## Ordered-pair chronology -/

/-- Same-oriented ordered-pair fusion uses payload `second * first`. -/
theorem twoQubit_chronological {n : ℕ} (pair : OrderedWirePair n)
    (first second : TwoQubitUnitary) :
    (FusionPrimitive.twoQubit pair (second * first)).denotation =
      (FusionPrimitive.twoQubit pair second).denotation *
        (FusionPrimitive.twoQubit pair first).denotation := by
  exact twoWireUnitary_mul pair second first

/-- Reversing the pair requires the explicit local bit-swap reindexing. -/
theorem twoQubit_swap_denotation {n : ℕ} (pair : OrderedWirePair n)
    (U : TwoQubitUnitary) :
    (FusionPrimitive.twoQubit pair.swap U).denotation =
      (FusionPrimitive.twoQubit pair
        (reindexUnitary reverseTwoQubitBasis U)).denotation := by
  exact twoWireUnitary_swap pair U

/--
Fuse `pair,U` followed by `pair.swap,V`, retaining the first node's orientation.
-/
theorem twoQubit_then_swap_chronological {n : ℕ}
    (pair : OrderedWirePair n) (first second : TwoQubitUnitary) :
    (FusionPrimitive.twoQubit pair
        (reindexUnitary reverseTwoQubitBasis second * first)).denotation =
      (FusionPrimitive.twoQubit pair.swap second).denotation *
        (FusionPrimitive.twoQubit pair first).denotation := by
  rw [twoQubit_chronological, twoQubit_swap_denotation]

/--
Fuse `pair.swap,U` followed by `pair,V`, retaining the second node's orientation.
-/
theorem swap_then_twoQubit_chronological {n : ℕ}
    (pair : OrderedWirePair n) (first second : TwoQubitUnitary) :
    (FusionPrimitive.twoQubit pair
        (second * reindexUnitary reverseTwoQubitBasis first)).denotation =
      (FusionPrimitive.twoQubit pair second).denotation *
        (FusionPrimitive.twoQubit pair.swap first).denotation := by
  rw [twoQubit_chronological, twoQubit_swap_denotation]

/-! ## Endpoint absorption -/

/-- Absorb a preceding gate on the pair's first wire into a two-qubit payload. -/
theorem oneQubit_first_then_twoQubit {n : ℕ}
    (pair : OrderedWirePair n) (first : QubitUnitary)
    (second : TwoQubitUnitary) :
    (FusionPrimitive.twoQubit pair
        (second * localZeroPayload first)).denotation =
      (FusionPrimitive.twoQubit pair second).denotation *
        (FusionPrimitive.oneQubit pair.first first).denotation := by
  rw [twoQubit_chronological]
  change twoWireUnitary pair second *
      twoWireUnitary pair (localZeroPayload first) =
    twoWireUnitary pair second * localUnitary pair.first first
  rw [twoWireUnitary_localZeroPayload]

/-- Absorb a preceding gate on the pair's second wire into a two-qubit payload. -/
theorem oneQubit_second_then_twoQubit {n : ℕ}
    (pair : OrderedWirePair n) (first : QubitUnitary)
    (second : TwoQubitUnitary) :
    (FusionPrimitive.twoQubit pair
        (second * localOnePayload first)).denotation =
      (FusionPrimitive.twoQubit pair second).denotation *
        (FusionPrimitive.oneQubit pair.second first).denotation := by
  rw [twoQubit_chronological]
  change twoWireUnitary pair second *
      twoWireUnitary pair (localOnePayload first) =
    twoWireUnitary pair second * localUnitary pair.second first
  rw [twoWireUnitary_localOnePayload]

/-- Absorb a following gate on the pair's first wire into a two-qubit payload. -/
theorem twoQubit_then_oneQubit_first {n : ℕ}
    (pair : OrderedWirePair n) (first : TwoQubitUnitary)
    (second : QubitUnitary) :
    (FusionPrimitive.twoQubit pair
        (localZeroPayload second * first)).denotation =
      (FusionPrimitive.oneQubit pair.first second).denotation *
        (FusionPrimitive.twoQubit pair first).denotation := by
  rw [twoQubit_chronological]
  change twoWireUnitary pair (localZeroPayload second) *
      twoWireUnitary pair first =
    localUnitary pair.first second * twoWireUnitary pair first
  rw [twoWireUnitary_localZeroPayload]

/-- Absorb a following gate on the pair's second wire into a two-qubit payload. -/
theorem twoQubit_then_oneQubit_second {n : ℕ}
    (pair : OrderedWirePair n) (first : TwoQubitUnitary)
    (second : QubitUnitary) :
    (FusionPrimitive.twoQubit pair
        (localOnePayload second * first)).denotation =
      (FusionPrimitive.oneQubit pair.second second).denotation *
        (FusionPrimitive.twoQubit pair first).denotation := by
  rw [twoQubit_chronological]
  change twoWireUnitary pair (localOnePayload second) *
      twoWireUnitary pair first =
    localUnitary pair.second second * twoWireUnitary pair first
  rw [twoWireUnitary_localOnePayload]

/-! ## Proof irrelevance and structural orientation -/

/-- Distinctness witnesses do not alter explicit two-qubit fusion syntax. -/
theorem twoQubit_mk_proof_irrel {n : ℕ} (first second : Fin n)
    (h h' : first ≠ second) (U : TwoQubitUnitary) :
    FusionPrimitive.twoQubit (⟨first, second, h⟩ : OrderedWirePair n) U =
      FusionPrimitive.twoQubit (⟨first, second, h'⟩ : OrderedWirePair n) U := by
  congr

/-- CNOT promotion is independent of the supplied distinctness witness. -/
theorem cnotAsTwoQubit_proof_irrel {n : ℕ} (control target : Fin n)
    (h h' : control ≠ target) :
    cnotAsTwoQubit control target h = cnotAsTwoQubit control target h' := by
  congr

/-- Swapping orientation retains the same unordered structural support. -/
@[simp]
theorem twoQubit_swap_support {n : ℕ} (pair : OrderedWirePair n)
    (U : TwoQubitUnitary) :
    (FusionPrimitive.twoQubit pair.swap U).support =
      (FusionPrimitive.twoQubit pair U).support := by
  simp [FusionPrimitive.support, Finset.pair_comm]

/-! ## Generic evaluator replacement -/

/-- Exact contract consumed by every adjacent fusion rule. -/
def IsChronologicalFusion {n : ℕ}
    (first second fused : FusionPrimitive n) : Prop :=
  fused.denotation = second.denotation * first.denotation

/-- Replacing the first two nodes of any tail by a certified fusion is exact. -/
theorem eval_fuse_head {n : ℕ}
    (first second fused : FusionPrimitive n) (tail : FusionCircuit n)
    (hfuse : IsChronologicalFusion first second fused) :
    FusionCircuit.eval (fused :: tail) =
      FusionCircuit.eval (first :: second :: tail) := by
  simp only [FusionCircuit.eval_cons]
  rw [hfuse, mul_assoc]

/-- The head replacement remains exact after any chronological prefix. -/
theorem eval_fuse_context {n : ℕ}
    (before tail : FusionCircuit n)
    (first second fused : FusionPrimitive n)
    (hfuse : IsChronologicalFusion first second fused) :
    FusionCircuit.eval
        (FusionCircuit.append before (fused :: tail)) =
      FusionCircuit.eval
        (FusionCircuit.append before (first :: second :: tail)) := by
  rw [FusionCircuit.eval_append, FusionCircuit.eval_append,
    eval_fuse_head first second fused tail hfuse]

/-- The same replacement theorem after trusted lowering to established syntax. -/
theorem eval_lower_fuse_context {n : ℕ}
    (before tail : FusionCircuit n)
    (first second fused : FusionPrimitive n)
    (hfuse : IsChronologicalFusion first second fused) :
    Circuit.eval
        (FusionCircuit.lower
          (FusionCircuit.append before (fused :: tail))) =
      Circuit.eval
        (FusionCircuit.lower
          (FusionCircuit.append before (first :: second :: tail))) := by
  rw [FusionCircuit.eval_lower, FusionCircuit.eval_lower]
  exact eval_fuse_context before tail first second fused hfuse

end Barenco.Optimization
