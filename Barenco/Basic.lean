import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Foundational finite-register types and convention checks

This module fixes the smallest representation choices used throughout the library.
It also contains executable convention checks that prevent later circuit diagrams
from silently using the paper's row-vector convention.
-/

namespace Barenco

open Matrix

/-- The computational basis of an `n`-qubit register, represented by its bits. -/
abbrev Basis (n : ℕ) := Fin n → Bool

/-- A semantic gate on `n` qubits is a complex matrix indexed by bit assignments. -/
abbrev Gate (n : ℕ) := Matrix (Basis n) (Basis n) ℂ

/-- A state-amplitude vector on an `n`-qubit computational basis. -/
abbrev State (n : ℕ) := Basis n → ℂ

/-- A semantic gate carrying a proof of matrix unitarity. -/
abbrev UnitaryGate (n : ℕ) := Matrix.unitaryGroup (Basis n) ℂ

/--
The natural-number index of a bit assignment in the paper's big-endian
lexicographic order. This bridge is descriptive; core gate semantics do not depend
on natural-number encodings.
-/
def basisIndex {n : ℕ} (x : Basis n) : ℕ :=
  ∑ i : Fin n, if x i then 2 ^ (n - 1 - i.1) else 0

/-- A convenient explicit two-bit assignment for convention checks. -/
def twoBit (high low : Bool) : Basis 2 := fun i =>
  if i = 0 then high else low

example : basisIndex (twoBit false false) = 0 := by decide
example : basisIndex (twoBit false true) = 1 := by decide
example : basisIndex (twoBit true false) = 2 := by decide
example : basisIndex (twoBit true true) = 3 := by decide

/--
Translate a matrix written in the paper's row-vector/right-action convention to
the library's standard column-vector/left-action convention.
-/
def fromPaper {n : ℕ} (U : Gate n) : Gate n := U.transpose

@[simp]
theorem fromPaper_apply {n : ℕ} (U : Gate n) (row col : Basis n) :
    fromPaper U row col = U col row := rfl

/-- Transposition reverses the paper's chronological product as required. -/
theorem fromPaper_mul {n : ℕ} (U V : Gate n) :
    fromPaper (U * V) = fromPaper V * fromPaper U := by
  exact Matrix.transpose_mul U V

/-- Translating a paper matrix preserves and reflects unitarity. -/
theorem fromPaper_mem_unitaryGroup_iff {n : ℕ} (U : Gate n) :
    fromPaper U ∈ Matrix.unitaryGroup (Basis n) ℂ ↔
      U ∈ Matrix.unitaryGroup (Basis n) ℂ := by
  exact Matrix.transpose_mem_unitaryGroup_iff

/--
Evaluate a chronological list of semantic gates. The head executes first, so later
gates multiply on the left.
-/
def evalGates {n : ℕ} : List (Gate n) → Gate n
  | [] => 1
  | U :: circuit => evalGates circuit * U

@[simp]
theorem evalGates_nil {n : ℕ} : evalGates ([] : List (Gate n)) = 1 := rfl

@[simp]
theorem evalGates_cons {n : ℕ} (U : Gate n) (circuit : List (Gate n)) :
    evalGates (U :: circuit) = evalGates circuit * U := rfl

@[simp]
theorem evalGates_singleton {n : ℕ} (U : Gate n) : evalGates [U] = U := by
  simp [evalGates]

/-- Two chronological gates denote the reversed standard matrix product. -/
@[simp]
theorem evalGates_pair {n : ℕ} (U V : Gate n) : evalGates [U, V] = V * U := by
  simp [evalGates]

/-- Chronological concatenation executes the left circuit before the right one. -/
theorem evalGates_append {n : ℕ} (first second : List (Gate n)) :
    evalGates (first ++ second) = evalGates second * evalGates first := by
  induction first with
  | nil => simp
  | cons U first ih =>
      simp only [List.cons_append, evalGates_cons, ih]
      rw [mul_assoc]

/-- Matrix multiplication has the expected identity law at the candidate gate type. -/
theorem gate_mul_one (n : ℕ) (U : Gate n) : U * 1 = U := by
  exact mul_one U

end Barenco
