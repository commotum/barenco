import Barenco.Cost

/-!
# Circuits for conventional ordered matrix products

`Circuit` stores gates in chronological order, so appending `first` then `second`
evaluates as `eval second * eval first`.  Algebraic decompositions instead list
factors in conventional matrix-product order, with the head on the left.

`orderedCircuitProduct` is the explicit bridge: it accepts circuits in
conventional product order and executes the list from right to left.  Its
evaluator is therefore exactly `List.prod` of the listed evaluators.  Resource
statements below inspect the resulting syntax; they are not inferred from the
semantic product theorem.
-/

namespace Barenco.Universality

noncomputable section

/--
Execute circuits supplied in conventional matrix-product order.

For `[first, second]`, `second` runs first and `first` runs second, so the
denotation is `eval first * eval second`.
-/
def orderedCircuitProduct {n : ℕ} : List (Circuit n) → Circuit n
  | [] => Circuit.identity n
  | circuit :: circuits =>
      Circuit.append (orderedCircuitProduct circuits) circuit

@[simp]
theorem orderedCircuitProduct_nil (n : ℕ) :
    orderedCircuitProduct ([] : List (Circuit n)) = Circuit.identity n := rfl

@[simp]
theorem orderedCircuitProduct_cons {n : ℕ} (circuit : Circuit n)
    (circuits : List (Circuit n)) :
    orderedCircuitProduct (circuit :: circuits) =
      Circuit.append (orderedCircuitProduct circuits) circuit := rfl

/-- Exact evaluator in conventional left-to-right matrix-product order. -/
@[simp]
theorem eval_orderedCircuitProduct {n : ℕ} (circuits : List (Circuit n)) :
    Circuit.eval (orderedCircuitProduct circuits) =
      (circuits.map Circuit.eval).prod := by
  induction circuits with
  | nil => simp [orderedCircuitProduct]
  | cons circuit circuits ih =>
      rw [orderedCircuitProduct_cons, Circuit.eval_append, ih]
      simp

/-- The assembled syntax contains exactly the sum of the component occurrences. -/
@[simp]
theorem gateCount_orderedCircuitProduct {n : ℕ}
    (circuits : List (Circuit n)) :
    Circuit.gateCount (orderedCircuitProduct circuits) =
      (circuits.map Circuit.gateCount).sum := by
  induction circuits with
  | nil => simp [orderedCircuitProduct]
  | cons circuit circuits ih =>
      rw [orderedCircuitProduct_cons, Circuit.gateCount_append, ih]
      simp [Nat.add_comm]

/--
Exact partial cost of an assembled product from exact costs of its components.

The hypothesis names a numeric cost for every component, so the conclusion also
certifies that no unsupported primitive occurs in the assembled circuit.
-/
theorem cost_orderedCircuitProduct {n : ℕ} (model : CostModel)
    (componentCost : Circuit n → ℕ) (circuits : List (Circuit n))
    (hcost : ∀ circuit ∈ circuits,
      Circuit.cost model circuit = some (componentCost circuit)) :
    Circuit.cost model (orderedCircuitProduct circuits) =
      some ((circuits.map componentCost).sum) := by
  induction circuits with
  | nil => simp [orderedCircuitProduct]
  | cons circuit circuits ih =>
      rw [orderedCircuitProduct_cons, Circuit.cost_append]
      rw [ih (fun tail htail => hcost tail (by simp [htail]))]
      rw [hcost circuit (by simp)]
      simp [Circuit.addCost, Nat.add_comm]

/-- Existential accepted-cost form when clients do not need a closed formula. -/
theorem exists_cost_orderedCircuitProduct {n : ℕ} (model : CostModel)
    (circuits : List (Circuit n))
    (hcost : ∀ circuit ∈ circuits,
      ∃ cost, Circuit.cost model circuit = some cost) :
    ∃ cost,
      Circuit.cost model (orderedCircuitProduct circuits) = some cost := by
  induction circuits with
  | nil => exact ⟨0, by simp [orderedCircuitProduct]⟩
  | cons circuit circuits ih =>
      obtain ⟨headCost, hheadCost⟩ := hcost circuit (by simp)
      obtain ⟨tailCost, htailCost⟩ :=
        ih (fun tail htail => hcost tail (by simp [htail]))
      refine ⟨tailCost + headCost, ?_⟩
      rw [orderedCircuitProduct_cons, Circuit.cost_append,
        htailCost, hheadCost]
      rfl

end

end Barenco.Universality
