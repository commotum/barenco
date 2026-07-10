# 8-ANCILLA

Status: in progress (semantic and primitive construction layers complete; resource
wrappers, diagnostics, public integration, and final audits remain).

## Current Facts

- This stage file did not exist in the initial scaffold; the authoritative Stage
  8 objective and completion requirements were previously only in `0-plan.md`.
  It is created now, before any Stage 8 Lean architecture or implementation, as
  required by `BUILD-PLAN.md`.
- The source material is Lemma 7.9, Corollary 7.10, Lemma 7.11, and Corollary
  7.12 on manuscript pp. 24–25, Markdown lines 854–889, plus
  `lemma-7-9-linear-su2-control.png` and
  `lemma-7-11-one-fixed-bit.png`. Diagrams execute left-to-right.
- Lemma 7.9 partitions the full control family into a prefix and one final
  control. Its exact chronology is
  `C(last,A,target); MCX(prefix,target); C(last,B,target);`
  `MCX(prefix,target); C(last,C,target)`. In standard-column semantics the four
  cases reduce to `I`, `CBA`, `X²`, and `CXBXA`; the Stage 4 ABC theorem supplies
  `CBA=I` and `CXBXA=W` for `W∈SU(2)`.
- Determinant one is necessary for this exact five-macro topology, not merely a
  sufficient hypothesis: the inactive and active target products differ by two
  Pauli-X factors, whose determinant contribution squares to one. The selected
  `W`, `A`, `B`, and `C` interfaces should therefore retain `QubitSpecialUnitary`
  certificates instead of weakening immediately to arbitrary U(2).
- Corollary 7.10 prints `∧_{n−2}(W)`, but Lemma 7.9, its diagram, its dependency
  on the one-fewer-control Corollary 7.4 X gate, and the following n-bit Toffoli
  discussion all identify the intended result as the fully controlled
  `∧_{n−1}(W)`. This is correction C-022 and must not be silently hidden.
- Lemma 7.11 uses `p=n−2` data controls, one clean-zero auxiliary wire, and one
  target. Its chronology is
  `MCX(data,aux); C(aux,U,target); MCX(data,aux)`. On an arbitrary auxiliary input
  bit `a`, the controlled target condition is `a xor conjunction(data)`; therefore
  the circuit is not the desired full-register unitary outside the `a=0` input
  subspace. The auxiliary is restored because the same MCX is applied twice.
- Stage 7 already supplies the exact reusable primitive needed by both diagrams.
  `expandedRecursivePrefixXCircuit` implements an MCX on the last ordered control
  using the original target as dirty workspace and restores that workspace. For
  Lemma 7.11 it applies directly after treating the clean auxiliary as the last
  ordered control. For Lemma 7.9, swapping the last-control and target roles makes
  the same circuit implement the prefix MCX on the original target while using
  the final control as dirty workspace.
- For `p≥5` prefix/data controls, one literal Stage 7 MCX expansion has exact
  profile `(32p−80,24p−52,56p−132)` in one-qubit/CNOT/total operations. A
  selected arbitrary singly controlled unitary has `(4,2,6)`, while a selected
  controlled special-unitary factor has the stronger `(3,2,5)` Lemma 5.1
  implementation. Thus the strongest current literal Lemma 7.9 audit target is
  `(64p−151,48p−98,112p−249)`, equivalently
  `(64n−279,48n−194,112n−473)` for logical width `n=p+2`. Lemma 7.11 is
  `(64p−156,48p−102,112p−258)`, equivalently total `112n−482`. These
  formulas are audit targets, not accepted theorems until linked to explicit
  syntax.
- Both linear primitive expansions require `p+2≥7`, hence logical width
  `n≥7`, because they invoke corrected Corollary 7.4. The semantic macro
  identities themselves are valid at smaller boundaries and should be stated
  separately.
- `CostModel.oneQubitCNOT` remains the applicable Sections 3–7 model. Macro
  circuits containing controlled-one-qubit nodes have cost `none`; only their
  named primitive expansions may receive numeric costs.
- Existing `State n` is an arbitrary amplitude function, not a normalized-state
  subtype. A clean-ancilla theorem can therefore quantify arbitrary data and
  spectator amplitudes by a support predicate saying every basis amplitude with
  the auxiliary bit unequal to zero vanishes. Exact equality on that support is
  stronger and more reusable than testing classical inputs alone.

## Source Claim Audit

| Claim | Source content | Audited status and routing |
|---|---|---|
| Lemma 7.9 | Fully controlled `W∈SU(2)` from three final-control gates and two prefix-controlled X gates; proof refers to Lemmas 5.1 and 4.3. | Exact macro identity is recoverable for arbitrary ambient layouts. Prove the four control branches explicitly, select one checked ABC factorization, then expand both kinds of macro separately. |
| Corollary 7.10 | Printed `∧_{n−2}(W)` has `Θ(n)` basic cost. | Correct to the intended fully controlled `∧_{n−1}(W)` construction, prove an exact linear upper count from syntax for `n≥7`, and do not assert optimal `Θ(n)`. Record the printed subscript mismatch through C-022. |
| Phase-relaxed Toffoli example | A particular `W` gives an n-bit Toffoli transformation “congruent modulo phase shifts.” | Compute the exact basis-column phase for the fully controlled gate. Do not call it global phase; expose basis-phase, classical-basis, and measurement consequences separately. |
| Lemma 7.11 | General `∧_{n−2}(U)` using a zero-initialized auxiliary that incurs no net change; proof is only “by inspection.” | Prove the exact arbitrary-basis action for any auxiliary bit, then the desired equality on the clean-zero support for arbitrary superpositions. Prove auxiliary-zero preservation and an explicit factorization witness. Do not claim full-unitary equality. |
| Corollary 7.12 | The clean-auxiliary construction has `Θ(n)` cost and the bit is reusable. | Prove exact component/total upper counts for the named primitive syntax at `n≥7`. Reusability follows from the quantified clean-zero restoration theorem, not from a classical truth table. No lower bound in this cost/ancilla model is supplied. |

The two printed `Θ(n)` claims require a new correction entry: the displayed
algorithms have linear executed counts, but no matching lower bound is proved in
the same model, and identity targets give an immediate counterexample to any
uniform optimal-cost interpretation. Export exact construction counts and `O(n)`
language only.

## Proposed Lean Architecture

- `Barenco/State/CleanWire.lean`: low-dependency public `fixedWireSubspace` and
  `cleanZeroSubspace : Submodule ℂ (State n)`, a theorem lifting basis-column
  equality to every subspace member, and a split-target linear equivalence
  `(ComplementBasis aux → ℂ) ≃ₗ[ℂ] cleanZeroSubspace aux`. Include
  predicate/membership simp lemmas and preservation by a controlled gate whose
  target differs from the fixed wire. This makes factorization/no-entanglement a
  literal theorem, not only prose around a support predicate.
- `Barenco/OneQubit/SelectedABC.lean`: a compact selected
  column-chronological ABC factorization record for a `QubitSpecialUnitary`, with
  the exact inactive and active product equations.
- `Barenco/ControlledCircuit/SelectedSpecial.lean`: select the existing five-node
  controlled-SU(2) witness with exact `(3,2,5)` one-qubit/CNOT/total resource
  contract. Keep the six-node `Selected` wrapper for Lemma 7.11's arbitrary U(2).
- `Barenco/MultiControl/LastTargetSwap.lean`: swap the last ordered control with
  the target, prove all prefix/target projections, and reuse
  `expandedRecursivePrefixXCircuit` as an exact primitive expansion of an MCX
  from the prefix onto the original target.
- `Barenco/MultiControl/LinearSpecialUnitary.lean`: parameterized Lemma 7.9 macro
  chronology, exact target-product/four-case evaluator, selected ABC wrapper, and
  structural macro counts/cost rejection.
- `Barenco/MultiControl/LinearSpecialUnitaryExpansion.lean`: substitute three selected
  five-node controlled-SU(2) circuits and two swapped-layout expanded MCXs; prove exact
  evaluator preservation and component/total/cost formulas.
- `Barenco/MultiControl/LinearSpecialUnitaryPhase.lean`: isolate the source's
  special `W`, compute its exact fully controlled input-column phase, and derive
  only the justified basis behavior and measurement consequences.
- `Barenco/MultiControl/CleanAncilla.lean`: reuse
  `OrderedControlLayout (p+1) ambientWidth` with its first `p` controls interpreted
  as data and its last control interpreted as the auxiliary; expose clean names
  rather than introducing a duplicate structure. Prove the exact
  arbitrary-auxiliary basis action, clean-zero subspace correctness,
  restoration/factorization, and macro resources.
- `Barenco/MultiControl/CleanAncillaExpansion.lean`: substitute two existing
  expanded prefix MCXs and one selected controlled-U circuit, retaining all clean
  subspace/restoration theorems and proving exact primitive resources.
- `Barenco/MultiControl/LinearResources.lean`: define width-indexed numeric count
  functions for both linear constructions, link them exactly to the named syntax,
  and prove explicit `O(n)` upper bounds without asserting optimal `Theta(n)`.
- `Barenco/MultiControl/AncillaExamples.lean`: root-excluded canonical width-seven
  and width-eight checks, an auxiliary-one counterexample for a nonidentity U,
  exact resource profiles, and fixed-wire factorization diagnostics.
- Keep `Basic`, `Semantics`, `Controlled`, `Circuit`, and completed Stage 7 leaves
  unchanged unless the support proof exposes a genuinely general missing lemma.

## Detailed Implementation Plan

1. Finish the independent source/count/API audits and record any additional
   correction entries before code.
2. Implement and strict-build `State/CleanWire.lean`; prove supported-state
   lifting and the explicit clean-wire linear equivalence without circuit-syntax
   dependencies.
3. Implement the last-control/target swap and exact expanded prefix-to-main-target
   X bridge, with arbitrary ambient wires and inherited exact counts.
4. Package a selected ABC factorization and prove the exact Lemma 7.9 macro
   evaluator before any resource expansion.
5. Expand Lemma 7.9 into one-qubit/CNOT syntax and derive exact p- and width-indexed
   counts. Formalize the special W example only at the strongest checked phase
   relation.
6. Define the clean-ancilla layout and three-macro Lemma 7.11 circuit. Prove its
   general auxiliary-bit basis formula, then lift the clean-zero columns to all
   supported states and prove output factorization/restoration.
7. Expand the clean circuit using the exact Stage 7 prefix-X syntax and selected
   controlled U. Prove exact component/total/cost counts and logical-width/one-
   ancilla contracts.
8. Add low-width diagnostics; update root, traceability, conventions, corrections,
   axiom audit, this file, and `0-plan.md`; run focused/adjacent builds, strict and
   trust-zero checks, forbidden scans, two full builds, and headline axiom audits.

## Boundary and No-Cheating Checks

- Lemma 7.9's macro evaluator is valid for every nonempty total control family;
  the `n≥7` bound belongs only to the chosen linear primitive expansion.
- Lemma 7.11 is never stated as equality of full unitaries. Its hypothesis is a
  quantified amplitude-support condition, and its conclusion covers arbitrary
  data/spectator superpositions.
- Auxiliary restoration includes an explicit fixed-wire output predicate and
  factorization witness. Equality of the auxiliary's classical bit on basis
  inputs is not treated as absence of residual entanglement.
- The final control used as dirty workspace in Lemma 7.9 and the data target used
  as dirty workspace in Lemma 7.11 are restored by exact full-register evaluator
  theorems before surrounding-gate correctness is invoked.
- Exact macro semantics, primitive evaluator preservation, primitive counts,
  logical width, clean-ancilla count, and asymptotic/linear upper language remain
  separate theorem layers.
- The W example uses an explicit basis-phase function. Basis-dependent phase is
  not rewritten as one global scalar.
- No `Primitive.unclassified`, semantic dummy gate, hard-coded full matrix,
  classical-only truth table, or count inferred from semantic equality may enter
  a completed theorem.
- No `Θ(n)` optimality theorem is exported without a matching lower bound in the
  same cost and ancilla model.
- No `sorry`, `admit`, `by?`, custom `axiom`, `opaque`, `native_decide`, or
  `bv_decide` in completed Stage 8 modules.

## Completion Requirements

- [ ] Lemma 7.9 has an exact arbitrary-width macro evaluator, selected-SU(2)
  wrapper, and explicit one-qubit/CNOT expansion with syntax-derived linear cost.
- [ ] Corollary 7.10 is corrected transparently, including the printed index
  mismatch, exact threshold, construction-specific upper count, and exact phase
  relation for the source's W example.
- [ ] Lemma 7.11 has an exact general auxiliary-bit basis formula and a clean-zero
  arbitrary-state theorem that proves restoration and factorization.
- [ ] Corollary 7.12 has a counted primitive circuit, one-clean-ancilla/width
  contract, exact linear upper count, and reusable-output theorem.
- [ ] Canonical smallest-width examples include the invalid auxiliary-one branch
  and confirm all exact component counts.
- [ ] Traceability, conventions, corrections, axiom audit, this stage file, and
  `0-plan.md` are synchronized; focused/adjacent, strict/trust-zero, forbidden,
  diff, two full-build, and axiom-audit evidence is recorded.

## Stage Results

- Stage file created before Stage 8 implementation. Initial audit fixes the two
  diagram chronologies, the clean-subspace boundary, the `n≥7` expansion threshold,
  and the raw syntax count targets above.
- Independent PDF/diagram, API, and count audits agree on every chronology,
  boundary, and raw formula. They additionally establish determinant-one as
  necessary for Lemma 7.9's five-macro topology, identify the stronger five-node
  controlled-SU(2) subexpansion, and require a literal clean-wire subspace/linear
  factorization API. C-010 and C-022 have been expanded accordingly, and new
  C-026 records why the two printed `Θ(n)` statements are construction upper
  bounds rather than optimal-synthesis theorems. No Stage 8 Lean file was changed
  during these audits.
- `LastTargetSwap.lean` now exchanges the final ordered control with the target,
  proves the prefix layout identity, and reuses Stage 7 as
  `expandedPrefixTargetXCircuit`. Its evaluator is exactly the original
  prefix-controlled target X; the transported dirty wire is the original final
  control, the target is restored, and inherited counts are
  `(32p−80,24p−52,56p−132)`. Strict/trust-zero warning-as-error checks and a
  3,483-job focused build pass.
- `SelectedABC.lean` packages one checked column-chronological special-unitary
  factor triple, and `SelectedSpecial.lean` turns such a target into an exact
  selected five-node controlled circuit with `(3,2,5)` component/total cost.
  Both leaves pass strict/trust-zero checks, their combined 2,372-job focused
  build, forbidden/diff scans, and standard-only representative axiom audits.
- `LinearSpecialUnitary.lean` stores Lemma 7.9's exact five-macro chronology,
  proves its arbitrary-register target-local basis action, checks all four
  prefix/final-control branches, and derives full controlled-W evaluator equality
  from explicit `CBA=I` and `CXBXA=W` products. The selected ABC wrapper is exact
  for every nonempty total control family, including an empty prefix; macro count
  is five and the early-basic cost is honestly `none`. Strict/trust-zero checks
  and its 2,929-job focused build pass.
- `State/CleanWire.lean` supplies the missing general foundation: basis-column
  equality lifts to arbitrary supported amplitude vectors;
  `fixedWireSubspace`/`cleanZeroSubspace` are literal submodules; split-target
  embed/restrict maps form a linear equivalence with complementary-wire states;
  and controlled gates on another target preserve the subspace. Thus every clean
  state has a machine-checked factorization witness. Strict/trust-zero checks and
  its 2,361-job focused build pass; representative axioms are standard only.
- `CleanAncilla.lean` reconstructs the exact three-macro Lemma 7.11 circuit on an
  arbitrary ambient layout. It proves the general firing condition through the
  intermediate auxiliary, including the complementary auxiliary-one behavior;
  lifts the clean-zero basis columns to every vector in `cleanZeroSubspace`;
  proves output closure; and returns an explicit complementary-state
  factorization witness, so restoration/no residual entanglement is literal.
  Macro count is three and unexpanded cost is `none`. Strict/trust-zero checks and
  its 2,922-job focused build pass.
- `LinearSpecialUnitaryExpansion.lean` substitutes three selected five-node
  controlled-SU(2) circuits and two exact swapped-layout MCXs. It preserves the
  full controlled-W evaluator and proves exact profiles
  `(64p−151,48p−98,112p−249)` and width forms
  `(64n−279,48n−194,112n−473)`, including `(169,142,311)` at `n=7`.
  Strict/trust-zero checks, a 3,487-job focused build, scans, and standard-only
  representative axiom audits pass.
- `LinearSpecialUnitaryPhase.lean` packages the source's W as an actual special
  unitary and proves the fully controlled circuit differs from controlled X by a
  minus sign exactly when all controls and the input target are one. It exports
  `BasisPhaseEq`, `SameBasisBehavior`, and `BasisMeasurementEq`, never a false
  global-phase claim. Strict/trust-zero checks and its 2,940-job focused build
  pass.
- `CleanAncillaExpansion.lean` substitutes two exact corrected-Corollary-7.4
  prefix MCXs and the selected six-node controlled-U circuit. Its evaluator is
  exactly the three-macro Lemma 7.11 evaluator; the arbitrary-auxiliary basis
  formula, clean-zero arbitrary-state equality, output closure, and explicit
  factorization all transport to the primitive syntax. It declares exactly one
  required clean wire and proves the structural one-clean-ancilla contract. Exact
  profiles are `(64p−156,48p−102,112p−258)` and, at logical width `n=p+2`,
  `(64n−284,48n−198,112n−482)`, including `(164,138,302)` at `n=7`.
  Strict/trust-zero checks, a 3,485-job focused build, scans, standard-only axiom
  checks, and an independent chronology/restoration/count review pass.
