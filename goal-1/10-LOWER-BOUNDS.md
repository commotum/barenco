# 10-LOWER-BOUNDS

Status: in progress (source and architecture audit begun; no lower-bound theorem
is considered complete yet).

## Current Facts

- The only proved lower-bound argument in the paper's Sections 3--7 is Lemma 7.7.
  It concerns exact simulation of a fully controlled nonscalar one-qubit unitary
  by arbitrary one-qubit gates and CNOTs. Although the statement says at least
  `n-1` "basic operations," the proof actually establishes the stronger claim
  that at least `n-1` CNOT occurrences are necessary; arbitrary one-qubit gates
  do not add edges to the interaction graph.
- The intended invariant is an undirected interaction graph on the register
  wires. One-qubit operations stay inside one vertex. Every CNOT occurrence adds
  at most one edge. A connected graph on `n` finite vertices has at least `n-1`
  edges, so a circuit with fewer CNOTs has a nonempty proper wire partition with
  no gate crossing it.
- The semantic step suppressed by the source is substantial: every circuit whose
  gates stay on one side of a partition must factor, after a checked basis
  reindexing, as a Kronecker product of two unitaries. A fully positive-controlled
  target factors across a nontrivial partition only if its one-qubit target is
  scalar. This tensor obstruction, including the target-on-either-side cases,
  must be proved explicitly.
- `Circuit` permits several macro and unclassified primitive kinds. A theorem
  merely assuming a numeric cost or inspecting `Primitive.kind` is not a semantic
  classification theorem: structural metadata alone should not be used to infer
  locality. Stage 10 will introduce or package a proof-carrying one-qubit/CNOT
  syntax and map it to the existing trusted `Primitive.oneQubit` and
  `Primitive.cnot` constructors. The lower bound will quantify over that exact
  allowed syntax and link its counts to `Circuit.cost`.
- The nonscalar boundary is essential. If `U = z I` with `|z|=1`, its positive
  controlled version is a diagonal phase on the controls and does not have the
  target-dependence used by Lemma 7.7. The theorem must not silently include this
  case. At one register wire the claimed bound is zero and should be discharged
  explicitly rather than forcing a nonexistent nontrivial partition.
- Section 5 gives topology classifications for two-CNOT and one-CNOT circuit
  families, already formalized as `twoCNOTFamily_iff` and `oneCNOTFamily_iff`.
  These are exact iff results for named topologies, not global minimum-CNOT
  theorems over every possible circuit.
- Corollaries 5.3 and 6.2 are constructive "at most" results. Section 8 explicitly
  says its small arbitrary-two-qubit counts were supported by numerical evidence,
  not proved minimal. No minimum theorem may be inferred from those upper bounds.
- Section 8's six-gate `U(8)` diagram reaches the dimension `64`, but equality of
  parameter dimensions does not prove surjectivity. Its formula
  `(4^n-3n-1)/9` is presented as a dimension-counting suggestion/conjecture and
  lacks a formal parameter map, smooth image/fiber argument, quotient treatment,
  and generic-versus-worst-case quantifier. It remains excluded unless those
  missing mathematical ingredients are supplied independently.

## Source Claim Audit

| Claim | Source content | Audited status and routing |
|---|---|---|
| Lemma 7.7 combinatorics | Fewer than `n-1` XOR gates disconnect the wire graph. | Planned proof for a proof-carrying one-qubit/CNOT syntax, with an occurrence-to-edge inequality that handles duplicate CNOT edges. |
| Lemma 7.7 factorization | A disconnected network transformation "must therefore" be `A tensor B`. | Planned explicit basis-splitting equivalence and Kronecker evaluator theorem; this does not follow from a support count alone. |
| Lemma 7.7 target obstruction | A nonscalar fully controlled target is not of that form. | Planned iff/counterdirection theorem across every nonempty proper wire partition, with the scalar and one-wire boundaries explicit. |
| Section 5 special topologies | Exact iff descriptions for the displayed two-CNOT and one-CNOT families. | Already proved for those named topologies; audit whether any genuinely global lower corollary follows without assuming a normal form. |
| Section 5/6 counts | Six and sixteen basic gates suffice for the displayed exact constructions. | Constructive upper bounds only; no minimum wording will be added. |
| Section 8 small counts | Five/three/thirteen constructions and alleged six-gate general `U(8)`. | Upper constructions belong to later resource work; numerical minimality is excluded, and six-gate surjectivity remains unresolved. |
| Section 8 dimension lower bound | Suggested `(4^n-3n-1)/9` arbitrary-two-qubit lower bound. | Intentionally excluded as an unconditional theorem; preserve the exact missing manifold/image assumptions in corrections and traceability. |

## Proposed Lean Architecture

- `Barenco/LowerBounds/BasicCircuit.lean`: proof-carrying inductive syntax with
  exactly arbitrary one-qubit and CNOT constructors; erasure to `Circuit`,
  evaluator preservation, CNOT/total counts, and exact
  `CostModel.oneQubitCNOT` linkage.
- `Barenco/LowerBounds/InteractionGraph.lean`: undirected CNOT interaction graph,
  duplicate-safe edge cardinality bound, connected-graph lower bound, and an
  explicit disconnected partition witness.
- `Barenco/LowerBounds/PartitionFactorization.lean`: function-space basis split by
  a decidable wire predicate, reindexed Kronecker factorization for each allowed
  primitive and for sequential circuits, with multiplication order checked.
- `Barenco/LowerBounds/Lemma77.lean`: scalar-target definition/equivalences,
  nonfactorization of a fully positive-controlled target, the `n-1` CNOT lower
  bound, the weaker total-gate/cost corollary, and boundary diagnostics.
- A root-excluded examples leaf may check widths one, two, and three after the
  general theorem is stable.

File boundaries may be merged if the reusable APIs are clearer together, but the
graph, semantic factorization, target obstruction, and resource corollary remain
separate theorem layers.

## Detailed Implementation Plan

1. Finish the source audit and inspect pinned mathlib APIs for finite simple
   graphs, connected edge-cardinality bounds, `Equiv.piEquivPiSubtypeProd`, matrix
   reindexing, and Kronecker multiplication.
2. Implement the restricted basic syntax and prove erasure/evaluator/count/cost
   bridges without changing the trusted generic `Circuit` representation.
3. Define the CNOT interaction graph and prove that fewer than `n-1` occurrences
   yield a nontrivial disconnected partition for `n>=2`.
4. Prove primitive and circuit Kronecker factorization across every partition not
   crossed by a CNOT edge.
5. Prove that factorization of a fully controlled target across any nontrivial
   partition forces its one-qubit target to be scalar; audit exact versus
   global-phase equality and export only what is established.
6. Combine the invariant and obstruction into a lower bound on CNOT occurrences,
   then derive total-gate and accepted-cost consequences from syntax.
7. Add boundary examples, public imports, axiom checks, corrections/traceability/
   convention updates, forbidden-token scans, strict/trust-zero checks, focused
   builds, and two full builds.

## Boundary and No-Cheating Checks

- The allowed primitive set is part of every headline theorem; Toffoli,
  controlled-one-qubit macros, arbitrary-two-qubit primitives, and unclassified
  semantic gates are not admitted accidentally.
- Edge cardinality is bounded by CNOT occurrences, not identified with them;
  repeated gates on the same pair may produce duplicate graph edges.
- Disconnection produces a named nonempty proper partition and an exact semantic
  factorization, not merely a statement about syntactic supports.
- The Kronecker order follows the chosen basis equivalence and is verified by
  entries/evaluation; paper notation does not choose the Lean index order.
- "Nonscalar" is defined algebraically and reconciled with the paper's unit-phase
  scalar form for certified unitaries.
- Exact equality, global-phase equality, channel equality, and basis behavior are
  not interchanged. The first lower-bound theorem targets exact circuit equality.
- A structural lower bound is not generalized to ancilla-assisted, measurement,
  approximate, or arbitrary-two-qubit models without a new invariant.
- No result is called minimal or `Omega` merely because a named construction has
  a matching-looking count.
- No `sorry`, `admit`, `by?`, custom `axiom`, `opaque`, `native_decide`, or
  `bv_decide` may occur in completed modules.

## Completion Requirements

- [ ] The restricted one-qubit/CNOT syntax has exact evaluator and resource
  bridges to the existing library.
- [ ] The interaction-graph occurrence bound and disconnected-partition theorem
  compile for every finite register, with width-zero/one cases explicit.
- [ ] Partition factorization is proved on arbitrary-width registers and is
  preserved by chronological composition.
- [ ] A fully controlled nonscalar target is proved nonfactorable across every
  nontrivial wire partition.
- [ ] Lemma 7.7 is exported with an explicit primitive set, exact target relation,
  CNOT count, total count, and cost-model corollary.
- [ ] Section 5/6 topology and Section 8 heuristic/minimality claims are correctly
  scoped in corrections, traceability, and conventions.
- [ ] Boundary examples, public-root imports, maintained axiom entries, strict/
  trust-zero, forbidden/diff, focused, and two full-build checks pass and are
  recorded.

## Stage Results

- Stage file created before Stage 10 implementation. Initial audit identifies
  Lemma 7.7 as the rigorous lower-bound target, strengthens its intended count to
  CNOT occurrences, separates graph/factorization/nonfactorization/resource
  layers, and quarantines Section 8 dimension counting.
