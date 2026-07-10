# 5-CONTROLLED

Status: in progress.

## Current Facts

- The source material is available in the original PDF, the local transcription,
  and four extracted diagrams:
  `lemma-5-1-controlled-su2.png`, `lemma-5-2-controlled-phase.png`,
  `lemma-5-4-two-xor-special-case.png`, and
  `lemma-5-5-one-xor-special-case.png`. The diagrams execute left-to-right.
- In the paper's row convention, Lemma 5.1 applies `A`, XOR, `B`, XOR, `C` to
  the target. In the library's standard-column semantics, the chronological list
  evaluates to `C * X * B * X * A` on an active control and `C * B * A` on an
  inactive control. Stage 4 proves exactly these two matrix identities for every
  `W : QubitSpecialUnitary`, but does not yet construct a `Circuit`.
- `Primitive.oneQubit`, `Primitive.cnot`, and `Primitive.positiveControlled` are
  correctness-by-construction syntax. `Circuit.eval` treats the list head as the
  first operation, and `Circuit.eval_append` puts later circuits on the left.
  `Circuit.gateCount`, `kindCount`, and partial `Circuit.cost` inspect syntax only.
- All target-local and positively controlled gates are reindexed block-diagonal
  matrices over `splitTarget`. Mathlib supplies `Matrix.blockDiagonal_mul` and
  `Matrix.blockDiagonal_inj`, so a narrow target-block algebra can prove complete
  circuit characterizations without four-by-four coordinate expansion or a new
  semantic model.
- Lemma 5.2 is stronger and cleaner on an arbitrary ambient register: a scalar
  phase controlled from `control` onto any distinct `target` is exactly the local
  diagonal phase `diag(1, exp(i*delta))` on `control`; every other wire is
  untouched because both sides are equal full-register matrices.
- The standard-column transpose of Lemma 5.4's family can be stated, after
  renaming the unrestricted middle angle, as
  `rz alpha * ry theta * rz alpha`. Its chronological circuit is `A`, XOR, `B`,
  XOR, so inactive and active target products are `B*A` and `X*B*X*A`.
- The standard-column transpose of Lemma 5.5 is most transparently stated as
  `X * (rz alpha * ry theta * rz alpha)` (equivalently the paper's displayed
  family after renaming `alpha`). Its chronological circuit is `A`, XOR, `B`,
  with inactive and active products `B*A` and `B*X*A`.
- Corollary 5.6 calls two controlled-`V` gates “basic,” contradicting the
  Sections 3–7 definition that only arbitrary one-qubit gates and XOR/CNOT are
  basic. The current `oneQubitCNOT` model correctly rejects an unexpanded
  `.controlledOneQubit` primitive. The formalization must report the six-operation
  macro structure separately from any fully expanded one-qubit+CNOT cost.
- `BUILD-PLAN.md` is authoritative. New block algebra and circuit builders belong
  in narrow leaves; the established high-fanout `Controlled`, `Circuit`, and
  `Cost` modules should remain unchanged unless a checked reusable gap requires a
  small foundational lemma.

## Updated Assumptions

- Lemma 5.1's “if and only if” will quantify the existence of certified
  `A,B,C : QubitSpecialUnitary` whose explicit circuit evaluates to the desired
  controlled gate. The converse target is the exact determinant-one condition on
  the already-certified `W : QubitUnitary`.
- Circuit correctness should be proved for every finite ambient width and every
  distinct `control,target : Fin n`, not only for a hard-coded two-qubit basis.
  The two-qubit matrices remain diagnostic examples.
- A reusable evaluator characterization should expose both control branches:
  equality with controlled `W` is equivalent to the inactive product being `I`
  and the active product being `W`. This supports both directions of Lemmas 5.1,
  5.4, and 5.5 rather than proving only the displayed constructions.
- The special-case converses require an independently checked classification of
  conjugates of Pauli-X (traceless determinant-`-1` unitaries), including zero
  coordinate cases. A parameter-count argument or sampled matrix calculation is
  insufficient.
- Corollary 5.3 should use the exact Stage 4 determinant-phase split and the proved
  controlled scalar-phase identity. Its resource theorem must name
  `CostModel.oneQubitCNOT` and derive four one-qubit plus two CNOT occurrences from
  the constructed syntax.
- Corollary 5.6 needs two levels: an exact six-node macro circuit containing two
  controlled-one-qubit primitives, for which `oneQubitCNOT` cost is deliberately
  `none`, and a separately expanded circuit/cost theorem if the Lemma 5.5
  expansions are composed. No macro count will be relabeled as basic-gate cost.

## Big Picture Objective

Reconstruct every Section 5 controlled-one-qubit diagram as explicit
full-register circuit syntax, prove the exact evaluator equalities and both
directions of the claimed characterizations, and derive resource statements only
from those circuits under explicit primitive models.

## Detailed Implementation Plan

- Add a target-block leaf wrapping the existing reindexed block-diagonal
  representation. Prove multiplication, identity, injectivity, and bridges for
  local, controlled, and CNOT matrices. Use it to characterize alternating
  target-local/CNOT circuits by their inactive and active one-qubit products.
- Define chronological builders for the five-gate A/X/B/X/C circuit, the
  four-gate A/X/B/X circuit, and the three-gate A/X/B circuit. Prove their exact
  evaluators and iff characterizations against a single positively controlled
  target unitary on arbitrary distinct wires.
- Derive Lemma 5.1 from `specialUnitary_exists_columnChronologicalABC`. Prove the
  converse determinant calculation from the active branch, including both
  `det X = -1` factors. Export exact gate/kind/cost theorems.
- Define the paper's control phase `E(delta)`, certify it, prove its entry formula
  and equality to `rz(-delta) * phaseShift(delta/2)`, and prove Lemma 5.2 as a
  full-register equality by basis-column action or matrix extensionality.
- Compose the Lemma 5.1 and phase circuits using
  `specialUnitaryPart`/`determinantPhaseAngle` to obtain Corollary 5.3. Prove exact
  evaluator equality and the syntax-derived `4 + 2 = 6` one-qubit+CNOT cost.
- Prove a complete classification of Pauli-X conjugates, preferably in a separate
  heavy proof leaf. Use it together with the general evaluator characterizations
  to prove both iff directions of Lemmas 5.4 and 5.5, with explicit paper-row and
  standard-column parameter bridges.
- Reconstruct Corollary 5.6 with a named controlled-`V` macro circuit. Prove its
  semantics and structural six-node count, prove that the Sections 3–7 cost model
  rejects it before expansion, then compose the Lemma 5.5 expansions and state the
  exact expanded cost after checking all adjacent cancellations/merges.
- Add diagnostic two-qubit truth tables, arbitrary-width/non-adjacent examples,
  phase endpoints, identity and Pauli special cases, determinant converses, and
  cost computations. Update the root, traceability, correction log, conventions,
  and axiom audit only after the public leaves stabilize.

## Build Structure

- `Barenco/ControlledCircuit/Block.lean`: low-dependency proof-side/public target
  block algebra and local/controlled/CNOT bridges; imports `Barenco.Circuit` only.
- `Barenco/ControlledCircuit/Decomposition.lean`: runtime/public chronological
  circuit builders plus proof-side/public evaluator characterizations and Lemma
  5.1; imports Stage 4 Lemma 4.3 and `Block`.
- `Barenco/ControlledCircuit/Phase.lean`: runtime/public control-phase gate and
  Corollary 5.3 construction; imports global-phase/Euler leaves only as needed.
- `Barenco/ControlledCircuit/Special.lean`: heavy proof-side/public Pauli-conjugate
  classification, Lemmas 5.4–5.5, and corrected Corollary 5.6 semantics/resources.
- `Barenco/ControlledCircuitExamples.lean`: diagnostic only, excluded from the
  public root.
- `Barenco.lean` remains untouched until all stable public leaves compile.
  Focused builds target each leaf; adjacent builds target diagnostics, cost
  consumers, `Barenco.AxiomAudit`, and the public root. A root change requires two
  consecutive full builds.
- Runtime/public declarations are certified phase gates and circuit constructors.
  Proof-side/public declarations are block laws, evaluator/iff theorems,
  determinant/classification facts, and resource equations. Concrete examples are
  diagnostic. No fallback or temporary declaration may enter the root.

## Boundary Checks

- Every diagram theorem names an actual `Circuit`; a one-qubit matrix identity is
  not reported as a larger-register circuit equality.
- Control and target are explicit and distinct. Proofs quantify all other ambient
  wires, so untouched-wire and no-ancilla behavior follows from exact
  full-register evaluator equality rather than a two-qubit sample.
- Paper-row products and semantic chronological products remain separately named;
  transposition and factor reversal are never implicit.
- The converse of an iff is proved from evaluator equality, not assumed from the
  intended target or inferred by parameter counting.
- A gate count comes from `Circuit.gateCount`/`kindCount`; a cost comes from a named
  `CostModel`. Unsupported controlled macros remain `none` until expanded.
- Global scalar phase, a diagonal phase on the control wire, and equality up to
  global phase remain distinct. Lemma 5.2 is exact matrix equality.

## No-Cheating Checks

- No four-by-four numerical spot check substitutes for arbitrary-width matrix
  equality.
- No use of `Primitive.unclassified` in a counted construction.
- No relabeling of `.controlledOneQubit` as one CNOT or one basic operation under
  `CostModel.oneQubitCNOT`.
- No only-if theorem proved merely from the determinant of the intended target;
  the determinant equation must be derived from the circuit's active branch.
- No sampled-angle or dimension-count proof of the Lemma 5.4/5.5 classifications.
- No `sorry`, `admit`, `by?`, custom axiom, `native_decide`, or `bv_decide`.

## Completion Requirements

- [ ] All four Section 5 diagrams have named chronological circuits, exact
  arbitrary-register evaluator theorems, and source/ordering documentation.
- [ ] Lemmas 5.1, 5.4, and 5.5 compile in both directions with all unitary,
  determinant, trace, and angle assumptions explicit; Lemma 5.2 is exact.
- [ ] Corollary 5.3 has a constructed six-primitive circuit with exactly four
  one-qubit gates, two CNOT gates, and cost `some 6` under
  `CostModel.oneQubitCNOT`.
- [ ] Corollary 5.6 distinguishes its six-node controlled-`V` macro count from a
  fully expanded one-qubit+CNOT cost and records any merge convention.
- [ ] Focused, adjacent, warning-as-error, shortcut scans, two full builds, and
  headline axiom evidence satisfy `BUILD-PLAN.md`.
- [ ] Traceability and corrections record exact circuit layers, both iff
  directions, determinant/phase facts, and the repaired “basic operation” claim.

## Stage Results

- In progress. First implementation target: the target-block algebra and the
  five-gate evaluator characterization, while the independent source audit checks
  the special-case iff statements and Corollary 5.6 terminology.
