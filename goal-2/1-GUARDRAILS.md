# 1-GUARDRAILS

Status: in progress (2026-07-10).

## Current Facts

- Goal 1 is complete and the working tree began this stage clean at commit
  `aaef54f`. The pinned baseline is Lean 4.31.0 with mathlib commit
  `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`; the maintained audit currently has
  319 `#print axioms` entries.
- `Circuit n` is `List (Primitive n)` in chronological order. Its evaluator is
  `eval (primitive :: tail) = eval tail * primitive.denotation`, so a chronological
  pair `[U,V]` fuses to local product `V * U`.
- `Primitive` has a private constructor and only three stored fields: `kind`, an
  unordered structural `support`, and a certified full-register `denotation`.
  There is no retained target/control/pair/local-matrix payload and no generic
  theorem that disjoint support metadata implies commuting denotations.
- `PrimitiveKind.arbitraryTwoQubit` and its Section 8 unit price already exist, but
  no trusted smart constructor currently inhabits that kind. The only general
  semantic wrapper is `Primitive.unclassified`, which has full support and is
  rejected by both named models.
- `Primitive.adjoint` retains kind/support and inverses the denotation. A new
  inspectable optimization layer must retain enough payload to express its local
  inverse rather than trying to recover it from the full-register matrix.
- Existing semantic infrastructure includes certified reindex, block-diagonal,
  and Kronecker unitary constructors; `splitTarget` and target-block algebra handle
  one selected wire. The precise lowest-dependency ordered-pair construction is
  still being audited.
- `selectedControlledU2Circuit` and the selected exact-Toffoli expansion use
  `Classical.choose` witnesses whose specs retain semantics and aggregate counts
  but not optimizer-visible boundary factors. Transparent factor and explicit
  expansion APIs exist below those selection layers and must be used instead.
- The relative-phase A circuit is the literal chronology
  `A(target); CNOT(second,target); A(target); CNOT(first,target);`
  `A†(target); CNOT(second,target); A†(target)`. Its existing exact evaluator and
  `BasisPhaseEq` consequences are arbitrary-width; its literal Section 8 cost is
  seven. The paper's three-gate statement is a constructed upper-count target, not
  a minimality claim.
- For `m=n-1>=1` controls, the existing raw Gray expansion has exactly
  `4*(2^m-1)` one-qubit nodes and `3*2^m-4` CNOTs. The source prints post-merger
  counts `2*2^m` and `3*2^m-4` respectively but supplies no merger syntax.
- For logical width `n>=7`, the corrected balanced Corollary 7.4 circuit has raw
  profile `(32n-144,24n-100,56n-244)`. The source's `48n-204` target would require
  one-qubit count `24n-104` if the checked CNOT count is unchanged. The phase-safe
  chronology uses `Arel; Bhybrid; adjoint(Arel); Bhybrid`; neither the source's
  invalid smallest split nor two forward A copies may be restored for a lower
  number.

## Updated Assumptions

- A separate payload-preserving optimization IR lowering into the stable
  `Primitive`/`Circuit` core is currently the preferred architecture. A direct
  `Primitive` redesign would migrate a high-fanout API and still require explicit
  ordered-pair payloads. This remains provisional until the import/fanout audit is
  recorded below.
- The semantic local type should be an ordered two-bit basis, likely
  `Basis 2 = Fin 2 -> Bool` or an explicitly equivalent `Bool × Bool`. The final
  choice must make the `00,01,10,11` convention and pair reversal theorem explicit.
- A trusted `Primitive.twoQubit` constructor will probably require a narrow edit to
  `Barenco/Circuit.lean`, because the private constructor prevents a later module
  from manufacturing a correctly tagged primitive. Its semantic embedding must
  live below `Circuit` to avoid a cycle.
- The relative-phase cost-three target appears constructively reachable without
  commutation by grouping nodes `1–3`, `4`, and `5–7`, each on one ordered pair.
- A coherent Gray expansion that chooses factors once and uses the literal adjoint
  for opposite signs may expose one inverse one-qubit pair at every internal block
  boundary. Sign alternation, chronology, and boundary arithmetic remain proof
  obligations rather than accepted facts.
- Corollary 7.4 may remain not recovered even if generic normalization is sound.
  One normalizer result cannot refute the source number without a scoped
  completeness or lower-bound theorem.

## Big Picture Objective

Freeze Goal 2's representation, equality, locality, cost, source-claim, module,
and verification boundaries before any Lean implementation begins.

## Detailed Implementation Plan

- Complete a declaration-level inventory of the local/mathlib APIs usable for an
  ordered two-wire split, full-register embedding, unitarity, multiplication,
  inverse, swap orientation, and basis action.
- Compare the separate optimizer IR and direct-`Primitive`-refactor designs using
  actual dependency ownership and optimizer-input requirements.
- Inspect the exact source passages, corrections C-003/C-004/C-025/C-032/C-035,
  current selected-factor APIs, and theorem signatures for all three test families.
- Freeze the ordered pair convention, supported optimizer grammar, exact equality
  relation, two normalization policies, opaque/unsupported barrier behavior, and
  verified/refuted/not-recovered status discipline.
- Freeze tentative Stage 2–5 module ownership, declaration classifications, and
  focused/adjacent build commands.
- Run the cached focused baseline, strict and trust-zero root/audit compilation,
  forbidden-source scans, and `git diff --check` before any Lean source change.
- Fold final facts and the completed design decision into `goal-2/0-plan.md`.

## Build Structure

- Stage 1 changes documentation only: this stage file and the current-facts/status
  portions of `goal-2/0-plan.md`.
- Expected Stage 2 runtime/public leaf: a low-dependency module under
  `Barenco/TwoQubit/` owning ordered pair semantics. It must not import `Circuit`,
  `Cost`, optimization modules, examples, or paper-specific constructions.
- Expected Stage 3 high-fanout but narrow edit: `Barenco/Circuit.lean` gains only
  the trusted constructor and cheap structural/denotation lemmas; cost consequences
  remain in `Barenco/Cost.lean` or a narrow consumer leaf.
- Expected Stage 4 runtime/public leaves under `Barenco/Optimization/` own the
  payload-preserving IR and lowering; paper-specific bridges remain higher leaves.
- Expected Stage 5 runtime/public leaves under `Barenco/Optimization/` own fusion
  laws, executable normalization, and resource soundness. Diagnostics remain in a
  root-excluded examples/audit module.
- Stage 1 focused baseline command:
  `lake build Barenco.Circuit Barenco.Cost Barenco.ThreeQubit.RelativePhase`
  `Barenco.MultiControl.GrayExpansion Barenco.MultiControl.Corollary74Expansion`
  `Barenco.AxiomAudit Barenco`.
- Stage 1 strict/trust commands compile `Barenco.lean` and
  `Barenco/AxiomAudit.lean` directly with `-DwarningAsError=true`, with and without
  `-t0`.

## Boundary Checks

- Stage 1 defines architecture and evidence only. It does not add a semantic
  constructor, optimizer runtime, test-case circuit, or resource theorem.
- Ordered wire pairs remain ordered even though structural support is a finset.
  Equal wires are rejected by a proof argument; widths below two have no such
  input.
- Exact equality is the optimizer soundness target. Existing basis-phase results
  are inherited only after an exact bridge to the original circuit.
- Structural support is an upper bound and not a proof of minimal semantic support.
  Scalar and identity two-wire matrices remain legal without being relabeled as
  smaller gates.
- The early policy may fuse/cancel one-qubit nodes while retaining literal CNOTs;
  the Section 8 policy may absorb eligible operations into a `U(4)` node. The two
  output costs are never conflated.
- Opaque chosen circuits and unsupported generic primitives are barriers until a
  transparent proved expansion is supplied.
- No ancilla is introduced by the two-wire embedding or normalizer. Test-case
  existing dirty/clean contracts must be preserved by exact evaluator equality.

## No-Cheating Checks

- Search confirms that Stage 1 introduces no `Primitive.unclassified` use, no
  arbitrary-two-qubit smart constructor, no optimizer, and no count theorem.
- The selected design must never infer a local matrix from `.kind`, `.support`, or
  support cardinality.
- Every future fused node must lower through a trusted constructor built from a
  certified local unitary and ordered wires.
- Every future count must inspect the actual normalized syntax; no disputed formula
  is accepted as a definition or arithmetic postulate.
- No global phase is deleted in exact normalization.
- Optimizer failure is classified as not recovered unless a theorem proves a
  same-scope impossibility result.
- Baseline forbidden scans cover all project Lean files for proof holes, custom
  axioms, opaque declarations, and forbidden decision shortcuts.

## Completion Requirements

- [ ] Local/mathlib two-wire API inventory is recorded with exact declaration and
  import owners.
- [ ] Separate-IR versus direct-refactor decision is frozen using dependency and
  trust-boundary evidence.
- [ ] Source chronologies, formulas, equality relations, distinctness assumptions,
  widths, and current theorem names are independently recorded for all test cases.
- [ ] Ordered-pair convention, optimizer grammar, exact soundness target, cost
  policies, barrier semantics, and result-status vocabulary are frozen.
- [ ] Stage 2–5 module ownership, declaration classifications, and focused/adjacent
  commands are recorded.
- [ ] Cached focused baseline, strict/trust-zero root and audit, forbidden scans,
  and `git diff --check` pass with exact results recorded.
- [ ] `goal-2/0-plan.md` is folded forward and agrees with this completed stage.

## Stage Results

- Stage file created before any Lean source change. API/source/architecture audits
  and baseline verification are in progress.
