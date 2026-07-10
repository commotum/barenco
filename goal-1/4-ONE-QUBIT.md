# 4-ONE-QUBIT

Status: in progress.

## Current Facts

- PDF pages 8–10 and the local transcription agree on all Section 4 signs:
  `Ry(θ) = [[cos(θ/2), sin(θ/2)],[-sin(θ/2),cos(θ/2)]]`,
  `Rz(α) = diag(exp(iα/2),exp(-iα/2))`, `Ph(δ) = exp(iδ) I`, and
  `X = [[0,1],[1,0]]`.
- The paper uses row vectors/right action. Exact displayed matrices therefore need
  paper-facing names, while gates used by the library's column-vector semantics are
  their `fromPaper` transposes. Only the displayed `Ry` changes entries under this
  translation.
- Lemma 4.2 consists of six exact multiplication/conjugation identities. A
  warning-clean scratch probe at `/tmp/BarencoStage4Probe.lean` already checks a
  Bool-indexed two-by-two helper, its determinant bridge, and all six raw identities.
- Lemma 4.3 uses
  `A = Rz α Ry(θ/2)`,
  `B = Ry(-θ/2) Rz(-(α+β)/2)`, and
  `C = Rz((β-α)/2)`, with paper-row identities `ABC=I` and `AXBXC=W`.
  Translating to semantic matrices reverses both products.
- Mathlib 4.31.0 exposes `Equiv.finTwoEquiv`, matrix reindex/determinant APIs,
  `Matrix.specialUnitaryGroup`, complex argument/exponential facts, real inverse
  trigonometric facts, and the trigonometric addition laws needed here.
- The paper's proof of the special-unitary Euler case suppresses degenerate
  zero-entry phase choices. Its global phase argument also needs the explicit fact
  `det (Ph δ) = exp(2 i δ)`; `det = 1` permits both scalar phases `1` and `-1`.
- `BUILD-PLAN.md` requires narrow module ownership and focused/adjacent evidence;
  the heavy Euler and root arguments must not block compilation of elementary
  Section 4 identities.

## Updated Assumptions

- `QubitSpecialUnitary` should abbreviate mathlib's
  `Matrix.specialUnitaryGroup Bool ℂ`, rather than introducing a project axiom or an
  unrelated determinant predicate.
- Paper-facing matrices and standard-column semantic gates will both be public,
  with explicit transpose bridge theorems. Future circuits use only the semantic
  versions unless a theorem explicitly states a paper-row product.
- Euler existence must either choose phases through `Complex.arg` with explicit
  zero-entry branches or prove a canonical SU(2) entry form first. Parameterized
  reconstruction is useful independently and should compile before surjectivity.
- Arbitrary one-qubit unitary roots are a separate spectral/axis-angle obligation;
  halving the Euler angles is invalid because the factors do not commute.

## Big Picture Objective

Independently formalize the Section 4 one-qubit matrix language, all six Lemma 4.2
identities, the strongest fully justified U(2)/SU(2) Euler theorem, Lemma 4.3's
constructive and existential decompositions, and the unitary-root facts actually
required by later controlled-gate stages.

## Detailed Implementation Plan

- Add a small explicit Bool-indexed matrix constructor and define `cis`, `paperRy`,
  `paperRz`, `paperPhase`, and the displayed Pauli-X. Prove entry, determinant,
  adjoint/negation, and all six Lemma 4.2 identities.
- Define semantic column gates with `fromPaper`, prove their exact bridge and
  identity families, and package the rotations/phase as `QubitUnitary` and, where
  determinant one, `QubitSpecialUnitary`.
- Prove the parameterized Euler entry formula. Then prove a canonical entry theorem
  for an arbitrary SU(2) matrix and handle zero/nonzero phase choices explicitly to
  establish the existential SU(2) Euler result.
- Derive the U(2) Euler result by choosing half the argument of the unitary
  determinant, removing its scalar phase, applying the SU(2) theorem, and proving
  the determinant calculation rather than assuming it.
- Define the paper's `A,B,C` parametrically and prove `ABC=I` and `AXBXC=W` as raw
  matrix identities. Translate them into the reversed standard-column products and
  a chronological semantic circuit-ready statement. Derive existential Lemma 4.3
  only from the proved SU(2) Euler theorem.
- Isolate arbitrary square/iterated unitary-root existence in a later Section 4 leaf.
  Probe spectral, functional-calculus, or explicit SU(2) axis-angle routes. If full
  existence cannot yet be established, keep the exact root equation as an explicit
  hypothesis for dependent construction lemmas and document the obstruction; do
  not choose a root by fiat.
- Add low-dimensional checks for zero angles, `π`, Pauli-X conjugation, determinant,
  transpose orientation, and chronological A/B/C order. Update root exports,
  traceability, corrections, and the axiom audit only after public leaves stabilize.

## Build Structure

- `Barenco/OneQubit/Matrix.lean`: low-dependency runtime/public explicit matrices,
  cheap entry/determinant facts, and proof-side/public Lemma 4.2 algebra.
- `Barenco/OneQubit/Certified.lean`: public unitary/SU packages and semantic
  `fromPaper` variants; imports `Matrix` but not circuit, cost, measurement, or norm
  leaves.
- `Barenco/OneQubit/Euler.lean`: heavy proof-side/public parameterized and
  existential Euler theorems; imports argument/inverse-trigonometric support.
- `Barenco/OneQubit/Decomposition.lean`: public A/B/C definitions and Lemma 4.3
  identities; the parameterized algebra depends only on `Certified`, while its
  existential corollary imports `Euler` if a split avoids widening dependencies.
- `Barenco/OneQubit/Roots.lean`: isolated noncomputable public root construction and
  power laws if established; no dependent circuit module imports it prematurely.
- `Barenco/OneQubitExamples.lean`: diagnostic orientation/boundary checks, excluded
  from the public root.
- `Barenco.lean` changes only when the stable Section 4 leaves compile. Focused
  builds target each leaf; adjacent builds target the next leaf, diagnostics,
  `AxiomAudit`, and the root. Changing the root requires two full builds.
- Runtime/public: explicit matrices, certified gates, factor/root constructors.
  Proof-side/public: identities, unitarity, determinants, Euler/decomposition/power
  laws. Diagnostic: concrete examples. No fallback or temporary declaration may be
  imported by the public root.

## Boundary Checks

- A raw paper-row identity is never reported as a chronological column-semantic
  circuit theorem without applying `fromPaper` and reversing multiplication order.
- Matrix equality is proved extensionally for all four entries, not inferred from a
  handful of numerical angles.
- Certified gates carry actual `unitaryGroup` membership; determinant-one claims
  use `specialUnitaryGroup` membership and an explicit determinant proof.
- Euler angle nonuniqueness and zero entries are allowed, but no undefined phase or
  division by a possibly zero amplitude enters a theorem.
- Root theorems state the exact exponent and certify unitarity. A named matrix `V`
  is not evidence that `V^k=U`.

## No-Cheating Checks

- No direct use of the paper's displayed `Ry` as a semantic column gate.
- No proof of Lemma 4.1 solely by parameter counting or by checking sampled
  matrices.
- No silent replacement of `exp(2 i δ)=1` by `δ=0`; periodic and `-I` cases remain
  valid.
- No halving of noncommuting Euler factors to claim a matrix root.
- No `sorry`, `admit`, custom axiom, `native_decide`, or `bv_decide`.

## Completion Requirements

- [ ] Explicit paper and semantic matrices, bridge theorems, determinants,
  adjoints, unitarity/SU certificates, and all six Lemma 4.2 identities compile.
- [ ] Parameterized and existential SU(2) Euler theorems compile with degenerate
  cases covered.
- [ ] The U(2) Euler theorem compiles with its determinant/global-phase argument.
- [ ] Parameterized and existential Lemma 4.3 decompositions compile in both raw
  paper order and translated semantic/chronological order.
- [ ] The strongest established arbitrary-unitary root API is recorded; every later
  dependency either uses its proved constructor or exposes an explicit root
  hypothesis.
- [ ] Focused, adjacent, warning-as-error, scan, two full-build, and headline axiom
  evidence is recorded under `BUILD-PLAN.md`.
- [ ] Traceability and corrections distinguish proved identities, conditional
  statements, remaining root/Euler obstructions, and all row/column differences.

## Stage Results

- In progress. First implementation target: `Barenco/OneQubit/Matrix.lean`, using
  the compiled scratch probe rather than re-discovering the elementary algebra.
