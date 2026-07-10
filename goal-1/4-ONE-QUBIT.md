# 4-ONE-QUBIT

Status: complete.

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
  zero-entry phase choices. The completed proof covers them with total
  `Complex.arg` choices and a canonical `SU(2)` entry theorem. Its global-phase
  argument is repaired using the explicit fact `det (Ph δ) = exp(2 i δ)`;
  `det = 1` permits both scalar phases `1` and `-1`, and the latter is absorbed by
  a checked `2*pi` shift of a Z angle.
- Exact positive `k`-th roots now exist for every finite-dimensional certified
  complex unitary. The construction uses finite-spectrum continuous functional
  calculus, certifies unitarity, and proves the exact power equation. It does not
  claim continuity in the input unitary or the coherent approximation estimates
  needed later in Section 7.
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
- Euler existence chooses phases through total `Complex.arg` after proving a
  canonical `SU(2)` entry form; the zero-entry cases are covered without division
  by amplitudes.
- Arbitrary finite-dimensional unitary roots are supplied by a spectral
  functional-calculus construction. Halving Euler angles remains invalid because
  the factors do not commute.

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

- [x] Explicit paper and semantic matrices, bridge theorems, determinants,
  adjoints, unitarity/SU certificates, and all six Lemma 4.2 identities compile.
- [x] Parameterized and existential SU(2) Euler theorems compile with degenerate
  cases covered.
- [x] The U(2) Euler theorem compiles with its determinant/global-phase argument.
- [x] Parameterized and existential Lemma 4.3 decompositions compile in both raw
  paper order and translated semantic/chronological order.
- [x] The strongest established arbitrary-unitary root API is recorded; every later
  dependency either uses its proved constructor or exposes an explicit root
  hypothesis.
- [x] Focused, adjacent, warning-as-error, scan, two full-build, and headline axiom
  evidence is recorded under `BUILD-PLAN.md`.
- [x] Traceability and corrections distinguish proved identities, conditional
  statements, remaining root/Euler obstructions, and all row/column differences.

## Stage Results

- `Barenco/OneQubit/Matrix.lean` defines the displayed paper-row matrices
  `paperRy`, `paperRz`, `paperPhase`, and `paperX`, proves their entries,
  determinants, adjoints, zero-angle laws, and all six exact identities of Lemma
  4.2. These are raw matrix statements and do not claim circuit semantics.
- `Barenco/OneQubit/Certified.lean` introduces
  `QubitSpecialUnitary := Matrix.specialUnitaryGroup Bool ℂ`, certified paper gates,
  and the standard-column semantic gates `ry`, `rz`, `phaseShift`, and `sigmaX`.
  Explicit transpose/sign bridges make the paper's row-vector convention visible.
- `Barenco/OneQubit/Decomposition.lean` proves the parameterized Lemma 4.3
  identities `paperA_mul_paperB_mul_paperC` and
  `paperA_mul_X_mul_paperB_mul_X_mul_paperC`, then proves the reversed column
  products `C*B*A=I` and `C*X*B*X*A=columnEuler`. The result is circuit-ready
  algebra, not yet a `Circuit` or resource theorem.
- `Barenco/OneQubit/Euler.lean` proves a canonical `SU(2)` entry form, exact
  parameterized Euler entries, and existential paper/column Euler decompositions
  with the middle angle in `[0, pi]`. The proof handles vanishing entries with
  total argument choices; it has no hidden nonzero hypothesis.
- `Barenco/OneQubit/GlobalPhase.lean` chooses
  `delta = arg(det U)/2` in `(-pi/2, pi/2]`, removes the certified scalar phase,
  proves determinant one, and exactly reconstructs `U`.
  `Barenco/OneQubit/U2Euler.lean` combines this with the `SU(2)` theorem to prove
  full exact `U(2)` Euler existence. It also proves the paper's omitted `-1`
  absorption step through `paperPhase_pi_mul_paperRz`.
- `Barenco/OneQubit/Lemma43.lean` derives existential raw and chronological-column
  A/B/C witnesses for every special unitary. An independent audit checked the
  reversed factor order and confirmed that no circuit/resource conclusion is
  claimed at this layer.
- `Barenco/OneQubit/Roots.lean` defines `unitaryRoot k U` for any finite index type
  using finite-spectrum continuous functional calculus. For `0 < k`,
  `unitaryRoot_pow` proves `(unitaryRoot k U)^k = U`; square and iterated
  power-of-two corollaries are exported. The construction is exact and certified,
  including zero-width matrices, but it does not supply a continuous choice or a
  coherent root sequence with Section 7 approximation bounds.
- `Barenco/OneQubit/CircuitBridge.lean` proves the semantic Pauli-X names and local
  embeddings coincide with the earlier circuit core. `Barenco/OneQubitExamples.lean`
  is diagnostic only and checks `pi` signs, Pauli-X, zero-angle A/B/C order,
  square/iterated roots, zero-width root behavior, and the outer-angle reversal.
- Declaration classification: matrices/certified gates/factor and root constructors
  are runtime/public; algebra, Euler, determinant, decomposition, and power laws
  are proof-side/public; `OneQubitExamples` is diagnostic and is excluded from the
  public root. No fallback or temporary declaration is exported.
- Every Stage 4 source file, the public root, and `Barenco/AxiomAudit.lean` passed
  `lake env lean -DwarningAsError=true`. The combined focused/adjacent build passed
  with 2935 jobs. After the public-root change, two consecutive full
  `lake build` runs passed with 2933 jobs each.
- The maintained audit now checks 46 headline declarations. All Stage 4 additions,
  including Euler existence, determinant normalization, Lemma 4.3, roots, and the
  Pauli bridge, depend only on Lean/mathlib's `propext`, `Classical.choice`, and
  `Quot.sound`; no project-specific axiom appears.
- Repository scans found no `sorry`, `admit`, `by?`, `native_decide`, `bv_decide`,
  project `axiom`, or project `opaque` declaration in Lean sources. Lean trailing
  whitespace and `git diff --check` were clean.
- The next stage must promote the A/B/C algebra into explicit two-wire circuits,
  prove evaluator equality by control-basis cases, and derive Section 5 costs from
  syntax. Exact unitary-root existence is available for later stages; coherent
  approximation/norm claims remain a Stage 9 obligation.
