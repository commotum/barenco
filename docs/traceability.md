# Paper-to-Lean Traceability

Primary source: `Barenco/barenco-1995.pdf` (arXiv `quant-ph/9503016v1`). Markdown
line numbers refer to `Barenco/barenco-1995.md` and are navigation aids only.

## Status Vocabulary

- **planned** — in the accepted project scope but not yet formalized.
- **proved as stated** — source claim and assumptions are represented faithfully.
- **corrected and proved** — a documented repaired statement is proved.
- **additional assumptions** — proved with assumptions absent or implicit in source.
- **partial** — some verification layers are complete; the row names which ones.
- **excluded** — intentionally not theoremized, with a documented reason.
- **unresolved** — exact obstruction is known or investigation remains open.

Verification layers use `A` algebraic identity, `C` full circuit correctness, `W`
wire/ancilla preservation, `R` exact structural resources, and `O` asymptotics.

## Foundations and Notation

| ID | Source | Paper content | Lean counterpart | Layers | Status / notes |
|---|---|---|---|---|---|
| D2-control | pp. 6–7; lines 88–138 | Definition and lower-right-block matrix for `∧ₘ(U)` | `positiveControlledRaw`, `positiveControlledUnitary`, `positiveControlledRaw_truthTable`; paper-order wrapper/lexicographic block theorem planned | A,C,W | partial: arbitrary positive control sets/targets, exact basis action, untouched wires, and unitarity proved; source-row and `Fin (2^n)` matrix presentation remains |
| D2-Toffoli | p. 6; lines 127–138 | `∧ₘ(σx)` Boolean action | `pauliX`, `xRaw_mulVec_basisKet`, positive-control specialization; `cnotRaw_mulVec_basisKet` for `m=1` | A,C,W | partial: reusable general semantics proved; named all-controls paper wrapper and lexicographic theorem remain |
| C2-dense | pp. 6–7; lines 146–150 | cited claim that “almost any” fixed controlled-U densely generates | no local theorem from this paper | A,C,O | intentionally excluded from paper reconstruction: source cites [29,31] and gives no proof; exact universality with all U(2) primitives is handled separately |
| N3-diagrams | pp. 7–8; lines 158–168; image `notation-basic-gates.png` | wire/control/target notation; time left-to-right | `evalGates_pair`, `fromPaper_paperProduct`, `Circuit.eval_append`, `Primitive.oneQubit`, `Primitive.cnot` | C | corrected and proved for chronology, typed one-qubit/CNOT wires, and source/semantic translation; later diagram-specific circuits remain in their rows |
| N3-basic | p. 8; line 166 | “basic” = arbitrary one-qubit or CNOT | private-constructor `Primitive`; trusted `.oneQubit`/`.cnot`; `Circuit.registerWidth`, `gateCount`, `kindCount`, `touchedSupport`, `cost`; `CostModel.oneQubitCNOT` | R | corrected and proved at the syntax/cost-model layer: support is bounded by ambient width and unsupported kinds make cost `none`; no paper decomposition count follows until its circuit exists |
| F3-phase | §6.2, pp. 15–16; lines 552–584 | informal “congruent modulo phase shifts” language | `GlobalPhaseEq`, input-column `BasisPhaseEq`, `SameBasisBehavior`, `BasisMeasurementEq` and implication/equivalence laws | A | partial foundation: distinct relations and valid implications are proved; neither relative-Toffoli diagram nor any cancellation witness is yet formalized |
| F3-measure | §6.2 and pp. 22–23; lines 552–584, 770–774 | phase-sensitive quantum use and measurement-probability discussion | `conjugationChannel`, `ChannelEq`, arbitrary-matrix/effect `BornWeight` and `AllMeasurementEq`; `channelEq_iff_allMeasurementEq`; `ChannelEq.toBasisMeasurementEq`; `operatorDistance_basisOutcomeProbability_le` | A | corrected clarification proved algebraically: global phase cancels and all-matrix/effect equality separates channels; the `2ε` bound is proved for one computational-basis outcome of a norm-at-most-one pure state; physical density/effect restrictions and arbitrary-event bounds remain open |

## Section 4 — Matrix Properties

| ID | Source | Paper content | Lean counterpart | Layers | Status / notes |
|---|---|---|---|---|---|
| L4.1-SU | pp. 8–9; lines 172–267 | exact `Rz Ry Rz` form for every SU(2) matrix | `QubitSpecialUnitary`; `specialUnitary_canonical`; `paperEuler_entry_formula`; `specialUnitary_exists_paperEuler`; `specialUnitary_exists_columnEuler`; `specialUnitary_exists_rz_mul_ry_mul_rz` | A | corrected and proved: total `Complex.arg` choices cover zero entries, the middle angle lies in `[0,π]`, and paper-row versus semantic-column outer-factor order is explicit |
| L4.1-U2 | pp. 8–9; lines 172–267 | scalar phase times an SU(2) Euler form for every U(2) matrix | `determinantPhaseAngle`, `specialUnitaryPart`, `phaseShift_mul_specialUnitaryPart`, `unitary_exists_paperPhase_mul_paperEuler`, `unitary_exists_phaseShift_mul_rz_mul_ry_mul_rz`; `paperPhase_pi_mul_paperRz` | A | corrected and proved: the principal half-argument branch is explicit, reconstruction is exact, and the possible scalar `-I` is absorbed by a `2π` Z-angle shift rather than silently setting the phase to zero |
| L4.2 | p. 9; line 269 | six `Ry`, `Rz`, scalar-phase, and Pauli-X identities | raw `paperRy_mul`, `paperRz_mul`, `paperPhase_mul`, `paperX_sq`, and two `paperX` conjugation theorems; semantic `ry_mul`, `rz_mul`, `phaseShift_mul`, `sigmaX_sq`, and two `sigmaX` conjugation theorems; certified gate packages | A | proved as stated for all real parameters in both conventions; exact matrix identities only, with no circuit syntax or resource conclusion |
| L4.3 | pp. 9–10; lines 278–341 | `A B C = I` and `A X B X C = W` for `W∈SU(2)` | `paperA`, `paperB`, `paperC` and SU certificates; parameterized raw/column identities; `specialUnitary_exists_paperABC`; `specialUnitary_exists_columnChronologicalABC` | A | proved as stated at the algebraic layer: raw order is `A B C`, while chronological standard-column semantics is the reversed `Cᵀ Bᵀ Aᵀ`; no `Circuit` or count theorem follows |
| I4-root | root choices used at pp. 14–24; lines 530–544, 718–722, 782–827 | existence of square, iterated, and approximation roots | finite-index `unitaryRoot`, `unitaryRoot_pow`, `exists_unitary_pow_eq`, `unitarySquareRoot_pow_two`, `unitaryRoot_pow_two_pow` | A | corrected and proved in a stronger finite-index exact form for every `k>0`; individual roots are certified, but a coherent successive-root sequence, its L² operator-norm decay, and every dependent circuit/resource theorem remain open |

## Section 5 — Two-Bit Networks

| ID | Source | Paper content | Lean counterpart | Layers | Status / notes |
|---|---|---|---|---|---|
| L5.1 | pp. 10–11; line 347; image `lemma-5-1-controlled-su2.png` | two-CNOT/three-one-qubit circuit iff target is SU(2) | `controlledABCCircuit`; `eval_controlledABCCircuit_eq_iff`; `controlledSU2Circuit_correct_iff`; `controlledABCCircuit_oneQubitCNOTCost` | A,C,W,R | proved in both directions as exact arbitrary-register circuit equality; the converse derives `det W=1` from the active branch and both `det X=-1` factors; syntax cost is exactly three one-qubit plus two CNOT gates |
| L5.2 | p. 11; line 361; image `lemma-5-2-controlled-phase.png` | controlled scalar phase equals a phase gate on control | `controlPhase`; `controlPhase_eq_matrix2`; `controlledScalarUnitary_eq_localControl`; `controlledPhaseCircuit`; `eval_controlledPhaseCircuit` | A,C,W,R | proved exactly for arbitrary ambient width: controlled `Ph(delta)` is the local control gate `diag(1,cis delta)`, not an ignorable global phase; circuit cost is one one-qubit gate |
| C5.3 | p. 11; line 391 | controlled U(2) uses ≤4 one-qubit + 2 CNOT | `controlledU2Circuit`; `eval_controlledU2Circuit_of_products`; `controlledU2Circuit_exists`; `controlledU2Circuit_kindCounts`; `controlledU2Circuit_oneQubitCNOTCost` | C,R | proved as a constructed exact upper bound: six syntax occurrences, exactly four one-qubit and two CNOT, with cost `some 6` under `oneQubitCNOT` |
| L5.4 | pp. 12–13; line 408; image `lemma-5-4-two-xor-special-case.png` | characterization of two-CNOT/two-inverse-gate family | `twoCNOTCircuit`; `eval_twoCNOTCircuit_eq_iff`; `symmetricEuler`; Pauli-conjugate classification; `twoCNOTFamily_iff`; `twoCNOTCircuit_oneQubitCNOTCost` | A,C,R | corrected and proved in both directions, including zero phase-carrying coordinates; column family is `rz alpha * ry theta * rz alpha`; exact syntax cost is two one-qubit plus two CNOT gates |
| L5.5 | p. 13; line 471; image `lemma-5-5-one-xor-special-case.png` | characterization of one-CNOT family | `oneCNOTCircuit`; `eval_oneCNOTCircuit_eq_iff`; `oneCNOTSpecialFamily_iff`; `unitaryPauliConjugate_eq_specialUnitaryPart`; `oneCNOTFamily_iff`; `oneCNOTCircuit_oneQubitCNOTCost` | A,C,R | corrected and proved in both directions; the omitted converse derives `B=A⁻¹`, and arbitrary U(2) witnesses are phase-normalized exactly; column family is `X * symmetricEuler`; cost is two one-qubit plus one CNOT |
| C5.6 | p. 14; line 512 | controlled U from four one-qubit + two controlled special-family gates | `controlledVMacroU2Circuit`; `controlledVMacroU2Circuit_exists`; macro gate/kind counts and `oneQubitCNOTCost`; `expandedVMacroU2Circuit`; expansion/merge evaluator theorems; expanded/merged cost theorem | C,R | corrected and proved: six nodes only in the enlarged one-qubit+selected-controlled-V library, and the Section-3 cost is deliberately `none` before expansion; explicit expansion has eight one-qubit plus two CNOT occurrences (cost 10), while three proved local merge groups recover the four-plus-two circuit (cost 6) |
| N5-Z | p. 14; image `controlled-z-symmetry.png` | controlled-Z symmetric under wire swap | `sigmaZUnitary`; `controlledZRaw_truthTable`; `controlledZRaw_swap`; `controlledZUnitary_swap` | A,C | proved as exact arbitrary-register equality; the relative sign occurs exactly when both named wires are true |

## Section 6 — Three-Bit Networks

| ID | Source | Paper content | Lean counterpart | Layers | Status / notes |
|---|---|---|---|---|---|
| L6.1 | pp. 14–15; line 526; image `lemma-6-1-controlled-controlled-u.png` | exact doubly controlled U from V, V†, CNOT with `V²=U` | exact witness `unitarySquareRoot` / `unitarySquareRoot_pow_two`; `ccuCircuit_correct` planned | A,C,W,R | partial: a certified exact `V` now exists for every finite unitary; the displayed circuit, full-register correctness, wire preservation, and count remain planned |
| C6.2 | p. 15; line 548 | ≤8 one-qubit + 8 CNOT | `ccuCircuit_oneQubitCNOTCost` (planned) | C,R | planned upper bound |
| U6.2-W | pp. 15–16; lines 552–566 | `∧₂(W)` has Toffoli basis behavior with a relative sign | exact diagonal-phase witness (planned) | A,C | planned; not global phase |
| U6.2-A | p. 16; lines 567–575; image `relative-phase-toffoli-a.png` | A-rotation relative-phase Toffoli circuit | `relativeToffoliA_correct` (planned) | A,C,W,R | planned; phase on computational-basis input 101 to be checked |
| U6.2-B | p. 16; lines 577–583; image `relative-phase-toffoli-b.png` | alternate B-rotation circuit with same phases | `relativeToffoliB_correct` (planned) | A,C,W,R | planned |

## Section 7 — n-Bit Networks

| ID | Source | Paper content | Lean counterpart | Layers | Status / notes |
|---|---|---|---|---|---|
| U7-Gray4 | p. 17; lines 585–614; image `four-bit-gray-code-construction.png` | four-bit Gray/parity controlled-U construction | four-bit basis/evaluator theorem (planned) | A,C,W,R | planned |
| L7.1 | pp. 17–18; line 616 | general omitted Gray-code construction; exact gate counts | `grayControlledCircuit_correct` and counts (planned) | A,C,W,R,O | planned; source omits proof, custom Gray library needed |
| L7.2 | pp. 18–19; line 668; image `lemma-7-2-linear-multi-control.png` | dirty-wire multi-X from `4(m−2)` Toffolis | `borrowedMultiXCircuit_correct` (planned) | C,W,R | planned; full equality must cover entangled borrowed wires |
| L7.3 | pp. 19–20; line 682; image `lemma-7-3-four-block-construction.png` | four-block dirty-wire construction | `fourBlockMultiX_correct` (planned) | C,W,R | planned; source proof only “by inspection” |
| C7.4 | p. 20; line 688 | `8(n−5)` Toffolis and `48n−204` early-basic upper bound | repaired partition/cost theorem (planned) | C,W,R,O | planned correction; see C-003/C-004/C-005 |
| L7.5 | p. 21; line 718; image `lemma-7-5-quadratic-general-control.png` | recursive fully controlled U using square root | exact `unitarySquareRoot`; `recursiveControlledCircuit_correct` planned | A,C,W,R | partial: square-root existence is proved; recursive circuit semantics, wire obligations, and structural cost are not |
| C7.6 | pp. 21–22; line 724 | claimed `Θ(n²)` and `48n²+O(n)` | construction recurrence upper bound (planned) | R,O | planned correction; no optimal quadratic lower bound in paper |
| L7.7 | p. 22; line 750 | nonscalar fully controlled U needs ≥`n−1` CNOTs | `fullyControlled_cnotLowerBound` (planned) | C,R,O | planned; formal dependency/connectivity invariant required |
| D7-approx | pp. 22–23; line 770 | distance induced by the Euclidean vector norm | `operatorDistance` using scoped `Matrix.Norms.L2Operator`; metric laws, multiplication bounds, unitary invariance, product-error/state-action bounds; `operatorDistance_basisOutcomeProbability_le` | A | corrected and proved for the exact L² induced operator norm, including the paper's factor-two bound for a single basis outcome; no approximation circuit or arbitrary-event theorem is implied |
| P7-approx | pp. 22–23; line 772 | event probabilities differ by ≤`2ε` | `eventProbability_sub_le` (planned) | A | planned; hypotheses/constant to verify |
| L7.8 | pp. 23–24; line 774 | recursive-root approximate controlled U in claimed `Θ(n log(1/ε))` | individual exact roots `unitaryRoot_pow_two_pow` plus the established `operatorDistance` API; coherent-root/norm/circuit theorem planned | A,C,R,O | partial correction: exact positive roots and the norm framework are proved, but `V_{k+1}²=V_k`, `operatorDistance V_k I≤π/2^k`, bounded recursion depth, circuit correctness, and any asymptotic upper bound remain; see C-007–C-010 |
| L7.9 | p. 24; line 854; image `lemma-7-9-linear-su2-control.png` | multi-control SU(2) ABC circuit | `controlledSU2Linear_correct` (planned) | A,C,W,R | planned |
| C7.10 | p. 24; line 862 | claimed linear `∧_{n−2}(W)` construction | explicit linear upper bound (planned) | C,W,R,O | planned correction: width/borrowed-wire threshold explicit |
| L7.11 | p. 25; line 879; image `lemma-7-11-one-fixed-bit.png` | general controlled U with one zero fixed/restored wire | `controlledWithCleanAncilla_correct` (planned) | C,W,R | planned; subspace theorem, source proof only “by inspection” |
| C7.12 | p. 25; line 887 | claimed linear construction with fixed wire | explicit clean-ancilla linear upper bound (planned) | C,W,R,O | planned correction: threshold and upper-bound status explicit |

## Section 8 — General Synthesis and Changed Cost Model

| ID | Source | Paper content | Lean counterpart | Layers | Status / notes |
|---|---|---|---|---|---|
| N8-basic | p. 26; lines 891–895 | “basic” changes to arbitrary two-qubit gate | `CostModel.arbitraryTwoQubit`; partial `Circuit.cost` and explicit rejection theorems | R | corrected and proved as a distinct syntax-only cost model; arbitrary-two-qubit smart constructor and Section 8 circuit/count theorems remain planned |
| U8-Toffoli5 | p. 26; lines 895–900 | exact Toffoli in five arbitrary two-qubit gates | circuit/cost corollary (planned) | C,R | planned constructed upper bound; not minimality |
| U8-relToffoli3 | p. 26; lines 895–900 | relative-phase Toffoli in three after merging | optimized syntax theorem (planned) | C,R | planned; phase target explicit |
| U8-Toffoli4-13 | p. 26; lines 895–900 | four-bit Toffoli in thirteen arbitrary two-qubit gates | circuit/cost corollary (planned) | C,R | planned constructed upper bound |
| M8-minimal | p. 26; lines 899–902 | numerical evidence that preceding counts are minimal | none unless a new exhaustive proof is supplied | R | excluded as paper theorem; source explicitly has no proof |
| U8-six | pp. 26–27; lines 903–933; image `six-two-bit-gates-u8.png` | six arbitrary U(4) gates allegedly realize every U(8) | candidate architecture only (planned investigation) | A,C,R | unresolved; dimension 64 does not prove surjectivity |
| H8-dim | pp. 26–27; lines 909–936 | parameter increments 16,12,9,… | documented parameter heuristic | R,O | excluded pending manifold/image-dimension proof |
| H8-lower | p. 27; lines 931–937 | conjectural `(4^n−3n−1)/9` two-qubit lower bound | none as unconditional theorem | R,O | excluded; paper calls it a conjecture based on dimension counting |
| U8-twolevel | p. 27; lines 939–957 | unitary decomposition into two-level rotations and diagonal phases | constructive finite-unitary elimination (planned) | A | planned; product/elimination order must be supplied |
| U8-gray | pp. 27–28; lines 959–976 | Gray path and negative controls implement a two-level rotation | `twoLevelViaGray_correct` (planned) | C,W,R | planned |
| U8-pathcount | p. 28; lines 973–979 | each path uses `2m−3`, `m≤n+1` multi-control gates | structural count theorem (planned) | R | planned |
| U8-general | pp. 27–28; lines 939–983 | exact arbitrary n-qubit unitary, no work bits, claimed `Θ(n³4^n)` | exact universality + uniform construction upper bound (planned) | A,C,W,R,O | planned correction; source outline lacks lower bound/product details |

## Headline Result Assembly

| ID | Source | Paper content | Lean counterpart | Layers | Status / notes |
|---|---|---|---|---|---|
| T-universal | abstract, pp. 1/6/27–28 | all one-qubit U(2) gates + CNOT exactly generate all finite-qubit unitaries | `exists_circuit_of_unitary` (planned) | A,C,W | planned; no named theorem/proof in source, assembled from corrected stages |
| T-universal-cost | abstract and §8 | resource upper bound for the explicit general construction | named cost theorem (planned) | R,O | planned; cost models and upper-bound status explicit |
