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
| D2-control | pp. 6–7; lines 88–138 | Definition and lower-right-block matrix for `∧ₘ(U)` | `Barenco.controlled`, basis-action and lexicographic bridge (planned) | A,C,W | planned; transpose bridge required by source row action |
| D2-Toffoli | p. 6; lines 127–138 | `∧ₘ(σx)` Boolean action | `Barenco.multiControlledX` (planned) | A,C,W | planned |
| C2-dense | pp. 6–7; lines 146–150 | cited claim that “almost any” fixed controlled-U densely generates | no local theorem from this paper | A,C,O | intentionally excluded from paper reconstruction: source cites [29,31] and gives no proof; exact universality with all U(2) primitives is handled separately |
| N3-diagrams | pp. 7–8; lines 158–168 | wire/control/target notation; time left-to-right | circuit chronology and convention tests (planned) | C | planned |
| N3-basic | p. 8; line 166 | “basic” = arbitrary one-qubit or CNOT | `CostModel.oneQubitCNOT` (planned) | R | planned |

## Section 4 — Matrix Properties

| ID | Source | Paper content | Lean counterpart | Layers | Status / notes |
|---|---|---|---|---|---|
| L4.1 | p. 8; line 172 | Euler/global-phase decomposition of U(2), SU(2) case | `u2_euler`, `su2_euler` (planned) | A | planned; existential angle boundary cases require independent proof |
| L4.2 | p. 9; line 269 | `Ry`, `Rz`, phase, and Pauli-X identities | rotation identity family (planned) | A | planned |
| L4.3 | pp. 9–10; line 278 | `A B C = I` and `A X B X C = W` for `W∈SU(2)` | `su2_abc_decomposition` (planned) | A | planned; translated column order documented |

## Section 5 — Two-Bit Networks

| ID | Source | Paper content | Lean counterpart | Layers | Status / notes |
|---|---|---|---|---|---|
| L5.1 | pp. 10–11; line 347; image `lemma-5-1-controlled-su2.png` | two-CNOT/three-one-qubit circuit iff target is SU(2) | `controlledSU2Circuit_correct_iff` (planned) | A,C,W,R | planned; both directions required |
| L5.2 | p. 11; line 361; image `lemma-5-2-controlled-phase.png` | controlled scalar phase equals a phase gate on control | `controlledScalar_eq_phaseControl` (planned) | A,C,W,R | planned |
| C5.3 | p. 11; line 391 | controlled U(2) uses ≤4 one-qubit + 2 CNOT | `controlledU2_cost` (planned) | C,R | planned; constructed upper bound |
| L5.4 | pp. 12–13; line 408; image `lemma-5-4-two-xor-special-case.png` | characterization of two-CNOT/two-inverse-gate family | `twoCNOTFamily_iff` (planned) | A,C,R | planned |
| L5.5 | p. 13; line 471; image `lemma-5-5-one-xor-special-case.png` | characterization of one-CNOT family | `oneCNOTFamily_iff` (planned) | A,C,R | planned |
| C5.6 | p. 14; line 512 | controlled U from four one-qubit + two controlled special-family gates | `controlledU_viaSpecialFamily` (planned) | C,R | planned; source terminology calls nonprimitive controlled gates “basic,” to be corrected |
| N5-Z | p. 14; image `controlled-z-symmetry.png` | controlled-Z symmetric under wire swap | `controlledZ_swap` (planned) | A,C | planned |

## Section 6 — Three-Bit Networks

| ID | Source | Paper content | Lean counterpart | Layers | Status / notes |
|---|---|---|---|---|---|
| L6.1 | pp. 14–15; line 526; image `lemma-6-1-controlled-controlled-u.png` | exact doubly controlled U from V, V†, CNOT with `V²=U` | `ccuCircuit_correct` (planned) | A,C,W,R | planned; root existence separated from conditional identity |
| C6.2 | p. 15; line 548 | ≤8 one-qubit + 8 CNOT | `ccuCircuit_oneQubitCNOTCost` (planned) | C,R | planned upper bound |
| U6.2-W | pp. 15–16; lines 552–566 | `∧₂(W)` has Toffoli basis behavior with a relative sign | exact diagonal-phase witness (planned) | A,C | planned; not global phase |
| U6.2-A | p. 16; lines 567–575; image `relative-phase-toffoli-a.png` | A-rotation relative-phase Toffoli circuit | `relativeToffoliA_correct` (planned) | A,C,W,R | planned; phase of `|101⟩` to be checked |
| U6.2-B | p. 16; lines 577–583; image `relative-phase-toffoli-b.png` | alternate B-rotation circuit with same phases | `relativeToffoliB_correct` (planned) | A,C,W,R | planned |

## Section 7 — n-Bit Networks

| ID | Source | Paper content | Lean counterpart | Layers | Status / notes |
|---|---|---|---|---|---|
| U7-Gray4 | p. 17; lines 585–614; image `four-bit-gray-code-construction.png` | four-bit Gray/parity controlled-U construction | four-bit basis/evaluator theorem (planned) | A,C,W,R | planned |
| L7.1 | pp. 17–18; line 616 | general omitted Gray-code construction; exact gate counts | `grayControlledCircuit_correct` and counts (planned) | A,C,W,R,O | planned; source omits proof, custom Gray library needed |
| L7.2 | pp. 18–19; line 668; image `lemma-7-2-linear-multi-control.png` | dirty-wire multi-X from `4(m−2)` Toffolis | `borrowedMultiXCircuit_correct` (planned) | C,W,R | planned; full equality must cover entangled borrowed wires |
| L7.3 | pp. 19–20; line 682; image `lemma-7-3-four-block-construction.png` | four-block dirty-wire construction | `fourBlockMultiX_correct` (planned) | C,W,R | planned; source proof only “by inspection” |
| C7.4 | p. 20; line 688 | `8(n−5)` Toffolis and `48n−204` early-basic upper bound | repaired partition/cost theorem (planned) | C,W,R,O | planned correction; see C-003/C-004/C-005 |
| L7.5 | p. 21; line 718; image `lemma-7-5-quadratic-general-control.png` | recursive fully controlled U using square root | `recursiveControlledCircuit_correct` (planned) | C,W,R | planned |
| C7.6 | pp. 21–22; line 724 | claimed `Θ(n²)` and `48n²+O(n)` | construction recurrence upper bound (planned) | R,O | planned correction; no optimal quadratic lower bound in paper |
| L7.7 | p. 22; line 750 | nonscalar fully controlled U needs ≥`n−1` CNOTs | `fullyControlled_cnotLowerBound` (planned) | C,R,O | planned; formal dependency/connectivity invariant required |
| D7-approx | pp. 22–23; line 770 | induced Euclidean operator distance | L² operator-distance definition (planned) | A | planned |
| P7-approx | pp. 22–23; line 772 | event probabilities differ by ≤`2ε` | `eventProbability_sub_le` (planned) | A | planned; hypotheses/constant to verify |
| L7.8 | pp. 23–24; line 774 | recursive-root approximate controlled U in claimed `Θ(n log(1/ε))` | capped-depth corrected upper bound (planned) | A,C,R,O | planned correction; see C-007–C-010 |
| L7.9 | p. 24; line 854; image `lemma-7-9-linear-su2-control.png` | multi-control SU(2) ABC circuit | `controlledSU2Linear_correct` (planned) | A,C,W,R | planned |
| C7.10 | p. 24; line 862 | claimed linear `∧_{n−2}(W)` construction | explicit linear upper bound (planned) | C,W,R,O | planned correction: width/borrowed-wire threshold explicit |
| L7.11 | p. 25; line 879; image `lemma-7-11-one-fixed-bit.png` | general controlled U with one zero fixed/restored wire | `controlledWithCleanAncilla_correct` (planned) | C,W,R | planned; subspace theorem, source proof only “by inspection” |
| C7.12 | p. 25; line 887 | claimed linear construction with fixed wire | explicit clean-ancilla linear upper bound (planned) | C,W,R,O | planned correction: threshold and upper-bound status explicit |

## Section 8 — General Synthesis and Changed Cost Model

| ID | Source | Paper content | Lean counterpart | Layers | Status / notes |
|---|---|---|---|---|---|
| N8-basic | p. 26; lines 891–895 | “basic” changes to arbitrary two-qubit gate | `CostModel.arbitraryTwoQubit` (planned) | R | planned |
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
