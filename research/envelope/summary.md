# Phase 2: tightness of Terras's mini-max envelope

Generated finite engineering/mathematical comparison for the accelerated map `T(n)=n/2` (even), `(3n+1)/2` (odd). No originality claim, no all-`r` theorem, and no proof of CST or Collatz is asserted. P1a is **refuted**; P1b remains open.

Reproduce this table and `evidence.json` from the repository root with:

```text
cargo run --locked --release -- envelope --out-dir research/envelope
```

## Definitions and scope

Exactly `1 <= r <= 12`, with `k = bit_length(3^r) <= 20`. Each family contains every parity word whose first coefficient crossing is at length `k` and has `r` odd steps. Write `T^k(n)=(3^r*n+c)/2^k`, `d=2^k-3^r`, and let `m` be the least class member **at least 2**. The word `10` has residue 1 but `m=5`.

`C_r=max c`, `m_r=min m`, `R_r=max c/(d*m)`, `U_r=C_r/(d*m_r)`, and `E_r=U_r/R_r`. If `R_r=0`, `E_r` and its comparison with 2 are **N/A** (JSON `null`); no value is imputed. All fractions are reduced using gcd; all rankings and comparisons use BigUint cross products.

## Exhaustive results

Each extremum cell lists **all** tied words as `word (m, c)` in lexicographic order, followed by the number of ties. A single listed word means a unique extremizer. Counts, margins, normalized residues and the independent Terras offsets are also recorded in `evidence.json`; arbitrary-size integers are decimal strings.

| r | k | count | C_r words (m, c); ties | m_r words (m, c); ties | R_r words (m, c); ties | R_r | U_r | E_r | E_r <= 2 |
|---|---|---|---|---|---|---|---|---|---|
| 1 | 2 | 1 | `10` (5, 1); 1 tie(s) | `10` (5, 1); 1 tie(s) | `10` (5, 1); 1 tie(s) | 1/5 | 1/5 | 1/1 | yes |
| 2 | 4 | 1 | `1100` (3, 5); 1 tie(s) | `1100` (3, 5); 1 tie(s) | `1100` (3, 5); 1 tie(s) | 5/21 | 5/21 | 1/1 | yes |
| 3 | 5 | 2 | `11010` (11, 23); 1 tie(s) | `11010` (11, 23); 1 tie(s) | `11010` (11, 23); 1 tie(s) | 23/55 | 23/55 | 1/1 | yes |
| 4 | 7 | 3 | `1101100` (59, 85); 1 tie(s) | `1110100` (7, 73); 1 tie(s) | `1110100` (7, 73); 1 tie(s) | 73/329 | 85/329 | 85/73 | yes |
| 5 | 8 | 7 | `11011010` (123, 319); 1 tie(s) | `11101100` (39, 251); 1 tie(s) | `11101100` (39, 251); 1 tie(s) | 251/507 | 319/507 | 319/251 | yes |
| 6 | 10 | 12 | `1101101100` (507, 1085); 1 tie(s) | `1111101000` (287, 697); 1 tie(s) | `1101110100` (347, 989); 1 tie(s) | 989/102365 | 31/2419 | 53785/40549 | yes |
| 7 | 12 | 30 | `110110110100` (1019, 3767); 1 tie(s) | `111011101000` (231, 2707); 1 tie(s) | `111011101000` (231, 2707); 1 tie(s) | 2707/440979 | 3767/440979 | 3767/2707 | yes |
| 8 | 13 | 85 | `1101101101010` (3067, 13349); 1 tie(s) | `1111110100010` (191, 8417); 1 tie(s) | `1111001110100` (207, 9937); 1 tie(s) | 9937/337617 | 1907/44503 | 2763243/1897967 | yes |
| 9 | 15 | 173 | `110110110101100` (7163, 44143); 1 tie(s) | `111111101000100` (127, 23395); 1 tie(s) | `111111101000100` (127, 23395); 1 tie(s) | 4679/332359 | 44143/1661795 | 44143/23395 | yes |
| 10 | 16 | 476 | `1101101101011010` (56315, 148813); 1 tie(s) | `1110111110001010` (359, 100609); 1 tie(s) | `1110111110001010` (359, 100609); 1 tie(s) | 100609/2328833 | 148813/2328833 | 148813/100609 | yes |
| 11 | 18 | 961 | `110110110101101100` (23547, 479207); 1 tie(s) | `111111111010100000` (511, 179707); 1 tie(s) | `111111111010100000` (511, 179707); 1 tie(s) | 16337/3948497 | 479207/43433467 | 479207/179707 | no |
| 12 | 20 | 2652 | `11011011010110110100` (416763, 1568693); 1 tie(s) | `11110111110001010100` (239, 911873); 1 tie(s) | `11110111110001010100` (239, 911873); 1 tie(s) | 911873/123595265 | 1568693/123595265 | 1568693/911873 | yes |

## Finite prediction E_r <= 2

**refuted on the tested domain**: the first counterexample is `r=11`, `k=18`, with `E_r=479207/179707 > 2`. This refutes only the finite prediction. All twelve families were still evaluated.

Neither outcome proves P1b or any infinite-family statement.

## Checks and stopping behavior

Each family count agrees with both independent recurrences in `src/counting.rs`. The enumerated maximum offset agrees with Terras's independent extremal-word recurrence: start with power 1 and offset 0; at positions `i=0..k-2` choose odd iff `3^(odd count so far) < 2^(i+1)`, update `c <- 3*c+2^i` on odd steps, and append a final zero. This is the construction of Theorems 2.4 and 2.6 described in [the primary-source audit](../literature-cst.md).

Every enumerated word, including every reported extremizer, has its modular-inverse residue checked against the independent lifting construction. The independent certificate verifier rederives its closed-form affine offset and checks two members by direct iteration. Its least member `m >= 2` is additionally checked by direct iteration for its parities and affine identity. The independent test in `tests/envelope.rs` scans a full residue period by direct iteration and rechecks all extrema, ties and exact fractions.

P1a is never used to rank classes. At `r=6`, `1111101000` has `(m,c)=(287,697)`, while `1101110100` has `(347,989)` and `989/(295*347) > 697/(295*287)` (cross-product difference 12385280).

The command has fixed bounds and terminates at `r=12`, or immediately on the first invariant failure. An `E_r>2` is a result, not an invariant failure. No artifact is replaced until all mathematical checks pass. It retains one family at a time (at most 2652 classes); the full run checks 4403 classes. Runtime in milliseconds is printed to stderr and omitted from these deterministic artifacts. See the repository README for measured performance.
