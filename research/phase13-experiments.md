# Phase 13: certified finite profiles and benchmarks

All data are finite evidence, not asymptotic proofs. The nonconvergence proof
is in [the theory report](phase13-theory.md), independent of these observations.
The exact JSON, including every numerator, denominator and minimality
certificate, is `phase13/heights.json.gz` (standard gzip; 3.0 MB compressed).
It contains 1,688 certified records in ten families through N=16,384.

## Reproduction and independent checks

```bash
python3 research/phase13/test_height.py
python3 research/phase13/experiments.py --check
python3 research/phase13/verify_certificates.py research/phase13/heights.json.gz
python3 research/phase13/verify_analytics.py --check
```

The two reconstruction engines share no minimization implementation. The
independent verifier imports neither and checks the no-smaller-height count,
reverse rational inverse branches and actual numerator iteration. The full
small test covers all 4,095 residues through 11 bits, 31,750 signed cylinder
controls, 25,432 signed floor sums and seven rejected corrupt certificates.
It separately rules out 262,400 numerator/denominator pairs below H_12 by
actual iteration. Arbitrary-precision comparisons extend to 2,048 bits.

The reference algorithm took 0.995s at 1,024 bits and 11.488s at 2,048 bits
for `7^N mod 2^N`, agreeing with the optimized engine. A 4,096-bit reference
run was **cancelled at the explicit 55-second limit**, with exit 124 and no
result; it is not reported passing. The optimized engine and independent
minimality certificates are the practical large-N route. No fixed denominator
cutoff or reconstruction uniqueness assumption replaces complete coverage.

## Primary word: dramatic finite jumps

| N | Exact H_N or its bit length | log2(H_N)/N | Interpretation |
|---|---|---|---|
| 11 | 3, witness -3/1 | 0.144088 | Early rational shadow |
| 12 | 513, witness 509/513 | 0.750235 | First shadow failure |
| 67 | 29 bits | 0.420094 | Substituted shadow level 1 |
| 68 | 39 bits | 0.566250 | Next exact failure |
| 403 | 164 bits | 0.405635 | Shadow level 2 |
| 404 | 240 bits | 0.592017 | Next exact failure |
| 2,419 | 982 bits | 0.405685 | Shadow level 3 |
| 2,420 | 1,438 bits | 0.593923 | Next exact failure |
| 14,515 | 5,870 bits | 0.404366 | Shadow level 4 |
| 14,516 | 8,646 bits | 0.595568 | Next exact failure |
| 16,384 | 8,646 bits | 0.527665 | Same height plateau at the cap |

“b bits” means the exact integer H has binary length b; it is not a rounded
substitute for the integer in the certificate file. Every displayed large-N
row includes its exact minimizing p/q, basis, congruence and no-smaller-height
transcripts there. `analytics.json` independently constructs the shadow
fractions and their first failures at levels 0..4. In all five cases the
shadow is a minimum, and `2*H^2<2^L` gives an additional uniqueness control.
At levels 1..4 the raw shadow pairs happen to be coprime; this observation is
not an infinite coprimality theorem.

## Other words and controls

All morphisms use the fixed point beginning with 1. Thue–Morse is exactly
`1->10,0->01`, the complement of the usual zero-start convention, agreeing
with the repository's Phase 8 bit convention. The equal-weight comparison is
`1->110,0->011`. The two Phase 11 words are `110/111` and `1011/1111`.

The table gives extrema over the **dense** finite interval 128<=N<=16,384;
these are not estimates with error bounds for infinite liminf/limsup.

| Family | Smallest ratio (N) | Largest ratio (N) | H at N=16,384, bit length |
|---|---|---|---|
| frontierSix | 0.404366 (14,515) | 0.595568 (14,516) | 8,646 |
| Phase 11 110/111 | 0.396408 (6,560) | 0.603415 (6,561) | 7,801 |
| Phase 11 1011/1111 | 0.299856 (149) | 0.691327 (150) | 8,192 |
| Phase 8 110/011 | 0.471126 (156) | 0.520198 (141) | 8,193 |
| Thue–Morse 10/01 | 0.469235 (192) | 0.527969 (193) | 8,193 |
| Alternating 10 | 0 | 0 | 1 |
| All ones | 0 | 0 | 1 |
| All zeros | 0 | 0 | 1 |
| SHA-256 counter control | 0.486459 (141) | 0.508608 (204) | 8,192 |
| Near rational | 0 (128) | 0.984733 (131) | 8,192 |

The periodic controls have H_N=1 at **every** sampled and intervening N, with
seeds 1/1, -1/1 and 0/1 respectively. The near-rational parity word is
`(10)^64` followed by the one-start Thue–Morse word; the infinite continuation
is aperiodic. The synthetic control uses a fixed SHA-256 counter byte stream,
specified in the script, not a claim of cryptographic or mathematical
randomness. Its literal tested bits are stored with the dataset.

Power checkpoints alone would hide the strong primary excursions. Both sides
of every jump exceeding eight height bits are now saved. Plateau age, last
jump and exact jump ratios are recorded; “plateau age” is elapsed length at
that checkpoint, not a promise of how long the plateau will continue.

## Runtime, resources and falsification

`benchmark.json` records one actual run. Per-family cumulative elapsed seconds
for the instrumented profile pass (including selected certificate generation
and independent verification) were 22.408, 41.020, 19.695, 20.295, 40.745,
0.447, 2.171, 0.112, 41.855 and 30.507 in the table's family order. Python
allocation peaks ranged from 0.36 MB to 26.74 MB. These exclude residue
construction, the first checkpoint-selection pass, interpreter startup and
some native allocator memory; they are not process RSS or formal complexity
bounds. Timings vary by machine and tracemalloc substantially affects them.

The hard cap is 16,384 bits. SIGINT cancels normally and completed families
can be resumed from the ignored checkpoint file. Full command details and
certificate semantics are in `phase13/README.md`. The bounded CI run uses the
committed cap; there is no distributed, GPU or open-ended search.

Falsified claims include universal square-root existence for all residues,
acceptance of even-q shortest vectors, equality of ordinary parity-digit
complexity with seed height, the common-image-multiplier shortcut (first
failure on source 10 at 12 bits), and numerical convergence of the primary
profile. The last has an all-level written disproof, not just a finite outlier.
Exact B=c, eventual exact optimality of the shadow family, and analogous
asymptotic descriptions for the other words remain conjectural/unresolved.
