# Exact rational-height experiments

Run from the repository root with Python 3. No new dependencies are required.

```bash
python3 research/phase13/test_height.py
python3 research/phase13/experiments.py --check
python3 research/phase13/verify_certificates.py research/phase13/heights.json.gz
python3 research/phase13/verify_analytics.py --check
python3 research/phase13/verify_modular.py --check
```

`height_reference.py` uses two Euclidean floor sums for bounded-box existence,
then binary search for the least height and a witness. It is independent of
`height_lattice.py`, which replicates Klapper–Goresky's adaptive odd-coset
algorithm on the **ordinary digits of the seed residue**. Both accept
arbitrary-precision integers; no float participates in minimization.

`heights.json.gz` is deterministic JSON evidence (gzip timestamp zero). Each selected N includes the exact
residue, height, primitive witness, odd denominator, basis and determinant,
transition, plateau age, and a no-smaller-height certificate. Ratios are
approximate display values. `benchmark.json` records machine-dependent
elapsed times and Python allocation peaks separately; these are observations,
not certificate contents or universal complexity claims.

The checker compares approximate display ratios with tolerance 1e-14 for
libm rounding; every integer, witness and certificate field must match exactly.
`analytics.json` independently checks literal shadow levels, and `modular.json`
records a bounded deeper gcd audit and exact affine-map cycles modulo 347 and
347^2. Their mathematical scope is stated in the theory report.

The certificate is defined and proved in `../phase13-theory.md` Section 4.
Its two flat integer lists contain successive `(q_a,q_b)` quotient pairs.
The initial floor-sum states are determined by N,A,H. The verifier checks
every Euclidean identity, hence the exact zero count at H-1; a plausible
small lattice vector alone is insufficient. The independent verifier also
uses reversed Fraction branches and actual signed numerator iteration.

To extend a bounded run, use for example:

```bash
python3 research/phase13/experiments.py --write --max-bits 7776
```

The hard cap is 16,384 bits; default runs use 1,024 bits. SIGINT cancels
normally. Completed families are checkpointed in ignored `resume.json`;
`--write --resume --max-bits 7776` resumes those families after verifying
their certificates. A partially computed family restarts. No job is assumed
to survive a session. `--check` uses the committed dataset's own size and
recomputes all families; it never silently accepts a smaller run.

Selected checkpoints include all N through 128, powers of 2,3,4,6, the cap,
both sides of every jump exceeding eight height bits, and both reported dense
extrema for each family. Dense transitions
are processed even between saved checkpoints. The
reports distinguish finite observations, written theorems, kernel theorems
and imported source statements. See the journal for current obligations.
