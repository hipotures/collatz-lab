# Phase 5, Gate B: Mahler exclusion for the uniform family `mu_L`, the case `L = 5`, and a general criterion

**Issue:** [#10](https://github.com/hipotures/collatz-lab/issues/10), Gate B. Gate A
([`lean-semantic-audit.md`](lean-semantic-audit.md)) found no critical defect in
[PR #9](https://github.com/hipotures/collatz-lab/pull/9), so this investigation proceeded.

**Result in one paragraph.** For every block length $L \ge 4$, the word
$w_L = \lim_j \mu_L^j(1)$ with $\mu_L(1) = 1^{L-1}0$, $\mu_L(0) = 1^{L-2}01$ is an
all-prefix coefficient survivor, is not eventually periodic, and is **not** the parity
itinerary of any rational number with odd denominator; in particular it is not the itinerary
of any integer. The proof is the 2-adic Mahler argument of issue #7 with the linear form
built from the periodic approximant $(1^{L-1}0)^\infty$, which agrees with $w_L$ on its first
$N = L^2 - 2$ symbols. For $L = 5$ every constant is written out. A sufficient criterion for
arbitrary uniform equal-weight morphisms is proved in §8. At Phase 5 these were written proofs only. **Phase 6 now kernel-checks
Theorem 4.1 (all `L >= 4`, including Theorem 5.1) and Corollary 9.1**, using
finite integer identities; see [`lean-family-formalization.md`](lean-family-formalization.md).
The arbitrary-morphism criterion is now kernel-checked in Phase 7; see
[`lean-equal-weight-formalization.md`](lean-equal-weight-formalization.md).
The general symbolic family properties remain written proofs. None of these
results says anything about general Collatz orbits.

Reproduce every finite check in this memo from the repository root:

```text
python3 research/mahler-family/verify_family.py     # rewrites research/mahler-family/{evidence.json,summary.md}
cargo test --locked --test mahler_family            # 12 independent Rust checks, run by CI
```

Generated artifacts: [`mahler-family/summary.md`](mahler-family/summary.md),
[`mahler-family/evidence.json`](mahler-family/evidence.json).

---

## 1. Status table

Labels are the repository's: `proven-by-algebra`, `verified-for-finite-domain`,
`conjectured`, `refuted`. "Unformalized" means: written proof only, not kernel-checked.

| Claim | Status | Where |
|---|---|---|
| Symbol recurrence for $w_L$, all $L \ge 3$ | `proven-by-algebra` | Lemma 2.1 |
| All-prefix noncrossing $3^{r_k} > 2^k$, all $L \ge 4$ (fails for $L = 3$) | `proven-by-algebra` / `refuted` for $L=3$ | Theorem 2.2 |
| $w_L$ not eventually periodic, all $L \ge 3$ | `proven-by-algebra` | Theorem 2.3 |
| Mahler equation for $F_L$ and seed identity $x(w_L) = -\frac{B - 2^{L-2}}{B-A} + \frac{2^{L-2}}{B}F_{L,2}(A/B)$ | `proven-by-algebra` | Lemma 3.1, Theorem 3.3 |
| **$L = 5$: no rational with odd denominator realizes $w_5$** | `proven-by-algebra`, kernel-checked in Phase 6 | Theorem 5.1 |
| **All $L \ge 4$: no rational with odd denominator realizes $w_L$** | `proven-by-algebra`, kernel-checked in Phase 6 | Theorem 4.1 |
| Sufficient criterion (C) for uniform equal-weight morphisms | Lean-kernel-verified in Phase 7 | Theorem 8.1 |
| Tails $\sigma^t(w_L)$ and words eventually equal to them | `proven-by-algebra`, kernel-checked in Phase 6 | Corollary 9.1 |
| Identities of the proofs at tower levels $k \le 2$ ($L = 4, 5$), $k \le 1$ ($6 \le L \le 12$), and on all 144 admissible morphisms with $L \le 5$ | `verified-for-finite-domain` | §5.3, §8.3 |
| Padé table for $L = 5$, degree bound $1 \le m \le 16$ | `verified-for-finite-domain` | §6 |
| "`Odd D_k`" for the uncancelled tower | `refuted` ($v_2(D_1^{\mathrm{unc}}) = L(L-2)$) | §7 |
| Uniform equal-weight morphisms that fail (C) | `10/01` excluded in Lean in Phase 7; other cases require separate certificates | §8.4; `mahler-uncovered-morphisms.md` |
| Periodicity Conjecture, non-automatic survivor words, CST, Collatz | `conjectured`, untouched | §11 |

Three statements that must not be merged:

1. *Symbolic:* $w_L$ exists, survives, and is aperiodic (Section 2). This is combinatorics on words.
2. *Finite realization:* for every $K$ there are infinitely many positive integers whose first
   $K$ parities are $w_L(0), \dots, w_L(K-1)$, and each satisfies $T^K(n) > n$. This is true
   for **every** survivor word, including the periodic control $(1^{L-1}0)^\infty$, whose
   seed is the negative rational $-(B - 2^{L-1})/(B-A)$.
3. *Infinite realization:* no positive integer (indeed no element of $\mathbb{Z}_2 \cap \mathbb{Q}$)
   has the whole word as its itinerary (Sections 4 and 5). Only this needs the Mahler argument.

---

## 2. The family and its symbolic properties

Fix an integer $L \ge 3$ and define the $L$-uniform morphism
$$\mu_L(1) = 1^{L-1}0, \qquad \mu_L(0) = 1^{L-2}01, \qquad w_L = \lim_{j\to\infty}\mu_L^j(1).$$
The limit exists because $\mu_L(1)$ begins with $1$, so $\mu_L^j(1)$ is a prefix of
$\mu_L^{j+1}(1)$. Write $w = w_L$, $A = 2^L$, $B = 3^{L-1}$. $T$ is the accelerated map,
$T(x) = x/2$ for even $x$ and $(3x+1)/2$ for odd $x$, on $\mathbb{Z}_2$.

### Lemma 2.1 (symbol recurrence)
*For all $n \ge 0$:*
$$w(Ln + j) = 1 \ (0 \le j \le L-3), \qquad w(Ln + L-2) = w(n), \qquad w(Ln + L-1) = 1 - w(n).$$
*Conversely these relations determine $w$ uniquely.*

**Proof.** $w = \mu_L(w)$, so the block at positions $Ln, \dots, Ln+L-1$ is $\mu_L(w(n))$.
Both images start with $1^{L-2}$; the last two letters are $10$ if $w(n) = 1$ and $01$ if
$w(n) = 0$, that is $(w(n), 1 - w(n))$. For uniqueness, the relations express $w(i)$ through
$w(\lfloor i/L \rfloor)$ with $\lfloor i/L \rfloor < i$ for $i \ge 1$, and give $w(0) = 1$
directly ($j = 0 \le L - 3$). $\blacksquare$

In particular $w(n) = 1$ for $0 \le n \le L-2$ and $w(L-1) = 0$.

### Theorem 2.2 (all-prefix coefficient noncrossing)
*Let $L \ge 4$ and let $r_k$ be the number of ones among $w(0), \dots, w(k-1)$. Then
$3^{r_k} > 2^k$ for every $k \ge 1$. For $L = 3$ the statement is false.*

**Proof.** First, $3^{L-2} > 2^{L-1}$ for $L \ge 4$: it is $9 > 8$ at $L = 4$, and the left
side triples while the right side doubles. Hence also $B = 3^{L-1} > 3 \cdot 2^{L-1} > 2^L = A$.

Write $k = Lq + s$ with $q \ge 0$ and $1 \le s \le L$. The prefix consists of $q$ full
blocks, each with $L - 1$ ones, followed by the length-$s$ prefix of a block $\mu_L(b)$.
That partial prefix has $s$ ones if $s \le L-2$, at least $L-2$ ones if $s = L-1$, and
$L - 1$ ones if $s = L$. Therefore
$$\frac{3^{r_k}}{2^k} \ \ge\ \Bigl(\frac{B}{A}\Bigr)^{q} \cdot
\min\Bigl\{ \bigl(\tfrac32\bigr)^{s}\ (1 \le s \le L-2),\ \ \frac{3^{L-2}}{2^{L-1}},\ \ \frac{3^{L-1}}{2^{L}} \Bigr\} \ >\ 1 .$$
For $L = 3$: $w_3 = 110\,110\,101\cdots$ and its prefix $11011010$ has $5$ ones in $8$
symbols, $3^5 = 243 < 256 = 2^8$. $\blacksquare$

### Theorem 2.3 (aperiodicity)
*For $L \ge 3$, $w$ is not eventually periodic.*

**Proof.** By Lemma 2.1, each block contains exactly one $0$, located at residue $L-2$ or
$L-1$ modulo $L$: the zero of block $n$ is at $Ln + L - 1 - w(n)$. Residues $0, \dots, L-3$
always carry $1$.

Suppose $w(m + p) = w(m)$ for all $m \ge M$, with $p \ge 1$, and argue by strong induction on
$p$. Let $\rho = p \bmod L$.

- $\rho = 0$. Put $p' = p/L$. For $n \ge M$ we have $Ln + L - 2 \ge M$, so
  $w(n + p') = w(L(n+p') + L-2) = w(Ln + L - 2 + p) = w(Ln + L-2) = w(n)$. Thus $p' < p$ is an
  eventual period: contradiction with the induction hypothesis.
- $\rho \notin \{0, 1, L-1\}$. A zero at position $m \ge M$ has residue in $\{L-2, L-1\}$ and
  is mapped to a zero at $m + p$ with residue in $\{L-2+\rho, L-1+\rho\} \bmod L$, which is
  disjoint from $\{L-2, L-1\}$. Zeros exist beyond $M$ (one per block): contradiction.
- $\rho = 1$. A zero at residue $L-1$ would be mapped to residue $0$, which never carries a
  zero. So every block $n$ beyond $M$ has its zero at residue $L-2$, that is $w(n) = 1$ for
  all large $n$. But $w(Ln + L - 1) = 1 - w(n) = 0$ for large $n$: contradiction.
- $\rho = L-1$. A zero at residue $L-2$ would be mapped to residue $L-3$, which never carries
  a zero. So $w(n) = 0$ for all large $n$, contradicting $w(Ln) = 1$. $\blacksquare$

Theorem 2.3 alone does not show that the 2-adic seed is irrational: that implication is the
open Periodicity Conjecture ([`infinite-itineraries.md`](infinite-itineraries.md) §2.1).

---

## 3. Generating function and seed identity

Let $F(t) = F_L(t) = \sum_{n \ge 0} w(n) t^n \in \mathbb{Z}[[t]]$ and
$$C(t) = \sum_{j=0}^{L-3} t^j + t^{L-1}.$$

### Lemma 3.1 (Mahler equation)
*In $\mathbb{Z}[[t]]$:*
$$F(t) = \frac{C(t)}{1 - t^L} + \bigl(t^{L-2} - t^{L-1}\bigr) F(t^L).$$

**Proof.** Split $n = Lm + j$ and apply Lemma 2.1:
$F(t) = \sum_m t^{Lm}\bigl(\sum_{j \le L-3} t^j + w(m) t^{L-2} + (1 - w(m)) t^{L-1}\bigr)
= C(t)\sum_m t^{Lm} + (t^{L-2} - t^{L-1})\sum_m w(m) t^{Lm}$. $\blacksquare$

### Lemma 3.2 (block offsets)
*If $y \in \mathbb{Z}_2$ has first $L$ parities $\mu_L(b)$, then $A\,T^L(y) = B y + c_b$ with*
$$c_1 = B - 2^{L-1}, \qquad c_0 = B - 2^{L-2}, \qquad\text{so}\qquad c_b = c_0 - 2^{L-2} b .$$

**Proof.** After $m$ consecutive odd steps, $2^m T^m(y) = 3^m y + 3^m - 2^m$ (induction:
$\bigl(3(3^m y + 3^m - 2^m)/2^m + 1\bigr)/2 = (3^{m+1} y + 3^{m+1} - 2^{m+1})/2^{m+1}$).
For $\mu_L(1) = 1^{L-1}0$: $L-1$ odd steps and one halving give
$T^L(y) = (3^{L-1} y + 3^{L-1} - 2^{L-1})/2^L$. For $\mu_L(0) = 1^{L-2}01$: with
$y' = T^{L-2}(y) = (3^{L-2}y + 3^{L-2} - 2^{L-2})/2^{L-2}$, one halving and one odd step give
$T^L(y) = (3y' + 2)/4 = (3^{L-1} y + 3^{L-1} - 3\cdot 2^{L-2} + 2 \cdot 2^{L-2})/2^L$. $\blacksquare$

For a power series $G \in \mathbb{Z}[[t]]$ and $z \in 2\mathbb{Z}_2$ write $G_2(z)$ for the
2-adic sum $\sum g_n z^n$. It converges because $|g_n z^n|_2 \le 2^{-n}$; $G \mapsto G_2(z)$ is
a ring homomorphism $\mathbb{Z}[[t]] \to \mathbb{Z}_2$ (products of convergent series in a
complete non-archimedean field are given by the Cauchy product), and
$\bigl(G(t^L)\bigr)_2(z) = G_2(z^L)$ termwise. The real sum of the same series is a different
number and plays no role here.

### Theorem 3.3 (seed identity, from first principles)
*Let $x \in \mathbb{Z}_2$ have parity itinerary $w$, i.e. $T^j(x) \equiv w(j) \pmod 2$ for all
$j \ge 0$. Then, in $\mathbb{Z}_2$,*
$$x = -\frac{c_0}{B - A} + \frac{2^{L-2}}{B}\,F_2\!\Bigl(\frac{A}{B}\Bigr),
\qquad\text{equivalently}\qquad B\bigl((B-A)x + c_0\bigr) = 2^{L-2}(B-A)\,F_2\!\Bigl(\frac AB\Bigr).$$

**Proof.** Put $y_n = T^{Ln}(x) \in \mathbb{Z}_2$ and $g_n = (B-A) y_n + c_0$. The parities of
$y_n$ are block $n$ of $w$, namely $\mu_L(w(n))$, so Lemma 3.2 gives
$A y_{n+1} = B y_n + c_0 - 2^{L-2} w(n)$, hence
$$A g_{n+1} = (B-A)\bigl(By_n + c_0 - 2^{L-2}w(n)\bigr) + A c_0 = B g_n - 2^{L-2}(B-A)\, w(n).$$
Unrolling $M$ times,
$g_0 = \frac{2^{L-2}(B-A)}{B}\sum_{n<M} w(n)\bigl(\tfrac AB\bigr)^n + \bigl(\tfrac AB\bigr)^M g_M$.
Since $g_M \in \mathbb{Z}_2$ and $v_2\bigl((A/B)^M\bigr) = LM \to \infty$, letting $M \to \infty$
gives $g_0 = \frac{2^{L-2}(B-A)}{B} F_2(A/B)$. $\blacksquare$

The proof does not use the Bernstein–Lagarias bijection; it only uses that iterates of a
2-adic integer are 2-adic integers. Cross-check with the issue's suggested form: for
$L = 5$, $x = -\frac{73}{49} + \frac{8}{81}F_2\bigl(\frac{32}{81}\bigr)$; for $L = 4$,
$x = -\frac{23}{11} + \frac{4}{27}F_2\bigl(\frac{16}{27}\bigr)$, the identity of issue #7.

---

## 4. Main theorem for the whole family

### Theorem 4.1 (no rational realization, all $L \ge 4$; `proven-by-algebra`, kernel-checked in Phase 6)
*Let $L \ge 4$. There are no integers $p$ and odd $q \ge 1$ such that $x = p/q$ has parity
itinerary $w_L$ under $T$. In particular no integer has itinerary $w_L$.*

Throughout the proof, $a_k = A^{L^k}$, $b_k = B^{L^k}$, $z_k = a_k/b_k \in \mathbb{Z}_2$, so
$a_{k+1} = a_k^L$, $b_{k+1} = b_k^L$, $z_{k+1} = z_k^L$, $v_2(z_k) = L^{k+1}$, and
$f_k = F_2(z_k) \in \mathbb{Z}_2$. Also $N = L^2 - 2$.

Assume, for contradiction, that $x = p/q$ ($q \ge 1$ odd) has itinerary $w$.

#### Step 1: an integer tower with odd denominators

Evaluating Lemma 3.1 at $z_k$ and clearing $1 - z_k^L$:
$$\bigl(1 - z_k^L\bigr) f_k = C(z_k) + z_k^{L-2}(1 - z_k)\bigl(1 - z_k^L\bigr) f_{k+1}. \tag{4.1}$$

Define positive odd integers
$$D_0 = (B-A)\,q, \qquad D_{k+1} = D_k\,(b_k - a_k)\,(b_k^L - a_k^L)$$
($b_k > a_k > 0$ by Theorem 2.2's inequality $B > A$; $b_k$ is odd and $a_k$ even), and put
$u_k = D_k f_k \in \mathbb{Z}_2$.

**Claim: $u_k \in \mathbb{Z}$ for every $k$.** The key fact is
$\mathbb{Z}[\tfrac12] \cap \mathbb{Z}_2 = \mathbb{Z}$ (a fraction $m/2^e$ with $m$ odd and
$e \ge 1$ has negative 2-adic valuation).

- $k = 0$. By Theorem 3.3, $f_0 = \dfrac{B((B-A)x + c_0)}{2^{L-2}(B-A)}$, so
  $$u_0 = \frac{B\bigl((B-A)p + c_0 q\bigr)}{2^{L-2}} \in \mathbb{Z}[\tfrac12] \cap \mathbb{Z}_2 = \mathbb{Z}.$$
  (Equivalently $2^{L-2} \mid (B-A)p + c_0 q$; for $L = 4$ this is $4 \mid 11p + 23q$.)
- $k \to k+1$. Write $a = a_k$, $b = b_k$ and let
  $C_h(a,b) = b^{L-1}C(a/b) = \sum_{j=0}^{L-3} a^j b^{L-1-j} + a^{L-1}$. Multiply (4.1) by
  $D_k b^{2L-1}$. Using $1 - z^L = (b^L - a^L)/b^L$ and
  $z^{L-2}(1-z)(1-z^L) = a^{L-2}(b-a)(b^L - a^L)/b^{2L-1}$:
  $$b^{L-1}(b^L - a^L)\,u_k = D_k\, b^L\, C_h(a,b) + a^{L-2}\,u_{k+1}.$$
  Hence
  $$a_k^{L-2}\,u_{k+1} = b_k^{L-1}\,\Delta_k, \qquad
  \Delta_k := (b_k^L - a_k^L)\,u_k - D_k\, b_k\, C_h(a_k, b_k) \in \mathbb{Z}. \tag{4.2}$$
  So $u_{k+1} \in \mathbb{Z}[\tfrac12] \cap \mathbb{Z}_2 = \mathbb{Z}$, and $a_k^{L-2} \mid \Delta_k$
  because $b_k$ is odd.

For $L = 4$ this is exactly the tower of issue #7: $D_{k+1} = D_k(b_k - a_k)(b_k^4 - a_k^4)$,
$u_{k+1} = b_k^3 \Delta_k / a_k^2$.

#### Step 2: a nonzero integer linear form that is highly 2-divisible

Let $P(t) = (1 + t + \dots + t^{L-2})/(1 - t^L) = \sum \pi(n) t^n$, the generating function of
$(1^{L-1}0)^\infty$, and
$$R(t) := \bigl(1 + t + \dots + t^{L-2}\bigr) - \bigl(1 - t^L\bigr)F(t) = (1 - t^L)\bigl(P(t) - F(t)\bigr) \in \mathbb{Z}[[t]].$$

**Claim: $R(t) = t^N\bigl(1 + t\,G(t)\bigr)$ with $G \in \mathbb{Z}[[t]]$, $N = L^2 - 2$.** By
Lemma 2.1, $w(m) = 1$ for $m \le L-2$, so blocks $0, \dots, L-2$ of $w$ are $\mu_L(1) = 1^{L-1}0$
and agree with $\pi$. Block $L-1$ is $\mu_L(w(L-1)) = \mu_L(0) = 1^{L-2}01$: it agrees with
$\pi$ at its first $L-2$ positions, and at position $L(L-1) + (L-2) = N$ it has $w(N) = 0$
while $\pi(N) = 1$. So $P - F = t^N + O(t^{N+1})$, and multiplying by $1 - t^L$ does not change
the lowest term.

Evaluating at $z_k \in 2\mathbb{Z}_2$: $R_2(z_k) = z_k^N \cdot (1 + z_k G_2(z_k))$ and the second
factor is a 2-adic unit. Therefore
$$v_2\bigl(R_2(z_k)\bigr) = N\,v_2(z_k) = N L^{k+1}. \tag{4.3}$$

Define the homogeneous forms $P_0(a,b) = \sum_{j=0}^{L-2} a^j b^{L-j}$,
$P_1(a,b) = -(b^L - a^L)$, and
$$E_k := D_k\,P_0(a_k, b_k) + u_k\,P_1(a_k, b_k) \in \mathbb{Z}.$$
Then $E_k = D_k b_k^L\bigl[(1 + z_k + \dots + z_k^{L-2}) - (1 - z_k^L) f_k\bigr] = D_k\, b_k^L\, R_2(z_k)$.
As $D_k b_k^L$ is odd, (4.3) gives
$$E_k \ne 0, \qquad v_2(E_k) = N L^{k+1}, \qquad |E_k| \ge 2^{N L^{k+1}} = 2^{L(L^2-2)\,L^k}. \tag{4.4}$$

#### Step 3: archimedean heights

Let $\rho_k = a_k/b_k = (A/B)^{L^k}$. Since $A/B = 2(2/3)^{L-1} \le 16/27$ for $L \ge 4$, we have
$\rho_k \le 16/27$ and $1/(1 - \rho_k) \le 27/11 < 3$. With $a = a_k$, $b = b_k$:

- $C_h(a,b) = b^{L-1}\bigl(\sum_{j \le L-3}\rho^j + \rho^{L-1}\bigr) < b^{L-1}/(1-\rho) < 3\,b^{L-1}$;
- $|\Delta_k| \le (b^L - a^L)|u_k| + D_k\, b\, C_h < b^L\bigl(|u_k| + 3 D_k\bigr)$;
- by (4.2), $|u_{k+1}| < \dfrac{b^{2L-1}}{a^{L-2}}\bigl(|u_k| + 3D_k\bigr)$;
- $D_{k+1} < b^{L+1} D_k = b^{2L-1} D_k / b^{L-2}$.

With $H_k := |u_k| + D_k$, and using $a^{L-2} \ge 16^2 = 256$, $b^{L-2} \ge 27^2 = 729$:
$$H_{k+1} \le b_k^{2L-1}\Bigl(\frac{|u_k|}{256} + \Bigl(\frac{3}{256} + \frac{1}{729}\Bigr)D_k\Bigr) \le b_k^{2L-1} H_k .$$
Since $\prod_{j<k} b_j = B^{(L^k - 1)/(L-1)} = 3^{L^k - 1}$,
$$H_k \le H_0 \cdot 3^{(2L-1)(L^k - 1)} < H_0 \cdot 3^{(2L-1)L^k}.$$
Finally $P_0(a,b) = b^L\sum_{j \le L-2}\rho^j < 3\,b^L$ and $|P_1(a,b)| < b^L$, and
$b_k^L = 3^{L(L-1)L^k}$, so
$$|E_k| \le 3\, b_k^L\, H_k < 3 H_0 \cdot 3^{(L^2 + L - 1)\,L^k}. \tag{4.5}$$

#### Step 4: contradiction

From (4.4) and (4.5), for every $k \ge 0$:
$$2^{L(L^2-2)\,L^k} < 3H_0 \cdot 3^{(L^2+L-1)\,L^k}.$$
Because $3^5 = 243 < 256 = 2^8$, $3^{y} < 2^{8y/5}$ for $y > 0$, so
$$2^{\,g(L)\,L^k/5} < 3H_0, \qquad g(L) := 5L(L^2 - 2) - 8(L^2 + L - 1) = 5L^3 - 8L^2 - 18L + 8 .$$
For $L \ge 4$: $5L^3 \ge 20L^2$ and $12L^2 \ge 48L$, so
$g(L) \ge 12L^2 - 18L + 8 \ge 30L + 8 \ge 128$. Hence
$$2^{25\,L^k} < 3H_0 = 3\Bigl(\Bigl|\frac{B((B-A)p + c_0q)}{2^{L-2}}\Bigr| + (B-A)q\Bigr) \qquad\text{for all } k \ge 0,$$
which is false for large $k$. $\blacksquare$

**Remarks.**

- The inequality $g(L) > 0$ is proved for all $L \ge 4$ by the two-line estimate above. The
  Rust test evaluates $2^{L(L^2-2)} > 3^{L^2+L-1}$ for $4 \le L \le 64$ only as an illustration.
- The only place $L \ge 4$ is used is the height constants ($A/B \le 16/27$, $a^{L-2} \ge 256$).
  The method does not need the word to be a survivor; see §8 for $L = 3$.
- **Integer-only reformulation (used in Phase 6).** $u_k = D_k f_k$ in $\mathbb{Z}_2$ is
  equivalent to the family of integer congruences
  $b_k^{n-1}u_k \equiv D_k \sum_{j<n} w(j)\,a_k^j b_k^{n-1-j} \pmod{a_k^n}$ for all $n \ge 1$, which
  is the form used in PR #9 for $L = 4$ (`tower_congruence_all`). Step 2 then reads
  $b_k^{N}E_k \equiv D_k\,a_k^N b_k^{L} \pmod{a_k^{N+1}}$. Phase 6 formalizes Steps 1–2 in this form for every $L \ge 4$; see
  `CollatzLab.Family.tower_congruence` and `CollatzLab.Family.valuation`.

---

## 5. The case $L = 5$ written out

$\mu_5(1) = 11110$, $\mu_5(0) = 11101$,
$$w_5 = 11110\,11110\,11110\,11110\,11101\,11110\cdots$$
$A = 32$, $B = 81$, $B - A = 49$, $c_1 = 65$, $c_0 = 73$, $N = 23$.

### 5.1 Statement

### Theorem 5.1 ($L = 5$; `proven-by-algebra`, kernel-checked in Phase 6)
*No rational number with odd denominator has parity itinerary $w_5$. Explicitly, if $x = p/q$
with $q \ge 1$ odd realized $w_5$, then with*
$$a_k = 32^{5^k},\quad b_k = 81^{5^k},\quad D_0 = 49q,\quad u_0 = \frac{81(49p + 73q)}{8},$$
$$D_{k+1} = D_k(b_k - a_k)(b_k^5 - a_k^5),\qquad
\Delta_k = (b_k^5 - a_k^5)u_k - D_k b_k\bigl(b_k^4 + a_kb_k^3 + a_k^2b_k^2 + a_k^4\bigr),\qquad
u_{k+1} = \frac{b_k^4\,\Delta_k}{a_k^3},$$
$$E_k = D_k\bigl(b_k^5 + a_kb_k^4 + a_k^2b_k^3 + a_k^3b_k^2\bigr) - u_k\bigl(b_k^5 - a_k^5\bigr),$$
*all of $u_k, D_k, E_k$ would be integers with $D_k$ odd and positive, and for every $k \ge 0$:*

1. *$8 \mid 49p + 73q$ and $a_k^3 \mid \Delta_k$ (integrality);*
2. *$E_k \ne 0$ and $v_2(E_k) = 23 \cdot 5^{k+1} = 115 \cdot 5^k$ (nonvanishing, exact valuation);*
3. *$H_{k+1} \le b_k^9 H_k$ for $H_k = |u_k| + D_k$, hence $H_k < H_0 \cdot 3^{9\cdot 5^k}$ and
   $|E_k| < 3H_0 \cdot 3^{29 \cdot 5^k}$ (heights);*
4. *consequently $2^{69\cdot 5^k} < \bigl(2^{115}/3^{29}\bigr)^{5^k} < 3H_0$ for all $k$, which is impossible.*

**Proof.** This is Theorem 4.1 with $L = 5$; the constants specialise as follows.

| Quantity | General $L$ | $L = 5$ |
|---|---|---|
| seed identity | $B((B-A)x + c_0) = 2^{L-2}(B-A)F_2(A/B)$ | $81(49x + 73) = 392\,F_2(32/81)$ |
| Mahler equation | $F(t) = \frac{C(t)}{1-t^L} + t^{L-2}(1-t)F(t^L)$ | $F(t) = \frac{1 + t + t^2 + t^4}{1 - t^5} + (t^3 - t^4)F(t^5)$ |
| tower step (4.2) | $a^{L-2}u_{k+1} = b^{L-1}\Delta_k$ | $a^3 u_{k+1} = b^4 \Delta_k$ |
| approximant | $(1 + \dots + t^{L-2}) - (1 - t^L)F = t^{L^2-2} + \cdots$ | $(1 + t + t^2 + t^3) - (1 - t^5)F(t) = t^{23} - t^{24} + \cdots$ |
| valuation (4.4) | $N L^{k+1}$ | $115 \cdot 5^k$ |
| $1/(1-\rho)$ bound | $\le 27/11$ | $81/49$ |
| height step | $b_k^{2L-1}$, needs $\frac{3}{a^{L-2}} + \frac{1}{b^{L-2}} \le 1$ | $b_k^9$; $\frac{3}{32^3} + \frac{1}{81^3} < 1$ |
| archimedean exponent | $3^{(L^2+L-1)L^k}$ | $3^{29\cdot 5^k}$ |
| margin | $2^{g(L)L^k/5}$, $g(L) \ge 128$ | $2^{115} > 2^{69}\cdot 3^{29}$ (exact integers) |

Item 4: $2^{115} = 41538374868278621028243970633760768$ and
$2^{69}\cdot 3^{29} = 40512224221827380280140849737629696$, so the ratio $2^{115}/3^{29}$
lies between $2^{69}$ and $2^{70}$. $\blacksquare$

### 5.2 Periodic control

For the periodic word $u = (11110)^\infty$ every block offset is $c_1 = 65$, so its seed is
the fixed point of $y \mapsto (81y + 65)/32$. Equivalently, put $w(n) = 1$ for all $n$ in the
block formula, which replaces $F_2(32/81)$ by $1/(1 - 32/81)$:
$$x(u) = -\frac{65}{49} = -\frac{73}{49} + \frac{8}{81}\cdot\frac{1}{1 - 32/81}.$$
The two seeds agree modulo $2^{23}$ and differ modulo $2^{24}$ (the words first differ at
index $23$). At every checkpoint $K$ the positive integer $n_K \equiv -65/49 \pmod{2^K}$
follows $(11110)^{K/5}$ and grows, yet the control word has a negative rational seed. This is
the concrete reason finite prefix data cannot decide the infinite question.

### 5.3 Finite certificates (`verified-for-finite-domain`)

| Check | Range | Tool |
|---|---|---|
| substitution word = recurrence word; noncrossing | $4 \le L \le 12$, 4096 symbols (Python); $4 \le L \le 9$ (Rust) | both |
| seed residue: parity-position series = bitwise lifting (96 bits) = closed formula; direct iteration of $x_K + 2^K$ follows the prefix and grows | $K = 256$ for $4 \le L \le 12$ and $K \in \{20, \dots, 1280\}$ for $L = 5$ (Python); $K = 40L$ for $4 \le L \le 8$ (Rust) | both |
| Mahler equation (4.1), tower step (4.2), $E_k = D_k b_k^L R_2(z_k)$, $D_k$ odd, $v_2(E_k) = N L^{k+1}$, evaluated on the true 2-adic value $f_k$ with $q = 1$ | $k \le 2$ for $L = 4, 5$; $k \le 1$ for $6 \le L \le 12$ (Python) and $L = 6, 7$ (Rust) | both |
| $v_2(E_k)$ for $L = 5$ | $115,\ 575,\ 2875$ ($k = 0, 1, 2$) | both |
| $v_2(E_k)$ for $L = 4$ | $56,\ 224,\ 896$, the values recorded in issue #7 | both |
| level-0 integer congruence $81^{n-1}u_0 \equiv 49\,\mathrm{preS}(32, 81, n) \pmod{32^n}$, using the crate's `homogenised_prefix_sum` | $1 \le n \le 80$ | Rust |
| adversarial controls: $c_1$ in place of $c_0$, dropping the factor $81$, using the $L = 4$ word | all rejected | Rust |

These checks use the genuine 2-adic number $x(w_5)$ truncated modulo a power of two. They
cannot instantiate the hypothetical rational seed of the theorem, because none exists.

---

## 6. The bounded Padé search for $L = 5$ (`verified-for-finite-domain`)

One search was run, with degree bound $1 \le m \le 16$, exact rational Gauss–Jordan
elimination, no floating point. For each $m$ it finds the minimal-degree solution of
$p_0 + p_1 F = O(t^{2m+1})$ with $\deg p_i \le m$, removes a common power of $t$, makes it
primitive, and reads off its true order $N$ and leading coefficient $c$. The asymptotic ledger
for a pair of reduced degree $M$ and order $N$ in the tower of §4 is
$2^{5N}$ against $3^{4M+9}$ (the factor $3^{(L-1)M}$ from $b_k^M$ and $3^{2L-1}$ from the height step).

| $m$ | null dim | shift | $M$ | $N$ | $c$ | $v_2(c)$ | reduced $p_0$ | reduced $p_1$ | ledger |
|---|---|---|---|---|---|---|---|---|---|
| 1 | 1 | 0 | 1 | 4 | $1$ | 0 | $1$ | $-1 + t$ | $2^{20} < 3^{13}$ **fails** |
| 2 | 1 | 1 | 1 | 4 | $1$ | 0 | $1$ | $-1 + t$ | **fails** (same pair) |
| 3 | 1 | 0 | 3 | 7 | $-3$ | 0 | $1 + 2t + 3t^2 + t^3$ | $-1 - t - t^2 + 2t^3$ | $2^{35} > 3^{21}$ |
| 4 | 1 | 0 | 4 | 9 | $4$ | 2 | $3 + 2t + t^2 - 4t^4$ | $-3 + t + t^2 + t^3 + t^4$ | $2^{45} > 3^{25}$ |
| **5** | 1 | 0 | **5** | **23** | **$1$** | **0** | $1 + t + t^2 + t^3$ | $-1 + t^5$ | $2^{115} > 3^{29}$ |
| 6–11 | 2–7 | 0 | 5 | 23 | $1$ | 0 | same | same | same |
| 12–16 | 6–2 | 2–10 | 5 | 23 | $1$ | 0 | same (shifted by $t^{2m-22}$) | same | same |

Observations.

1. The degree-5 pair is the periodic approximant of §4: order $23$ against the generic $11$,
   coefficients in $\{0, \pm1\}$, leading coefficient $1$.
2. Rows 6–16 form one singular block: the nullspace is spanned by multiples of the degree-5
   pair. No new primitive approximant appears up to $m = 16$. By analogy with
   $L = 4$ (where $N$ jumps $14 \to 58$ at $m = 16$) the next periodic approximant is expected
   to be $-1 + t^{25}$ at $m = 25$; this was **not** computed, and the search was not extended
   to $m = 24$, because the degree-5 pair already closes the proof with a margin of $2^{69}$ per
   level and nothing would be learned.
3. Rows 3 and 4 close the *asymptotic* ledger, but using them in a proof would need extra
   bookkeeping (the constant $\|p\|_1$, and for $m = 4$ the leading coefficient $4$, which is
   harmless only because $v_2(c) = 2 < v_2(z_k) = 5^{k+1}$). They are recorded as observations
   and are not used.
4. As a control, the same routine reproduces all 16 pairs $(N, c)$ of the $L = 4$ table in
   [`infinite-itineraries.md`](infinite-itineraries.md) §7.4.

---

## 7. Strategies that do not work, and what the $t^{L-2}(1-t)$ factor really obstructs

1. **Naive truncation.** Truncating $F_2(a_k/b_k)$ after $n$ terms gains $2^{Ln}$ 2-adically
   against a denominator $B^n$. Since $A < B$ for $L \ge 4$ (ratio of logarithms
   $\frac{L\log 2}{(L-1)\log 3}$, about $0.789$ for $L = 5$), truncation loses at every scale.
2. **The $[1/1]$ pair.** $(1, -1 + t)$ has order $4$ for $L = 5$; $2^{20} = 1048576 < 3^{13} = 1594323$.
3. **The uncancelled `Odd D_k` invariant** (the template of `Rung1.lean` for
   $\sigma: 1 \mapsto 110, 0 \mapsto 011$). The Mahler multiplier is
   $t^{L-2}(1 - t)$, which vanishes to order $L - 2$ at $0$ because both images share the prefix
   $1^{L-2}$. Homogenising without cancellation gives
   $D^{\mathrm{unc}}_{k+1} = D^{\mathrm{unc}}_k\, a_k^{L-2}(b_k - a_k)(b_k^L - a_k^L)$, so
   $v_2(D^{\mathrm{unc}}_1) = L(L-2)$: $8$ for $L = 4$, $15$ for $L = 5$. The invariant
   "`D_k` is odd" is **refuted** for every member of the family.

   This refutes a lemma, not the method. Two repairs exist:
   - *Cancel* $a_k^{L-2}$, as in (4.2). Integrality of the quotient is the content of Step 1.
   - *Drop oddness.* With $u^{\mathrm{unc}}_k = D^{\mathrm{unc}}_k f_k$ one still has
     $E^{\mathrm{unc}}_k = D^{\mathrm{unc}}_k\, b_k^L R_2(z_k)$, which is nonzero with
     $v_2 \ge N L^{k+1}$ for any nonzero integer $D^{\mathrm{unc}}_k$. The heights satisfy
     $D^{\mathrm{unc}}_{k+1} < a^{L-2}b^{L+1}D^{\mathrm{unc}}_k < b^{2L-1}D^{\mathrm{unc}}_k$ and
     $|u^{\mathrm{unc}}_{k+1}| = b^{L-1}|\Delta^{\mathrm{unc}}_k| < b^{2L-1}(|u^{\mathrm{unc}}_k| + 3D^{\mathrm{unc}}_k)$,
     so $H^{\mathrm{unc}}_{k+1} < 4\,b_k^{2L-1}H^{\mathrm{unc}}_k$ and the same ledger closes
     (the factor $4^k$ is negligible against $2^{25L^k}$).

   So the statement in [`infinite-itineraries.md`](infinite-itineraries.md) Proposition 6.1 that
   the uncancelled denominator "absorbs" valuation needed for the contradiction is accurate
   only for a proof that insists on exact valuations through an odd denominator. A lower bound
   on $v_2(E_k)$ plus $E_k \ne 0$ is all the contradiction consumes. The cancelled tower is
   kept as the main line because it matches PR #9 and gives cleaner constants.
4. **Aperiodicity alone.** Theorem 2.3 does not imply irrationality of the seed; that step is
   the open Periodicity Conjecture.
5. **Not attempted in Phase 5:** a Lean formalization of Theorem 4.1 or 5.1 (now completed
   in Phase 6). Irrationality measures and transcendence of $x(w_L)$ remain outside scope.

---

## 8. A parameterized sufficient criterion

The proof of Theorem 4.1 uses very little about the family. This section isolates the
hypotheses.

### 8.1 Setting

Let $L \ge 2$ and let $\mu$ be an $L$-uniform binary morphism with images
$\mu(0), \mu(1) \in \{0,1\}^L$ such that

- **(H1)** $\mu(1)$ begins with $1$ (so $w_\mu = \lim \mu^j(1)$ exists);
- **(H2)** $\mu(0)$ and $\mu(1)$ contain the same number $r \ge 1$ of ones;
- **(H3)** $\mu(0) \ne \mu(1)$.

By (H2) and (H3), $\mu(1) \ne 1^L$ and the images differ in at least two positions. Define

- $t = \min\{j : \mu(1)_j = 0\}$, so $1 \le t \le L-1$;
- $s = \min\{j : \mu(0)_j \ne \mu(1)_j\}$ and $e = \max\{j : \mu(0)_j \ne \mu(1)_j\}$, so $0 \le s < e \le L-1$;
- $N = Lt + s$, $A = 2^L$, $B = 3^r$, $m = \max(A, B)$.

### Theorem 8.1 (criterion; Lean-kernel-verified in Phase 7)
*Assume (H1)–(H3) and*
$$\textbf{(C)}\qquad 2^{\,L(L-1)N} > m^{\,L^2 + e}.$$
*Then no rational number with odd denominator has parity itinerary $w_\mu$.*

**Proof.** Write $Q_b(t) = \sum_{j<L}\mu(b)_j t^j$ and $\Gamma = Q_1 - Q_0$. By the definition of
$s$ and $e$, $\Gamma(t) = t^s\,\Gamma^*(t)$ with $\Gamma^*$ of degree $d = e - s$, coefficients in
$\{-1, 0, 1\}$ and $\Gamma^*(0) = \pm1$.

*Mahler equation.* $w(Ln + j) = \mu(0)_j + w(n)\bigl(\mu(1)_j - \mu(0)_j\bigr)$ gives
$F(t) = Q_0(t)/(1 - t^L) + \Gamma(t)F(t^L)$.

*Seed identity.* With $c_b = c(\mu(b))$ the block offsets ($A\,T^L(y) = By + c_b$),
$c_{w(n)} = c_0 + (c_1 - c_0)w(n)$, and the computation of Theorem 3.3 gives
$B\bigl((B-A)x + c_0\bigr) = (B-A)(c_0 - c_1)F_2(A/B)$. Moreover $v_2(c_0 - c_1) = s$: writing
$c(v) = \sum_i 3^{r-1-i}2^{d_i}$ over the positions $d_i$ of the ones, the two offsets share all
terms with $d_i < s$, exactly one of them has a term $3^{\ast}2^s$, and all remaining terms are
divisible by $2^{s+1}$. Write $c_0 - c_1 = 2^s\kappa$ with $\kappa$ odd.

*Tower.* Suppose $x = p/q$ realizes $w_\mu$. Let $a_k = A^{L^k}$, $b_k = B^{L^k}$,
$f_k = F_2(a_k/b_k)$, and let $\Gamma^*_h(a,b) = b^{d}\,\Gamma^*(a/b)$,
$Q_{b,h}(a,b) = b^{L-1}Q_b(a/b)$ be the homogenisations. $\Gamma^*_h(a_k, b_k)$ is an odd integer
(its $b^d$ coefficient is $\pm1$ and all other terms are even), in particular nonzero, and
$b_k^L - a_k^L$ is odd and nonzero. Put
$$D_0 = |B-A|\,|\kappa|\,q, \qquad D_{k+1} = D_k\,\bigl|\Gamma^*_h(a_k,b_k)\bigr|\,\bigl|b_k^L - a_k^L\bigr|, \qquad u_k = D_kf_k .$$
All $D_k$ are odd positive integers. $u_0 = \pm B((B-A)p + c_0q)/2^s \in \mathbb{Z}[\tfrac12]\cap\mathbb{Z}_2 = \mathbb{Z}$.
Multiplying the Mahler equation at $z_k$ by $D_k b_k^{L+e}$ gives, with a sign $\varsigma_k = \pm1$,
$$a_k^{s}\,\varsigma_k\,u_{k+1} = b_k^{e}\,\Delta_k, \qquad \Delta_k := (b_k^L - a_k^L)u_k - D_k\,b_k\,Q_{0,h}(a_k,b_k),$$
so $u_{k+1} \in \mathbb{Z}$ by induction.

*Linear form.* $R(t) := Q_1(t) - (1 - t^L)F(t) = (1-t^L)(P - F)$ with $P$ the generating function
of $\mu(1)^\infty$. The first $L$ symbols of $w$ are $\mu(1)$, so $w(n) = 1$ for $n < t$ and
$w(t) = 0$. Hence blocks $0, \dots, t-1$ of $w$ are $\mu(1)$ and block $t$ is $\mu(0)$, which
first differs from $\mu(1)$ at offset $s$. So $R(t) = \pm t^N + O(t^{N+1})$ with integer
coefficients, and $v_2(R_2(z_k)) = N L^{k+1}$. The integer
$E_k := D_k\,b_k\,Q_{1,h}(a_k,b_k) - (b_k^L - a_k^L)u_k = D_kb_k^L R_2(z_k)$ satisfies
$E_k \ne 0$ and $|E_k| \ge 2^{NL^{k+1}}$.

*Heights.* Let $m_k = \max(a_k, b_k) = m^{L^k}$ and $H_k = |u_k| + D_k$. Then
$|Q_{b,h}| \le L\,m_k^{L-1}$, $|\Gamma^*_h| \le L\,m_k^{d}$, $|b^L - a^L| \le m_k^L$, so
$|\Delta_k| \le m_k^L(|u_k| + L D_k)$, $|u_{k+1}| \le m_k^{L+e}(|u_k| + LD_k)$ (using $a_k^s \ge 1$),
$D_{k+1} \le L\,m_k^{L+d}D_k \le L\,m_k^{L+e}D_k$, hence $H_{k+1} \le 2L\,m_k^{L+e}H_k$ and
$$H_k \le (2L)^k\,m^{(L+e)(L^k-1)/(L-1)}H_0, \qquad |E_k| \le L\,m_k^L H_k \le L(2L)^kH_0\cdot m^{\,L^k (L^2+e)/(L-1)} .$$

*Contradiction.* Raising $2^{NL\cdot L^k} \le |E_k|$ to the power $L-1$:
$$\Bigl(\frac{2^{L(L-1)N}}{m^{L^2+e}}\Bigr)^{L^k} \le \bigl(L(2L)^kH_0\bigr)^{L-1}\qquad\text{for all } k \ge 0 .$$
Under (C) the left side grows doubly exponentially in $k$ and the right side singly exponentially. $\blacksquare$

### 8.2 The family as an instance

For $\mu_L$: $t = L-1$, $s = L-2$, $e = L-1$, $N = L^2 - 2$, $m = B = 3^{L-1}$ (for $L \ge 4$), and (C)
reads $2^{L(L^2-2)} > 3^{L^2+L-1}$, the inequality of Step 4. Theorem 4.1 is Theorem 8.1 for this
family with sharper explicit constants. For $L = 3$ ($1 \mapsto 110$, $0 \mapsto 101$; $m = 9$,
$N = 7$, $e = 2$) (C) reads $2^{42} > 9^{11}$, which holds: the seed of $w_3$ is irrational too,
although $w_3$ is not a survivor (Theorem 2.2).

### 8.3 Bounded observations (`verified-for-finite-domain`)

For every admissible morphism (H1)–(H3) with $2 \le L \le 5$, the script checks the Mahler
equation, $v_2(c_0 - c_1) = s$, the seed identity, the tower step, $D_k$ odd, the order $N$ and
unit leading coefficient of $R$, and $v_2(E_k) = NL^{k+1}$ at levels $k = 0, 1$.

| $L$ | admissible morphisms | identities verified | (C) holds |
|---|---|---|---|
| 2 | 1 | 1 | 0 |
| 3 | 6 | 6 | 2 |
| 4 | 27 | 27 | 11 |
| 5 | 110 | 110 | 52 |

The identity checks support the algebra of the proof; they are not evidence for irrationality
where (C) fails. Among the instances where (C) holds is $\sigma: 1 \mapsto 110,\ 0 \mapsto 011$
($t = 2$, $s = 0$, $e = 2$, $N = 6$; $2^{36} > 9^{11}$), the running example of `msharpe248/collatz`.

### 8.4 Where the criterion stops, and the next parameter to study

(C) fails when the periodic approximant is too short. The clearest case is $t = 1$
($\mu(1)$ begins with $10$): then $N = L + s < 2L$, while the approximant has degree $L$, so its
order is below the generic Padé order $2L + 1$. Examples: the Thue–Morse-type morphism
$1 \mapsto 10$, $0 \mapsto 01$ ($L = 2$, $A = 4$, $B = 3$, $N = 2$; $2^{4} < 4^{5}$) and
$1 \mapsto 101$, $0 \mapsto 011$ ($L = 3$, $N = 3$).

For such morphisms the method needs genuine Padé approximants $(p_0, p_1)$ of some degree $M$,
and the proof obligations change in three ways: (i) nonvanishing of $E_k$ needs
$v_2(c) < v_2(z_k)$ for the leading coefficient $c$, or a zero estimate; (ii) the ledger becomes
$2^{L(L-1)N} > m^{(L-1)M + L + e}$ up to constants; (iii) no closed form for the pair is known,
so each morphism needs its own finite certificate. Whether a certificate exists for
**every** admissible morphism is not settled here. The smallest instance beyond this
periodic-control criterion is $L = 2$, $1 \mapsto 10$, $0 \mapsto 01$, at $z = 4/3$.
Phase 7 excludes it in Lean by contraction and records stronger Padé certificates;
see `mahler-uncovered-morphisms.md`.

Within the issue's family there is no remaining parameter: all $L \ge 4$ are covered by
Theorem 4.1, and $L = 3$ by §8.2.

---

## 9. Shift tails

### Corollary 9.1 (`proven-by-algebra`; family case kernel-checked in Phase 6)
*Let $w$ be a word for which the conclusion of Theorem 4.1 or 8.1 holds (in particular $w = w_L$,
$L \ge 4$). Let $v$ be any infinite word such that $v(s + j) = w(t + j)$ for all $j \ge 0$, for some
$s, t \ge 0$. Then no rational number with odd denominator has itinerary $v$. In particular no
positive integer has an itinerary that eventually coincides with a tail of $w$.*

**Proof.** If $y = p/q$ ($q$ odd) has itinerary $v$, then $y' = T^s(y)$ is rational with the same
odd denominator (the step preserves it) and has itinerary $\sigma^t(w)$. The inverse branches
$T_0^{-1}(z) = 2z$ and $T_1^{-1}(z) = (2z-1)/3$ map $\mathbb{Z}_2\cap\mathbb{Q}$ into itself and
prepend the parity $0$, respectively $1$. Applying $T^{-1}_{w(t-1)}, \dots, T^{-1}_{w(0)}$ to $y'$
yields a rational with odd denominator and itinerary $w$: contradiction. $\blacksquare$

This is the argument of [`infinite-itineraries.md`](infinite-itineraries.md) Lemma 7.2 and
Corollary 7.3; it is independent of the word. A Rust test checks the inverse-branch
bookkeeping on prefixes of $w_5$.

**Scope.** For each $L$ the set of words covered by Corollary 9.1 is countable (a finite prefix
and a pair $(s, t)$), and so is the union over all $L \ge 4$ and over all morphisms satisfying
(C). The set of infinite survivor words has the cardinality of the continuum. A hypothetical
divergent Collatz orbit need not be eventually automatic, need not be a coefficient survivor
without CST, and is not addressed by any statement in this memo.

---

## 10. Literature and non-novelty

No originality is claimed for the method or for the results.

- **Method.** Mahler's method (K. Mahler, *Arithmetische Eigenschaften der Lösungen einer Klasse
  von Funktionalgleichungen*, Math. Ann. 101 (1929), 342–366; Ku. Nishioka, *Mahler Functions and
  Transcendence*, Lecture Notes in Mathematics 1631, Springer, 1996). The argument above is its
  most elementary form: an order-one inhomogeneous equation, an explicit approximant, and a
  valuation computation in place of a zero estimate.
- **Automatic digit expansions are a different object.** B. Adamczewski and Y. Bugeaud, *On the
  complexity of algebraic numbers I. Expansions in integer bases*, Ann. of Math. 165 (2007),
  547–565, treats numbers whose base-$b$ (or Hensel) *digits* are automatic. The seed
  $x(w) = -\sum_i 2^{d_i}/3^{i+1}$ is a value of an automatic power series at the non-integer
  point $A/B$; its 2-adic digits are not known to be automatic, so that theorem does not apply
  directly. The same remark is made in `msharpe248/collatz` (`analysis/RUNG1_ATTACK.md`).
- **`msharpe248/collatz`** (read at commit `ec8174b567d5cab4960024782210b5f5db02bd3a`, dated
  2026-09-06: `README.md`, `analysis/RUNG1_ATTACK.md`, `analysis/RESEARCH_STATUS.md`,
  `paper/rung1.tex`, `lean/Collatz/Rung1.lean`, `analysis/mahler_candidates.json`).
  - It proves, in Lean and on paper, the exclusion of the shifts of the fixed point of
    $\sigma: 1 \mapsto 110, 0 \mapsto 011$ for natural numbers
    (`no_shifted_sigWord_itinerary`); at this commit `Rung1.lean` contains no `sorry`.
  - `paper/rung1.tex` states that irrationality of $p$-adic Mahler values at rational points
    inside the unit disc "is a known type of result", citing Loxton–van der Poorten (J. Reine
    Angew. Math. 330 (1982), 159–172, as cited there) and Bundschuh–Väänänen, says no statement covering its
    specific value was located, and makes no priority claim for the irrationality itself.
  - It describes the extension to every constant-length substitution with equal block weights
    as a programme ("One theorem covers the class"; "A parametric Lean theorem with the
    certificate as an explicit input is the natural next formalization"), with the Padé
    certificate as an input to be found per word.
  - In the files listed above I found no mention of the morphisms $\mu_L$ for $L \ge 4$, of
    $11110/11101$, of the point $32/81$, or of a closed-form certificate such as (C). This is an
    absence-of-evidence statement about one commit, not a novelty claim.
  - **Correction to this repository's earlier memo.** [`infinite-itineraries.md`](infinite-itineraries.md)
    §2.3 says that `Rung1.lean` contains two `sorry` declarations and that the upstream README
    introduces the 4-uniform morphism $1110/1101$. Neither is true at commit `ec8174b`. The memo
    may describe an older upstream state; it should be re-dated or corrected.
- **What I did not find.** A published statement of Theorem 4.1 or of criterion (C). A handful
  of web searches for $p$-adic versions of Mahler's method at rational points returned the general
  references above and work on $p$-adic numbers with automatic digit expansions, not this
  result. The Bundschuh–Väänänen reference was not obtained and is cited only through the
  upstream paper. Given how short the proof is, the reasonable default is that results of this
  shape are known to specialists.

---

## 11. Open proof obligations

1. **Formalization.** Phase 6 completes Theorems 4.1 and 5.1 and the family case of
   Corollary 9.1 for every $L \ge 4$, using the integer-congruence reformulation;
   see [`lean-family-formalization.md`](lean-family-formalization.md). Phase 7
   now completes arbitrary-morphism Theorem 8.1 and all tails; see
   `lean-equal-weight-formalization.md`. The family's general symbolic survival
   and aperiodicity proofs and standalone formal-series/2-adic analytic
   statements remain written proofs.
2. **Morphisms failing (C)** (§8.4): Phase 7 excludes `10/01` in Lean and
   kernel-checks `101/011` using an improved periodic-control certificate;
   see `mahler-uncovered-morphisms.md`. General coverage remains open.
3. **Non-uniform or unequal-weight morphisms.** If the images have different numbers of ones,
   the block multiplier is not constant and the reduction to a single-variable Mahler equation
   at one rational point breaks down. Not investigated.
4. **Everything beyond countably many automatic words:** the Periodicity Conjecture, general
   survivor words, CST, and the Collatz conjecture are untouched.
