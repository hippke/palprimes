# Almost primes with digits 0 and 1 in every base

Paper: `paper.pdf` (source `paper.tex`). Repository: https://github.com/hippke/palprimes, folder
`papers/digits01-almost-primes`.

## Statement

Let r ≥ 3, X = r^s, and let W be the set of integers below X whose base-r digits are all 0 or 1 and
whose last digit is 1 (so #W = X^λ/2 with λ = log 2/log r).

- **Level of distribution.** For every θ < λ/2 = log 2/(2 log r), W is equidistributed in residue
  classes on average over the moduli q ≤ X^θ coprime to r, uniformly in the class, with saving
  exp(−c√log X). This is a level (#W)^{1/2−ε}. For r = 3 and r = 4, certified block majorants give the
  levels 0.35368507 and 0.26029616.
- **Almost primes.** Combined with Greaves' weighted sieve (Acta Arith. 40, 1982), W contains
  ≫ #W/log X elements with at most k(r) prime factors (counted with multiplicity) and no prime factor
  below X^c, where k(r) ≤ 2 log₂ r + 1.13 for every r ≥ 3, k(3) = 3 and k(4) = 4.
  The bound of Dartyge and Mauduit (J. Number Theory 81, 2000) is k(r) ~ 8r/π.

| r | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 12 | 16 | 20 | 50 | 100 | 1000 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| k(r) | 3 | 4 | 5 | 6 | 6 | 7 | 7 | 7 | 8 | 9 | 9 | 12 | 14 | 21 |

## Status

Proof written out in `paper.pdf`, not peer reviewed. The numerical certificates for r = 3, 4 and the
table of k(r) are reproducible with `scripts/run_all.py`.

Relation to known results (Dartyge–Mauduit, J. Number Theory 81 (2000) and 91 (2001), Konyagin,
Period. Math. Hungar. 42 (2001)).
- The level (#W)^{1/2−ε} is new for r ≥ 5. For r = 3 Dartyge–Mauduit 2000 already have (#W)^{1/2} and
  Dartyge–Mauduit 2001 have X^{0.342}, for r = 4 Dartyge–Mauduit 2001 have X^{1/4} = (#W)^{1/2}. Their
  2000 levels for r ≥ 4 are below λ/2 (0.1769 for r = 4, asymptotically π/(4r)), and Konyagin's general
  level X^c has a small c.
- The bound k(r) ≤ 2 log₂ r + 1.13 (against k(r) ~ 8r/π) and k(4) = 4 (against k(4) = 5) are new as far as
  we know. Dartyge–Mauduit 2001 note that their level X^{1/4} for r = 4 is not enough for four prime factors.
- k(3) = 3 is due to Dartyge–Mauduit 2001. The certified level 0.35368507 for r = 3 exceeds their 0.342.
- The certified levels for r = 3, 4 rely on computer-verified inequalities (interval arithmetic, below).
  The exact level λ/2 for all r needs no computation.

## Files

- `paper.tex`, `paper.pdf`: the paper (amsart).
- `data/majorant_r3_l4.json`, `data/majorant_r4_l4.json`: block majorants T(t) = τ₀ + 2 Σ τ_u cos(2πut),
  τ_u = ints[u]/2^50 exactly, blocks of l = 4 digits, exponent p = 99/100. `data/SHA256SUMS`.
- `scripts/certify.py`: rigorous certificate (python-flint/Arb ball arithmetic) of T ≥ K_4^p on R and of
  the level ψ_T = −log_r(τ₀)/4. An optional second argument shifts ints[0] (negative control).
- `scripts/neg_control.py`: lowers τ₀ by 10⁻⁶ and exhibits a point where the shifted T is not a majorant.
- `scripts/greaves_k.py`: Greaves' constants δ_R, parameter checks, the table of k(r), the bound
  k(r) ≤ 2 log₂ r + 1.13 for 3 ≤ r ≤ 5000, the square-lemma conditions and the side condition for r = 3, 4.
- `scripts/theory_checks.py`: numerical controls of the lemmas (not part of the proofs).
- `scripts/prop_h_test.py`: direct numerical test of Proposition 4.4, of the condition k ≤ r − 1 in Lemma 4.2
  and of Lemma 4.5.
- `scripts/run_all.py`: runs all of the above and writes `logs/`.
- `logs/`: outputs of one full run.

## Reproduction

Requirements: Python 3.9+, python-flint (tested with 0.9.0), numpy, mpmath.

```
python -I scripts/run_all.py
```

Runtime about one to four minutes on one core. The certificates take below 1 s each. Expected results (see
`logs/`):

- `certify.log`: r = 3, 745 intervals, ψ_T ∈ 0.353685071115, CERTIFIED=True. r = 4, 925 intervals,
  ψ_T ∈ 0.260296167808, CERTIFIED=True. Both negative controls CERTIFIED=False and REFUTED=True.
- `certify_sensitivity.log`: τ₀ − 2·10⁻⁹ fails, τ₀ − 2·10⁻¹⁰ still certifies.
- `prop_h_test.log`: max S(D)/bound = 1.5e−2 over 80 cases, all ok=True.
- `greaves_k.log`: thresholds 1/(R − δ_R) = 0.3448269, 0.2574977, 0.2050032, … and the k(r) table above.
