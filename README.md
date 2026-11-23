# palprimes

The aim of the project is to prove that **there are infinitely many palindromic primes in every
base b ≥ 2**.

## What is a palprime?

A *palindrome* is a number that reads the same forwards and backwards, like 121 or 7337.
A *prime* is a number greater than 1 that can only be divided evenly by 1 and by itself, like 2, 3, 5,
7, 11 or 13. A *palindromic prime*, or *palprime* for short, is a number that is both.

- The first palprimes are 2, 3, 5, 7, 11, 101, 131, 151, 181, 191, 313, 353, 373, 383, …
- 13 is a prime but not a palindrome (backwards it reads 31).
- 12321 is a palindrome but not a prime (it is 111 × 111).
- Apart from 11, every palprime has an odd number of digits. Every palindrome with an even number of
  digits, such as 1221 or 345543, is divisible by 11.

The same idea works in any base. In base 2 (binary), numbers are written with the digits 0 and 1:

- 5 is 101 in binary, 7 is 111, 17 is 10001 and 31 is 11111, so all four are binary palprimes.
- 11 is 1011 in binary, which is not a palindrome, so 11 is a palprime in base 10 but not in base 2.

Palprimes become rarer as the numbers grow. Whether they go on forever is still an open question
in every base.

This repository collects the results on the way there, with machine-checked proofs in Lean 4 where
available.

## Results

| Result | Status |
|---|---|
| Infinitely many palindromic primes in every base | open (the goal; `Palprimes.PalprimesInfinite b` in `lean/Palprimes/Statements.lean`) |
| **Infinitely many palindromes with at most 4 prime factors (with multiplicity) in every base b ≥ 2** | **proved in Lean** (`Palprimes.MT.infinite_palindromes_Omega_le_four`) |
| Stronger form: infinitely many palindromes n with Ω(n) ≤ 4 and every prime factor > n^{0.0326}. Among the palindromes with 2N + 1 digits coprime to b³ − b, at least a proportion c/log x, x = b^{2N+1}, are of this kind (c > 0 depends on b and is not explicit) | proved in Lean (`Palprimes.MT.infinite_palindromes_Omega_le_four_large_factors`, `Palprimes.MT.many_palindromes_Omega_le_four`) |
| Infinitely many palindromes with at most 5 prime factors (with multiplicity) in every base b ≥ 2 | proved in Lean (`Palprimes.infinite_palindromes_Omega_le_five`) |
| Stronger form: infinitely many palindromes n with Ω(n) ≤ 5 and every prime factor ≥ n^{1/20}. Among the palindromes with 2N + 1 digits coprime to b³ − b, at least a proportion 1/(40 log x), x = b^{2N+1}, are of this kind | proved in Lean (`Palprimes.infinite_palindromes_Omega_le_five_large_factors`, `Palprimes.many_palindromes_Omega_le_five`) |
| Palindromes have level of distribution θ = 0.2608 with weights 3^ω (moduli coprime to b³ − b) in every base b ≥ 2 | proved in Lean (`Palprimes.MT.level_piStar_theta`, from L¹ majorants; the elementary proof of 6/25 is `Palprimes.level_piStar_weighted`) |
| Prime-square divisors of palindromes: Σ_{x^{1/40} ≤ p ≤ x^{0.2499}} A_{p²} ≤ X/log³x (Proposition W) | proved in Lean (`Palprimes.squares_piStar2`; the range x^{1/20} to x^{23/100} is `Palprimes.squares_piStar`), the paper proof reaches any range up to x^{c}, c < 1/4 (`notes/PROP_W.md`) |
| Level of distribution 1/4 − ε for palindromes in every base, hence Ω ≤ 5 | paper proof (`papers/omega5-every-base`) |
| κ-palindromic primes: for every κ < 9/20 and every base there are infinitely many primes whose last ⌊κL/2⌋ digits mirror their first ⌊κL/2⌋ digits (L = number of digits). For bases that are powers of an odd prime, Harman (Acta Arith. 125, 2006) remarks without written proof that the method of preassigned digits reaches κ < 0.472, so the range 5/12 ≤ κ < 9/20 is new for b = 2 and the other bases | paper proof (`papers/kappa-palindromic-9-20`: `note.pdf`, full proof in `proof.md`) |
| The same on GRH for every κ < 2/3, with an asymptotic count | paper proof on GRH (`papers/grh-mirrored-primes`) |
| Function-field analogue: palindromic irreducible polynomials over F_q with coefficients in a restricted set S, asymptotic count for α_S < q^{−3/4} | paper proof (`papers/function-field`) |
| Almost primes with digits 0 and 1 in base r ≥ 3: level of distribution (#W)^{1/2−ε} (new for r ≥ 5), hence ≫ #W/log X such integers with at most k(r) ≤ 2 log₂ r + 1.13 prime factors (Dartyge–Mauduit 2000: k(r) ~ 8r/π), and k(4) = 4 (Dartyge–Mauduit: 5) | paper proof with interval-arithmetic certificates (`papers/digits01-almost-primes`) |
| Exact counts of palprimes in bases 2 to 16 up to 1.8·10¹⁹ | data (`data/palprime_counts.csv`) |

"Proved in Lean" means machine-checked as described under Verification. "Paper proof" means a written
proof that has passed independent audits within the project. These proofs have not been peer reviewed.

The GRH note uses the generalized Riemann hypothesis for Dirichlet L-functions. Levent Alpöge has
released a proof of it as a Lean library ([announcement](https://alpo.ge/remark.pdf)). The Lean and
Mathlib communities [certified the Lean verification of the Riemann hypothesis](https://leanprover-community.github.io/blog/posts/riemann-hypothesis/),
and this project treats GRH as a theorem.

The main theorem, as stated in `lean/Palprimes/Omega4/Final.lean`:

```lean
theorem infinite_palindromes_Omega_le_four (b : ℕ) (hb : 2 ≤ b) :
    {n : ℕ | IsPalindrome b n ∧ Nat.IsAtMostAlmostPrime 4 n}.Infinite
```

Here `IsPalindrome b n` means `(Nat.digits b n).reverse = Nat.digits b n`, and Mathlib's
`Nat.IsAtMostAlmostPrime 4 n` means `n ≠ 0 ∧ Ω n ≤ 4`. GRH is not used.

The proof combines Greaves' weighted sieve (Acta Arith. 40 (1982), Theorem 1) with a level of
distribution θ = 0.2608 for palindromes in every base. The level comes from L¹ bounds for the digit
exponential sums (TL¹), obtained from trigonometric majorants: an explicit Fejér family for b ≥ 10,
and computer-found majorants for b = 2 to 9, whose inequalities are checked by the Lean kernel
(`decide +kernel`, no `native_decide`). The other ingredients are Greaves' Lemma 4.2 (the
Rosser–Iwaniec linear sieve asymptotic, `Palprimes/E1/`), the main-term limit and its positivity
(`Palprimes/MainTerm/`), and Proposition W for prime squares up to x^{0.2499}.

The Ω ≤ 5 theorem, in `lean/Palprimes/AlmostPrime/OmegaLeFive.lean`, has a shorter proof (Richert
weights and level 6/25):

```lean
theorem infinite_palindromes_Omega_le_five (b : ℕ) (hb : 2 ≤ b) :
    {n : ℕ | IsPalindrome b n ∧ Nat.IsAtMostAlmostPrime 5 n}.Infinite
```

The stronger forms, in `lean/Palprimes/AlmostPrime/OmegaLeFiveCount.lean`:

```lean
theorem infinite_palindromes_Omega_le_five_large_factors (b : ℕ) (hb : 2 ≤ b) :
    {n : ℕ | IsPalindrome b n ∧ Nat.IsAtMostAlmostPrime 5 n ∧
      ∀ p ∈ n.primeFactors, (n : ℝ) ^ ((1 : ℝ) / 20) ≤ (p : ℝ)}.Infinite

theorem many_palindromes_Omega_le_five (b : ℕ) (hb : 2 ≤ b) :
    ∃ N₀, ∀ N ≥ N₀,
      1 / 40 * ((#(piStar b N) : ℝ) / Real.log ((b : ℝ) ^ (2 * N + 1))) ≤
        (#((piStar b N).filter (fun n => Nat.IsAtMostAlmostPrime 5 n ∧
          ∀ p ∈ n.primeFactors, ((b : ℝ) ^ (2 * N + 1)) ^ ((1 : ℝ) / 20) ≤ (p : ℝ))) : ℝ)
```

`piStar b N` is the set of base-b palindromes with exactly 2N + 1 digits that are coprime to b³ − b.

## Verification

The proof uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`. It has no
`sorry`, no `native_decide` and no custom axioms. It passed the following checks (`notes/LEAN_AUDIT.md`):

- **Kernel replay:** `leanchecker` on every module, and `leanchecker --fresh Palprimes.Omega4.Final`
  (the whole closure, Mathlib included, replayed from an empty environment).
- **Comparator:** `lake comparator --paranoid` against `lean/Audit/Challenge.lean`, which states the
  seven theorems (Ω ≤ 5 and Ω ≤ 4, each with its counting and large-factor forms, and the level of
  distribution) with Mathlib definitions only. Five kernels accept all seven: Lean, Lean paranoid,
  nanoda, lean4lean and con-leche. con-ron accepts the Ω ≤ 5 theorems but runs out of memory (over
  40 GB) on four `decide +kernel` certificates of the Ω ≤ 4 proof, comparisons of powers with up to
  about 45 million bits, so it gives no verdict on the Ω ≤ 4 theorems.

To reproduce, with Lean and Mathlib v4.37.0-rc1:

```bash
cd lean
lake exe cache get
lake build
lake env lean scripts/axioms.lean
lake build Audit && lake comparator --config Audit/comparator.json --paranoid
```

The Ω ≤ 4 proof is large (about 39k lines in total, 244 modules). The kernel check of the base-2 and
base-3 majorant certificates (`Palprimes/Major2D/`) takes about 1.5 hours on one core, and the
comparator about 3 hours for its first kernel (Lean paranoid). Build `Palprimes/Major2D/` with few
parallel jobs, since a certificate module can need up to about 12 GB of memory. `lake build` overflows its stack for import depth
≥ 22; the library is at depth 21.

Run `leanchecker` with explicit module names only, for example
`lake env leanchecker Palprimes.AlmostPrime.OmegaLeFive`. Without a module name it checks all
modules in parallel, each loading Mathlib, and needs a lot of memory.

## Layout

```
lean/                    Lean 4 project (library Palprimes, about 39k lines)
  Palprimes/Defs.lean        palindromes, Π*_b, exponential-sum notation
  Palprimes/Statements.lean  target statements (definitions only)
  Palprimes/Digits/          digit API, Lemma 3 (injectivity), counting Π*_b
  Palprimes/ExpSum/          collision counts, large sieve, Farey sums, Col's bound
  Palprimes/Level/           divisor bound, level of distribution
  Palprimes/Squares/         Proposition W
  Palprimes/Sieve/           Mertens and Selberg (vendored from PNT+), weighted sieve, certificate
  Palprimes/AlmostPrime/     the Ω ≤ 5 theorems (existence, count, large prime factors)
  Palprimes/Greaves/         Greaves 1982: Brun's identity for the weighted Rosser sum, Lemmas 3.1-3.3
  Palprimes/E1/              Greaves' Lemma 4.2 (Rosser-Iwaniec linear sieve asymptotic)
  Palprimes/MainTerm/        Greaves' main term, its limit and positivity
  Palprimes/TL1/             block majorants, TL¹ criterion, level of distribution θ = 0.2608
  Palprimes/Major/           TL¹ for b ≥ 10 (Fejér family)
  Palprimes/Major1D/         TL¹ for b = 4 to 9 (kernel-checked 1D majorants, generated data)
  Palprimes/Major2D/         TL¹ for b = 2, 3 (kernel-checked 2D block majorants, generated data)
  Palprimes/Omega4/          the Ω ≤ 4 theorem (assembly) and its corollaries
  Audit/                     comparator challenge and solution
  scripts/                   certificate generators (omega4/: the Ω ≤ 4 majorants), axiom check
papers/                  paper drafts (TeX and PDF, or Markdown)
  omega5-every-base/         Palindromes with at most five prime factors in every base
  kappa-palindromic-9-20/    κ-palindromic primes for κ < 9/20 (Heath-Brown–Iwaniec method)
  grh-mirrored-primes/       Primes with mirrored digits on GRH (κ < 2/3)
  function-field/            Palindromic irreducible polynomials with restricted coefficients
  digits01-almost-primes/    Almost primes with digits 0 and 1 in every base (Dartyge–Mauduit problem)
notes/                   the mathematics behind the Lean proof: proofs, sieve route, plan, audit
data/                    exact palprime counts (base, digits, palindromes, palprimes)
numerics/                Python checks used to design the sieve and audit Proposition W,
                         and the C programs that produced the counts
```

`lean/Palprimes/Sieve/Certificate.lean` is generated. To regenerate it, run
`python3 scripts/gen_cert.py && python3 scripts/gen_lean.py` in `lean/`. The majorant certificates of
`Palprimes/Major1D/` and `Palprimes/Major2D/` are generated by `lean/scripts/omega4/regen.sh`
(details in `lean/scripts/omega4/README.md`); the output is identical byte for byte.

## Credits and license

The Mertens and Selberg sieve files are adapted from
[PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) (see `NOTICE`).
The palindrome results build on Tuxanidy and Panario (arXiv 2307.16637).

Licensed under the Apache License 2.0 (`LICENSE`).
