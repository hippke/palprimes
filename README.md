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
| **Infinitely many palindromes with at most 5 prime factors (with multiplicity) in every base b ≥ 2** | **proved in Lean** (`Palprimes.infinite_palindromes_Omega_le_five`) |
| Stronger form: infinitely many palindromes n with Ω(n) ≤ 5 and every prime factor ≥ n^{1/20}. Among the palindromes with 2N + 1 digits coprime to b³ − b, at least a proportion 1/(40 log x), x = b^{2N+1}, are of this kind | proved in Lean (`Palprimes.infinite_palindromes_Omega_le_five_large_factors`, `Palprimes.many_palindromes_Omega_le_five`) |
| Palindromes have level of distribution 6/25 with weights 3^ω (moduli coprime to b³ − b) | proved in Lean (`Palprimes.level_piStar_weighted`), the paper proof reaches any θ < 1/4 (`notes/PROOF_buniform.md`) |
| Prime-square divisors of palindromes: Σ_{x^{1/20} ≤ p ≤ x^{23/100}} A_{p²} ≤ X/log³x (Proposition W) | proved in Lean (`Palprimes.squares_piStar`), the paper proof reaches any range up to x^{c}, c < 1/4 (`notes/PROP_W.md`) |
| Level of distribution 1/4 − ε for palindromes in every base, hence Ω ≤ 5 | paper proof (`papers/omega5-every-base`) |
| κ-palindromic primes: for every κ < 9/20 and every base there are infinitely many primes whose last ⌊κL/2⌋ digits mirror their first ⌊κL/2⌋ digits (L = number of digits) | paper proof (`papers/kappa-palindromic-9-20`) |
| The same on GRH for every κ < 2/3, with an asymptotic count | paper proof on GRH (`papers/grh-mirrored-primes`) |
| Function-field analogue: palindromic irreducible polynomials over F_q with coefficients in a restricted set S, asymptotic count for α_S < q^{−3/4} | paper proof (`papers/function-field`) |
| Exact counts of palprimes in bases 2 to 16 up to 1.8·10¹⁹ | data (`data/palprime_counts.csv`) |

"Proved in Lean" means machine-checked as described under Verification. "Paper proof" means a written
proof that has passed independent audits within the project. These proofs have not been peer reviewed.

The GRH note uses the generalized Riemann hypothesis for Dirichlet L-functions. Levent Alpöge has
released a proof of it as a Lean library ([announcement](https://alpo.ge/remark.pdf)). The Lean and
Mathlib communities [certified the Lean verification of the Riemann hypothesis](https://leanprover-community.github.io/blog/posts/riemann-hypothesis/),
and this project treats GRH as a theorem.

The main theorem, as stated in `lean/Palprimes/AlmostPrime/OmegaLeFive.lean`:

```lean
theorem infinite_palindromes_Omega_le_five (b : ℕ) (hb : 2 ≤ b) :
    {n : ℕ | IsPalindrome b n ∧ Nat.IsAtMostAlmostPrime 5 n}.Infinite
```

Here `IsPalindrome b n` means `(Nat.digits b n).reverse = Nat.digits b n`, and Mathlib's
`Nat.IsAtMostAlmostPrime 5 n` means `n ≠ 0 ∧ Ω n ≤ 5`.

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

- **Kernel replay:** `leanchecker` on every module.
- **Comparator:** `lake comparator --paranoid` against `lean/Audit/Challenge.lean`, which states the
  three theorems with Mathlib definitions only. Six kernels accept them: Lean, Lean paranoid, nanoda,
  lean4lean, con-ron and con-leche.

To reproduce, with Lean and Mathlib v4.37.0-rc1:

```bash
cd lean
lake exe cache get
lake build
lake env lean scripts/axioms.lean
lake build Audit && lake comparator --config Audit/comparator.json --paranoid
```

Run `leanchecker` with explicit module names only, for example
`lake env leanchecker Palprimes.AlmostPrime.OmegaLeFive`. Without a module name it checks all
modules in parallel, each loading Mathlib, and needs a lot of memory.

## Layout

```
lean/                    Lean 4 project (library Palprimes, about 13k lines)
  Palprimes/Defs.lean        palindromes, Π*_b, exponential-sum notation
  Palprimes/Statements.lean  target statements (definitions only)
  Palprimes/Digits/          digit API, Lemma 3 (injectivity), counting Π*_b
  Palprimes/ExpSum/          collision counts, large sieve, Farey sums, Col's bound
  Palprimes/Level/           divisor bound, level of distribution
  Palprimes/Squares/         Proposition W
  Palprimes/Sieve/           Mertens and Selberg (vendored from PNT+), weighted sieve, certificate
  Palprimes/AlmostPrime/     the Ω ≤ 5 theorems (existence, count, large prime factors)
  Audit/                     comparator challenge and solution
  scripts/                   certificate generators, axiom check
papers/                  paper drafts (TeX and PDF, or Markdown)
  omega5-every-base/         Palindromes with at most five prime factors in every base
  kappa-palindromic-9-20/    κ-palindromic primes for κ < 9/20 (Heath-Brown–Iwaniec method)
  grh-mirrored-primes/       Primes with mirrored digits on GRH (κ < 2/3)
  function-field/            Palindromic irreducible polynomials with restricted coefficients
notes/                   the mathematics behind the Lean proof: proofs, sieve route, plan, audit
data/                    exact palprime counts (base, digits, palindromes, palprimes)
numerics/                Python checks used to design the sieve and audit Proposition W,
                         and the C programs that produced the counts
```

`lean/Palprimes/Sieve/Certificate.lean` is generated. To regenerate it, run
`python3 scripts/gen_cert.py && python3 scripts/gen_lean.py` in `lean/`.

## Credits and license

The Mertens and Selberg sieve files are adapted from
[PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) (see `NOTICE`).
The palindrome results build on Tuxanidy and Panario (arXiv 2307.16637).

Licensed under the Apache License 2.0 (`LICENSE`).
