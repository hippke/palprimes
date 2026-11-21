# palprimes

The aim of the project is to prove that **there are infinitely many palindromic primes in every
base b ≥ 2**. This repository collects the results on the way there, with machine-checked proofs in
Lean 4 where available.

## Results

| Result | Status |
|---|---|
| Infinitely many palindromic primes in every base | open (the goal; `Palprimes.PalprimesInfinite b` in `lean/Palprimes/Statements.lean`) |
| **Infinitely many palindromes with at most 5 prime factors (with multiplicity) in every base b ≥ 2** | **proved in Lean** (`Palprimes.infinite_palindromes_Omega_le_five`) |
| Palindromes have level of distribution 6/25 with weights 3^ω (moduli coprime to b³ − b) | proved in Lean (`Palprimes.level_piStar_weighted`), the paper proof reaches any θ < 1/4 (`notes/PROOF_buniform.md`) |
| Prime-square divisors of palindromes: Σ_{x^{1/20} ≤ p ≤ x^{23/100}} A_{p²} ≤ X/log³x (Proposition W) | proved in Lean (`Palprimes.squares_piStar`), the paper proof reaches any range up to x^{c}, c < 1/4 (`notes/PROP_W.md`) |

The main theorem, as stated in `lean/Palprimes/AlmostPrime/OmegaLeFive.lean`:

```lean
theorem infinite_palindromes_Omega_le_five (b : ℕ) (hb : 2 ≤ b) :
    {n : ℕ | IsPalindrome b n ∧ Nat.IsAtMostAlmostPrime 5 n}.Infinite
```

Here `IsPalindrome b n` means `(Nat.digits b n).reverse = Nat.digits b n`, and Mathlib's
`Nat.IsAtMostAlmostPrime 5 n` means `n ≠ 0 ∧ Ω n ≤ 5`.

## Verification

The proof uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`. It has no
`sorry`, no `native_decide` and no custom axioms. It passed the following checks (`notes/LEAN_AUDIT.md`):

- **Kernel replay:** `leanchecker` on every module.
- **Comparator:** `lake comparator --paranoid` against `lean/Audit/Challenge.lean`, which states the
  theorem with Mathlib definitions only. Six kernels accept it: Lean, Lean paranoid, nanoda,
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
lean/                    Lean 4 project (library Palprimes, about 12.6k lines)
  Palprimes/Defs.lean        palindromes, Π*_b, exponential-sum notation
  Palprimes/Statements.lean  target statements (definitions only)
  Palprimes/Digits/          digit API, Lemma 3 (injectivity), counting Π*_b
  Palprimes/ExpSum/          collision counts, large sieve, Farey sums, Col's bound
  Palprimes/Level/           divisor bound, level of distribution
  Palprimes/Squares/         Proposition W
  Palprimes/Sieve/           Mertens and Selberg (vendored from PNT+), weighted sieve, certificate
  Palprimes/AlmostPrime/     the Ω ≤ 5 theorem
  Audit/                     comparator challenge and solution
  scripts/                   certificate generators, axiom check
notes/                   the mathematics: proofs, sieve route, plan, audit
numerics/                Python checks used to design the sieve and audit Proposition W
```

`lean/Palprimes/Sieve/Certificate.lean` is generated. To regenerate it, run
`python3 scripts/gen_cert.py && python3 scripts/gen_lean.py` in `lean/`.

## Credits and license

The Mertens and Selberg sieve files are adapted from
[PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) (see `NOTICE`).
The palindrome results build on Tuxanidy and Panario (arXiv 2307.16637).

Licensed under the Apache License 2.0 (`LICENSE`).
