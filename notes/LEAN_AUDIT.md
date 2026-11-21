# Audit of the Ω ≤ 5 theorem (2026-11-21 evening)

The audit was run on the development tree, where the theorem was named `PalLean.infinite_palindromes_omega_le_five`. In this repository it is `Palprimes.infinite_palindromes_Omega_le_five`. The checks were repeated on this repository before the first push (see the end of this file).

Theorem (Main.lean): `∀ b ≥ 2, {n | IsPalindrome b n ∧ Nat.IsAtMostAlmostPrime 5 n}.Infinite`.
`IsPalindrome b n := (Nat.digits b n).reverse = Nat.digits b n` (Defs.lean:31).
Toolchain: Lean / Mathlib v4.37.0-rc1.

| Check | Result |
|---|---|
| `#print axioms` | `propext`, `Classical.choice`, `Quot.sound` only |
| grep for `sorry`, `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe`, `opaque`, `debug.skipKernelTC` | none in proofs (`sorry` occurs only in comments) |
| Dependencies | all packages at their official tags (mathlib v4.37.0-rc1 = 31ce06ea), clean `git status` |
| Reference restatement (`scratch/RefCheck.lean`) | plain-Mathlib target (digits palindrome, n ≠ 0, length of `primeFactorsList` ≤ 5) follows by unfolding; non-triviality checks pass |
| Adversarial review (Fable, high effort; `scratch/adv_*.lean`) | statement faithful; exact binders `(b : ℕ) (hb : 2 ≤ b)`; chain lemmas closed; section hypotheses (Mertens) discharged inside `sieve_omega_le_five`; `IsPalindrome` agrees with `Nat.toDigits` for b ≤ 14, n < 20000 |
| `leanchecker` (replay from imports) | all 24 PalLean modules accepted, exit 0 |
| `lake comparator --paranoid` (`audit/comparator.json`, `audit/comparator2.out`) | **accepted**, sandboxed: statement identical to `PalLean/Audit/Challenge.lean` (Mathlib only, `sorry`), axioms whitelisted, kernels Lean default, Lean paranoid, nanoda, lean4lean, con-ron, con-leche all accept (≈ 61k declarations, 411 s) |
| `leanchecker --fresh PalLean.Main` | **accepted**, exit 0 after 1206 s: the full closure, Mathlib included, replayed through the kernel from an empty environment |

## Caveats
- Comparator assumes a clean build (no pre-existing `.lake`). Here it reused the existing build artefacts. A run from a fresh clone is the next step for full isolation.
- Trusted: Mathlib and the toolchain, plus `lakefile.toml` and `lake-manifest.json`.

## Minor findings (no effect on the theorem)
1. A stale `Statement.olean` from the old skeleton (a `sorry` version) was still importable in the development tree. Deleted, and absent from this repository.
2. `autoImplicit` was on during development. This repository sets `autoImplicit = false`, and everything builds with it.
3. The header of the weighted-sieve file still described M14 as open. Fixed (`Sieve/Weighted.lean`).

## Incident
A `leanchecker --help` call caused the OOM kill of the app. leanchecker treats `--help` as an unknown flag, so with no module given it checks every PalLean module in parallel, each with its own copy of Mathlib. Always pass explicit module names and run under `systemd-run --user --scope -p MemoryMax=…`.

## Re-check on this repository (before the first push)
- `lake build` with `autoImplicit = false`: success. `scripts/axioms.lean`: `propext`, `Classical.choice`,
  `Quot.sound` only, for both `infinite_palindromes_Omega_le_five` and `almostPalprimesInfinite_five`.
- `leanchecker` on each of the 26 modules (`Palprimes.*`, `Audit.*`): all accepted.
- `lake comparator --config Audit/comparator.json --paranoid`: **accepted**, sandboxed. The statement
  matches `Audit/Challenge.lean`, the axioms are whitelisted, and all six kernels accept (Lean default,
  Lean paranoid, nanoda, lean4lean, con-ron, con-leche).
- `scripts/gen_cert.py` and `scripts/gen_lean.py` regenerate `Sieve/Certificate.lean` byte for byte.
