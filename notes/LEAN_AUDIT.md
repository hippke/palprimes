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

## Strengthening (counting form and large prime factors)
New theorems `many_palindromes_Omega_le_five` (at least #Π*_b(2N)/(40 log x) palindromes with Ω ≤ 5 and all
prime factors ≥ x^{1/20}) and `infinite_palindromes_Omega_le_five_large_factors` (infinitely many palindromes
n with Ω(n) ≤ 5 and all prime factors ≥ n^{1/20}). Checks after adding them:
- `scripts/axioms.lean`: standard axioms only for all four headline theorems.
- `leanchecker` on each of the 28 modules: all accepted.
- `lake comparator --paranoid` with three theorems in `Audit/Challenge.lean` (Mathlib definitions only, Π*_b written out):
  **accepted**, sandboxed, statements match, axioms whitelisted, all six kernels accept.

# Audit of the Ω ≤ 4 theorem (2026-11-22)

Theorem (`Palprimes/Omega4/Final.lean`): `Palprimes.MT.infinite_palindromes_Omega_le_four (b : ℕ) (hb : 2 ≤ b) :
{n | IsPalindrome b n ∧ Nat.IsAtMostAlmostPrime 4 n}.Infinite`, and `almostPalprimesInfinite_four`.
Same toolchain (Lean / Mathlib v4.37.0-rc1). Closure of Final: 240 Palprimes modules, import depth 19,
the root `Palprimes.lean` at depth 20 (`lake build` overflows its stack at depth ≥ 22, so MainTerm/Approx1
was merged into Approx2 and Tuples2 into Tuples3). The superseded `Omega4/Ge4.lean` (b ≥ 4, conditional on
Greaves' Lemma 4.2) and `Omega4/Uncond4.lean` (b ≥ 4) are not in the repository. Audit budget: 4 cores,
64 GB. Logs in the development tree (`lean/audit4/`).

| Check (item of the 7-point list) | Result |
|---|---|
| `#print axioms` (3) | `propext`, `Classical.choice`, `Quot.sound` only, for both headline theorems |
| Extended grep (3, 5) | no `sorry`, `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe`, `opaque`, `debug.*`, `reduceBool`, `trustCompiler`, `initialize`, `import all`. Benign hits: one tactic macro (`Sieve/Certificate.lean:32`), three Decidable instances in `Greaves/Brun.lean` (one `Classical.dec`), `local notation3` and `quotPrecheck false` in the vendored Selberg file, `exponentiation.threshold` in `Major2D/Sound.lean:599` |
| Environment scan (`adv/Scan.lean`) (3, 5) | all 6352 constants of the 240 loaded Palprimes modules: 0 axioms, 0 opaques, 0 `Quot` constants; the 39 "unsafe/partial" entries are compiler-generated `_unsafe_rec` auxiliaries; 1 name outside the `Palprimes` root (Mathlib's auto-generated `Nat.primeFactors.eq_def`); only Lake utility modules load besides Init/Std/Lean/Mathlib/Batteries/Aesop/Qq; the orphan `MainTerm/Probe*.olean` are not loaded |
| Statement faithfulness (4, 5) | `RefCheck4.lean`: plain-Mathlib restatement `¬ Set.Finite {n | digits palindrome ∧ n ≠ 0 ∧ (primeFactorsList n).length ≤ 4}` follows by unfolding, standard axioms; `pp.all` prints of the theorem, `IsPalindrome`, `IsAtMostAlmostPrime`; 8 sanity examples (121 palindrome, 120 and 6 in base 2 not, 0 excluded, 1 included, 32 has Ω = 5) all pass. `Audit/Challenge.lean` gets a fourth theorem `palindromes_omega_le_four`, Mathlib only, root namespace |
| Intermediate statements (6) | `tl1_all` dispatches b = 2, 3, 4..9, ≥ 10 to `tl1_two`, `tl1_three`, `tl1_small`, `tl1_ge_ten`; no hypothesis is left. The Boolean checkers of Major2D are linked inside the type theory (`chk2 : checkList cfg2 L2 = true` consumed by `good_all`), so data and soundness lemma share the same constants |
| Dependencies, stale oleans (2, 7) | all 9 packages at manifest revisions, clean; mathlib = tag v4.37.0-rc1 (31ce06ea). `adv/srchash.py` recomputes Lake's source hash for all 246 modules: 0 mismatches; no olean older than an import |
| `leanchecker` per module (1, 2) | all 244 current Palprimes modules + `Audit.Challenge` + `Audit.Solution` accepted (14 modules rebuilt after the depth merge re-checked, `lc2_summary.txt`); about 6200 s kernel time, 5444 s of it Major2D; peak 12.2 GB |
| `lake comparator --paranoid` (1, 4, 3) | statements of all four challenge theorems match and the axioms are whitelisted (the comparator runs `compareStatements` and `checkAxioms` before any kernel and aborts on failure). Lean paranoid kernel **accepts** (11354 s wall, 16 GB). The comparator was then stopped so the remaining kernels could run in parallel, so it wrote no final JSON report |
| Other five kernels, in parallel (1) | same export (`solution_export.ndjson`, copy of the comparator's own export, identical sha256), same command lines and bwrap sandbox as `Lake/CLI/Check.lean` (`kern/run_one.sh`), each kernel in its own memory-capped scope (`kern/summary.txt`): nanoda **accepts** (exit 0, 6785 s, 12.8 GB); lean4lean **accepts** ("checked 65276 declarations", 8294 s, 13.5 GB); Lean default **accepts** (exit 0, 4794 s, 13.8 GB); con-leche **accepts** ("accepted 65279 declarations (--verified)", 6923 s, 13.4 GB; run with `--jobs=1`, since its default of one worker per hardware thread exceeded 24 GB). con-ron gives **no verdict**: it runs out of memory on the four `decide +kernel` power certificates `cond2_2`, `cond3_2` (`Major2D/B2Light.lean`) and `cond2_3`, `cond3_3` (`Major2D/B3Light.lean`), comparisons of powers such as `358572778288936^937500` (≈ 45 million bits). Isolated in a small export, `cond2_3` alone (≈ 3 million bits) takes con-ron over 16 GB in 30 s, while con-leche accepts each of the four in about 1 s. The full con-ron run reached 61020 of 65279 declarations before `cond2_2` and was stopped by the 40 GB cap (also with `--jobs=1`) |
| `leanchecker --fresh Palprimes.Omega4.Final` (1, 2) | **accepted**, exit 0, no output, after 11563 s wall (peak 19.3 GB): the full closure, Mathlib included, replayed through the kernel from an empty environment |
| Adversarial review (Fable, `adv/ADV_REPORT.md`) | no critical or major finding; minor findings below |

## Minor findings
1. The Ω ≤ 4 development was untracked in git during the audit, so "unchanged against the published
   commit" covered only the Ω ≤ 5 part. Committed after the audit, with no change to the audited sources
   apart from removing the two superseded files and adding the import to the root module.
2. Sources changed during the per-module replay (the depth merge). All current oleans were replayed after
   their last build (14 modules re-checked).
3. Orphan oleans `MainTerm/Probe.olean`, `Probe2.olean`, `Probe3.olean` without source; not loaded by Final.
4. Residual trust in the kernel's GMP Nat arithmetic: 367 `decide +kernel` (130 files in Major2D), up to a
   ≈ 45-million-bit power in `B2Light.cond2_2`. Mitigation: nanoda, lean4lean and con-leche check all of them
   independently; con-ron cannot (memory, see the kernel row).

## Corollaries (2026-11-23)
New module `Palprimes/Omega4/Corollaries.lean` (100 lines, no new mathematics, only assembly of audited
lemmas): `level_piStar_theta` (level θ = 0.2608 with weights 3^ω, moduli coprime to b³ − b),
`many_palindromes_Omega_le_four` (at least c · #Π*_b(2N)/log x palindromes with Ω ≤ 4 and all prime factors
> x^{0.0326}, 0.0326 = θ T₀, T₀ = 1/8) and `infinite_palindromes_Omega_le_four_large_factors`. The root module
is now at import depth 21. `Audit/Challenge.lean` states seven theorems. Logs in `lean/audit5/`.
- `scripts/axioms.lean`: `propext`, `Classical.choice`, `Quot.sound` only, for all nine headline theorems.
- `leanchecker` on `Palprimes.Omega4.Corollaries`, `Audit.Challenge`, `Audit.Solution`: accepted (exit 0, no
  output). All other modules are unchanged since the Ω ≤ 4 audit.
- `lake comparator` (Lean default kernel, sandboxed): statements of all seven theorems match, axioms
  whitelisted, **accepted** ("Your solution is okay!", 4793 s, 15 GB).
- Other kernels on the comparator's export, same command lines and sandbox, each in its own memory-capped
  scope (`kern/summary.txt`): Lean paranoid **accepts** (exit 0, 7644 s, 15.0 GB); lean4lean **accepts**
  ("checked 65292 declarations", 16589 s, 13.3 GB, two kernels sharing two cores); nanoda **accepts**
  (exit 0, 9550 s, 13.1 GB); con-leche **accepts** ("accepted 65295 declarations (--verified)", `--jobs=1`,
  6711 s, 13.4 GB). con-ron not rerun (same power certificates as before, no verdict).
