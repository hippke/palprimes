# Audit of the Ω ≤ 3 theorem (2026-11-24, host2)

Package `/astro/palindromic-primes/lean/omega3/main` (lake package `Omega3`, Lean/Mathlib v4.37.0-rc1),
path dependency on `palprimes/lean` (library `Palprimes`, git clean at b42f86c) and its Mathlib checkout.
Theorems (`Omega3/Final.lean`):
- `Omega3.infinite_palindromes_Omega_le_three (b) (hb : 5 ≤ b) : {n | Palprimes.IsPalindrome b n ∧ Nat.IsAtMostAlmostPrime 3 n}.Infinite`
- `Omega3.many_palindromes_Omega_le_three` (at least `c 3^N / log x` elements of `Π*_b(2N)` with `Ω ≤ 3` and all prime factors `> x^{1/250}`)
- `Omega3.infinite_palindromes_Omega_le_three_large_factors` (`Ω ≤ 3`, all prime factors `> n^{1/250}`)

Machine: host2 (Ryzen 7950X), all steps pinned to physical cores 8–15 (`taskset -c 8-15,24-31`), every step in
its own `systemd-run --scope -p MemoryMax=… -p MemorySwapMax=0`, at most 64 GB in total at any time.
Times in the logs are host2 UTC (local CET − 1 h). Logs: `host2/` next to this file (copy of
host2:`/astro/palindromic-primes/lean/omega3/audit_host2`, the export itself removed). Peak memory: `cg` = the
scope's cgroup `memory.peak` (comparable to what the cap limits), `RSS` = summed RSS of the process tree
from `memrun.py` (as in the earlier audits; overcounts shared olean mappings).

| Check | Result | Wall | Peak memory |
|---|---|---|---|
| Toolchain identity | host2 toolchain byte-identical to the local one (sha256 of all 16054 files of `leanprover--lean4---v4.37.0-rc1`, kernels included), so nothing was synced | – | – |
| Rebuild from source (`lake build Omega3.Final Omega3.Items.S02_Neg`, `LEAN_NUM_THREADS=8`, 64G scope; `build.log`) | **success**: all 129 Omega3 modules built from source (`.lake/build` deleted first), the 75 Palprimes modules of the closure only replayed (none rebuilt), Mathlib up to date. Slowest: SkelSieve 104 s, S10_Chk 96 s, M12_KF 55 s, L15 51 s, M12_KC 46 s | 276 s | cg 20.1 GB |
| Frozen files (`sha256sum -c scripts/frozen.sha256`; `frozen_check.log`) | all 10 OK (also locally after the audit) | – | – |
| Source scan (`source_scan.log`) | 129 files: no `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe`, `opaque`, `partial`, `debug.*`, `reduceBool`, `trustCompiler`, `initialize`, `import all`, macros/elab, `run_cmd`, `#eval`, `csimp`. Only hit: the word "sorry-free" in a doc comment (`Skeleton.lean:9`). Options: `maxHeartbeats` (13), `maxRecDepth` (12), linter options. 26 `decide +kernel` (S10_Chk 5, M12 15, M12_KF 1, M12_KC 1, L04 2, L05 2). One local `Decidable` instance (`L13.lean:54`, `unfold; infer_instance`) | – | – |
| `#print axioms` (`axioms_check.lean`, `axioms.log`) | `propext`, `Classical.choice`, `Quot.sound` only, for all three theorems; `#check` output matches the statements above | 3 s | – |
| Palprimes modules in the closure | 75, all of them in the earlier audits' module lists (`audit4/modules*.txt`); palprimes unchanged since the corollary audit (b42f86c), so none re-checked here | – | – |
| `leanchecker` per module, explicit names, 2 at a time (`lc_summary.txt`, `lc/`) | **accepted**: all 131 modules (129 `Omega3.*` incl. the orphan `Items.S02_Neg`, plus `Omega3.Audit.Challenge`, `Omega3.Audit.Solution`), exit 0, no output. Slowest: S10_Chk 92 s, M12_KF 46 s, M12_KC 36 s (716 s summed) | 358 s | cg 15.8 GB (scope); RSS ≤ 12.5 GB per module (M12_KF) |
| `lake comparator` (Lean default kernel, sandboxed; `comparator.log`) | **accepted**: Challenge and Solution built and exported inside the sandbox, statements of all three challenge theorems match, axioms whitelisted, "Lean default kernel accepts the solution", "Your solution is okay!", exit 0 | 324 s | cg 10.5 GB |
| Lean paranoid kernel on the same export (`kern/`) | **accepted** (exit 0, silent) | 358 s | cg 11.1 GB |
| lean4lean | **accepted**, "checked 64860 declarations" | 351 s | cg 9.0 GB |
| nanoda | **accepted** (exit 0, silent) | 108 s | cg 10.0 GB |
| con-leche (`--jobs=1`) | **accepted**, "accepted 64863 declarations (--verified)" | 240 s | cg 7.7 GB |
| con-ron | **accepted**, "accepted 64863 declarations (--verified)" | 209 s | cg 13.0 GB |
| `leanchecker --fresh Omega3.Final` (`fresh.log`) | **accepted**, exit 0, no output: the full closure (Mathlib, 75 Palprimes and 128 Omega3 modules) replayed from an empty environment | 1200 s | cg 9.2 GB (RSS 16.8 GB) |

Kernel details: export = copy of the comparator's own export (`/tmp/tmp.XXqAOLBe`, 578 MB, sha256
`48c9dc59e0a287da9503c3bd75f0b72e21922cf449c0379e9bac552069177f48`, identical copy), same command lines and bwrap
sandbox as `Lake/CLI/Check.lean` (`host2/kern/run_one.sh`, adapted from `audit5/kern/run_one.sh`), two kernels at a
time in separate 32G scopes (`host2/lanes.sh`, `host2/kern/summary.txt`). The slowest declarations are the
`decide +kernel` certificates `Omega3.M12.h2F_eq` (con-leche 51 s, lean4lean 59 s), `Omega3.M12.restC_eq`
(38 s, 49 s) and `Omega3.S10.chk0..4` (about 20–25 s each). Unlike the Ω ≤ 4 audit, con-ron gives a verdict:
the Major2D power certificates (`B2Light`/`B3Light`) are not in the closure of `Omega3.Final`.

## Comparator challenge
`Omega3/Audit/Challenge.lean` (Mathlib only, root namespace, in the style of `palprimes/lean/Audit/Challenge.lean`):
`palindromes_omega_le_three`, `palindromes_omega_le_three_large_factors`, `palindromes_omega_le_three_count`, with
palindromes as `(Nat.digits b n).reverse = Nat.digits b n`, `Π*_b(2N)` written out as
`(Finset.Ico (b^(2N)) (b^(2N+1))).filter (palindrome ∧ Nat.Coprime n (b^3 − b))`, `x = (b : ℝ)^(2N+1)`, `c₀ = 1/250`,
`Ω` as `ArithmeticFunction.cardFactors` (exactly the predicate of the frozen `MainCount`). Config
`Omega3/Audit/comparator.json` (permitted axioms propext, Quot.sound, Classical.choice). All three files are new
files in the local package; no frozen file was touched.

## Findings
1. **Lake stack overflow at import depth 22.** `Omega3.Final` is at depth 21 (Palprimes/Omega3 modules only). A
   Solution with `import Omega3.Final` (depth 22) makes `lake build` itself abort with "Stack overflow detected"
   (exit 134; `ulimit -s` 1 GB does not help; `lake env lean` elaborates the same file without problem,
   `sol_direct.log`; first version kept as `host2/Solution_importFinal.lean.txt`). The Solution therefore imports
   exactly the 51 modules `Final` imports and repeats its proof terms (`audit_allItems` = the 49-item tuple,
   `(skeleton audit_allItems).1`, `.2`, `skeleton_largeFactors audit_allItems`). The `Final` constants themselves are
   covered by the per-module `leanchecker` run and by the `--fresh` replay. Same limit as recorded for Palprimes.
2. **File ownership after rsync.** rsync kept uid 1000 and mode 600 on many `.trace`/`.c` files of the Mathlib
   checkout; inside the comparator's bwrap user namespace root cannot read them ("permission denied",
   `host2/comparator_fail1.log`). Fixed by `chown -R root:root` of the host2 copy only.
3. Orphan `Omega3/Items/S02_Neg.lean` (the counterexample to the unfixed S02 statement) is not imported by
   `Final`; it was built and checked anyway. A stale `Omega3/Test.olean` without source exists in the local build
   only (not used on host2, where `.lake/build` was rebuilt from scratch).
4. Residual trust: the kernels' GMP Nat arithmetic for the 26 `decide +kernel` certificates, now checked by all six
   kernels.

## host2 state after the audit
Export removed. Remaining on host2: `/astro/palindromic-primes/palprimes/lean` (14 GB) and
`/astro/palindromic-primes/lean/omega3/main` (5.0 GB with the fresh build), logs `audit_host2/` (1.7 MB); about 19 GB
in total, 28 GB free on the root disk. Delete `/astro/palindromic-primes` on host2 when it is no longer needed.
