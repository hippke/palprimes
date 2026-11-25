# Lean audit of the Ω ≤ 2 theorem for κ-palindromes (`lean/KappaOmega2/`)

Two audits. Part 1 is the independent audit of the working package `omega-2/lean/OK2` (2026-11-25, local machine, built with `k2build.py`). Part 2 is the audit of the repository version on host2 (library renamed `OK2` → `KappaOmega2`, `Omega2.LemmaR`/`FejerPsi4` moved into it, statement file merged into `FinalK.lean`, lake build, comparator and six kernels).

## Part 1: audit of the working package


Verdict. Accepted with remarks.
`kappa_palindromes_omega_le_two` (Mathlib definitions only, b ≥ 3, κ = 7/10, Ω ≤ 2) rebuilds from source in a fresh directory, uses only propext, Classical.choice and Quot.sound, and is accepted by leanchecker (124 modules one by one and two `--fresh` replays of the whole closure incl. Mathlib and Palprimes).
The statement is the intended theorem, is not vacuous and does not follow from an easy argument. The R = 2 constants satisfy Greaves' conditions exactly.
Remarks are cosmetic or about hygiene (stale docstrings in frozen files, orphan Ω ≤ 3 modules in OK2/, a driver that hides warnings). None affects the result.

Auditor run 2026-11-25 10:07 to 11:04 CET (`date`), local machine only, at most 2 Lean processes, each in
`systemd-run --user --scope -q -p MemoryMax=20G -p MemorySwapMax=0 nice -n 10`. Nothing was written outside `audit_lean/`.
Sources of `omega-2/lean/OK2` and `Omega2` were hashed at the start and the end of the audit (154 files, unchanged,
`logs/source_sha256_start.txt`).

### Table of checks

| # | Check | Result | Wall time | Log |
|---|---|---|---|---|
| 1 | Fresh rebuild of `OK2.Check.Solution` with a copy of `k2build.py` (`k2build_audit.py`, only ROOT pinned to `omega-2/lean` and OUT = `audit_lean/build`), `-j 2 --mem 20G` | success, 124 modules built (the whole OK2/Omega2 closure), 0 failed, set of built oleans identical to the source closure. Slowest LK10 141 s, QK04_Cut 124 s, QK04 88 s, SkelSieve 69 s. 1319 s summed | 10:07:47 to 10:22:17 (14.5 min) | `logs/build.log` |
| 1a | First attempt from `audit_lean/` as cwd | failed at once (Lean requires the input file inside the root dir = cwd), driver must run with cwd `omega-2/lean`. Nothing written | 0 s | `logs/build_attempt1_wrong_cwd.log` |
| 2 | `#print axioms` (own file `AuditAxioms.lean` against the fresh build) for `kappa_palindromes_omega_le_two`, `OK2.infinite_kappaPal_Omega_le_two`, `OK2.many_kappaPal_Omega_le_two`, `OK2.skeletonK`, `OK2.allItemsK` | all five `[propext, Classical.choice, Quot.sound]` | 6 s | `logs/AuditAxioms.log` |
| 2a | Origin of every constant in the type of the main theorem (own `#audit_origins` command) | only `Init.*` and Mathlib modules (`Nat.digits`, `List.getD`, `ArithmeticFunction.cardFactors`, `Set.Infinite`, ...), no OK2/Palprimes constant, `#check` with `pp.fullNames` shows the statement as written | – | `logs/AuditAxioms.log` |
| 3a | leanchecker controls (positive `AuditPos`, negative `AuditNeg` = `False` proved by `True.intro` added with `debug.skipKernelTC`) | positive accepted, negative rejected ("declaration type mismatch") | 4 s | `logs/lc_controls.log` |
| 3b | `leanchecker --fresh OK2.Check.Solution` with LEAN_PATH = Mathlib packages + Palprimes build (read only) + `audit_lean/build` only (the original `.k2build` and `omega-2/lean/.lake/build` not on the path) | accepted, exit 0, no output besides "replaying" | 2126 s | `logs/lc_fresh.log`, `logs/lc/fresh_*.log` |
| 3c | `leanchecker --fresh OK2.FinalK`, same path, in parallel with 3b | accepted, exit 0 | 2131 s | same |
| 3d | leanchecker per module (new constants of each module replayed on its imports), all 124 closure modules, 2 at a time | all accepted. Slowest M12_KF 46 s, M12_KC 34 s, M12 8 s (the `decide +kernel` certificates) | 11:00:33 to 11:03:18 | `logs/lc_modules.log`, `logs/lc/` |
| 4 | Source scan of the 124 closure modules (34 911 lines), comments stripped (nested block and line comments), scanner control on a synthetic text | no `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe`, `opaque`, `partial`, `macro`, `elab`, `syntax`, `notation`, `run_cmd`, `#eval`, `debug.`, `trustCompiler`, `reduceBool`, `initialize`, `import all`, `csimp`, `decide := true`, `#exit`, `meta`. Hits only in comments ("sorry-free", "notation", "prefix"). One local instance `Decidable (IsKappaPal b n)` by `unfold; infer_instance` (DefsK:46, harmless). 19 `decide +kernel` (M12 17, M12_KF 1, M12_KC 1) | 1 s | `logs/source_scan.log`, `logs/scan_controls.log` |
| 4a | Options | `maxHeartbeats` 14 (1·10⁶ 3, 2·10⁶ 2, 4·10⁶ 7, 8·10⁶ 2 in M02 and QK04), `maxRecDepth` 7 (2·10⁴ to 10⁵), linter options 108. List below | – | `logs/source_scan.log` |
| 5 | Statement faithfulness and non-vacuity | faithful, see section "Statement" | – | – |
| 5a | Constants (exact rationals, controls with the Omega3 constants and a negative control) | V + 2U = 200/103 = 1/θ, 2V + U = 1, W(1) = U − V, c₀ = θV = 1/100, c₁ = θU = 99/200, θ(V + 2U) = 1, k²(2/3)² = 4(U − 1/3) = 776/309, 1/3 ≤ 2U − 1. Omega3 control gives V + 3U = 1/θ, 2V + U = 1, c₀ = 1/250, c₁ = 83/250. Negative control V + 3U = 1/θ fails at the R = 2 constants | – | `logs/constants_check.log` |
| 6 | Diff of frozen files against Omega3 (Omega3 → OK2 renamed) | Defs 7 constants and `ptarget` ν ≤ 3 → ν ≤ 2, DefsSieve HTableStmt head 1/85 → 2/103, Statements S01 `V + 3U` → `V + 2U`. Nothing else. SkelSieve and SkelMain byte-identical after renaming | – | `logs/diff_*.txt` |
| 6a | Item files against Omega3 | 99 files unchanged, changed S01, S05, S10, S11_Core, S13, S14, M04, M04_Band, M05_Core, M07, M10_L, M11, M11_A, M12, M12_Base, M13, M13_H (numerics only, as listed in `logs/sieve_port/NOTES.md`), 24 new LK/QK files | – | `logs/items_diff_counts.txt` |
| 6b | Palprimes oleans | `palprimes` git HEAD 29a5e0a, clean tree, no change under `lean/Palprimes` since b42f86c (state of the Omega3 audit). Its oleans were replayed by both `--fresh` runs | – | – |

maxHeartbeats and maxRecDepth settings. SkelSieve:57, SkelMain:69, SkeletonK:46, S08:49, LK10:15, LK15:50, QK04_Cut:11
(4·10⁶), M02:66, QK04:14 (8·10⁶), M04_Band:291, M07:172 (2·10⁶), M11_B:652, M11:16, LK10:312 (1·10⁶), maxRecDepth in
S11:415, M05:48 (2·10⁴) and M07:14, M11:17, M12_KF:8, M12_KC:8, M12:282 (10⁵).

### Statement

`kappa_palindromes_omega_le_two (b) (hb : 3 ≤ b)` says that the set of n with n ≠ 0, Ω(n) ≤ 2 and
`(digits b n).getD i 0 = (digits b n).getD (L − 1 − i) 0` for all i < ⌊7L/20⌋ (L = number of base-b digits) is infinite.

- Reading. `Nat.digits` is little-endian, so index i is the i-th digit from the bottom and L − 1 − i the i-th from the
  top. For L ≥ 1 one has ⌊7L/20⌋ ≤ ⌊L/2⌋, so both indices are in range and the default 0 of `getD` is never used.
  This is the mirror condition of palindromes restricted to 7/10 of the digits (κ = 7/10). Concrete checks in
  `AuditAxioms.lean` (`IsKappaPal 10 1234521` true, `1234512` false, by `decide`).
- Degenerate members. Only L ≤ 2 (⌊7L/20⌋ = 0) gives no condition, a finite set. For L ≥ 3 the top digit is nonzero
  and must equal the bottom digit, so numbers with trailing zeros (p·b^k) are excluded. n = 0 is excluded.
- Non-triviality. The set of κ-palindromes up to x has about x^{0.65} elements. Products such as p(b^k + 1) or squares
  of sparse palindromes need unproved prime statements (generalised Fermat or primes with sparse digits). Known prime
  results with preassigned or mirrored digits reach κ below 0.48 (Harman 2006, our κ < 9/20), so they do not cover
  κ = 7/10 even for Ω = 1. A Greaves R = 2 sieve with level 0.515 > 1/(2 − δ₂) ≈ 0.5114 is a real input.
- Bridge. `OK2.IsKappaPal` is literally the same formula (`#print`), `Nat.IsAtMostAlmostPrime 2 n` is Mathlib's
  `n ≠ 0 ∧ Ω n ≤ 2`, and Solution.lean closes the bridge by `convert` and `simp only`. `kpiStar` = integers in
  [b^{2N}, b^{2N+1}) with `IsKappaPal` and coprime to b³ − b, `mK N = ⌊7(2N + 1)/20⌋` matches ⌊7L/20⌋ at L = 2N + 1.
  `MainCountK` gives at least c·2^m·W/log x such n with all prime factors > x^{1/100}, which tends to infinity. The
  factor 2^m (not b^m) comes from max a_n ≤ 2^{−m}/W and is a weaker count than the true size, documented as such.
- Base 2 is excluded (b ≥ 3), as documented in the plan.

### Changes relative to Omega3

- Constants. θ = 103/200, U = 99/103, V = m = 2/103, W(1) = 97/103, k² = 582/103, c₀ = 1/100, c₁ = 99/200 satisfy
  Greaves' R = 2 relations V + 2U = 1/θ and 2V + U = 1 exactly, and c₀ = θV, c₁ = θU (also proved in SkeletonK as
  `thS_mm`, `thS_UU`). Wf stays continuous at 1/3 and U.
- ν ≤ 2 in `ptarget` and `V + 2U` in S01 are exactly the R = 2 form of Greaves' Lemma 1 (a < y^{V+2U} = x).
- HTableStmt head 2/103 = m is the point below which Wf = 0, as 1/85 was for Omega3. It is required by M13 and makes
  M12 certify MvalLower ≥ 9/1000 on [2/103, 1/4] (true value about 0.013 by the agent's kernel check).
- S10 with empty bands. BandOK B for B = ⟨[1/3], [], []⟩ requires 1/3 ≤ 2U − 1 (= 95/103) and k²(1 − 1/3)² ≤ 4(U − 1/3),
  which holds with equality. S07 (unchanged, quantified over every BandOK B) then gives admissibility for all δ, so no
  Σ₂ band is needed, BandAllow and the c_η bounds are vacuous and bandCost = 0. This is legitimate, the cost
  condition of the plain Greaves weights is exactly what BandOK encodes, and the item is used by the skeleton
  only through these conditions.
- Weakened or vacuous items. None found that matters. S13 keeps the exponent (1/2)(2/3)^84 (true, weaker than
  possible), S10 keeps the cap 7/1000, M12 keeps 9/1000. Hypotheses of the κ items (LK10, LK15, QK04) are all
  discharged in SkelLevelK and SkeletonK with the record data, otherwise the closed theorem would not typecheck. Any
  item that were vacuous could not make the final theorem weaker, its statement is fixed and Mathlib-only.

### Issues

| # | Location | Severity | Issue | Fix |
|---|---|---|---|---|
| 1 | `OK2/Defs.lean` 26–43, `OK2/Statements.lean` header, MainTheorem/MainCount docstrings, S10, M12, L07 docstrings, `DefsSieve.lean` | cosmetic | docstrings of frozen files still describe Omega3 (θ = 17/50, U = 83/85, V = 1/85, k² = 9999/1000, Ω ≤ 3, b ≥ 5, five bands) while the code has the R = 2 values | update the comments in a re-freeze (does not change any term) |
| 2 | `OK2/Final.lean`, `Skeleton.lean`, `SkelLevel.lean`, `Corollaries.lean`, `Items/L04`–`L17`, `Q01`–`Q04`, `S02_Neg`, `L16_tent`, `LK01_Ax`, `Check/AxSkel` | minor | 30 modules in OK2/ outside the closure of the theorem. Some are the Ω ≤ 3 palindrome skeleton with R = 2 constants (`OK2.MainTheorem` claims Ω ≤ 3 for palindromes) and the sieve-port notes report SkelLevel and L07_Gen failing. Not built or checked here | move to an attic folder or document them as stale, so that `k2build.py all` and readers do not pick them up |
| 3 | `lean/scripts/k2build.py` | minor | prints Lean messages only on failure, so warnings (including "declaration uses sorry") are invisible. Needs cwd = `omega-2/lean` (Lean root check), not documented. LEAN_PATH also lists `palprimes/lean/.lake/build` (contains Omega3 oleans) and `omega-2/lean/.lake/build` (lake-built Omega2), which could shadow a module that the driver did not build | log all messages, document the cwd, drop `.lake/build` from the path. Mitigated here by the axioms check and by a leanchecker path without these directories |
| 4 | `OK2/Items/LK10.lean`, `QK04*.lean` | remark | build times 90–140 s with maxHeartbeats 4·10⁶ to 8·10⁶, the only fragile spots for a toolchain bump | none needed |

### Not checked

- The other kernels of the Omega3 audit (lake comparator with a Challenge file, paranoid kernel, lean4lean, nanoda,
  con-leche, con-ron). They are in the toolchain bin directory but were outside this brief. The comparator would also
  need a lake setup, which this package cannot use.
- The orphan modules of issue 2, and the Omega2 modules LemmaR2, LemmaR2D (not in the closure).
- The Palprimes modules were not re-scanned at source level (prior audits, sources unchanged since b42f86c). Their
  oleans were kernel-replayed by the `--fresh` runs.
- The mathematics behind the items (Greaves R = 2 main term, Parseval squares) beyond what the kernel check implies.
  The kernel check makes the closed theorem independent of that.
- Residual trust: the Lean kernel with GMP arithmetic for the 19 `decide +kernel` certificates, and the toolchain
  leanchecker (one kernel implementation).

### Files

`k2build_audit.py` (driver copy), `scan.py` (closure and token scan), `lc_run.py` (leanchecker runner),
`AuditAxioms.lean`, `AuditPos.lean`, `AuditNeg.lean` (controls), `build/` (fresh oleans, about 124 modules plus
controls), `logs/`.

## Part 2: audit of the repository version (host2, 2026-11-25)

Changes against Part 1 (no proof term changed): `OK2` renamed to `KappaOmega2` and `Omega2` to `KappaOmega2` (sed on
whole words), `Omega2/LemmaR.lean` and `Omega2/FejerPsi4.lean` moved into `KappaOmega2/`, the Mathlib-only statement of
`OK2/Check/Solution.lean` moved into `FinalK.lean` (a module importing `FinalK` would be at import depth 22, where
lake overflows its stack), the counting form added with Mathlib definitions only (`kappa_palindromes_omega_le_two_count`,
proved by the term `many_kappaPal_Omega_le_two b hb`), comparator files `KappaOmega2/Audit/{Challenge,Solution}.lean`
and `comparator.json` (Solution imports the modules `FinalK` imports and repeats its proof terms), and a lake library
`KappaOmega2` with `globs = ["KappaOmega2.+"]`. The same `globs` line was added to the `Omega3` library: with roots
only, lake does not know the item modules, and a fresh clone could not build `Omega3`; the local build had worked
only because of oleans left from an earlier root module.

Machine: host2 (Ryzen 7950X), all steps pinned to physical cores 8–15 (`taskset -c 8-15,24-31`), each in its own
`systemd-run --scope -p MemoryMax=… -p MemorySwapMax=0`, at most 64 GB at any time. Host2 toolchain identical to the
local one (checked in the Ω ≤ 3 audit, unchanged). Times are host2 UTC. Logs and scripts: local
`/astro/palindromic-primes/lean/kappa2_audit/host2_logs/` (the host2 copy has been deleted).

| Check | Result | Wall | Peak memory (cgroup) |
|---|---|---|---|
| Local lake build (`lake build KappaOmega2`) | success, only the Challenge uses `sorry`; axioms standard | 529 s | – |
| Rebuild from source on host2 (oleans of `KappaOmega2` and `Omega3` deleted, `lake build KappaOmega2 Omega3`) | **success**, all modules of both libraries built, Palprimes and Mathlib replayed | 399 s | 34.2 GB |
| `#print axioms` (`axioms_check.lean`) | `propext`, `Classical.choice`, `Quot.sound` for `kappa_palindromes_omega_le_two`, `kappa_palindromes_omega_le_two_count`, `KappaOmega2.infinite_kappaPal_Omega_le_two`, `KappaOmega2.many_kappaPal_Omega_le_two`; `#check` shows the statements as written | 2 s | 0.5 GB |
| `leanchecker` per module, explicit names, 2 at a time (`lc_summary.txt`) | **accepted**: all 125 modules (123 of the library, Challenge, Solution), exit 0, no output. Slowest M12_KF 45 s, M12_KC 36 s | 385 s | 15.9 GB |
| `lake comparator` (Lean default kernel, sandboxed; `comparator2.log`) | **accepted**: both challenge theorems match, axioms whitelisted, "Lean default kernel accepts the solution", "Your solution is okay!" | 203 s | 10.5 GB |
| Lean paranoid kernel on the same export | **accepted** (exit 0, silent) | 193 s | 11.1 GB |
| lean4lean | **accepted**, "checked 64489 declarations" | 202 s | 9.0 GB |
| nanoda | **accepted** (exit 0, silent) | 69 s | 9.7 GB |
| con-leche (`--jobs=1`) | **accepted**, "accepted 64492 declarations (--verified)" | 125 s | 7.7 GB |
| con-ron | **accepted**, "accepted 64492 declarations (--verified)" | 180 s | 7.5 GB |
| `leanchecker --fresh KappaOmega2.FinalK` | **accepted**, exit 0 (summary line `k2-fresh … rc 0`, 996 s; `fresh.log` was later overwritten by a redundant second run that was stopped) | 996 s | 9.2 GB |

Export: 574 MB, sha256 `3def6be82b294047280f9e1375dde07d63397124dbf7e9c57c0516d2466b2291`, hard-linked from the
comparator's temporary file while its kernel ran. Two attempts before it took the comparator's 219-byte nanoda config
(which points to the export) instead of the export, the kernel runs on that file (`kern/first_try/`) are void.
The slowest declarations are the `decide +kernel` certificates `KappaOmega2.M12.h2F_eq` (lean4lean 57 s) and
`KappaOmega2.M12.restC_eq` (48 s). Residual trust: the kernels' GMP Nat arithmetic for these certificates, now
checked by all six kernels.
