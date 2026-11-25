> Repository note (2026-11-25): written in the working package `omega-2/lean`, where the library was called `OK2`. Here it is `lean/KappaOmega2/` (namespace `KappaOmega2`); `Omega2.LemmaR` and `Omega2.FejerPsi4` are `KappaOmega2.LemmaR` and `KappaOmega2.FejerPsi4`, the statement file `OK2/Check/Solution.lean` is now part of `KappaOmega2/FinalK.lean`, and the build uses lake instead of `k2build.py`.

# Sieve and main-term port of OK2 to R = 2

Verdict (2026-11-25 08:01 CET). All S and M items of OK2 build with the R = 2 constants (84 modules, 0 failures).
Each `theorem itemXnn : ItemXnn` (S01 to S15, M01 to M13) depends only on propext, Classical.choice and Quot.sound.
No statement problem was found. Defs, DefsSieve, Statements and Skel files are unchanged.
M12 now certifies MvalLower ≥ 0.009 with a lot of room (true lower bound of the table 0.0208).

## Changes per item

- S01 (Greaves Lemma 1). The counting step `Palprimes.Greaves.nu_le` is generic in R. The proof now calls it with
  R = 2 and the target `nu a Y ≤ 2`. Nothing else changed.
- S05. The odd large ν case used `1/m = 85`. It now uses `1/m = 103/2`, so `|F| > 51.5` gives `|F| ≥ 52 ≥ 2`.
- S10. No bands. `B = ⟨[1/3], [], []⟩`, `ε₀ = 1`. BandOK holds (last edge 1/3 ≤ 2U − 1, and
  `kSq (2/3)² = 4(U − 1/3) = 776/309` with equality). BandAllow and the cEta bounds are vacuous, bandCost B = 0.
  The ten helper files S10_Band, Box, Check, Chk, Cost, Data, Glue, Log, Mono, Real were moved to
  `logs/sieve_port/S10_old/` (with the old S10.lean). Nothing else imported them.
- S11_Core, S13, M05_Core (same lemma `c_rho`/`s13_rho` in three copies). ν(δ) ≤ 1/m now gives ν(δ) ≤ 51
  instead of 85. The exponent `(1/2)(2/3)^84` of the statement S13 is kept (still valid, weaker than needed).
  The prime case uses `(1/2)(2/3)^84 ≤ 1 − U = 4/103`.
- S14, M04, M04_Band, M13_H. Numeric rewrites `UU = 99/103`, `mm = 2/103`, `W1 = 97/103`, `kSq = 582/103`, and
  `t − 2/103 ≤ kSq t²` at t = 1/3. M04 stays general in B (statement quantifies over all BandOK data).
- M07. `c2 = (1/2)(2/3)^84` kept. `c2 ≤ 4/103` replaces `c2 ≤ 2/85`. Card bounds |Δ| ≤ 103/2, |Δ′| ≤ 50.
- M10_L. Uniform Lemma 9 is used with exponent S = 1/m = 103/2 (real) instead of 85. The bound
  `V(y^m) ≤ 86 V(y)` still holds (true factor 1 + 51.5).
- M11_A, M11. Tuple lengths of the n-sum are now ≤ 51 (chi_tuple, chibar_tuple, explA_snoc) and the level sum runs
  over k ∈ [1, 25] instead of [1, 42] (card_of_cond gives |U| + 2 < 51.5, h86(2k, t) = 0 for 2k ≥ 52 and t > m).
  The constant `25 Mm^85` replaces `42 Mm^85` in M11.
- M13. The split point 1/85 is now 2/103 (head of HTableStmt). `m13_W_zero` and `m13_hS_eq` take `t ≤ 2/103` and
  `2/103 ≤ t`.
- M12_Base. New W. Kinks of `min(kSq t², t − m)` at t1 = 0.0222030 and t2 = 0.1547729. Breakpoints
  2/103, 16/721 (≤ t1, linear part), 1/45 to 2/13 (quadratic part), 5/32 (≥ t2, linear part) to 1/2. The two small
  gaps are bounded below by 0. `base_ge` proves base ≥ 3/100 (closed form value of the bound 0.034979, exact base
  0.0374693) by series bounds for log(1 − y) with y ∈ {4/103, 25/128, 1/8, 206/72821, 1/5, 7/52, 5/32}.
  `intW_le` uses `W ≤ t − 2/103` and `W ≤ (582/103) t²`.
- M12. The h-bounds HbQ_j on the Omega3 cells ξ_j = (101/100)^j/85 (KF, KC tables and crude tail, independent of θ,
  U and W) are kept unchanged. The table of the item is their restriction to [2/103, 1/4]. Edges ξ′_0 = 2/103
  (with ξ_50 ≤ 2/103 < ξ_51, kernel checked), ξ′_i = ξ_{50+i} for 1 ≤ i < 258, ξ′_258 = 1/4, bounds H′_i = HbQ_{50+i}.
  Cell i lies in old cell 50 + i, so `hS_le` applies directly. Kernel check `sum_le` gives cell sum ≤ 17/1000
  (exact 0.0166380), so MvalLower ≥ 3/100 − 17/1000 = 0.013 ≥ 9/1000.

## Scripts and logs

- `lean/scripts/sieve_port/m12_restrict.py` evaluates the restricted table (exact rationals for the cell sum,
  mpmath for the base). Positive control with the Omega3 constants reproduces base 0.0321844 and cell sum
  0.0227576 ≤ 0.023 of the Omega3 M12. Negative control with head outside the cell is rejected. Output in
  `m12_restrict.log`. The R = 2 result is base 0.0374693, cell sum 0.0166380, MvalLower ≥ 0.0208313, consistent
  with 𝓜(W) ≈ 0.0216 of `logs/greaves_R2.log`.
- `lean/scripts/sieve_port/errs.py` compiles one module through k2build and prints its errors in full.
- `k2build_SM.log` is the clean rebuild of all 84 S and M modules (sources touched first), 07:57 to 08:01 CET,
  `done: 84 built, 0 failed`. No sorry warning in the log.
- `axioms_SM.log` is the `#print axioms` output for the 28 items (file AxSM.lean compiled with the driver LEAN_PATH).
- `M12_old.lean`, `M12_Base_old.lean` and `S10_old/` keep the Ω ≤ 3 versions for comparison.

## Statement problems

None. All S and M statements are provable with the new constants as frozen. Remarks for the lead.
S13 still states the exponent (1/2)(2/3)^84, valid but far from sharp at ν ≤ 51. ItemS10 keeps the cost cap 7/1000
and the docstrings of Statements still mention θ = 0.340, 1/85 and Ω ≤ 3 (text only). OK2.SkelLevel and
OK2.Items.L07_Gen failed in the step 1 log and belong to the other agent (not touched here).
