# NOTES: Ω ≤ 3 Lean round, step 1 (blueprint, definitions, statements, skeleton)

Started 2026-11-24 18:43 CET (`date`). Package `Omega3` in this folder, path requires to the prebuilt palprimes checkout
(mathlib and the eight other packages) and to `palprimes` itself. A `lake build --no-build` dry run reported "All targets
up-to-date" for `Palprimes.Omega4.Final`, nothing under palprimes/ was written (checked with `find -newer` and
`git status`), so Palprimes modules are imported directly (no copies).

## 1. State
- `Omega3/Defs.lean`, `Omega3/DefsSieve.lean`: definitions and the named `…Stmt` propositions (no theorems).
- `Omega3/Statements.lean`: 49 items `ItemL01 … ItemM13`, `MainTheorem`, `MainCount`, `AllItems`.
- `Omega3/SkelLevel.lean`, `SkelSieve.lean`, `SkelMain.lean`, `Skeleton.lean`: `Omega3.skeleton : AllItems → MainTheorem ∧ MainCount`,
  sorry-free, `#print axioms` = [propext, Classical.choice, Quot.sound] (`scripts/Axioms.lean`). Build of the whole package
  about 2–3 min (the skeleton files are the slow part, maxHeartbeats 4·10⁶ on three theorems).
- `Omega3/Corollaries.lean`: `MainLargeFactors` (every prime factor `> n^{1/250}`) and `skeleton_largeFactors : AllItems → MainLargeFactors`
  (not frozen; standard axioms).
- `Omega3/Final.lean`: intended final form, commented out.
- `Omega3/Items/L02.lean`, `Omega3/Items/L03.lean`: ported from the pilot proofs (ItemE, ItemN) by renaming; both PASS
  `scripts/check_item.sh`. L01 (pilot ItemM) needs `Pilot.e` replaced by `Palprimes.ee` in its helper lemmas (not done).
- `scripts/check_item.sh <ID>`: frozen-hash check, forbidden tokens, no imports of other items or of the skeleton,
  type check `example : Omega3.Item<ID> := Omega3.item<ID>`, standard axioms only.
- `scripts/sanity/*.py`, logs in `logs/sanity_*.log` (§4).
- Frozen: see §6.

## 2. Decisions
1. The sieve is formalised as a coefficient vector `cSieve b B ε y n` (Greaves' Σ₁ part plus `−(1+ε)` times the expanded
   λ² forms). Three properties make the sieve: pointwise `Σ_{n∣a} c(n) ≤ [ν ≤ 3] w(p(a))`, `|c(n)| ≤ K 3^{ω(n)}` on squarefree
   `n ≤ y`, and the main term `Σ c(n)γ(n)/n ≥ c/log y`. The `1 + ε` factor absorbs the `1 + O(L/log y)` of Greaves' Lemma 3;
   `ε` is fixed in the skeleton after M05's constant is known.
2. Lemma A weights `lamA b η̂ x` serve for every λ²-term: `η̂ = []` gives Selberg's weights (so (F4) is S08 at `η̂ = []`, and
   `Q(λ_x) = 1/G` is the `η̂ = []` case of M02). Supports use `n < z` strictly (`ltSet`) so that `d ∣ A/δ` is automatically coprime
   to `δ` even when `√(y/δ)` is an integer.
3. Band data is existential (S10: `∃ B ε₀, …`). The r188 design at θ = 0.340 uses η̂ on 60 geometric (irrational) u-cells,
   so it has to be regenerated with rational cells by the S10 prover. Once fixed, freeze it as `Omega3/DataBands.lean` and
   split S10 into allowance, `c_η ≤ c_i`, cost.
4. `h`-table likewise existential (M12); M13 turns any valid table into a lower bound for `𝓜(W)`.
5. Weight `W` uses `k² = 9999/1000` (r188 used k = 3.16227, k² = 9.99995); `T_c = m = 1/85` since `7/625 < m`. Hence
   `P⁻(n) > x^{1/250}` (= `x^{θm}`) and the square range is `(x^{1/250}, x^{83/250}]`.
6. TL¹ window start θ₀ = 3/10 (any θ₀ < θ is allowed by Lemma SS); with the Fejér majorant lA = 0 and (iii*) needs only θ_w > 0.
   Proposition C_w is stated with the cut A₁ only (no Lemma 2.10_w), (ii*) at δ′ = 2θ and (iii*) at δ′ = 2θ₀.
7. Counting form with `3^N` (every weight of record has max g ≤ 1/3, checked b = 5..400): count ≥ c 3^N/log x.
8. Items use Palprimes theorems freely (allowed), never other items. Where an item needs another item's conclusion it takes
   the named `…Stmt` as a hypothesis (L06, L07, L10, L11, L15, Q04, S11, M07, M08, M10, M11).

## 3. Problems found in the route while writing statements (report)
1. **Greaves' Lemma 2 (and (2.10), (2.15)) is false for non-squarefree `a`** (as an identity of the defined quantities).
   Brute force: 296 of 6000 random cases with `p² ∣ a`, `p < z` violate (2.23), 0 of the squarefree ones
   (`scripts/sanity/greaves_comb.py`, first run in this session; the logged run applies it to `A = (a, P(z))`). Harmless for the
   sieve (its linear form only sees `A`), fixed here by evaluating `Σ(·, z)` at `A`: S01 (Lemma 1) holds in that form for all
   `a` (2482 cases, 0 violations), S02 is stated for squarefree `A ∣ P(z)`.
2. **Greaves' Lemma 10 is false for odd `ν(n)`** (17–34 of 400 random cases); it holds for even `ν(n)` (0 of 1600 in four
   strict/non-strict variants), which is the only case Lemma 11 uses. Stated with `Even (ω n)`.
3. **Greaves' Lemma 9 as printed ("s ≥ 1") is false for the − sign with 1 ≤ s < 2**: `T⁻(y, w) = 1 − Σ_{p<w} ρ(p)/p T⁺(y/p, p)`
   has a negative main term ≍ −V(w) there while the `t`-sum is empty (numerically −0.006, −0.34, −0.55 V(y^{2/3}) at
   y = 10⁴, 10⁵, 10⁶, `logs/sanity_g4.log`). Lemma 11 needs − only at `y/(pd₁) > p²`, i.e. s > 2. Stated with `plus = false → 2 ≤ s`.
4. **A first version of S01/S05 was false** (caught in review): "w(p) ≤ log_y p − V for all p < y^U" fails for tiny primes
   (w = 0 > log_y p − V). Greaves' (1.8) has "when t > m". Corrected to the pair "w(p) = 0 for p ≤ y^V" and
   "w(p) ≤ log_y p − V for y^V < p < y^U".
5. Certificate targets were loosened to give the kernel certificates room: 𝓜(W) ≥ 0.009 (float 0.01042–0.01061) and band
   cost ≤ 0.007 (r188 5 bands 0.00607, 4 bands 0.0074); the skeleton needs only 𝓜(W) − cost ≥ 0.002 > 0.
6. The dossier and the P0 notes do not spell out where the Σ₂ bands end: with k² = 9.999 the r188 design has
   x_n = 0.625103127 and `k²(1 − x_n)² = 1.405336 ≤ 4(U − x_n) = 1.405470` (BandOK), and Lemma 4 (i) with plain weights holds
   above x_n (min slack +1.9·10⁻⁷ on a 1.6·10⁶-point grid) and fails below (−0.031), as it should.
7. Lemma 8 is not checkable numerically: at y ≤ 10⁶ the levels y/δ go down to y^{2/85} ≈ 1.4, so the Lemma 7 replacement
   error is O(1) (−0.78 V(y), `logs/sanity_g4_identity.log`). The exact part, M* (4.9) = M₁ − Σ χ̄ρφ/δ T⁺(y/δ, p(δ)) (4.10), was
   checked to 10⁻¹⁴ at y = 3·10³, 10⁴, 3·10⁴; so the transcription of M* is right and the residual is the asymptotic step.
   Lemma 11: (M* − E11)/V(y) = −0.007, −0.016, −0.027 at y = 10⁴, 10⁵, 10⁶: small but not decreasing. Not conclusive: Greaves
   drops the terms with (d, t) > 1 ("dealt with as in [6]") and the n-sum carries w(p) of the small primes, which vanish only
   once y^m exceeds them (y ≫ 7^{85} ≈ 10⁷²); every check at feasible y is far from the asymptotic regime because m = 1/85.
   This is the main reason to give M10 a written sub-blueprint from HR 1985 before Lean work.
8. Convergence in Lemma A and (F5) is slow (offsets of 0.1–0.4 at z = 10³–3·10³ in λ₁ + λ_q − g_η(u), and
   G(w)e^γV(w) = 1.34, 1.26, 1.21, 1.17, 1.16 at w = 10³…4·10⁶), consistent with O(1/log z) with a constant ≈ 2.3. Only
   the asymptotic statements are used, so this is not a problem for the proof, but no effective N₀ follows.
9. Not a problem but worth knowing: S07 (Lemma 4 (i) above x_n, (ii′)) and S13, S14 are exact statements for every y > 1,
   only S08, S09 (bound), M02–M11 are asymptotic.

## 4. Sanity checks (scripts/sanity, logs/)
| item(s) | check | result |
|---|---|---|
| L16 | record data b = 5..400 (sum 1, g(0), g(1) > 0, max ≤ 1/3, 0 < p < 1, H ≤ 2b − 2), exact | 0 failures |
| L01 | |G_fejer| = F_m, m ≤ 24, 400 random y each | max diff 1.2·10⁻¹⁴ |
| L03 | closed form, m = 1..40, exact | 0 mismatches |
| L04, L05 | P₆ − |G₆|, P₈ − |G₈| on 4·10⁵ points | min +1.6·10⁻⁷, +1.1·10⁻⁷ |
| L06 | T − |G|^p, b = 5..120, 2·10⁴ points | min −3·10⁻¹⁶ (equality at t = 0) |
| L07 | best ψ, lA, θ_w, κ for b = 5..300, 500, 10³, 10⁴, 10⁵ (mpmath 60 digits) | all pass; (ii) binding at b = 5 with κ ≤ 7.1·10⁻⁴; κ_max → 0 as b → ∞ (θ_w ~ 0.004 at 10⁵) but > 0; b = 5 witness ψ = 32/47 |
| L08, L09, L12, L14, L17, Q01, Q02 | brute force, small b, N | 0 violations |
| L13 | X_w by DP mod r, N ≤ 25 | constant 0.18–0.31, positive |
| Q03 | E′ identity, 154 cases | exact to 10⁻¹² |
| S01–S04 | random a, y, z, m, w (radical form) | 0 violations in 2482 cases each |
| S06, S09 (exact part), S11 (support), S12, S13, M01 | generic small (y, U, m, ε, w), toy bands, b = 5 | 0 violations / mismatches |
| S05, S07 | grid and 5·10⁵ sampled admissible tuples | 0 violations, min slack +1.9·10⁻⁷ (x = x_n) |
| S08, S09, M02 | Lemma A at z = 10³, 3·10³ | λ₁ = 1, |λ| ≤ 1, Q·G = 1 (η̂ = 0), 1.0095 vs c_η = 1.0122 |
| M03 | G(w)e^γV(w) → 1 | 1.34 → 1.16 for w = 10³ … 4·10⁶ |
| M09 | Lemma 10 brute force | even ν: 0/1600; odd ν: false (control) |
| M07, M08, M10, M11 | finite-y sums (y ≤ 10⁶) | §3 items 3, 6 |
| M12, M13 | 𝓜(W) from the Q = 2000 two-sided h cells | 𝓜(W) ∈ [0.01042, 0.01061] ≥ 0.009 |

## 5. Open questions and risks (for the parallel phase)
- M07, M08, M10, M11 (Greaves §4, Lemmas 8, 9, 11, 12) are transcriptions of a sketch that refers to Halberstam–Richert 1985
  for the proofs. Their provers should first write a sub-blueprint from HR 1985 (Lemma 5, (6.5)–(6.15)); if a statement has
  to change, change only `Lemma9Stmt`, `E11`, `Mstar`, `T9set` or the M-items and re-freeze. The skeleton uses only the
  combined Lemma 6 (`|M₁ − M₂₃ − 2e^γV(y)𝓜(W)| ≤ 3εV`) — any other split of Lemma 6 can replace M07, M08, M10, M11 without
  touching the rest.
- An alternative to Greaves §4 (cheaper?) is the Ω ≤ 4 MainTerm route (iterated prime sums → integrals with the Rosser
  regions, `Palprimes/MainTerm`), applied to M₁ − M₂₃ directly. Not explored here.
- S10, M12 are kernel certificates (10⁷–10⁸ ops) with data still to be generated (rational u-cells for the bands; h tables
  from 1/85 to 1/4).
- L07 must cover all b ≥ 5: b ≥ 16 by a b-uniform argument (τ₀ ≤ 2/b + 1/b², ψ_T ≥ 0.7, θ_w > 0 from the N₄ polynomial),
  b ≤ 15 by per-base rational exponents; κ depends on b (κ_max ~ 10⁻¹⁴ at b = 10⁵ with p = 1 − 1/b²).
- S11's bound uses that each n has at most one δ (Greaves p. 89); checked only for support, not the constant.
- The P0 changes (Fejér certificates for all b ≥ 5, route E′, θ = 0.340 design) remain unaudited; the sanity checks above
  are the only independent checks of their statements.

## 6. Freeze
Frozen in `scripts/frozen.sha256`: `Omega3/Defs.lean`, `Omega3/DefsSieve.lean`, `Omega3/Statements.lean`, the four skeleton
files, `lakefile.toml`, `lake-manifest.json`, `scripts/check_item.sh`. Confidence: high for parts L, Q, S and M01–M06, M09,
M12, M13 (sanity-checked); moderate for M07, M08, M10, M11 (transcriptions, see §5). A change to those requires a re-freeze
(new hash) by the lead; item proofs of other items stay valid as long as their statements and the definitions they use do
not change.
