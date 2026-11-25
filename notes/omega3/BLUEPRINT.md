# Blueprint: Ω ≤ 3 for palindromes in every base b ≥ 5 (Lean package `Omega3`)

Status: step 1 done (blueprint, definitions, 49 frozen item statements, compiled sorry-free skeleton). Started 2026-11-24 18:43 CET, this version 19:57 (`date`).
No item is proved here. Each item `Omega3.ItemXnn : Prop` in `Omega3/Statements.lean` is to be proved later in its own file
`Omega3/Items/Xnn.lean` (`theorem itemXnn : ItemXnn`), checked by `scripts/check_item.sh Xnn`.
`Omega3/Skeleton.lean` proves `skeleton : AllItems → MainTheorem ∧ MainCount` without sorry.

## 0. Target

```
theorem infinite_palindromes_Omega_le_three (b : ℕ) (hb : 5 ≤ b) :
    {n : ℕ | IsPalindrome b n ∧ Nat.IsAtMostAlmostPrime 3 n}.Infinite
theorem many_palindromes_Omega_le_three (b : ℕ) (hb : 5 ≤ b) :
    ∃ c > 0, ∃ N₀, ∀ N ≥ N₀, c * 3 ^ N / log x ≤ #{n ∈ piStar b N | Ω n ≤ 3 ∧ ∀ p ∣ n, x^(1/250) < p}
```
with `x = b^(2N+1)`, `piStar b N` the palindromes with exactly 2N + 1 digits coprime to b³ − b (Palprimes).
`MainTheorem`, `MainCount` in `Statements.lean`; `MainLargeFactors` (all prime factors `> n^{1/250}`) in `Corollaries.lean`, derived from `MainCount`. The counting form comes for free from the weighted chain: every weight of record
has max g ≤ 1/3, so the count is ≥ c·3^N/log x = x^{log 3/(2 log b)+o(1)} (not √x). P⁻(n) > x^{1/250} = x^{θm}.

## 1. Route and parameters (all exact rationals)

| symbol | value | meaning |
|---|---|---|
| θ | 17/50 = 0.340 | sieve level, y = x^θ |
| U | 83/85 | (2/θ − 1)/5, kink V + 3U = 1/θ |
| V = m | 1/85 | (1 − U)/2; W = 0 on [0, m] (T_c = m since 7/625 < m) |
| W(1) | 82/85 | U − V |
| k² | 9999/1000 | Σ₃ cap, W ≤ k²t² ≤ 10t² (Lemma 4 (ii′)) |
| c₀, c₁ | 1/250, 83/250 | θm, θU: P⁻ exponent and upper end of the square range |
| W(t) | 0 (t ≤ m), min(k²t², t − m) (m < t ≤ 1/3), t − V (1/3 < t ≤ U), W(1) (t > U) | design A₅ (mainterm NOTES §6) |
| z | y^U | Greaves' sifting limit |
| θ₀ | 3/10 | TL¹ window start (any θ₀ < θ works by Lemma SS; larger θ₀ helps (iii)) |
| x_n | last band edge (≈ 0.6251 in r188's 5-band design) | Σ₂ bands on [1/3, x_n) with Lemma A weights, Greaves' λ above; BandOK: k²(1 − x_n)² ≤ 4(U − x_n), x_n ≤ 2U − 1 |
| certificate targets | 𝓜(W) ≥ 0.009 (M12), band cost ≤ 0.007 (S10) | margin 𝓜(W) − cost ≥ 0.002 (float values 0.0104–0.0106 and 0.00607) |
| p_T | 1023/1024 (b ≤ 15), 1 − 1/b² (b ≥ 16) | majorant exponent |
| digit weight | Fejér (1,…,m,…,1)/m², m = ⌊(b+1)/2⌋, for b ∉ {6, 8}; r238 weights for b = 6, 8 | |
| majorant | T = (1 − p) + pF_m (Fejér), T = (1 − p) + pP (b = 6, 8, P ≥ |G_g| exact LP) | |

Chain (dossier v5 §2 with the three new P0 changes):
1. Weighted sequence a_n = Π_k g(e_k) on palindromes n = n(e) coprime to b³ − b (r238 §0). X_w ≍ 1 (Lemma 2.1_w).
2. Level: Prop C_w (cut A₁ only) with the record majorants gives TL¹_w(θ, κ_b, θ₀); Lemma SS, Lemma K and the window give the
   3^ω remainder sum ≤ exp(−c√log x) (Lemma W_w); Lemma 2.2_w + regrouping turn it into Σ_{d≤y} μ²3^ω|R_w(d)|.
3. Sieve: Greaves 1986 Theorem 1 through its proof, Σ₂ band weights by Lemma A (r188 §7), Σ₃ by Lemma 4 (ii′) (r182 §2),
   no Theorem R, no Lemmas F, T, S, E, G, G2. In Lean the sieve is a coefficient vector c_y,ε(n) (squarefree n ≤ y) with
   (pointwise) Σ_{n|a} c(n) ≤ [ν_{y,U}(a) ≤ 3] w(P⁻(a)), (size) |c(n)| ≤ K 3^ω(n), (main term) Σ_n c(n)γ(n)/n ≥ c/log y.
4. Main term: Greaves Lemma 6 (§4, Lemmas 7 to 12) + Lemma A part 2 + band cost (Lemma 5‴) + certificate 𝓜(W) − cost > 0.
5. Squares: Proposition CQ with route E′ (Parseval mod p², squares NOTES §2) on (x^{c₀}, x^{c₁}].
6. Count: weighted sum over the good set ≥ c/log x, a_n ≤ 3^{−N−1}, so #good ≥ c 3^N/log x.

## 2. Findings while writing statements (details and logs in NOTES.md §3)
1. Greaves' Lemma 2 ((2.23), and (2.10), (2.15) behind it) holds only for `a` squarefree in its `z`-smooth part. The sieve
   only sees `A = (a, P(z))`, so `Σ(·, z)` is evaluated at `A` (S01 for all `a`, S02 for squarefree `A ∣ P(z)`).
2. Greaves' Lemma 10 is false for odd `ν(n)`; stated for even `ν(n)` (the case used in Lemma 11).
3. Greaves' Lemma 9 ("s ≥ 1") is false for the − sign with `1 ≤ s < 2`; stated for `+` with `s ≥ 1` and `−` with `s ≥ 2`
   (the only case used in Lemma 11).
4. Greaves (1.8)'s line `W(t) ≤ t − m` holds only for `t > m`; S01/S05 state it as "`w = 0` up to `y^V`" plus the line above.

## 3. Item list (49 items, risk-first order)

Columns: rank, id (Lean `Omega3.Item<id>`), content, source, `…Stmt` hypotheses (dependencies supplied by the skeleton),
estimated lines, tier, flags. "new" = one of the three unaudited P0 changes (Fejér certificates for all b ≥ 5, route E′,
the θ = 0.340 design) or a statement first written here; "transcr" = transcription of Greaves §4 (a sketch referring to
Halberstam–Richert 1985); "cert" = kernel certificate with data still to be produced.

| # | id | content | source | hyps | lines | tier | flags |
|---|---|---|---|---|---|---|---|
| 1 | M08 | Lemma 9 (HR Reduction Lemma): `T^±(y, y^{1/s}) = Σ_t μ²ργ/t σ⁺(y/t) + o(V(y^{1/s}))` (`−`: s ≥ 2) | Greaves p. 93, HR 1985 Lemma 5 | Lemma7Stmt | 1200 | Opus | transcr, corrected (§2.3) |
| 2 | M10 | Lemma 11: `M*(y^U) = E11(y) + o(V(y))` | Greaves pp. 93–94, HR (6.5)–(6.15) | Lemma9Stmt, Lemma10Stmt | 1000 | Opus | transcr |
| 3 | M07 | Lemma 8: `M₁ − M₂₃ = M*(y^U) + o(V(y))` | Greaves pp. 90–92 | Lemma7Stmt | 800 | Opus | transcr (exact part (4.9) = (4.10) checked) |
| 4 | M11 | Lemma 12: `E11(y) = 2e^γV(y)(𝓜(W) + o(1))` | Greaves p. 94, 1982 Lemma 4.4 | Lemma7Stmt | 1200 | Opus | transcr |
| 5 | Q04 | Proposition CQ_E′ assembly: `Σ_{x^{c₀}<p≤x^{c₁}} A^w_{p²} ≤ 2X_w x^{−c₀} + x^{−η}` | squares NOTES §2, dossier v5 §3.2 | SqRedStmt, SqDiagStmt, SqParsevalStmt | 800 | Opus | new |
| 6 | S10 | band certificate: ∃ bands with Lemma 3″ allowance, `c_η ≤ c_i`, cost ≤ 0.007 | r188 §7–8 cert_add, mainterm NOTES §1 | — | 1200 + data | Opus | new, cert |
| 7 | M12 | ∃ h-table (cells from 1/85 to 1/4) with `MvalLower ≥ 0.009` | mainterm NOTES §4, r167 §3.1 | — | 1000 + data | Opus | new, cert |
| 8 | M13 | `HTableStmt ξ H → MvalLower ξ H ≤ 𝓜(W)` | r188 §1 | — | 500 | Sonnet | |
| 9 | L07 | record numerics for every b ≥ 5: τ₀ ≤ b^{−ψ}, A ≤ b^{lA}, m_w(4) ≤ b^{−1−θ_w}, (ii*), (iii*), (Q1), (Q2′) | certs NOTES §0–1 | FejerM4Stmt | 600 | Sonnet | new (b = 5 margin 7·10⁻⁴ in κ) |
| 10 | L04 | b = 6: `|G_{g₆}| ≤ P₆` on ℝ (28 Bernstein cells) | certs NOTES §0, json/amgm_b6 | — | 300 + data | Sonnet | new, cert |
| 11 | L05 | b = 8: `|G_{g₈}| ≤ P₈` on ℝ (34 cells) | certs NOTES §0, json/amgm_b8 | — | 350 + data | Sonnet | new, cert |
| 12 | S07 | Lemma 4 (i) above x_n and (ii′) for odd ν ≥ 3: `W(t) ≤ φ(δ)(2 log q/log(y/δ))²` | Greaves pp. 84–87, r182 §2 | — | 400 | Sonnet | new (ii′ one audit) |
| 13 | S08 | Lemma A part 3 (with η̂ = 0 Greaves' (F4)): `λ₁ + λ_q = g_η(u) + o(1)` uniformly in `q ≥ x^{u_lo}` | r188 §7, r183 §3.3 | — | 700 | Opus | |
| 14 | M02 | Lemma A part 2: `Q(Λ^η) ≤ (c_η + ε)/G(√x)` | r188 §7 | — | 700 | Opus | |
| 15 | L10 | Proposition C_w (cut A₁): scalar conditions ⇒ TL¹_w(θ, κ, θ₀) | r238 §2.7, r160 Prop. C, Palprimes TL1/Asymp | Lemma28Stmt, Lemma29wStmt | 900 | Opus | one audit |
| 16 | L12 | Lemma K (weighted Col bound) | r238 §2.3 | — | 500 | Opus | one audit |
| 17 | L15 | Lemma W_w ranges: Farey total up to y ≤ (log x)^{−A} | r238 §2.8 | LemmaKStmt, SSStmt, TL1w | 700 | Opus | one audit |
| 18 | M03 | (F5): `1/G(√x) ≤ (1 + ε)e^γV(√x)` | Greaves p. 83, HR §5.3 | — | 500 | Sonnet | |
| 19 | M06 | Lemma 7 from `Palprimes.E1.rosserAsymp_of_two_le` | Greaves p. 90 | — | 300 | Sonnet | |
| 20 | M09 | Lemma 10 (exact, even ν) | Greaves p. 93 | — | 300 | Sonnet | transcr, corrected (§2.2) |
| 21 | Q03 | E′: `Σ_{h<p²} |g_J(h/p² + β)|⁴ = p² m_w(4)^j` | squares NOTES §2, pilot ItemH | — | 300 | Sonnet | new |
| 22 | Q02 | `T_K` over square and prime moduli ((3.1), (3.2)) | dossier v5 §3.2 step 3 | — | 400 | Sonnet | one audit |
| 23 | Q01 | reduction `|A^w_{p²} − X_w/p²| ≤ τ(r) Σ_k p^{−2}(…)` | dossier v5 §3.2 step 1 | — | 300 | Sonnet | one audit |
| 24 | L13 | Lemma 2.1_w: `X_w ≥ c > 0` | r238 §2.1 | — | 500 | Sonnet | one audit |
| 25 | L11 | Lemma SS | r238 §2.4 | TL1w | 300 | Sonnet | one audit |
| 26 | L09 | Lemma 2.9_w (inner large sieve, exact fourth moment) | r238 §2.5 | — | 500 | Sonnet | |
| 27 | L08 | Lemma 2.8 (weight-free averaged majorant products) | r160 Lemma 2.8, Palprimes TL1/Ortho | — | 400 | Sonnet | |
| 28 | L14 | regrouping: `Σ_{d≤D} μ²3^ω|R_w(d)| ≤ τ(r)H(D) max_k Farey(k/r)` | r238 §2.2, r169 Lemma R | — | 400 | Sonnet | |
| 29 | M04 | band cost (Lemma 5′) | r183 §3.7 | — | 400 | Sonnet | |
| 30 | M05 | `M₂₃(y) ≤ C V(y)` | Greaves (3.32), Mertens | — | 400 | Sonnet | |
| 31 | S02 | Lemma 2 identity for squarefree `A ∣ P(z)` | Greaves pp. 79–81 | — | 600 | Sonnet | corrected (§2.1) |
| 32 | S01 | Lemma 1 (radical form) | Greaves p. 79 | — | 300 | Sonnet | corrected (§2.4) |
| 33 | S04 | `Σ₂ + Σ₃ ≥ −Σ_{δ∈𝒟, δ∣A} Λ{(A/δ, P(√(y/δ))), φ(δ), w}` | Greaves (3.28)–(3.31) | — | 300 | Sonnet | |
| 34 | S03 | `Σ₄ ≥ 0` | Greaves p. 89 | — | 150 | Sonnet | |
| 35 | S05 | the route's W: (1.8) lines, (3.10), Lemma 4 (iii), φ ≥ 0 on 𝒟 | Greaves pp. 84–87 | — | 300 | Sonnet | corrected (§2.4) |
| 36 | S11 | coefficients: support squarefree `n ≤ y`, `n ∣ P(z)`, `|c(n)| ≤ K3^{ω(n)}` | Greaves p. 89 | LemmaA1Stmt | 400 | Sonnet | |
| 37 | S12 | expansion `Σ_{n∣a} c(n) = Σ₁(A) − (1+ε)Σ_δ φ(δ)(Σ_{d∣A/δ} Λ_δ(d))²` | Greaves (3.6), (3.25) | — | 300 | Sonnet | |
| 38 | S13 | 𝒟 facts: squarefree, primes < z, `y ≤ δ p(δ)²`, `y/δ ≥ y^{(1/2)(2/3)^{84}}` | Greaves (3.15), (3.32) | — | 200 | Sonnet | |
| 39 | S14 | band primes: unique band, `c_δ ≥ 1`, `x ∈ [x_i, x_{i+1}]`, `φ(δ) = U − x` | — | — | 250 | Sonnet | |
| 40 | M01 | main-term identity `Σ c(n)γ(n)/n = M₁ − (1+ε)Σ_δ φγ/δ Q(Λ_δ)` | Greaves Lemma 5 algebra | — | 300 | Sonnet | |
| 41 | S09 | Lemma A part 1 (λ₁ = 1, |λ_d| ≤ C, support) | r188 §7 | — | 300 | Sonnet | |
| 42 | L06 | record majorants `T ≥ |G_g|^p`, all b ≥ 5 | certs NOTES §0 | BernoulliStmt, FejerAbsStmt, Cert6Stmt, Cert8Stmt | 250 | Sonnet | new |
| 43 | L17 | sequence facts: `0 ≤ a_n ≤ M^{N+1}`, support ⊆ Π*_b, `A^w_q = Σ_{q∣n} a_n`, `X_w ≤ 1` | r238 §2.1 | — | 250 | Sonnet | |
| 44 | S15 | facts on `(a, P(z))` | — | — | 150 | Haiku | |
| 45 | S06 | Lemma 3 pointwise (generic) | Greaves p. 84 | — | 120 | Haiku | |
| 46 | L16 | record data facts (digit weight, g(0), g(1) > 0, g ≤ 1/3, 0 < p < 1, H ≤ 2b − 2) | — | — | 200 | Haiku | |
| 47 | L03 | Fejér fourth moment closed form (= pilot ItemN) | certs NOTES §0 | — | done | — | PASS (ported) |
| 48 | L01 | `|G_g| = F_m` (= pilot ItemM) | certs NOTES §0 | — | 150 | Haiku | pilot proof, port `Pilot.e` → `ee` |
| 49 | L02 | Bernoulli (= pilot ItemE) | Mathlib | — | done | — | PASS (ported) |

Totals: 49 items. By tier: Opus 12 (M07, M08, M10, M11, Q04, S10, M12, S08, M02, L10, L12, L15), Sonnet 31, Haiku 4
(S15, S06, L16, L01), done 2 (L02, L03). By part: L (level) 17, Q (squares) 4, S (sieve) 15, M (main term) 13.
Estimated 21k lines for the items, plus data for S10, M12, L04, L05. Kernel certificates: L04, L05 (seconds),
S10 (≈ 10⁷ ops), M12 (3·10⁷–10⁸ ops).

### Recommended first items for the parallel phase
- Risk probes (Opus, start now): M08 and M10 with a written sub-blueprint from HR 1985 first (decides whether the §4
  statements stand), S10 (generate rational band data and the certificate; decides the θ = 0.340 design), M12 (h tables).
- Cheap and independent (Haiku/Sonnet): L01 (port), L16, S15, S06, S13, S14, L17, Q01, Q03, L08, S03, S12, M01, M09.
- Then the level chain L13, L12, L09, L10, L11, L14, L15 and L04, L05, L06, L07, and the squares Q02, Q04.

## 4. Pilot items (lean/omega3/pilot, Pilot/Statements.lean)
| pilot | here | relation |
|---|---|---|
| ItemE | ItemL02 (`BernoulliStmt`) | identical text; proof ported, PASS |
| ItemM | ItemL01 (`FejerAbsStmt`) | identical up to `Pilot.e` ↦ `Palprimes.ee` (same body) and `Pilot.fejerW/fejerK` ↦ `Omega3.fejerW/fejerK` (copied verbatim); the proof's helper lemmas about `e` need renaming |
| ItemN | ItemL03 (`FejerM4Stmt`) | identical text; proof ported (rename `ItemN`), PASS |
| ItemH | inside ItemQ03 | exact fourth moment of a polynomial whose frequencies are distinct mod q; Q03 applies it with q = p² and frequencies b^{N−j}m, p ∤ b |

## 5. How the items fit (skeleton, `Omega3/Skel*.lean`)
- `SkelLevel.level_bound`: L01–L05 → L06; L03 → L07; L06, L07, L08, L09, L16 → L10 (TL¹_w); L10 → L11; L12, L11, L10 → L15;
  L14 + L15 + Palprimes `sum_three_pow_omega_div_le`, `sum_inv_le_log` ⇒ `Σ_{d≤y} μ²3^ω|R_w(d)| ≤ (log x)^{−A}`.
- `SkelLevel.squares_bound`: L06, L07, L16, L17, Q01–Q04 ⇒ square sum `≤ (log x)^{−A}`.
- `SkelSieve.pointwise`: S12 → (S06 with S07 / S10-allowance, S08, S09, S13, S14) → S04 → S03 → S02 → S01, side conditions S05, S15.
- `SkelMain.mainterm_lower`: M01, M02 (+ S10's `c_η ≤ c_i`, S14), M03, M04, M05, M06–M11 (Lemma 6), M12 + M13, Mertens
  (`Palprimes.MT.VB_log`) ⇒ `Σ c(n)γ(n)/n ≥ c/log y` for a fixed ε.
- `Skeleton.count_lower`: sieve sum ≥ X_w·MT − K·level sum (S11 support and bound, L17 exchange), ≤ W(1)(#good·3^{−N−1} + square sum)
  (Palprimes `omega_eq_nu`), X_w ≥ c (L13) ⇒ `MainCount`; `mainTheorem_of_count` ⇒ `MainTheorem`.

## 6. Reused Palprimes results (not items)
`sum_cK_eq_zero` (Proposition S (a)), `palVal_injective`, `digits_palVal`, `mem_piStar`, `omega_eq_nu`, `MT.VB_log`,
`E1.VB_pos'`, `sum_three_pow_omega_div_le`, `sum_inv_le_log`, `E1.rosserAsymp_of_two_le` (for M06, M11), `large_sieve`
(L09), `majorant_sum_le` pattern (L08), `sum_sq_fourier_le_collision` (Q03), `MainTerm/PrimeRiemann` (M04, M11).
