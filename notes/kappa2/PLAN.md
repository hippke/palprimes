> Repository note (2026-11-25): written in the working package `omega-2/lean`, where the library was called `OK2`. Here it is `lean/KappaOmega2/` (namespace `KappaOmega2`); `Omega2.LemmaR` and `Omega2.FejerPsi4` are `KappaOmega2.LemmaR` and `KappaOmega2.FejerPsi4`, the statement file `OK2/Check/Solution.lean` is now part of `KappaOmega2/FinalK.lean`, and the build uses lake instead of `k2build.py`.

# Lean plan. Ω ≤ 2 for κ-palindromes (Theorem K2 / r298 Theorem Ω2_κ)

Written 2026-11-25 (omega-2 session). Plan only, nothing started. Reference for effort: the Omega3 package
(palprimes/lean/Omega3, Ω ≤ 3 for b ≥ 5, 49 items, about 37.5k lines including skeleton and data, 0 sorry, six kernels).
Its parts measured 9.6k lines (sieve S), 18.0k (main term M), 4.6k (level L), 2.0k (squares Q), 1.1k (skeleton).

## 0. Target and design decisions

Target (frozen statement, Mathlib definitions only).
```
def IsKappaPal (b m n : ℕ) : Prop :=
  let d := Nat.digits b n; m ≤ d.length / 2 ∧ ∀ i < m, d.getD i 0 = d.getD (d.length - 1 - i) 0
theorem infinite_kappaPal_Omega_le_two (b : ℕ) (hb : 3 ≤ b) :
  {n : ℕ | IsKappaPal b (⌊(7/10 : ℝ) * (Nat.digits b n).length / 2⌋₊) n ∧ Nat.IsAtMostAlmostPrime 2 n}.Infinite
```
plus a counting form (≥ c·X/log x elements of length L with Ω ≤ 2 and all prime factors > x^{c₀}).

Decisions that keep the Lean proof small.
1. Sieve level θ = 103/200 = 0.515 (not 0.5114). Greaves R = 2 main term 𝓜 ≥ 2.16·10⁻² there (logs/greaves_R2.log), three
   hundred times the margin at 0.5114, so the h-table certificate is easy. P⁻ exponent θT_c = 0.049.
2. One value κ = 7/10 in every base b ≥ 3 (κ₂ at θ = 0.515 with p → 1 is 0.7085 for b = 3, 0.7088 for b = 4, ≥ 0.735 for b ≥ 5).
   At p = 999/1000, θ_p(7/10) − 0.515 ≥ 0.0052 in base 3, the thinnest base.
3. Only the exact Fejér family (PROOF_K2 §6b). No numerical torus certificates (the t02 block of base 4 would cost about
   10⁸ certified cells). lA = 0, so the cut is a fixed tiny a′ and no D-dependent cut is needed. Base 2 is left out
   (κ₂(2) < 2/3, and it needs the r145 2D block).
4. Squares without Baier–Zhao. For κ-palindromes the per-modulus Parseval bound (Omega3's route E′) suffices on the whole
   range (x^{c₀}, x^{θU}]. With N = Wb^{2j} ≍ Q² the large-value count is x^{4a′}Q^{−1}(N + Q²)b^{−jψ₄}W^{−1}, exponent
   c(1 − ψ₄) − w(1 − ψ₄/2) + 4a′ < 0 for ψ₄ ≥ 1 and Q² ≥ W, and Q² < W is trivial counting (Σ_{p≤Q}#outer ≪ X_aQ/W).
   [own, to be checked on paper in item P0 before any Lean work]
5. Reuse Omega3 wherever its statements are parametric, re-instantiate where constants (thS, UU, mm, Wf) are hard-coded.

## 1. Items

Tier as in Omega3 (Opus = hard, Sonnet = routine, Haiku = small). Lines are estimates for new Lean code.

| # | item | content | reuse | lines | tier | risk |
|---|---|---|---|---|---|---|
| P0 | paper blueprint | exact rational parameters (θ, U, V, T_c, W), Greaves' pointwise inequality at R = 2, squares via route E′ for κ-palindromes (decision 4), K̃ with explicit constants, statement freeze, independent audit | PROOF_K2, r298, r167 | (doc) | Opus + audit | medium, decides S and Q |
| D1 | definitions | IsKappaPal, the weighted sequence a_n = 1_E(u₀)Πg(u_i) on n = Σu_ic_i + wb^m, X_a, A_d, Statements, Challenge file | Palprimes.Defs | 400 | Sonnet | low |
| D2 | digit bijection | n ↔ (u, w), injectivity, exact length L, coprime to b, IsKappaPal holds, counting #support | Palprimes Digits (palVal) | 600 | Sonnet | low |
| A1 | Lemma R, E (Diophantine) | done in omega-2/lean (LemmaR.lean, LemmaR2.lean), port | omega-2/lean | 50 | Haiku | none |
| A2 | Lemma E energy | Diophantine core ⇒ ∫|Π G(c_i·)M(b^m·)|⁴ = Π∫|G|⁴·∫|M|⁴ (collision count form) | Omega3 Q03 / pilot ItemH, Palprimes collision counts | 500 | Sonnet | low |
| F1 | Fejér family | |G_g| = F_M (odd b), |G_g| ≤ (F_M + F_{M+1})/2 (even b), T_p ≥ |G_g|^p by weighted AM–GM, PD, T_p(0) = 1 | Omega3 L01 (odd b, done), L02 Bernoulli | 300 | Sonnet | low (even b is new) |
| F2 | ψ₄ ≥ 1 | closed forms of ∫|G_g|⁴ (odd: Omega3 L03 done) plus even b, then FejerPsi4.lean | Omega3 L03, omega-2 FejerPsi4 | 400 | Sonnet | low |
| F3 | numeric conditions | for every b ≥ 3, at p = 999/1000, a′ fixed: (i), (ii), (iii) of C_κ and CQ_κ as rational inequalities in log b (uniform in b via ψ_T ≥ 1 − log_b 2 for b ≥ 9, explicit for 3 ≤ b ≤ 8) | Omega3 L07 pattern | 600 | Sonnet | low to medium (uniformity in b) |
| K1 | middle majorant K̃ | K̃ = (π²/4)Σ2^{−kp}F_{M_k} + (4/W)^p ≥ |M|^p, PD, support |s| < W/2, K̂(0) ≪ W^{−p}log W, K̃(0) ≪ 1 | Palprimes Fejér kernels (Major) | 700 | Sonnet | medium (real analysis bookkeeping) |
| L1 | Proposition C_κ | cut, large values by large sieve with A2, small values by expansion with A1 and K1, all primitive pairs, every dyadic D ∈ [x^ε, x^θ] | Omega3 L08–L10, Palprimes large_sieve, TL1 | 1500 | Opus | medium |
| L2 | Lemma W_κ | non-primitive h, small moduli by the free block (|r_d| ≤ X_a/W), dyadic sum, Σ μ²3^ω|r_d| ≤ (log x)^{−A} | Omega3 L14, L15, Palprimes sum_three_pow_omega | 600 | Sonnet | low |
| Q1 | squares CQ_κ | trivial range, small values (diagonal by Lemma R at moduli p²), large values by per-modulus Parseval (decision 4) | Omega3 Q01–Q04 (route E′) | 1200 | Opus | medium (decided by P0) |
| S1 | Greaves R = 2 pointwise | coefficient vector c(n) with Σ_{n|a}c(n) ≤ [ν_{y,U}(a) ≤ 2]w(P⁻(a)), |c(n)| ≤ K3^{ω(n)}; Lemmas 1, 2 generic, the R = 2 Σ-terms new, no bands | Omega3 S01–S15 (R = 3 with bands) | 3000 | Opus + Sonnet | medium to high (hard-coded R = 3 structure) |
| M1 | main term, Lemmas 5–12 | M₁ − M₂₃ and Lemmas 7–12 at the R = 2 constants | Omega3 M01–M11 (HR transcriptions) | 2500 | Opus | medium (re-instantiation of 18k lines, constants hard-coded) |
| M2 | h-table certificate | 𝓜(W) ≥ 0.02 at θ = 0.515, R = 2, envelope W, `decide +kernel` data | Omega3 M12, M13, r167 certM | 800 + data | Opus | low (large margin) |
| K2 | skeleton | sieve sum ≥ X_a·MT − K·level sum, ≤ W(1)(#good·max a_n + square sum), max a_n ≤ (1/M)^{m−1}, counting form, infinitude | Omega3 Skel*, Corollaries | 1200 | Opus | low |
| V1 | verification | build, axioms, leanchecker, comparator against the Challenge file, several kernels | Omega3 audit scripts | (scripts) | Sonnet | low |

Totals. About 14k to 15k new lines (P0 excluded), roughly 40 % of Omega3, because the level part is simpler (exact
densities 1/d, no Lemma K, no Lemma SS, no torus certificates, no D-dependent cut) and squares need no Baier–Zhao.
The large items are S1 and M1, and both are ports of existing code to R = 2.

## 2. Milestones

| milestone | content | items | effort |
|---|---|---|---|
| M-A, sieve check | Ω ≤ 2 for κ-palindromes with κ < 0.48 from the free block alone (level 1 − κ, squares by trivial counting since κ < 0.504), no majorants | D1, D2, S1, M1, M2, K2 (with a trivial level) | about 9k lines, most of the risk |
| M-B, main theorem | κ = 7/10 in every base b ≥ 3 | + A1, A2, F1, F2, F3, K1, L1, L2, Q1 | about 5k to 6k more lines |
| M-C, audit | six-kernel check as for Omega3 | V1 | scripts, hours |
| optional | κ arbitrary < κ_L(b) as a hypothesis on κ, base 2 with Palprimes' 2D blocks, θ closer to 0.5114 | | 1k to 3k lines |

M-A comes first because it tests the only real risk (Greaves at R = 2 with ported main-term code) without any analytic
level input. It is a weak theorem by itself (below 9/20 there is a prime result), but it isolates the sieve.

## 3. Calendar estimate

Omega3 went from blueprint to a six-kernel audit within about a day of parallel agent work, 49 items. With the same
setup this plan needs about 18 items. P0 with its audit about half a day, M-A about a day, M-B about a day, audit hours.
So two to three days of parallel agent work, if P0 confirms the R = 2 pointwise inequality and the Parseval squares.
Without parallel agents (one session), multiply by roughly 5.

## 4. Risks

1. Greaves at R = 2 (S1). Omega3 encodes R = 3 with Σ₂ bands and Σ₃ caps in hard-coded definitions. R = 2 needs its own
   Σ-decomposition. Greaves' paper covers general R, but the Lean structure must be redone. Probe first in P0.
2. Main-term transcriptions (M1). Omega3's M07, M08, M10, M11 are transcriptions of Greaves §4 that rest on
   Halberstam–Richert 1985 (moderate confidence in Omega3's own notes). At R = 2 they are re-instantiated, not re-derived.
3. Squares (Q1). Decision 4 is my own observation from this session and is not audited. If it fails, the fallback is
   Baier–Zhao in Lean, which is a large separate project (thousands of lines, not in Mathlib).
4. Uniformity in b (F3). Every inequality must hold for all b ≥ 3 at once. The Fejér bound ψ_T ≥ 1 − log_b 2 makes this
   monotone for large b, small b are explicit cases.
5. Ownership. Omega3 lives in palprimes/lean. The new package should be a separate lake package that imports Palprimes
   and Omega3 by path and never writes there.
