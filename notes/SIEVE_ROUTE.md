# Sieve route for the Lean proof (M12–M14), 2026-11-21 evening

Replaces the "crude sieve" sketch in PLAN_LEAN.md §2 and the open M14 choice in BLUEPRINT.md item 5.
No Dickman ρ, no fundamental lemma, no integrals in Lean: only Mertens 1–3 (ported from PNT+),
Selberg's Λ² bound (ported from PNT+), Rankin's trick, a one-prime smooth-number bound, and finite
step-function sums over geometric grids. Numerics: `crude3.py` (limit values).

## Setting
- A finite, 1 ≤ n ≤ x and (n, B) = 1 for n ∈ A, X = #A, L = log x, r_d = A_d − X/d.
- Level hypothesis (LH): Σ_{q ≤ D, (q,B)=1} 3^ω(q) |r_q| ≤ X/L³ with D = x^{6/25}.
- Squares (SH): Σ_{x^{1/20} ≤ p ≤ x^{23/100}} A_{p²} ≤ X/L³.
- Parameters: w = L/8, z = x^{1/20}, y = x^{23/100}, λ = 8/5.
  (z changed from x^{3/50}: margin +0.32 → +0.40.)
- Pset(t) = primes q < t with q ∤ B, P(t) = Π Pset(t), V(t) = Π_{Pset(t)} (1 − 1/q), β = φ(B)/B.
  For t > B: V(t) = V₁(t)/β with V₁ the full Mertens product.

## Chain
1. **Ω bookkeeping** (`richert_omega_le_five`, no lower sifting limit needed). If no p² | n for p < y and
   pen(n) = Σ_{p | n, p < y} (1 − log p / log y) < λ, then Ω(n) < λ + log x / log y = 1.6 + 100/23 < 6.
2. **Weighted sum.** S0 = sifted(A, z). W = Σ_{n ∈ S0} (λ − pen(n)) = λ #S0 − Σ_{z ≤ p < y} w_p #S0_p.
   pen ≥ 0, so W > λ · #{n ∈ S0 : ∃ p < y, p² | n} gives a good n. The bad count is ≤ X/L³ by SH
   (p < z cannot divide n ∈ S0).
3. **Start.** P(w) ≤ 4^w = x^{log 4/8} < D, so S(A, w) = Σ_{d | P(w)} μ(d) A_d = X V(w) + O(X/L³) exactly.
4. **Buchstab.** #S(A,w) − #S(A,z) ≤ Σ_{w ≤ p < z} #{n ∈ A : p | n, Pset(p)-free} (least prime factor).
5. **Selberg** for E_p = A.filter (p ∣ ·), mass X/p, primes Pset(p) (Buchstab) or Pset(z) (Richert), level D/p.
   Remainders are r_{pd} with all primes of d below p, so (p, d) ↦ pd is injective: total ≤ 2X/L³.
   Main terms X/(p S_p), S_p = Σ_{l | P, l² ≤ D/p} 1/φ(l).
6. **Lower bounds for S(t, ξ)** (sifting limit t, l ≤ ξ):
   - (Rankin) S ≥ V(t)^{-1} (1 − τ), τ ≤ ξ^{−a/log t} exp((e^a − 1)(1 + c₁/log t)), from Π(1 + (q^σ − 1)/q) and
     q^σ − 1 ≤ (e^a − 1) log q / log t, Mertens 1.
   - (smooth) S ≥ Σ_{n ≤ ξ, (n,B)=1, P⁺(n) < t} 1/n ≥ H_B(ξ) − Σ_{t ≤ p ≤ ξ} H_B(ξ/p)/p, H_B(u) = β log u + O_B(1).
     Gives S ≥ β log t · g_K(v) − O_B(1), v = log ξ / log t, g_K = v − log r Σ_j (v − r^j)_+ (grid r^j, Mertens 2).
     Limit: 2v − v log v − 1 on [1, e]. Monotone in ξ, so cap v at e.
7. **Telescoping.** V(w) − V(z) = Σ_{w ≤ p < z} V(p)/p (all p ≥ w > B). So
   #S0 ≥ X [V(z) − Σ_{w ≤ p < z} (V(p)/p)(F_p − 1)] − 3X/L³ with F_p = 1/(V(p) S_p).
8. **Prime sums → finite sums.** On u-intervals [u_i, u_{i+1}) with u_{i+1}/u_i = r, Mertens 2 gives
   Σ 1/p ≤ log r + C/(u_i L). The region p < x^{u₀} (u₀ = 1/100) uses Rankin only and Mertens 1:
   (weight log z/log p)·τ_p ≤ K·(log p / L), total ≤ K(u₀ + c/L), negligible.
   Errors that are not multiplicative in (F_p − 1) appear only for p ≥ x^{u₀}, where they are o(1).
9. **Numerics** (limit, `crude3.py`): f_c = 1 − ¼∫_3^∞(F_c − 1) = 0.941, T = Σ_R ≈ 1.109, λ f_c − T = +0.397
   with F_c(s) = min(e^γ max(1, 2/s), e^γ/g(s/2), 1/(1 − τ(s))), τ(s) = min_a exp(−a s/2 + e^a − 1).
   With only γ < 2/3 (mathlib) the margin is +0.153. Lean check: finitely many rational inequalities.

## Lean inputs
- Mertens 1, 2, 3 (`PalLean/Mertens.lean`, port of PNT+ IEANTN/Mertens.lean).
- Selberg (`PalLean/Selberg.lean`, port of PNT+ Sieve, `selberg_concrete`).
- Everything else written here.

## Discrete certificate (geom.py, discrete.py)
- Interval sums use Mertens 2 on (x^{u_i}, x^{u_{i+1}}] with u_{i+1}/u_i ≤ ρ, sup of each monotone factor at the
  worse endpoint. Rational geometric grids with ratio ρ (log ρ bounded once by Taylor) keep everything rational
  except log ρ, e^γ, e.
- Margins λ(1 − e_B) − e_R (u₀ = 1/100, v cap 2.7, Rankin a = log k with k^{−⌊v⌋} e^{k−1}):
  γ < 0.5773: m = 8 → +0.04, m = 16 → +0.22, m = 32 → +0.31 (m = grid points per octave, all three grids).
  γ < 2/3: m = 32 → +0.03 only. So an upper bound γ < 0.58 is wanted (H_n − log n, n ≈ 128, or PNT+).
- Sizes at m = 16: Richert 36 intervals, Buchstab 38 intervals, inner smooth grid ≤ 23 terms.

## Lean status and assembly plan (2026-11-21 evening)
Done (all compile, no sorry): `Mertens.lean` (port), `Selberg.lean` (port, `selberg_concrete`), `SieveG.lean`
(`rankin_rel`, `factored_le_selbergS`, `HB_approx`), `SieveComb.lean` (`PB`, `card_sift_ge`, `buchstab_le`,
`exists_good_of_weighted`, `HB_le_factored_add`), `SieveSums.lean` (`prime_grid_sum`), `SieveMain.lean`
(`selS`, `betaB`, `CsB`, `smooth_explicit`, `rankin_explicit`, `prod_PB_mul_beta`), `richert_omega_le_five`.

Assembly of `sieve_omega_le_five` (x large, L = log x, X = #A > 0, R = level sum ≤ X/L³):
- Thresholds: W = ⌊L/8⌋₊ (> B, ∏ PB B W ≤ 4^W ≤ D), Zc = ⌈x^{1/20}⌉₊, Yc = ⌈x^{23/100}⌉₊.
- S0 = A.filter (PB B Zc-free); bad n := ∃ p ∈ SH range prime, p² ∣ n; #bad ≤ X/L³.
- Σ_{S0} pen = Σ_{p ∈ RP} w_p #S0_p, RP = (Ico Zc Yc).filter prime (prime factors < y of n ∈ S0 are ≥ Zc).
- #S0_p ≤ Selberg (PB B Zc, mass X/p, level D/p); Buchstab terms: Selberg (PB B p, X/p, D/p).
  Remainders: (p, d) ↦ pd injective (p ∤ d, all primes of d below p), so total ≤ 2R.
- #S(W) ≥ X V(W) − R (`card_sift_ge`); telescoping V(W) − V(Zc) = Σ_{BP} V(p)/p.
- Core: (H_R) Σ_{RP} w_p/(p selS') ≤ e_R V(Zc), (H_B) Σ_{BP} (1/(p selS) − V(p)/p) ≤ e_B V(Zc),
  λ(1 − e_B) − e_R ≥ c₀ > 0, then W ≥ c₀ X V(Zc) − 3λR > λX/L³.
- Per-interval bounds as `∀ᶠ x in atTop` (one per grid interval, combined by `Filter.eventually_all`):
  Richert grid starts at a₀ = 49/1000 (covers p = Zc), ladder v_i < 10(0.24 − b_i) strictly (Zc ≈ x^{1/20} ceil);
  Buchstab smooth/Rankin with t = p, v ≤ 0.12/b_i − 1/2 exact.
- Tail p ≤ x^{u₀} (u₀ = 1/100): Rankin k = 3, V(p)/V(Zc) ≤ L/(4 log p), s e^{−αs} ≤ 1/(αe),
  then Σ log p/(pL) ≤ u₀ + c₁/L (Mertens 1): tail ≤ 0.011 V(Zc).
- Certificate (cert.py, 36/16/18/20 grids): margin +0.175 before tail and η-slacks.

## DONE 2026-11-21 (20:40 CET)
`sieve_omega_le_five` is proved, so the main theorem `infinite_palindromes_omega_le_five` holds with standard axioms only. Certificate: `gen_cert.py` and `gen_lean.py` → `PalLean/SieveCert.lean` (48 + 20 intervals, margin +0.158).
