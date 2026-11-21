# Lean formalization plan: Ω ≤ 5 palindromes in every base

2026-11-20, main session. Target: a sorry-free Lean 4 + mathlib proof of

    theorem infinite_palindromes_omega_le_five (b : ℕ) (hb : 2 ≤ b) :
        {n : ℕ | IsPalindrome b n ∧ Nat.IsAtMostAlmostPrime 5 n}.Infinite

Source proof: `r37_writeup/PROOF_buniform.md` (Prop. V, Lemma 3, §3) on top of Tuxanidy–Panario v3 (TP, arXiv 2307.16637v3).

## Status 2026-11-21 (20:40 CET): DONE
`PalLean.infinite_palindromes_omega_le_five` is proved, sorry-free, using only the standard axioms. That is 12.6k lines in 24 files, about the estimate in §4. Changes against the plan:
- The sieve (M12–M14) uses no fundamental lemma and no Dickman ρ. The ingredients are:
  - exact inclusion–exclusion at w = ⌊log x/8⌋;
  - one Buchstab step;
  - Selberg's Λ² sieve (PNT+ port) with lower bounds for S from Rankin's trick and a one-prime smooth-number bound;
  - Richert weights on [x^{1/20}, x^{23/100}) with λ = 8/5;
  - prime sums over rational grids from Mertens 2;
  - a generated rational certificate (`plan/sieve_route`).
- Mertens 1–3 and γ < 0.5773 were ported from PNT+ (`Mertens.lean`).

## 0. Installed
- elan 4.4.0 in `~/.elan`, Lean `v4.37.0-rc1`, mathlib `v4.37.0-rc1` (cache downloaded, 9133 files).
- Project `lean/PalLean` (now `lean/` in this repository). `lake build` works (33 s).
- `PalLean/Statement.lean` holds the main theorem and Lemma 3 as `sorry` statements. Both compile.
- Reference clone: `ext/PrimeNumberTheoremAnd` (PNT+, Lean v4.35, Apache 2.0, 172k lines).
- Use: `export PATH=$HOME/.elan/bin:$PATH; cd lean; lake build`.

## 1. What can be reused

| Need | Where | Status |
|---|---|---|
| Ω, `IsAtMostAlmostPrime k n` | mathlib `NumberTheory/AlmostPrime.lean` | ready |
| `Nat.digits`, `Nat.ofDigits`, `List.Palindrome` | mathlib `Data/Nat/Digits`, `Data/List/Palindrome` | ready, but the digit API is clumsy |
| Additive characters, orthogonality, DFT on `ZMod N` | mathlib `AddChar`, `Analysis/Fourier/ZMod`, `FiniteAbelian/PontryaginDuality` | ready |
| `Real.fourierChar`, AddCircle Fourier, Parseval | mathlib `Analysis/Fourier/AddCircle` | ready (for the large sieve) |
| Cauchy–Schwarz, Hölder on finite sums | mathlib `inner_mul_le_norm_mul_norm`, `Finset.inner_mul_le_norm_mul_norm` | ready |
| Möbius, multiplicative functions, ω, τ | mathlib `ArithmeticFunction` | ready |
| Chebyshev θ, ψ bounds, Abel summation | mathlib `NumberTheory/Chebyshev`, `AbelSummation` | ready |
| Mertens 1, 2, 3 (Σ log p/p, Σ 1/p, Π(1−1/p) with error O(1/log x)) | PNT+ `IEANTN/Mertens.lean` (2460 lines, no sorry) | vendor and port |
| Selberg Λ² sieve, S ≤ X/G + Σ 3^ω(d)\|R_d\| | mathlib `SelbergSieve.lean` (set-up) + PNT+ `Mathlib/NumberTheory/Sieve/*` (1544 lines, no sorry) | vendor and port |
| Brun–Titchmarsh (template for using the sieve) | PNT+ `BrunTitchmarsh.lean` | example |
| Large sieve inequality | nowhere (Zulip to-do lists only) | write |
| Divisor bound τ(n) ≤ C_ε n^ε | nowhere (only `card_divisors_le_self`) | write |
| Lower-bound linear sieve, fundamental lemma, Buchstab, weighted sieve | nowhere | write |
| Large sieve for square moduli (Baier–Zhao) | nowhere | write, or avoid (see §3) |

## 2. Simplifications compared with the paper route
Checked numerically in `plan/sieve_feasibility.py` (logs `plan/feas*.log`).
- **No Greaves or Jurkat–Richert sieve.** TP's Lemma 11.1 cites Greaves' book. A crude sieve suffices at our level: Selberg Λ² upper bound, a fundamental lemma from Brun's pure sieve (w = x^{c/log log x}), one Buchstab step, Richert's logarithmic weights on distinct primes. Squarefree case: positive at θ = 0.215 (W/XV = +0.026) and at θ = 0.24 (+0.49). For calibration, the optimal functions break even at θ = 0.2109 = 1/Δ₅, as in TP.
- **Fixed parameters instead of θ → 1/4.** Take for example κ = 0.97, θ = 0.245. All ε bookkeeping becomes concrete numbers.
- **Our own equidistribution proof instead of TP §8–9 verbatim.** Prop. V at short lengths L' ≍ log q covers every dyadic range R ≥ R₀(b). Col's L^∞ bound covers q ≤ R₀ and the polylog range. TP's 1/3 ≤ δ ≤ 2/5 Hölder machinery is not needed.
- **Only lower bounds.** "Infinitely many" needs S > 0 for large x, not ≍.
- **Remainders with 3^ω(d) weights are harmless.** Fourier grouping turns them into Σ_q 3^{ω(q)}/q Σ*_h |S(h/q)|, and 3^{ω(q)} = q^{o(1)} is absorbed by the power saving R^{−c} for large R. So the Selberg sieve's remainder form works as it is.
- **Prop. V needs no palindrome or digit API.** It is a statement about ψ(t) = (φ_b(t)/b)² and c_k = b^k + b^{2L−k}. The digit API enters only at the very end (M1, M2).

## 3. Square divisors (TP Prop. 10.1): resolved in S0 (2026-11-20)
- Need. Every Richert-type weighted sieve needs Σ_{x^α ≤ p ≤ x^{c₀}} A_{p²} ≪ X/log³x. Our crude sieve needs c₀ ≈ 0.19 at θ = 0.249 (`plan/feas_c0*.log`). TP's Lemma 11.1 asks for p up to D^{1/u_5} = D^{243/244}, just below x^{1/4}.
- **Proposition W** (`plan/squares/PROP_W.md`). For every b and every c < 1/4: Σ_{P ≤ p < 2P} A_{p²} ≪ X/P + X P^{−δ} for P ≤ x^c, with δ = θ_b·a/4 > 0. Same two-level Cauchy–Schwarz as Prop. V: outer block V, then K1 (doubled), K2 (single, shared), K3 (doubled). Every step is a collision count over complete residue systems mod p², using Lemma 3, Σ_h|f̂(h/q)|² = q·Pr(Z ≡ Z′ mod q), Pr(W = w) ≤ ‖f‖², and the fact that a nonzero |w| < x has ≤ log x/(2 log P) prime-square divisors p² ≥ P². No large sieve, no divisor bound, no Baier–Zhao.
  - Audit (`plan/squares/AUDIT_W.md`, independent code): correct. One fixable interface gap (shorter lengths and the top block of P*_b(x) are O(b log x) cylinders, handled by running W at c″ > c), now written into PROP_W.md.
  - Small-case checks: `plan/squares/chain.log`, `audit/audit_w.log`.
- **Prime cubes** are trivial: A_{p³} ≤ 2b^{3/2}X p^{−3/2} by a middle-block injectivity count. With cubes excluded, the crude sieve needs square control only up to x^{0.167} at θ = 0.249 and x^{0.175} at θ = 0.24 (`plan/feas_cubes*.log`). Optional, since W reaches any c < 1/4.
- Sieve margins with W at c₀ = 0.23 (`plan/feas_c0c.log`): crude W/XV = +0.40 (θ = 0.235), +0.46 (θ = 0.24), +0.51 (θ = 0.245). So θ = 0.24, c₀ = 0.23 is a comfortable fixed choice (κ near 0.96).
- Consequence: options (a) Baier–Zhao and (d) conditional milestone are no longer needed. Baier–Zhao and Zhao 2004 are on arXiv (math/0512271, math/0508125) if ever wanted.

## 4. Steps and effort (lines of Lean, rough ranges)

| # | Component | Depends on | Lines |
|---|---|---|---|
| S0 | Design note: fix κ, θ, α, β, λ, c₀ with margins. Rigorous discretized check of the crude sieve inequality (Python, rationals). Square-divisor route: **done**, Prop. W (§3) | – | (Python, remaining ½ day) |
| S1 | Blueprint: all definitions and the statements of M1–M13 as `sorry`, wired to the main theorem so that the main theorem compiles from them. **Done 2026-11-21** (`BLUEPRINT.md`, 595 lines, builds; main theorem proved from 4 interfaces) | S0 | 400–700 |
| M3 | Lemma 3. **Done 2026-11-21**, 140 lines of proof, by a lowest-digit/top-digit argument instead of the carry induction | – | 200–350 |
| M2a | Collision probability, Fourier factorization, residue identity, point-mass bound. **Done 2026-11-21**, about 590 lines (above the estimate, mostly the exact count b(2b²+1)/3 and the coordinatewise split of digit quadruples) | M3 | 300–500 |
| M4 | Large sieve, Gallagher form: Σ_r \|Σ_{n<N} a_n e(nα_r)\|² ≤ (πN + δ⁻¹)‖a‖², plus spacing of Farey points h/q and of their b^m-twists | – | 800–1200 |
| M5 | Divisor bound τ(n) ≤ C_ε n^ε, 3^{ω(n)} = n^{o(1)}, τ* = b^{o(L)} | – | 300–500 |
| M6 | TP L² lemma (divisor partner): Σ_{q~Q} Σ_h \|f̂(h/q+β)\|² ≤ 2Q(#q‖f‖² + τ*) | M5 | 400–600 |
| M7 | **Proposition V** (Cauchy–Schwarz split, A1 by M4, A3 by M6, exponent bookkeeping) | M2a, M4, M6 | 600–1000 |
| M8 | Col's L^∞ bound: Φ at h/q + k/(b³−b), (q, b³−b) = 1, ≤ b^M exp(−σ M/log q) | – | 700–1200 |
| M9 | Farey L¹ bound (§3: shallow, inner, rest blocks, twist h ↦ hb^{N−μN}, dyadic ranges, uniform o(N)) | M6, M7, M8 | 800–1300 |
| M1 | Palindromes ↔ digit vectors, injectivity, count, positive density of P*. **Done 2026-11-21**, about 650 lines | – | 600–900 |
| M2 | Exponential sum over P_N as product of φ_b(c_kα) (with middle digit and leading-digit restriction) | M1 | 300–500 |
| M10 | Level of distribution: Σ_{d≤D,(d,b³−b)=1} 3^{ω(d)} \|A_d − X/d\| ≪ X/log^C x. Fourier mod d, grouping into reduced fractions, characters mod b³−b, CRT | M2, M8, M9 | 1200–2000 |
| M11 | **Proposition W. Done 2026-11-21**, about 1200 lines, proved in physical space (Cauchy–Schwarz on residue fibres + splicing of independent digit blocks), b-adic prime blocks with m = ⌊N/20⌋ | M2a, M3 | 500–900 |
| M12 | Mertens inputs: port PNT+ Mertens (Π(1−1/p), Σ1/p), and prime sums ≈ integrals Σ_{u≤p<v} F(log p/log x)/p by Abel summation | – | port 300–600 + 400–800 |
| M13 | Sieve: Λ² upper bound with main term via smooth-number sums (port PNT+ Selberg), Brun pure-sieve fundamental lemma, Buchstab step, Richert weights, Ω ≤ 5 conclusion with the square bookkeeping | M12 | 2000–3500 |
| M14 | Rigorous numerics in Lean: positivity of λf_c(s) − ∫(1−u/β)F_c(…)du/u through monotone step bounds on about 50–100 intervals (norm_num, `Real.log`/`exp` bounds) | M13, S0 | 1000–2000 |
| M15 | Assembly: x = b^{2N+1}, choose parameters, main theorem | all | 300–500 |

Totals: about **11,000–17,500 lines** (S0 removed the Baier–Zhao option of 15,000–26,000). For scale, PNT+ has 172k lines and mathlib's Selberg file has 406.

Milestones that stand on their own:
- **A. Prop. V in Lean** (M3, M2a, M4, M5, M6, M7): about 2,600–4,200 lines. This is the new mathematics, machine-checked.
- **B. Level of distribution θ < 1/4 for palindromes** (A + M8, M9, M1, M2, M10): about 7,000–11,000 lines. Theorem 1 of the write-up.
- **C. Prop. W in Lean** (M3, M2a, M11): about 1,000–1,700 lines, shares Lemma 3 and the collision lemma with A.
- **D. Unconditional main theorem** (B + C + M12–M15).

## 5. Recommendation: where to start
Start with the new and critical parts, not with the digit API.
1. **S0 square-divisor research: done (2026-11-20).** Prop. W closes the gap with our own tools, so nothing external must be formalized. What remains of S0 is fixing the numeric parameters (θ = 0.24, c₀ = 0.23 look comfortable) and a rigorous rational check of the sieve inequality.
2. **S1 blueprint: done (2026-11-21).** See `BLUEPRINT.md` for the statement map and five design decisions (one length class, 3^ω weights through the Fourier route, M14 deferred to the lower-bound design).
3. **Milestone A: M3 → M2a → M4 → M5/M6 → M7, with M11 (Prop. W) right after M2a or at the end of A.** M11 needs only M3 and M2a, so it is a cheap second result on the same base. Lemma 3 is a quick, self-contained warm-up. The large sieve is reusable infrastructure that mathlib lacks. Prop. V is the new idea. None of them needs palindromes or digits.
4. Then M8–M10 (milestone B), the sieve (M12–M14), and the digit API last (M1, M2). The digit API is routine but tedious, and its exact shape follows from what M10 needs.

Starting "at the beginning" (digits, palindromes, exponential-sum factorization) would spend the first 1,000+ lines on routine API before touching anything that could fail.

## 6. Conventions
- One file per component under `PalLean/`, names as in §4 (`LemmaThree.lean`, `LargeSieve.lean`, `PropV.lean`, …).
- Explicit constants and `∃ C, ∀ N ≥ N₀` forms rather than `IsBigO` across files. Asymptotic o(N) losses as explicit `ε`-statements.
- Vendored PNT+ files keep their copyright headers (Apache 2.0) and go in `PalLean/Vendor/`.
- Do not trust `sorry`-free builds blindly: at milestones, run `#print axioms` on the top theorem (only `propext`, `Classical.choice`, `Quot.sound` allowed).
