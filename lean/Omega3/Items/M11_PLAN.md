# M11 sub-blueprint: Greaves 1986 Lemma 12, `|E11(y) − 2e^γV(y)𝓜(W)| ≤ εV(y)`

Written 2026-11-24 20:50 CET (`date`). Frozen statement:
```
ItemM11 : ∀ b, 2 ≤ b → Lemma7Stmt b → ∀ ε > 0, ∃ y₀, ∀ y ≥ y₀,
  |E11 b y − 2 e^γ VB b y · mvalW| ≤ ε VB b y
```
Verdict: **believed true as stated**; no counterexample, no false hypothesis. The transcription of E11 against
𝓜(W) and h86 was re-derived term by term (§1). Proved in Lean (§3).

## 1. Term-by-term limits (t = log p/log y, g(p) = rhoB/p, V = VB b)
Inputs: (I1) `σ⁺(η) = T⁺(η, η^{1/3}) = 2e^γV(η)(1 + o(1))`: Lemma 7 at s = 3 gives `e^γV(√η)(1+o(1))`, and
`V(√η) = 2V(η)(1 + o(1))` by Mertens (VB_log). (I2) `V(y/m') = V(y)/(1 − log m'/log y)·(1 + o(1))` uniformly for
`m' ≤ y^{1−c}` (VB_log). (I3) `T⁻(y, y^{1/2}) = V(√y)(f(2) + o(1)) = o(V(y))`, `f(2) = 0`: this is **not** in Lemma 7
(only `T⁺`); it needs Palprimes `E1.rosserAsymp_of_two_le` (Sminus at s = 2) plus the identification
`Tpm b false y w = Sminus b y s` (the same link M06 needs for `Splus`). (I4) prime Riemann sums:
`Σ_{y^a ≤ p < y^c} g(p)F(t) → ∫_a^c F(t)dt/t` for F of bounded variation (Palprimes MainTerm/PrimeRiemann) and the
iterated version for the chain sums (MainTerm/Chains, Tuples, Regular of the Ω ≤ 4 Mval).
- Term 1 `W1·T⁻(y, √y)` = o(V) by (I3).
- Term 2 `−Σ_{√y ≤ p ≤ y^U}(W1 − w(p))g(p)σ⁺(y/p)` → `−2e^γV(y)∫_{1/2}^{U}(W1 − W(t))/((1 − t)t)dt`, equal to the
  first part of 𝓜(W) since `W = W1` on `(U, 1]`.
- Term 3a `Σ_{p<√y} w(p)g(p)σ⁺(y/p)` → `2e^γV(y)∫_0^{1/2}W(t)/((1 − t)t)dt` (w = 0 for t ≤ m, so y/p ≥ y^{1/2}).
- Term 3b `−Σ_{p<√y} w(p)g(p)Σ_n χ̄(n)g(n)σ⁺(y/(pn))` → `−2e^γV(y)∫_0^{1/2}W(t)h(t,1)dt/t`: with `n = q₁⋯q_i`
  (`i` even, `q_j = y^{x_j}`), `χ̄_y(n) = 1` ⟺ `3x_j + x_{j−1} + ⋯ + x₁ < 1` (j < i) and `≥ 1` (j = i) (prefix form of χ,
  M07_PLAN §0; only the full prefix can newly violate), `p < p(n)` ⟺ `x < x_i`, `n p(n) < y/p` ⟺ `x_i < u`; this is
  `HRegion86 i x` up to boundaries of measure zero, and `σ⁺(y/(pn)) ~ 2e^γV(y)/u` by (I1), (I2) (`u > x_i > x > m`).
  `i x < 1` bounds `i ≤ 84`, so `hS`'s finite sum `k ≤ ⌊1/x⌋ + 1` covers all chains. The class condition of χ
  (even or ν ≤ 85) is the same as the region's (all j) because ν(n) ≤ 84.
Sum of the limits = `2e^γV(y)𝓜(W)`. ∎ (Greaves: "estimating sums by integrals in the established way", 1982 Lemma 4.4.)

## 2. Points to watch in a Lean proof
- `h86` is a Bochner integral over `Fin i → ℝ`; the integrand is bounded by `x^{−i−1}` on a bounded region, so it
  is integrable for `x > 0` (otherwise Lean's value 0 would change 𝓜(W)). The measurability/integrability of
  `t ↦ hS t` on `[m, 1/2]` must be proved (parametric integral, `StronglyMeasurable.integral_prod_right`).
- Uniformity of (I1) over `η = y/(pn) ≥ y^{m}` and of the Riemann sums over the (≤ 84)-dimensional regions with
  piecewise-linear boundaries; the Ω ≤ 4 Mval machinery handles the analogous 2-sided chain regions.

## 3. Status (2026-11-24 22:00)
Done in Lean, `scripts/check_item.sh M11` PASS. Files M11.lean, M11_A.lean, M11_B.lean; see reports/M11.md.
