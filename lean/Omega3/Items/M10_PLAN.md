# M10 sub-blueprint: Greaves 1986 Lemma 11, frozen form `ItemM10`

Started 2026-11-24 20:02 CET, this version 21:16 (`date`). Lean status: PASS (`scripts/check_item.sh M10`, 21:15). Sources: Greaves, Acta Arith. 47 (1986) pp. 92–94
(`r167_greaves1986_fit/img/pg-12.png`, `pg-13.png`), HR 1985 (6.5)–(6.15) via the mapping in `r184_inherited_inputs/NOTES.md` §1.1,
definitions in `Omega3/DefsSieve.lean`. Numerics: `reports/M10_scratch/gap_decomp.py`, logs `reports/M10_scratch/gap_*.log`.

```
ItemM10 : ∀ b ≥ 2, Lemma9Stmt b → Lemma10Stmt → ∀ ε > 0, ∃ y₀, ∀ y ≥ y₀,
  |Mstar b y (y^U) − E11 b y| ≤ ε · V(y)
```

## 0. Verdict

* The frozen statement is **true** (no correction needed). Every step below is either an exact identity of the Lean
  definitions or an asymptotic estimate with an explicit `o(V(y))`.
* It is **provable from the stated hypotheses plus proven Palprimes theorems** (done in Lean), but not from `Lemma9Stmt` alone:
  `Lemma9Stmt` is pointwise in `s` (`∀ s, ∀ ε, ∃ y₀`), while Lemma 11 applies Lemma 9 at `ζ = p`, `η = y/(pd₁)`, i.e. at
  `s = log η / log p` that varies continuously over `(2, 84)`. Uniformity on compact `s`-ranges is derived in §4 from
  the pointwise statement on a finite grid plus an equicontinuity estimate, which needs Rosser upper bounds
  `|T^±(η, ζ)| ≤ C·V(ζ)` (from Palprimes `E1.rosserAsymp_of_two_le` for `s ≤ 9` and a monotonicity argument for `s > 9`)
  and Mertens (Palprimes `MT.VB_log`, `E1.VB_log_bounds`). This roughly doubles the item (estimate below).
* Optional simplification (not needed any more, the derivation is done in Lean; would need a re-freeze): state `Lemma9Stmt` uniformly,
  `∀ S ε, ∃ ζ₀, ∀ ζ ≥ ζ₀, ∀ η, ∀ plus, s := log η/log ζ ∈ [1 or 2, S] → |T^plus(η, ζ) − T9sum η s plus| ≤ ε V(ζ)`
  (HR's Reduction Lemma is uniform for `log η/log ζ ≤ S`; Greaves' "O-constant may depend upon s" means exactly this),
  and give M10 also `Lemma7Stmt b` (σ⁺ upper bound). Then §4.3–§4.4 (about 1300 of the 3800 Lean lines) would disappear.
* The numeric gap in NOTES §3.7 is explained (§6): it is the Lemma 9 error at `ζ = p` for the tiny primes
  `7 ≤ p < y^{1/4}` that carry weight `w(p) > 0` at every feasible `y` (since `y^m < 7` until `y ≈ 10^{72}`), plus the
  `(d₁, t) > 1` terms of size `O(y^{−m} log^3 y)`. Extended to `y = 10^{11}` it saturates at about `−0.036 V(y)`; the
  per-prime relative errors decrease slowly in `log p`, as the asymptotic statement predicts. Expected size of the gap
  `O_m(V(y)(m log y)^{−1/3})` (HR's error exponent), i.e. no visible decay before `log y ≫ 1/m = 85`.

## 1. Notation (all as in the Lean definitions)

`g(n) = rhoB b n / n` (`= gB b n` on primes), `V(w) = MT.VB b w = Π_{p<w}(1 − g(p))`, `z = y^U`, `w(p) = wy y p`,
`P(w) = primorialLt w`. For squarefree `d`: `p(d) = minFac d`, `q(d)` = largest prime, `ν = ω`.
`χ^+_Y(d)`: every divisor `h ≠ 1` with `ν(h)` odd has `h p(h)² < Y` (`chiPlusProp`); `χ^-_Y` the same with `ν(h)` even
(`chiMinusProp`); `χ*_Y` odd with `ν(h) ≤ 1/m` (`chiStarProp`); `χ_Y` even or `ν(h) ≤ 1/m` (`chiProp`), so
`χ_Y = χ^-_Y · χ*_Y` (as propositions: `chiProp ↔ chiMinusProp ∧ chiStarProp`).
`T^±(Y, ζ) = Tpm b ± Y ζ = Σ_{d | P(ζ)} μ(d) g(d) χ^±_Y(d)`, `σ⁺(Y) = T⁺(Y, Y^{1/3})`.
`R^±(η, ζ) = Σ_{t ∈ S9(η, ζ, ±)} g(t) σ⁺(η/t)` with `S9` = squarefree `t | P(η)`, all primes `> ζ`, all primes `< η/t`,
`ν(t)` even (+) / odd (−). `T9sum b η s ± = R^±(η, η^{1/s})`.
For `d | P(z)` and a prime `p | d`: `d = d₁ p d₂`, `d₁ = d1of d p` (primes `> p`), `d₂` (primes `< p`).

Per-prime quantities (`p` prime, `p < z`):
* `H_p = Σ_{d | P(z), p | d} μ(d) g(d) χ^-_y(d) χ*_y(d₁)` (so `M*(z) = W(1) T^-(y, z) − Σ_{p<z} w(p) H_p`),
* `E_p = g(p) {σ⁺(y/p) − Σ_{n ∈ N_p} χ̄_y(n) g(n) σ⁺(y/(pn))}`, `N_p` = the `n`-set of `E11`
  (`n | P(y)`, `n ≠ 1`, `ν(n)` even, `p < p(n)`, `n p(n) < y/p`),
* `Δ_p = −H_p − E_p`.

## 2. Prefix lemmas (exact, divisor level; no "initial segments" needed)

P1. For a prime `M` larger than every prime of squarefree `d'`:
`χ^-_Y(M d') ↔ χ^+_{Y/M}(d')`. (Divisors `h = h'`, `h = Mh'`. The `Mh'` conditions are exactly `χ^+_{Y/M}(d')`;
the `h'` conditions with `ν(h')` even, `h' = q h''`, `q = p(h')`, follow: `h' q² = q³ h'' < M p(h'')² h'' < Y`.)
P1′. `χ^+_Y(M d') ↔ M³ < Y ∧ χ^-_{Y/M}(d')` (same argument; `h = M` gives `M³ < Y`).
P2 (factorisation (Greaves p. 92)). `d = d₁ p d₂` as above: `χ^-_y(d₁ p d₂) ↔ χ^-_y(d₁ p) ∧ χ^{ε}_{y/(p d₁)}(d₂)`,
`ε = +` if `ν(d₁)` even, `−` if odd. (For `h = h₁ h_p h₂`, `h₂ ≠ 1`: if `ν(h₂) ≢ ν(d₁)` the condition is implied by the
one for `d₁ p · h₂/p(h₂)` or, when `h₂ = q` is a single prime, by `d₁ p · p² < y`; if `ν(h₂) ≡ ν(d₁) + 1` the strongest is
`h₁ h_p = d₁ p`.) This is the only place where the "all divisors" definition differs from Rosser's initial segments;
the proofs above handle it directly.
P3. `χ*_y(d₁) ∧ χ^-_y(d₁ p) ↔ χ_y(d₁) ∧ χ^-_y(d₁ p)` (trivial: `χ_y = χ^- ∧ χ*` and every divisor of `d₁` divides `d₁p`).
P4. If `ν(d₁)` is even, all primes of `d₁` exceed `p` and `χ^-_y(d₁)`, then `χ^-_y(d₁ p)`: the new conditions are
`h₁ p³ < y` for `h₁ | d₁` with `ν(h₁)` odd; as `ν(d₁)` is even, `d₁` has a prime `r ∤ h₁`, and the even divisor `h₁ r`
of `d₁` gives `h₁ r · p(h₁ r)² < y` with `p < r`, `p < p(h₁ r)`. (No `ν ≤ 1/m` cut and no `p > y^m` needed. An earlier
draft argued via `χ*_y`, which only gives `h₁ p² < y`; corrected 20:40.)

## 3. Exact part: `M*(y^U) − E11(y) = Σ_{p < y^{1/4}} w(p) Δ_p` for `y ≥ 16`

X1a (split). `M*(z) = W(1) T^-(y, z) − Σ_{p<z} w(p) H_p` (swap `Σ_d Σ_{p|d}`).
X1b (Buchstab, top). `T^-(y, z) = T^-(y, √y) − Σ_{√y ≤ p < z} g(p) σ⁺(y/p)`: split `d | P(z)` by its largest prime
`p ≥ √y`, P1, and `T⁺(y/p, p) = σ⁺(y/p)` because `p ≥ (y/p)^{1/3}` (`p⁴ ≥ y`) and every prime `q` of `d'` with
`χ^+_{y/p}(d')` has `q³ < y/p`.
X1c (top range of the `w` part). For `√y ≤ p < z`: `H_p = −g(p)σ⁺(y/p)`. (`d₁ ≠ 1` is impossible: the divisor
`q₁ p` of `d` has `ν = 2` and `q₁ p · p² ≥ y²`.)
X1d (middle range). For `y^{1/4} ≤ p < √y`: `Δ_p = 0`. Odd `ν(d₁)` needs `d₁ p³ < y`, impossible as `d₁ > p`;
even `ν(d₁) ≥ 2` needs `d₁ p(d₁)² < y`, impossible as `> p⁴`; so `−H_p = g(p) T⁺(y/p, p) = g(p) σ⁺(y/p)`, and `N_p = ∅`
(`n p(n) > p³ ≥ y/p`).
X1e (the end point). The `E11` term `p = y^U` (only if `y^U` is a prime) has `W(1) − w(p) = W(1) − W(U) = 0`.
Together: `M* − E11 = W(1)·0 + Σ_{p ≥ √y} w(p)·0 + Σ_{y^{1/4} ≤ p < √y} w(p)·0 + Σ_{p < y^{1/4}} w(p) Δ_p`.
Checked numerically: the regrouping identity of §4.1 (coprime part of `S_p` = `E_p`) holds to 7e-15
(`reports/M10_scratch/gap_regroup_check.py`, `regroup_check.log`, y = 10⁴, 10⁶, 10⁸). The per-prime sum reproduces the logged `(M* − E11)/V` (−0.00730, −0.01580, −0.02669) to all
printed digits, and `Δ_p = 0` for `p ≥ y^{1/4}` at every `y` tested.

Since `w(p) = 0` for `p ≤ y^m` (X2a: `W = 0` on `[0, m]`), only `y^m < p < y^{1/4}` contributes.

## 4. Analytic part: `|Σ_{y^m < p < y^{1/4}} w(p) Δ_p| ≤ ε V(y)` for `y ≥ y₀(ε)`

### 4.1 Factorisation and the Lemma 9 / Lemma 10 decomposition (exact)
X2b. By P2 and `μ(d₁ p d₂) = −μ(d₁)μ(d₂)`:
`−H_p = g(p) Σ_{d₁} μ(d₁) g(d₁) χ*_y(d₁) χ^-_y(d₁p) T^{ε(d₁)}(η, p)`, `η = η(d₁) = y/(p d₁)`,
`d₁` over squarefree divisors of `P(z)` with all primes `> p`.
Let `s(d₁) = log η / log p`. Then: odd `ν(d₁)` with `χ^-_y(d₁p)`: `η > p²`, `s > 2`. Even `ν(d₁)` with `η ≤ p³`:
`T⁺(η, p) = σ⁺(η) = R⁺(η, p)` exactly (the only `t` is `1`: `t > 1` even has `t q(t) > p³ ≥ η`). Always `s < (1 − m)/m = 84`
(`η < y/p < p^{1/m − 1}`).
Define `S_p = g(p) Σ_{d₁} μ(d₁) g(d₁) χ*_y(d₁) χ^-_y(d₁p) R^{ε(d₁)}(η, p)`, `L_p = −H_p − S_p` (Lemma 9 errors),
`X_p = S_p − E_p`. Then `Δ_p = L_p + X_p`.
X2d (regrouping, Greaves p. 94 + Lemma 10). In `S_p`, (i) `χ^-_y(d₁p)` can be dropped when the `t`-sum is non-empty
(odd `ν(d₁)`: a prime `r > p` of `t` gives `d₁ p r² < y`, so every `h₁ p · p²` condition holds; even `ν(d₁)`: P4), and `χ*χ^- = χ` (P3, P4); (ii) the pairs `(d₁, t)` with
`(d₁, t) = 1` correspond to `n = d₁ t` (`n | P(z)`, `p(n) > p`, `ν(n)` even), `t = n/d₁`, and the conditions of `S9`
become `q(n/d₁) < y/(pn)`; their coefficient is `bfun y m p n`, which `Lemma10Stmt` evaluates
(**the only use of Lemma 10**; there `p < y^{1/4} < y`, so it is used only with `p < y`, the case that stays true after
the announced fix of `Lemma10Stmt` (frozen version false at `n = 1`, `p ≥ y`); the n = 1 value `b(1) = [1 < y/p] = 1` needs `p < y`)
(`1` for `n = 1`, `−χ̄_y(n)` if `n p(n) < y/p`, else `0`). `n ∈ N_p` with a prime `≥ z` has `χ̄_y(n) = 0`
(`χ_y(n/p(n)) = 0` through `q(n)³ ≥ y`). Hence the coprime part of `S_p` is exactly `E_p`, and
`X_p = g(p) Σ_{(d₁, t) > 1} μ(d₁) g(d₁) χ_y(d₁) g(t) σ⁺(η/t)`.

### 4.2 Mertens inputs (Palprimes)
M-a. `V(w) log w → κ_B` (`MT.VB_log`): for every `η' > 0` there is `w₀` with `(1 − η')κ ≤ V(w) log w ≤ (1 + η')κ`
(`E1.VB_log_bounds`).
M-b. `Π_{a ≤ q < c}(1 + g(q)) ≤ V(a)/V(c) ≤ C log c / log a` and `Σ_{a ≤ q < c} g(q) ≤ log(V(a)/V(c))`
(from `1 + x ≤ (1 − x)^{−1}`, `x ≤ −log(1 − x)`); with M-a, `Σ_{a ≤ q < a^{1+δ}} g(q) ≤ log(1 + δ) + 3η'` for `a ≥ w₀`.
M-c. `Σ_{q ≥ a} g(q) V(q) ≤ C/log a` (dyadic in `log q` from M-b) and `Σ_{q > a} g(q)² ≤ 1/(a − 1)`.

### 4.3 Rosser bounds (needed only for the uniformity of Lemma 9)
R-a (positivity, combinatorial). `T⁺(η, ζ) ≥ V(ζ)` and `T^-(η, ζ) ≤ V(ζ)` for all `η`, `ζ`: induction on `⌈ζ⌉` with
`T^σ(Y, z) = 1 − Σ_{M<z} g(M) [σ → M³ < Y] T^{¬σ}(Y/M, M)` (head recursion P1, P1′) and `V(z) = 1 − Σ_{M<z} g(M)V(M)`.
R-b (monotonicity). `A(ζ) = T⁺(η, ζ) − V(ζ)` and `B(ζ) = V(ζ) − T^-(η, ζ)` are non-decreasing in `ζ` (same identities, R-a).
R-c (upper bounds, `RosserBoundStmt`: `|T⁺(η, ζ)| ≤ C V(ζ)` for `ζ < η`, `|T^-(η, ζ)| ≤ C V(ζ)` for `ζ² < η`). By R-b,
`T⁺(η, ζ) ≤ V(ζ) + σ⁺(η)` (`A(ζ) ≤ A(η^{1/3})`, and `T⁺(η, ζ) = σ⁺(η)` when `ζ ≥ η^{1/3}`) and
`B(ζ) ≤ B(η^{1/2}) = V(η^{1/2}) − T^-(η, η^{1/2})`. So two one-parameter inputs suffice:
* `T^-(u, u^{1/2}) ≥ −V(u^{1/2})` for large `u`: this is the hypothesis `Lemma9Stmt` at `s = 2`, sign `−`, where the
  `t`-sum is empty (a prime `q > u^{1/2}` of `t` with `q < u/t ≤ u/q` is impossible);
* `σ⁺(u) ≤ C₁ V(u)`: Palprimes `E1.rosserAsymp_of_two_le` (Greaves' Lemma 4.2 for this density, uniform in
  `1 ≤ s ≤ 9`). Bridge: Palprimes' `Sg` uses the non-strict head condition `P³ ≤ z`; for the finitely many values
  `ΠE p(ΠE)²` there is `u' ∈ (u/2, u)` with `v < u ⇔ v ≤ u'`, so `σ⁺(u) = Splus(u', s')` with `s' = log u'/log u^{1/3} ∈ [1, 3)`,
  `≤ (FjrC(s') + 1) V(u^{1/3}) ≤ 4(2e^γ 8^{10} + 2e^γ + 1) V(u)` (`Fjr_le`, Mertens).
(The earlier sketch via RosserAsymp for all `s ≤ 9` and monotonicity above 9 was not needed.)

### 4.4 Uniform Lemma 9 from the pointwise hypothesis
Claim U. For every `S ≥ 3`, `ε > 0` there is `ζ₁` such that for every real `ζ ≥ ζ₁` and `η` with
`s = log η/log ζ ∈ [2, S]` (sign −) or `[3, S]` (sign +): `|T^±(η, ζ) − R^±(η, ζ)| ≤ ε V(ζ)`.
Proof. Grid `s_j = s_lo + jδ`, `δ = δ(ε, S)` small, finitely many `j`. `Lemma9Stmt` at `(s_j, ±, ε/3)` gives `y_j`;
take `ζ₁ ≥ max_j y_j^{1/2}`, so `η = ζ^s ≥ y_j`. For `s ∈ [s_j, s_{j+1}]` put `ζ_j = η^{1/s_j} ∈ [ζ, ζ^{1+δ}]`. Then
`|D(η, ζ)| ≤ |D(η, ζ_j)| + |T(η, ζ) − T(η, ζ_j)| + |R(η, ζ) − R(η, ζ_j)|` with
* `|D(η, ζ_j)| ≤ (ε/3) V(ζ_j) ≤ (ε/3) V(ζ)`,
* Buchstab: `|T(η, ζ_j) − T(η, ζ)| ≤ Σ_{ζ ≤ q < ζ_j} g(q) |T^∓(η/q, q)| ≤ C Σ g(q) V(q) ≤ C V(ζ)(log(1 + δ) + 3η')`
  (R-c; for sign + the `q³ < η` filter gives `log(η/q)/log q ≥ 2`, for sign − `log(η/q)/log q ≥ s_j − 1 ≥ 1`),
* `|R(η, ζ) − R(η, ζ_j)| = Σ_{t ∈ S9(η, ζ) \ S9(η, ζ_j)} g(t)σ⁺(η/t) ≤ Σ_{ζ < r ≤ ζ_j} g(r) Π_{r<q<√η}(1 + g(q)) · C V(ζ)
  ≤ C S V(ζ)(log(1 + δ) + 3η')` (`η/t > q(t) ≥ ζ`, so `σ⁺(η/t) ≤ C V(ζ)`; M-b).
Choose `δ`, `η'` with `C(1 + S)(log(1 + δ) + 3η') ≤ 2ε/3`. ∎

### 4.5 The Lemma 9 errors
For `y^m < p < y^{1/4}`, apply U with `S = 84`, `ζ = p` (needs `y^m ≥ ζ₁`), to every `d₁` with odd `ν(d₁)` and to every
even `d₁` with `η > p³` (the others are exact, X2b). Then
`|L_p| ≤ ε' g(p) V(p) Σ_{d₁} g(d₁) ≤ ε' g(p) V(p) Π_{p < q < z}(1 + g(q)) ≤ ε' C g(p) V(p) (U/m)`, and
`Σ_{y^m < p} w(p)|L_p| ≤ ε' C (U/m) Σ_{q > y^m} g(q)V(q) ≤ ε' C'(U/m)/(m log y) ≤ ε' C'' V(y)` (M-c, M-a, `w ≤ 1`).
With `ε' = ε/(2C'')`: `≤ (ε/2) V(y)` for `y ≥ y₁(ε)`.
(Greaves/HR: `O(V(y) log^{−1/5} y)`; here only `o(·)` is claimed.)

### 4.6 The terms with `(d₁, t) > 1` ("dealt with as in [6]", HR (6.10)–(6.14))
A common prime `r > p` gives `g(d₁)g(t) ≤ g(r)² g(d₁/r) g(t/r)`, so (crudely, all signs dropped)
`|X_p| ≤ g(p) Σ_{r > p} g(r)² · Π_{q<y}(1 + g(q))² · sup_u σ⁺(u)`, and
`sup_{u>0} σ⁺(u) ≤ Π_{q < y}(1 + g(q))` on the relevant range `u < y`. With M-b: `Π_{q<y}(1+g(q)) ≤ 1/V(y) ≤ C log y`, so
`|X_p| ≤ C³ log³ y / (p (p − 1))` and `Σ_{p > y^m} w(p)|X_p| ≤ C³ log³ y · y^{−m} ≤ (ε/2) V(y)` for `y ≥ y₂(ε)`
(`y^{−m} log⁴ y → 0`). No Rosser input needed here.

### 4.7 Assembly
`|M* − E11| = |Σ_{y^m<p<y^{1/4}} w(p)(L_p + X_p)| ≤ ε V(y)` for `y ≥ max(16, ζ₁^{1/m}, y₁, y₂)`. ∎

## 5. Lean (done, PASS 21:15; 3824 lines in 15 files)

| file | content | lines |
|---|---|---|
| M10_Defs | `Hp`, `Nset`, `Ep`, `DeltaP`, `S9`, `Rpm`, `D1set` | 55 |
| M10_Comb | powerset by maximum, set form `ChiS` of `χ^±`, P1 | 225 |
| M10_Sets | set form of `Tpm`, `σ⁺` after a head prime, `Nset = ∅` for `p⁴ ≥ y` | 169 |
| M10_Exact | X1a–X1e, `exact_split` | 353 |
| M10_XB | `K(y) ≤ 1/V(y)`, `Σ_{y^m<p} w K³/p² = o(V)` | 157 |
| M10_X | `S_p`, `X_p`, `Lemma10LtStmt` (Lemma 10 for `p < y` only), `|X_p| ≤ 2K³/p²` | 293 |
| M10_Regroup | P4, coefficientwise match with `bfun`, reindexing `n = d₁t`, `regroup : S_p − E_p = X_p` | 463 |
| M10_P2 | P2 (factorisation of `χ⁻(d₁ p d₂)`) | 268 |
| M10_L | `Lemma9UStmt`, `negHp_factor`, `Σ|A| ≤ V(p)/V(y^U)`, `L_bound_of` | 419 |
| M10_Buch | P1′, head sums, Buchstab differences | 163 |
| M10_U | Mertens increments/ratios, exact `+` case, equicontinuity, `lemma9U_of_RB` (grid) | 505 |
| M10_Bridge | non-strict head recursion, `Sg` = subset sum, shift `u → u'`, `sigma_upper` | 352 |
| M10_Rosser | R-a, R-b, `rosserBound_of`, `lemma9U_of` | 270 |
| M10_Analytic | `X_bound`, `analytic_bound` | 87 |
| M10 | `itemM10`, `itemM10_of_uniform`, `itemM10_of_rosser` | 45 |

Lemma 10 is used only through `lemma10Lt_of : Lemma10Stmt → Lemma10LtStmt` (adds `p < y`) and applied at `p < y^{1/4}`;
the proof does not use the falsity of the frozen `Lemma10Stmt` at `n = 1`, `p ≥ y`, and stays valid after the fix.

## 6. The numeric gap of NOTES §3.7

`reports/M10_scratch/gap_decomp.py` (b = 5, exact enumeration) computes `Δ_p`, `L_p` (Lemma 9 errors) and `X_p`
(`(d₁, t) > 1` terms) per prime. Results (`gap = (M* − E11)/V(y)`):

| y | y^m | y^{1/4} | gap | Lemma 9 part | (d₁,t)>1 part | part from p ≥ y^{0.15} |
|---|---|---|---|---|---|---|
| 10⁴ | 1.11 | 10 | −0.00730 | −0.00627 | −0.00103 | −0.00730 |
| 10⁵ | 1.15 | 17.8 | −0.01580 | −0.01132 | −0.00448 | −0.01580 |
| 10⁶ | 1.18 | 31.6 | −0.02669 | −0.02000 | −0.00669 | −0.02718 |
| 10⁷ | 1.21 | 56.2 | −0.02969 | −0.02240 | −0.00729 | −0.02971 |
| 10⁸ | 1.24 | 100 | −0.03225 | −0.02511 | −0.00713 | −0.03181 |
| 10⁹ | 1.28 | 178 | −0.03292 | −0.02630 | −0.00662 | −0.03079 |
| 10¹⁰ | 1.31 | 316 | −0.03533 | −0.02935 | −0.00598 | −0.03047 |
| 10¹¹ | 1.35 | 562 | −0.03596 | −0.03070 | −0.00525 | −0.02977 |

Reading.
1. Only `7 ≤ p < y^{1/4}` contributes (`Δ_p = 0` exactly above `y^{1/4}`, X1d). At `y = 10⁴` the whole gap is the single
   prime `p = 7`. The asymptotic statement needs `w(p) = 0` on these primes, i.e. `y^m > p`; for `p = 7` that is
   `y > 7^{85} ≈ 10^{72}`. So every feasible `y` is pre-asymptotic, as NOTES suspected.
2. The per-prime relative error `p L_p / V(p)` is the Lemma 9 error at `ζ = p` (tiny `ζ`), about `−0.03 … −0.15`.
   At fixed `t = log p/log y ≈ 0.2` it decreases: `−0.12, −0.10, −0.097, −0.084, −0.087, −0.096` at `y = 10⁶ … 10¹¹`
   (peak of the profile `−0.146, −0.134, −0.123, −0.092, −0.099` for `10⁷ … 10¹¹`), consistent with HR's
   `O(V(ζ) log^{−1/3} ζ)` and with the Lemma 9 checks in `logs/sanity_g4.log` (relative errors 0.1–0.44 at s = 3, 4).
3. The gap grows from `10⁴` to `10⁶` because the contributing range `[7, y^{1/4})` fills up (1, 4, 8, … primes); the
   increments shrink (`−0.0085, −0.0109, −0.0030, −0.0026, −0.0007, −0.0024, −0.0006` per decade) and the gap saturates
   near `−0.036 V`. Model: `gap ≈ ∫ W(t) δ(y^t) dt/t²` over `t ∈ (log 7/log y, 1/4)`, `W(t)/t² ≤ k² ≈ 10`,
   `∫ W/t² ≈ 1.3`, `δ` the weighted relative Lemma 9 error ≈ 0.03 now; it decays only when `δ(y^m)` does,
   i.e. as `(m log y)^{−1/3}`.
4. The `(d₁, t) > 1` part is concentrated at the smallest primes (`p X_p/V(p) ≈ −0.02` at `p = 7`, `≈ 1/p` decay) and
   is `O(y^{−m} log³ y)` asymptotically: invisible decay for `y < 10^{72}`.
5. Not a sign of a wrong statement: the transcription is exact (X1 identities hold to rounding), and the residual is
   precisely the sum of the two error types the proof bounds.
Side remark: at all feasible `y` the gap (−0.036 V) is as large as the main term `2e^γ V 𝓜(W) ≈ 0.037 V`; Lemma 11
(like Lemmas 7–9, 12, see NOTES §3.8) gives no effective `y₀`.
