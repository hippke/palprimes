# M08 sub-blueprint: Greaves' Lemma 9 (HR Reduction Lemma), frozen form `Lemma9Stmt`

Started 2026-11-24 20:03 CET (`date`). Statement (frozen): `ItemM08 : ∀ b ≥ 2, Lemma7Stmt b → Lemma9Stmt b`,
```
Lemma9Stmt b : ∀ s ≥ 1, ∀ plus, (plus = false → 2 ≤ s) → ∀ ε > 0, ∃ y₀, ∀ y ≥ y₀,
  |Tpm b plus y (y^{1/s}) − T9sum b y s plus| ≤ ε · V(y^{1/s}).
```

## Verdict
The frozen statement is **true and provable** as stated. The proof below does not use the hypothesis `Lemma7Stmt`
(it uses Palprimes' proven `E1.rosserAsymp_of_two_le`, i.e. Rosser–Iwaniec main terms, only at `s = 2` with
`f(2) = 0`). The route: an exact Buchstab-type tree identity (four recursions, all four checked numerically to 1e-16
on 25 random (Y, w), Y ≤ 1500, in the session scratchpad `chk.py`) plus three error types at the nodes of the tree,
summed with the telescoping identity `Σ_{a≤p<c} g(p)V(p) = V(a) − V(c)`.

## Notation
`g(p) = gB b p` (`1/p` for primes `p ∤ b³ − b`, else 0), `V = MT.VB b`, `T^σ(Y, w) = Tpm b σ Y w`,
`σ⁺(Y) = sigmaP b Y = T⁺(Y, Y^{1/3})`. For a real `w` and `σ`, let
`S9(Y, w, σ)` = squarefree `t ∣ P(Y)` with all primes `> w`, all primes `< Y/t`, `ω(t)` even (σ = +) or odd (σ = −),
and `R^σ(Y, w) = Σ_{t∈S9(Y,w,σ)} γ(t)/t σ⁺(Y/t)`. Then `T9set y s plus = S9(y, y^{1/s}, plus)` and
`T9sum b y s plus = R^plus(y, y^{1/s})` by definition.

## Step 1: set form of `Tpm`
`primorialLt w = Π_{p ∈ primesBelow w} p`, so (Palprimes `sum_divisors_primes`) divisors `d` correspond to subsets
`D ⊆ primesBelow w`, `d = ΠD`, with `μ(d) = (−1)^{|D|}`, `γ(d)/d = Π_{p∈D} g(p)`, `ω(ΠE) = |E|` (`primeFactors_prod`).
`χ^±_Y(ΠD)` ("every divisor `h ≠ 1` with `ω(h)` odd/even has `h p(h)² < Y`") becomes
`ChiS σ Y D : ∀ E ⊆ D, E ≠ ∅, par_σ |E| → (ΠE)·minFac(ΠE)² < Y`.

## Step 2: head recursion (Rosser's conditions read from the largest prime)
For primes `D'` all `< M` (M prime): `ChiS σ Y (insert M D') ↔ cond_σ(Y, M) ∧ ChiS (¬σ) (Y/M) D'`,
`cond_+ (Y, M) : M³ < Y`, `cond_− : True`.
(⇒) `E = {M}` gives cond; for `E' ⊆ D'` use `E = insert M E'` (`minFac` unchanged, parity flips).
(⇐) `E ∋ M`: `E = {M}` (then |E| = 1, σ = +, cond) or `E = insert M E'` (child condition).
`E ∌ M`: replace the largest element `q` of `E` by `M`: `E* = insert M (E \ {q})`, same parity,
`ΠE ≤ ΠE*`, `minFac(ΠE) ≤ minFac(ΠE*)`; `E*` is covered by the first case.
Grouping subsets by their maximum (`Σ_{D⊆S} F(D) = F(∅) + Σ_{M∈S} Σ_{D'⊆S, D'<M} F(insert M D')`) gives
`(A) T^σ(Y, w) = 1 − Σ_{p<w, cond_σ(Y,p)} g(p) T^{¬σ}(Y/p, p)` for every `Y > 0`, `w`.
Consequences (subtract (A) at two levels; `p < Y^{1/3} ⇔ p³ < Y`, `p < √Y ⇔ p² < Y`):
`(I1) T⁺(Y, w) = σ⁺(Y) + Σ_{p ≥ w, p³ < Y} g(p) T⁻(Y/p, p)`  (Y > 0),
`(I2) T⁻(Y, w) = T⁻(Y, √Y) + Σ_{p ≥ w, p² < Y} g(p) T⁺(Y/p, p)`  (0 < Y, w ≤ √Y).

## Step 3: recursion of the t-sums (smallest prime of t)
Grouping by the minimum `m` of the prime set of `t` (`t = m t'`, all primes of `t'` `> m`):
`(R1) R⁺(Y, w) = σ⁺(Y) + Σ_{w < p, p³ < Y} g(p) R⁻(Y/p, p)`,
`(R2) R⁻(Y, w) = Σ_{w < p, p² < Y} g(p) R⁺(Y/p, p)`  (Y > 0).
Membership: `t = m t' ∈ S9(Y, w, σ)` iff `w < m`, `t' ∈ S9(Y/m, m, ¬σ)` and `m < Y/(m t')`; the last condition
follows from `q(t') < Y/(m t')` when `t' ≠ 1`; when `t' = 1` it is `m² < Y`. For σ = + `t' ≠ 1` (even ω ≥ 2), and
`q > m`, `q < Y/(m t') ≤ Y/(m q)` give `m³ < Y`; for σ = − `m < Y/(mt')` gives `m² < Y`.

## Step 4: the difference recursion
`Δ^σ(Y, w) = T^σ(Y, w) − R^σ(Y, w)`. From (I1)–(R2), splitting the prime `p = w` (only if `w` is a prime):
`Δ⁺(Y, w) = [w prime, w³ < Y] g(w) T⁻(Y/w, w) + Σ_{w<p, p³<Y} g(p) Δ⁻(Y/p, p)`,
`Δ⁻(Y, w) = T⁻(Y, √Y) + [w prime, w² < Y] g(w) T⁺(Y/w, w) + Σ_{w<p, p²<Y} g(p) Δ⁺(Y/p, p)`  (w ≤ √Y).
Children satisfy the side conditions: from a + node, `p³ < Y ⇒ p ≤ √(Y/p)`; all nodes have `w ≥ W₀ := y^{1/s}`, `Y ≤ y`,
and − nodes have `Y ≥ w² ≥ W₀²`.

## Step 5: node errors
(a) crude bound: `|T^σ(Y, x)| ≤ Σ_{D⊆primesBelow x} Πg = Π_{p<x}(1 + g(p)) ≤ Π(1 − g(p))^{−1} = 1/V(x)`.
So the "p = w" terms are `≤ g(w)/V(w) ≤ 1/(W₀ V(y))` (w ≥ W₀, w < y, V antitone).
(b) leaf `T⁻(Y, √Y)`: with `z = ⌈Y⌉₊ − 1` (so `N < Y ⇔ N ≤ z` for naturals `N`), Rosser's non-strict conditions at
level `z` equal the strict ones at level `Y`, hence `T⁻(Y, x) = Sg (gB b) false z (toDec (primesBelow x))` (induction
over the primes from the top, `toDec_insert_max`). `primesBelow √Y = primesBelow √z ∪ {√z if it is a prime}`;
the extra prime `p = √z` costs `g(p)|T⁺(Y/p, p)| ≤ 1/(p V(p))`. With `Sminus b z 2 = Sg … (primesBelow z^{1/2})` and
RosserAsymp at s = 2, `fjr 2 = 0` (`I_2(2)` has empty region): `|T⁻(Y, √Y)| ≤ ε′ V(√z) + 1/(pV(p))`, for `z ≥ z₀`.
`V(√z) ≤ V(W₀/2) ≤ 6V(W₀)` for `W₀ ≥ 4` (Mertens ratio, Palprimes `VB_log_bounds` with η = 1/2), `p ≥ W₀/2`.
So every node error is `≤ η := 6ε′V(W₀) + 3/(W₀ V(y))` (with `p ≥ W₀/2` the leaf extra is `≤ 2/(W₀V(y))`).

## Step 6: summing over the tree
Claim, by induction on `n` with `Y < 2^n`: `|Δ^σ(Y, w)| ≤ η V(w)/V(Y)` for every node.
Step: `|Δ| ≤ η + Σ_{w<p<Y} g(p) η V(p)/V(Y/p) ≤ η (1 + Σ_{w≤p<Y} g(p)V(p)/V(Y)) = η V(w)/V(Y)` by
`V(Y/p) ≥ V(Y)` and the telescoping `Σ_{w≤p<Y} g(p)V(p) = V(w) − V(Y)` (Palprimes `E1.telescope`).
Base `Y < 1`: no primes `p ≥ 2` with `p² < Y`, sums empty.
At the root `(y, W₀)`: `|Tpm − T9sum| ≤ η V(W₀)/V(y)`, so it suffices that `η ≤ ε V(y)`:
`V(W₀)/V(y) ≤ 3 log y/log W₀ = 3s` (Mertens), take `ε′ = ε/(36 s)`; and `3/(W₀ V(y)²) ≤ ε/2` holds for large `y`
since `V(y) ≥ κ/(2 log y)` and `(log y)²/y^{1/s} → 0`.

## Remarks
- The `−` case needs `w ≤ √Y` at the root, i.e. `s ≥ 2`: consistent with the frozen correction.
- `Lemma7Stmt` is an unused hypothesis; the O(log^{-1/5}) rate of Greaves is not claimed (only o(V)).
- The "non-squarefree moduli" of Greaves/HR are the repeated-prime terms `p = w` of Step 4, bounded in Step 5 (a).

## Status (2026-11-24 20:28 CET, `date`)
Done: `Omega3/Items/M08_Comb.lean` (874 lines: Steps 1–5 combinatorics, Sg bridge, leaf bound) and
`Omega3/Items/M08.lean` (432 lines: tree bound, analytic inputs, `itemM08`). `scripts/check_item.sh M08`: PASS,
axioms [propext, Classical.choice, Quot.sound]. Lean names: Step 2 `chi_insert`, `TS_rec`, `Tpm_rec`, `I1`, `I2`;
Step 3 `cond9_insert`, `RS_rec`, `R1`, `R2`; Step 5 `abs_Tpm_le`, `Sg_eq_TS`, `leaf_bound`, `leaf_small`;
Step 6 `tree_bound`, `sum_children`, `ratio_le`, `half_le`, `small_le`.
