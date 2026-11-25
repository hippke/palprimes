# L12 sub-blueprint: Lemma K (weighted Col bound)

Written 2026-11-24 21:00 CET (`date`). Source r238 proof.md §2.3, ERRATA_r241 (M4: any adjacent pair works; we use
(0, 1)), dossier v5 §2.4. Frozen statement: for `b ≥ 2`, a digit weight `g` (`g ≥ 0`, `Σ_{a<b} g(a) = 1`), `q ≥ 2`,
`(q, |h|(b³ − b)) = 1`, `2 ≤ M ≤ N − 1`, `α = h/q + k/(b³ − b)`:
`Π_{1≤n≤M} ‖G_g(c_n α)‖ ≤ exp(−g(0)g(1)⌊(M − 1)/L⌋/(b⁴(b + 1)²))`, `L = max(1, ⌊log_b q⌋)`.
Verdict: **true as stated**. If `g(0)g(1) = 0` the right side is 1 and the claim is `‖G‖ ≤ 1`.

Proof (‖t‖ = `distZ t`, g* = g(0)g(1), κ = 8g*).
1. Pointwise. `‖G(t)‖² = Σ_{u,v<b} g(u)g(v)cos 2π(u − v)t`, `Σ_{u,v} g(u)g(v) = 1`, so
   `1 − ‖G‖² = Σ g(u)g(v)(1 − cos 2π(u − v)t) ≥` (terms (1,0), (0,1)) `2g*(1 − cos 2πt) ≥ 16g*‖t‖²`
   (`1 − cos 2πt = 2sin²πt`, Jordan `|sin πt| ≥ 2‖t‖`, Palprimes `abs_sin_pi_ge`). Hence
   `‖G(t)‖ ≤ √(exp(−16g*‖t‖²)) = exp(−κ‖t‖²)` and `Π_{n=1}^{M} ‖G(c_nα)‖ ≤ exp(−κ Σ_{n=1}^{M} ‖c_nα‖²)`.
2. Pairing (TP). For `1 ≤ n < M` (so `n + 1 < N`): `b c_n − c_{n+1} = (b² − 1)b^{j}`, `j = 2N − n − 1 ≥ 1`, and
   `(b² − 1)b^j k/(b³ − b) = k b^{j−1} ∈ ℤ`, so `E_n := ‖a b^j/q‖ ≤ b‖c_nα‖ + ‖c_{n+1}α‖`, `a = |h|(b² − 1)`
   (for `h < 0` use `‖G(−t)‖ = ‖G(t)‖` and `α ↦ −α`, `k ↦ −k`). So `E_n² ≤ (b + 1)²(‖c_nα‖² + ‖c_{n+1}α‖²)` and
   `Σ_{n<M} E_n² ≤ 2(b + 1)² Σ_{n≤M} ‖c_nα‖²`.
3. Windows (Maynard). `(a b, q) = 1`, `q < b^{L+1}`. In every `L` consecutive exponents `j` some `j` has
   `‖a b^j/q‖ ≥ 1/(2b²)`: otherwise `‖a b^{j₀+i}/q‖ = b^i‖a b^{j₀}/q‖ ≥ b^i/q` for `i < L` (no wrap while `b‖·‖ ≤ 1/2`),
   and at `i = L − 1` this is `> b^{L−1}/b^{L+1} = 1/b²`. The `W = ⌊(M − 1)/L⌋` disjoint windows inside `[1, M)`
   (mapped `n = 2N − j − 1`) give `Σ_{n<M} E_n² ≥ W/(4b⁴)`.
4. Combine: `Σ_{n≤M}‖c_nα‖² ≥ W/(8b⁴(b + 1)²)`, `κ·W/(8b⁴(b+1)²) = g*W/(b⁴(b+1)²)`. ∎
Lean: Omega3/Items/L12.lean, reusing Palprimes.ExpSum.ColBound (distZ lemmas, `window_sum_ge`, `abs_sin_pi_ge`);
the window lemma is re-proved with the shorter window `max 1 ⌊log_b q⌋` (Palprimes uses `⌊log_b q⌋ + 1`).
