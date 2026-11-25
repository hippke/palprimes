# S08 sub-blueprint: Lemma A part 3 (λ₁ + λ_q = g_η(u) + o(1))

Started 2026-11-24 21:30 CET. Statement `ItemS08` (Statements.lean) exactly as frozen. Verdict: true as stated
(the jumps of η̂ are matched exactly, because `etaQ q` uses η̂ at the same `u = log q/log z`).

Notation. `z = √x`, `L = log z`, `G(w) = GS b w = Σ_{1≤n<w} g(n)`, `g = gS b` (`1/φ(n)` on squarefree `n` coprime to
`B = b³ − b`), `β = Π_{p | B}(1 − 1/p) > 0`, `u_p = log p/L`, `η̂ = e.eval`, `M = s09Mv e ≥ |η̂|`, `u₀ = s09u0 e > 0`
(η̂ = 0 on `[0, u₀)`). `P = (ltSet z).filter Prime`. For `d ≥ 1`: `A_d = Σ_{k ∈ ltSet z, d | k} g(k)`.

## Step 1 (algebra, exact)
λ₁ = 1 (S09). For a prime `q` coprime to `B`: for `q | k`, `g(k) ≠ 0` gives `μ(k/q)μ(k) = −1`, so
λ_q = −q Σ_{q|k<z} g(k)(ν − η(k)) = −q(ν A_q − B_q), `B_q = Σ_{q|k<z} g(k)η(k) = Σ_{p∈P} etaQ(p) A_{lcm(p,q)}`
(swap of `Σ_k Σ_{p | k}`). Also `νG = 1 + H`, `H = Σ_k g(k)η(k) = Σ_{p∈P} etaQ(p) A_p`. `etaQ(p) = η̂(u_p)/G(z)`.

## Step 2 (G asymptotics) ∃ C, ∀ w ≥ 1, |G(w) − β log w| ≤ C; G(w) = 0 for w ≤ 1; G monotone.
- Lower: `G(w) ≥ H_B(K)` for `K = ⌈w⌉ − 1 < w` (M03 argument: radical grouping, `factored_le_selbergS`), and
  `H_B(K) ≥ β log K − C₁` (`HB_approx`), `log K ≥ log w − log 2` for `w ≥ 2`.
- Upper: for squarefree `n` coprime to `B`, `1/φ(n) = (1/n) Σ_{k ∈ F(n)} 1/k`, `F(n)` = numbers factored over the primes
  of `n` (Euler product, `inv_mul_euler_eq`). Split at `nk < w`. The pairs `(n, k)` with `nk < w` inject into
  `m = nk ≤ K` coprime to `B` (`rad(nk) = n`), giving `≤ H_B(K) ≤ β log K + C₁`. The rest is
  `≤ (1/n)√(n/w) Σ_{F(n)} k^{−1/2} = w^{−1/2} J(n)`, `J(n) = Π_{p|n} 1/(√p − 1)`. With
  `J(n) = n^{−1/2} Σ_{t ⊆ pf(n)} Π_{p∈t} j(p)`, `j(p) = 1/(√p − 1)`, swap, `Σ_{n<w, d|n} n^{−1/2} ≤ 2√w/d`
  (`Σ_{e≤M} e^{−1/2} ≤ 2√M`), and `Σ_{t ⊆ primes<w} Π_{p∈t} j(p)/p = Π(1 + j(p)/p) ≤ exp(4 Σ n^{−3/2})`.
  So `Σ_{n<w} w^{−1/2}J(n) ≤ 2 exp(4ζ(3/2))`.

## Step 3 (A_d) For squarefree `d` coprime to `B`: `A_d = g(d) Σ_{k' ∈ ltSet(z/d), (k',d)=1} g(k')` (k = dk').
Hence `d A_d ≤ d g(d) G(z/d)` and `d A_d ≥ (G(z/d) − Σ_{p|d} g(p) G(z)) ` (since `d g(d) ≥ 1` and the
non-coprime `k'` are covered by `p | k'`, `p | d`, each part `≤ g(p)G`). For `d = q` or `d = pq` with all primes `≥ Y ≥ 2`:
`|d A_d − G(z/d)| ≤ (24/Y) G(z)`.

## Step 4 (prime sums, uniform in s ∈ [0,1])  S(s) := Σ_{p∈P} (1/p) η̂(u_p) max(s − u_p, 0) → Â(s) uniformly.
`η̂(v) = Σ_j c_j 1[a_j ≤ v < m_j]` (from `foldl`: `eval (pr :: rest) v = [pr.1 ≤ v ∧ ∀ pr' ∈ rest, v < pr'.1] pr.2 + eval rest v`,
no sortedness needed; the condition is `a ≤ v < m` with `m = min(2, rest left ends)` for `v < 2`). For one piece with
`a > 0` and `m' = min(m, s)`: if `m' ≤ a` both sides are 0; else the sum is `s Σ_{z^a ≤ p < z^{m'}} 1/p − L⁻¹ Σ log p/p`
`= s log(m'/a) − (m' − a) + O(1/(a L))` (Mertens 1 and 2 on half-open intervals, sandwiched between `(A, T/2]` and
`(A/2, T]`), and `∫₀^s 1[a ≤ v < m](s − v)/v dv = s log(m'/a) − (m' − a)`. Induction on the list.
Also `Σ_{p ∈ P, p ≥ z^{u₀}} 1/p ≤ log(1/u₀) + 1` for `z` large.

## Step 5 (assembly) Let `δ = 24/Y + 2C/G(z)` with `Y = min(q, z^{u₀})`. Then uniformly in `u ∈ [2u_lo, 1)`:
`|qA_q/G − (1 − u)| ≤ δ`, `|H − Â(1)| ≤ M(δ)(log(1/u₀)+1) + ε'`, and
`|Σ_{p≠q} etaQ(p) q A_{pq} − Â(1 − u)| ≤ M δ (log(1/u₀)+1) + M/q + ε'` (using `|G(z/(pq)) − G(1 − u − u_p)₊| ≤ 2C`).
`λ₁ + λ_q − g_η(u) = −[(1+H) qA_q/G − (1 + Â(1))(1 − u)] + η̂(u)[qA_q/G − (1 − u)] + [Σ − Â(1 − u)]`, each `→ 0`.
`G(z) ≥ βL − C → ∞`. Finitely many `η̂ ∈ etas`: maximum of the thresholds.
