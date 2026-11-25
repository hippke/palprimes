# M02 sub-blueprint: Lemma A part 2, `Q(Λ^η) ≤ (c_η + ε)/G(√x)`

Started 2026-11-24 22:00 CET. Statement `ItemM02` exactly as frozen. Verdict: true as stated (in fact `Q·G → c_η`).
Notation as in S08_PLAN.md (`z = √x`, `G = G(z)`, `η_p = η̂(u_p)/G`, `A_d`, `R_p = pA_p/G`, `R_{p'p} = p'pA_{p'p}/G`,
`S(s) = Σ_{p<z} (1/p)η̂(u_p) max(s − u_p, 0)`). The S08 helpers are copied as `M02_G, _A, _P, _S, _L, _E` (renamed `m02…`).

## Step 1 (Selberg diagonalisation, exact)
For `d < z` put `V(d) = Σ_{d|k<z} μ(k/d) y_k`. Then `λ_d = d V(d)` for `(d, B) = 1`, and `λ_d = 0 = V(d)` otherwise
(`y_k = 0` unless `k` is squarefree and coprime to `B`). For coprime `d₁, d₂`: `ρ([d₁,d₂])/[d₁,d₂] = (d₁,d₂)/(d₁d₂)`,
so `Q = Σ_{d₁,d₂<z} V(d₁)V(d₂)(d₁,d₂) = Σ_{e<z} φ(e) (Σ_{e|d<z} V(d))²` (`(d₁,d₂) = Σ_{e|(d₁,d₂)} φ(e)`), and Möbius
inversion `Σ_{e|d|k} μ(k/d) = [k = e]` gives `Σ_{e|d} V(d) = y_e`. Hence `Q = Σ_e φ(e)y_e² = Σ_k g(k)(ν − η(k))²`.
With `νG = 1 + H`, `B₀ = Σ_k g(k)η(k)²`: `Q·G = 1 − H² + G B₀`.

## Step 2 (expansion of G B₀, exact)
`η(k) = Σ_{p∈P} [p|k] η_p`, so `G B₀ = Σ_{p,p'} G η_p η_{p'} A'_{p,p'}` and, splitting `p' = p`,
`G B₀ = T₁ + T₂`, `T₁ = Σ_p (1/p) η̂_p² R_p`, `T₂ = Σ_p (1/p) η̂_p W_p`, `W_p = Σ_{p' ≠ p} (1/p') η̂_{p'} R_{p'p}`.

## Step 3 (limits; δ = 11T + 2C/G as in S08, all primes with η̂ ≠ 0 are ≥ z^{u₀})
- `|T₁ − S₂(1)| ≤ M²K δ`, `S₂(1) → J₁ = ∫₀¹ η̂²(1 − u)/u` (S08 prime-sum lemma for the list with squared values).
- `|W_p − S(1 − u_p)| ≤ MKδ + Mδ` (the S08 estimate of `Σ''` with `q := p`), `S(1 − u_p) → Â(1 − u_p)` uniformly, so
  `T₂ = Σ_p (1/p) η̂_p Â(1 − u_p) + o(1)`, and by the Riemann lemma below `→ J₂ = ∫₀¹ η̂(u) Â(1 − u)/u du`.
- `H → Â(1)` (S08).
- Riemann lemma: for `0 < a < b ≤ 1` and `F` continuous on `[a, b]`, `Σ_{a ≤ u_p < b} F(u_p)/p → ∫_a^b F(v)/v dv`
  (uniform continuity, `N` cells, Mertens 2 on each cell). Step functions by induction over the list.
  `Â` is continuous: `Â(s) = Σ_j c_j I(a_j, m_j, s)`, `I(a, m, s) = s log(t/a) − (t − a)`, `t = max(min(m, s), a)`.

## Step 4 (identity) `c_η − 1 = J₁ + J₂ − Â(1)²`.
For `u₁, u₂ > 0`: `u₁u₂ min(1, r₁r₂) = (1 − u₁)(1 − u₂) − max(1 − u₁ − u₂, 0)`. So the inner integral of `c_η` is
`η̂(u₁)[(1 − u₁)Â(1) − Â(1 − u₁)]/u₁` (`∫₀¹ η̂(v) max(s − v, 0)/v = Â(s)` for `s ∈ [0,1]`), and the outer integral is
`Â(1)² − J₂`. Hence `Q·G − c_η = (T₁ − J₁) + (T₂ − J₂) − (H² − Â(1)²) → 0`, which gives `Q ≤ (c_η + ε)/G`.
