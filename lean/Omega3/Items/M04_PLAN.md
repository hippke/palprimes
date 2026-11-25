# M04 plan (opus-m04, 2026-11-24)

Statement (frozen): for b ≥ 2, BandOK B, ε > 0, eventually in y
Σ_{δ∈𝒟} φ(δ) ρ(δ)/δ · e^γ V(√(y/δ)) (c_δ − 1) ≤ 2 e^γ V(y) (Σ_i (c_i − 1) I_i + ε).
Judged true as stated. No integrals are needed.

## Step 1 (reduction to band primes, exact)
f(δ) := φ ρ/δ e^γ V(√(y/δ)) (cOf δ − 1). If no band contains δ, cOf δ = 1 and f(δ) = 0.
Otherwise δ is a prime, i₀ = Nat.find, cOf = c_{i₀} and (S14 copy) φ(δ) = U − x_δ ≥ 0 (x_δ = log δ/log y ≤ x_n ≤ 2U − 1),
so g(δ) := φ ρ/δ V(√(y/δ)) ≥ 0. All c_i ≥ 1 (getD default 1), hence
f(δ) ≤ Σ_{i<n} [inBand i δ] (c_i − 1) e^γ g(δ)   (single term i₀ ≤ sum of nonnegative terms).
Swap: LHS ≤ Σ_i (c_i − 1) e^γ Σ_{δ ∈ 𝒟, inBand i δ} g(δ). For a band prime ρ(δ)/δ = gB(δ), φ = U − x.

## Step 2 (one band, a = x_i ≥ 1/3, c = x_{i+1} ≤ 2U − 1 < 1; any set S of primes p with y^a ≤ p < y^c)
Claim: eventually Σ_{p∈S} (U − x_p) gB(p) V(√(y/p)) ≤ 2V(y)(I(a, c) + ε′), uniformly in S.
(a) Mertens 3 (`MT.VB_log`): |V(w) log w − κ| ≤ C/log w, κ > 0. For log w ≥ L₀ := max(log(B+4), C/(ηκ)):
    V(w) ≤ (1+η)κ/log w and V(y) log y ≥ (1−η)κ. With log √(y/p) = (1 − x) log y/2 ≥ (1 − c) log y/2:
    V(√(y/p)) ≤ R · 2V(y)/(1 − x), R = (1+η)/(1−η) ≤ 1 + 3η (η ≤ 1/3).
    So the term ≤ 2V(y) R h(x_p) gB(p), h(x) = (U − x)/(1 − x), decreasing, 0 ≤ h ≤ 1 on [0, c].
(b) Points s_j = a + (j − 1)Δ, j = 0..K+1, Δ = (c − a)/K ≤ 1/6, so s₀ = a − Δ ≥ a/2 > 0, s₁ = a, s_{K+1} = c.
    Indicator telescoping: Σ_{j≤K} [σ ∈ (log s_j, log s_{j+1}]] = 1 for σ = log x_p ∈ (log s₀, log c].
    h(x_p) ≤ Σ_j [..] h(s_j) (h decreasing). S ⊆ Pset y s₀ (primes in (y^{s₀}, y]); extend to Pset (nonneg terms), swap:
    Σ_S h gB ≤ Σ_j h(s_j) mu1(y; log s_j, log s_{j+1}).
(c) Mertens 2 (`MT.mu1_tendsto`, finitely many j): eventually mu1_j ≤ log s_{j+1} − log s_j + η′.
(d) Riemann sum vs closed form, F(x) = U log x + (1 − U) log(1 − x), I(a, c) = F(c) − F(a):
    for s < t < 1: h(s)(log t − log s) − (F(t) − F(s)) = (1−U)[log((1−s)/(1−t)) − s/(1−s) log(t/s)]
      ≤ (1−U)(t − s)²/((1−t)(1−s)t)   (log z ≤ z − 1, log z ≥ 1 − 1/z).
    j = 0 piece: h(s₀) log(a/s₀) ≤ Δ/s₀ ≤ 6Δ. Total Σ_S h gB ≤ I(a, c) + 6Δ + DΔ + (K+1)η′, D = 3(1−U)/(1−c)².
(e) I(a, c) ≤ U log(c/a) ≤ 2. Choose Δ ((6 + D)Δ ≤ ε′/3), η′ = ε′/(3(K+1)), 3η(2 + ε′) ≤ ε′/3. Then
    2V(y) R X ≤ 2V(y)(X + 3ηX) ≤ 2V(y)(I + ε′), X = Σ_S h gB ∈ [0, 2 + ε′].

## Step 3
ε′ = ε/(1 + Σ_i (c_i − 1)); eventually for all bands i < n (finite). Sum: LHS ≤ 2e^γ V(y)(bandCost + ε′Σ(c_i −1)) ≤ 2e^γV(y)(bandCost + ε).
