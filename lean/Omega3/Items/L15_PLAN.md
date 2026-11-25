# L15 (Lemma W_w, the ranges) sub-blueprint

Statement (frozen `ItemL15`): b ≥ 3, digit weight g, g(0), g(1) > 0, 0 < θ₀ < θ < 1/2, κ > 0, LemmaKStmt, SSStmt(θ, κ),
TL1w(θ, κ, θ₀) ⇒ ∀ A, eventually ∀ k < r = b³ − b: FareyW(N, ⌊x^θ⌋, k/r) ≤ (log x)^{−A}.
True as stated. TL1w is not needed (SSStmt already covers every dyadic D₀ ≤ D ≤ x^θ, uniformly in N; r238 §2.8 uses
TL¹ for the window only because there SS is applied below x^{θ₀}). Lemma K handles q < Q₁. The rate obtained is
ρ^{√N/m} (stronger than any power of log x), which is what r238's exp(−c√log x) gives.

## Constants
η = min(κ/(4θ), 1), 3^{ω(n)} ≤ C₃ n^η (Palprimes.three_pow_omega_le_rpow); D₀ from SSStmt at ε = κ/(4θ);
c₅ = κ/(2θ), ρ₂ = 2^{−c₅}; c_K = g(0)g(1)/(b⁴(b+1)²); m ∈ ℕ with c_K m ≥ 2 log b + 1; ρ₄ = max(e^{−1}, ρ₂) < 1.
For N: r = ⌊√N⌋, L₁ = ⌊r/m⌋, Q₁ = b^{L₁}. N₀ makes L₁ ≥ 1, L₁ ≥ n₀ (poly-geom lemma), b^{L₁} > 2D₀, N ≥ 3.

## Small moduli 2 ≤ q < Q₁
‖f_g(α)‖ ≤ Π_{1≤n≤N−1}‖G_g(c_nα)‖ ≤ exp(−c_K⌊(N−2)/L_q⌋) (Lemma K, α = h/q + k/r, (q, hr) = 1 for h reduced and
(q, r) = 1), L_q = max(1, ⌊log_b q⌋) ≤ L₁, so ≤ E = exp(−c_K s), s = ⌊(N−2)/L₁⌋ ≥ m(r − 3) (m L₁ ≤ r, r² ≤ N).
Each term 3^{ω(q)} q^{−1} L1*(q) ≤ C₃ q^η E ≤ C₃ Q₁ E, at most Q₁ terms: ≤ C₃ Q₁² E = C₃ exp(2L₁ log b − c_K s)
≤ C₃ e^{3c_K m} e^{−L₁} (L₁ ≤ r, c_K m ≥ 2 log b + 1).

## Middle and window q ≥ Q₁ (dyadic blocks D = 2^i, i = ⌊log₂ q⌋ ≥ ⌊log₂ Q₁⌋ ≥ L₁)
D > Q₁/2 > D₀ and D ≤ q ≤ ⌊x^θ⌋, so SSStmt applies: block ≤ D·D^{−κ/θ+κ/(4θ)}. With 3^{ω(q)}/q ≤ C₃(2D)^η/D on
[D, 2D): weighted block ≤ C₃2^η D^{η−3κ/(4θ)} ≤ C₃2^η ρ₂^i. Geometric sum over i ≥ ⌊log₂ Q₁⌋: ≤ C₃2^η ρ₂^{L₁}/(1 − ρ₂).

## Assembly
FareyW ≤ K ρ₄^{L₁}, K = C₃e^{3c_K m} + C₃2^η/(1 − ρ₂). log x = (2N+1) log b ≤ 2m²log b (L₁+1)² (N < (r+1)²,
r + 1 ≤ m(L₁+1)). Palprimes.eventually_poly_geom: K(2m² log b)^A (L₁+1)^{2A} ρ₄^{L₁} ≤ 1 for L₁ ≥ n₀. ∎
