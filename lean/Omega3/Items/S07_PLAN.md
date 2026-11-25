# S07 plan (Lemma 4 (i) above x_n and (ii′) for odd ν ≥ 3)

Statement (frozen): BandOK B, y > 1, δ ∈ 𝒟 = Dset y (y^U) m, δ in no band, q prime with q²δ < y ⇒
w(q) ≤ φ(δ)(2 log q/log(y/δ))², w = wy y, φ = phiW W1 w. True as stated.

Notation: t = log_y q > 0, l_p = log_y p, x = log_y δ = Σ_{p|δ} l_p (δ squarefree), so 2t + x < 1 and
2 log q/log(y/δ) = 2t/(1 − x). W1 = 1 − 3m, U = 1 − 2m, m = 1/85, k² = 9.999.

## Facts on 𝒟 (as in S13, copied with new names)
F1 δ squarefree, δ ≠ 1, every p | δ has p < y^U. F2 χ̄(δ) = 1 ⇒ χ(δ/p(δ)) = 1, χ(δ) = 0.
F3 y ≤ δ p(δ)² (the violating divisor contains p(δ)). F4 p | δ, p ≠ p(δ) ⇒ p³ < y (h = p divides δ/p(δ),
ω(p) = 1 ≤ 1/m, minFac p = p).

## Facts on W
W(t) = 0 for t ≤ m; W(t) ≤ t − m for t > m; W(t) ≤ k²t² for 0 ≤ t ≤ 1/3; W(x) = x − m for 1/3 ≤ x ≤ U;
W(l) ≤ (1 − 3m)l for 0 ≤ l ≤ 1/3 (l − m ≤ (1 − 3m)l ⟺ 3ml ≤ m).

## Case ν(δ) = 1 (δ = p prime)
F3 gives p³ ≥ y, x ≥ 1/3 = x₀. If x < x_n then a band contains p (walk along xs: first edge with x < x_{i+1};
no sortedness needed), contradicting the hypothesis; so x ≥ x_n. p < y^U gives x < U. φ(p) = W1 − W(x) = U − x.
Put s = 1 − x ∈ (2m, 1 − x_n], U − x = s − 2m; need W(t) ≤ 4(s − 2m)t²/s² for 0 < t < s/2.
- t ≤ m: W(t) = 0 ≤ RHS.
- t > m, s ≥ 4m: g(s) = (s − 2m)/s² is decreasing on [4m, ∞) ((s − 2m)s′² − (s′ − 2m)s² = (s′ − s)(ss′ − 2m(s + s′)) ≥ 0),
  so 4g(s) ≥ 4g(1 − x_n) ≥ k² (BandOK), and W(t) ≤ k²t² ≤ 4g(s)t² (t < 1/3).
- t > m, s < 4m: W(t) ≤ t − m and Q(s) = (t − m)s² − 4t²s + 8mt² ≤ 0 on [2t, 4t] (convex in s, Q(2t) = −4t²(t − m),
  Q(4t) = −8mt²); here 2t < s < 4m < 4t.

## Case ν(δ) ≥ 3 (odd, δ not prime)
p₀ = p(δ), l₀ = l_{p₀}. F3: 1 ≤ x + 2l₀. p₀^ν ≤ δ: νl₀ ≤ x. All l_p ≤ 1/3 (F4; p₀ ≤ any other p | δ).
- t ≤ m: W(t) = 0, need φ ≥ 0: Σ W(l_p) ≤ (1 − 3m)Σ l_p = (1 − 3m)x ≤ 1 − 3m = W1 (x < 1).
- t > m: 2t < 1 − x ≤ 2l₀ so every l_p ≥ l₀ > t > m, Σ W(l_p) ≤ x − νm ≤ x − 3m, φ ≥ 1 − x > 0.
  1 − x ≤ 2l₀ ≤ 2x/ν ≤ 2x/3 ⇒ 1 − x ≤ 2/5, t < 1/5. RHS ≥ (1 − x)·4t²/(1 − x)² = 4t²/(1 − x) ≥ 10t² ≥ k²t² ≥ W(t).
(x_n ≤ 2U − 1 in BandOK is not needed.)
