# L10 (Proposition C_w, cut A₁ only) sub-blueprint

Statement (frozen `ItemL10`): hypotheses b ≥ 3, digit weight g, 0 < p < 1, H ≤ 2b − 2, ‖G_g‖^p ≤ T (T = trigEval H τ),
0 < τ₀ ≤ b^{−ψ}, A(T) ≤ b^{lA}, m_w(4) ≤ b^{−(1+θ_w)}, θ_w > 0, κ > 0, 0 < θ₀ < θ < 1/2,
(ii) 2θ + 2κ < ψ + (1 − p)(2θθ_w − 2κ)/3, (iii) lA + 2κ < (1 − p)(2θ₀θ_w − 2κ)/3, Lemma 2.8, Lemma 2.9_w ⇒ TL1w(θ, κ, θ₀).
True as stated (no correction). The strict inequalities are only used as ≤; all losses are constants absorbed by x^{ε/2}.

## Notation
x = b^{2N+1}, D dyadic with x^{θ₀} < D ≤ x^θ, Qs = {d ∈ [D, 2D) : (d, b) = 1}, α = h/d + β, F = ‖f_g(α)‖.
j = ⌊log_b D⌋ (b^j ≤ D < b^{j+1}), J = [N − j, N), G = ‖g_J(α)‖, T_K(α) = Π_{k<N} T(c_k α),
τ* = D^{−θ_w/3} x^{κ/3} (the A₁ cut; Ξ-exponent −(δ′θ_w − 2κ)/3 with D = Ξ^{δ′}).

## Step 0. θ_w < 1
c_s = (g∗g)(s) ≥ 0, Σ_{s<2b−1} c_s = (Σ g)² = 1, Cauchy–Schwarz: m_w(4) = Σ c_s² ≥ 1/(2b − 1) > b^{−2}.
So b^{−(1+θ_w)} > b^{−2}, θ_w < 1, hence e₁ := 1 − (1 − p)θ_w/3 > 0 (this is the "(ii) binds at δ′ = 2θ" monotonicity).

## Step 1. Pointwise cut (Palprimes.cut_pointwise)
F ≤ G (factors outside J have modulus ≤ 1), F^p = Π_{k≤N}‖G_g(c_kα)‖^p ≤ Π_{k<N}‖·‖^p ≤ T_K(α), so
F ≤ τ*^{1−p} T_K(α) + τ*^{−3} G⁴.

## Step 2. Sum over the block
Small part: T_K ≥ 0, so Σ_d Σ*_h ≤ Σ_d Σ_{h<d}; Lemma 2.8 with K = [0, N), Td = C_ε₁ (4bx)^{ε₁} (divisor bound,
|w| ≤ 2Hx < 4bx): ≤ (Σ_d d) τ₀^N + 2D·Td·A^N ≤ 2D²b^{−ψN} + 2D·Td·b^{lA N}.
Large part: Lemma 2.9_w (1 ≤ j ≤ N for N large): ≤ (4D² + 2b·b^{2j}) m_w(4)^j ≤ (4 + 2b) D² (b^j)^{−(1+θ_w)}
≤ (4 + 2b) b^{1+θ_w} D^{1−θ_w}.

## Step 3. Exponents (b^{uN} = x^{u/2} b^{−u/2})
- large: τ*^{−3}(4 + 2b)b^{1+θ_w}D^{1−θ_w} = (4 + 2b)b^{1+θ_w}·D x^{−κ}.
- term 1: τ*^{1−p}·2D²b^{−ψN} = 2b^{ψ/2}·D·D^{e₁}x^{(1−p)κ/3 − ψ/2}; D^{e₁} ≤ x^{θe₁} (e₁ > 0), and
  θe₁ + (1 − p)κ/3 − ψ/2 ≤ −κ is (ii). So ≤ 2b^{ψ/2}·D x^{−κ}.
- term 2: τ*^{1−p}·2D·Td·b^{lA N} ≤ 2C_ε₁(4b)^{ε₁}b^{−lA/2}·D x^{ε₁} x^{lA/2 − (1−p)(θ₀θ_w − κ)/3} (D > x^{θ₀},
  exponent of D negative), and lA/2 − (1 − p)(θ₀θ_w − κ)/3 ≤ −κ is (iii). So ≤ C₂ D x^{−κ+ε₁}.
With ε₁ = ε/2 and N so large that C₁ + C₂ + C₃ ≤ x^{ε/2}: block ≤ D x^{−κ+ε}. ∎
