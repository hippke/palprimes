# Q04 (Proposition CQ_E′, assembly) sub-blueprint

Statement (frozen `ItemQ04`): b ≥ 3, digit weight g, 0 < p_T < 1, H ≤ 2b − 2, ‖G_g‖^{p_T} ≤ T, 0 < τ₀ ≤ b^{−ψ},
A(T) ≤ b^{lA}, m_w(4) ≤ b^{−(1+θ_w)}, θ_w > 0, 0 < c₀ < c₁ < 1/2, (Q1) 2c₁ < ψ, (Q2′) 3lA < (1 − p_T)ψθ_w,
SqRed, SqDiag, SqParseval ⇒ ∃ η > 0, eventually Σ_{x^{c₀}<p≤x^{c₁}} A^w_{p²} ≤ 2X_w x^{−c₀} + x^{−η}.
True as stated, no correction. Source: squares NOTES §2 (route E′), dossier v5 §3.2 steps 1–5, 7, 9.

## Preliminaries
- θ_w < 1 (m_w(4) ≥ 1/(2b − 1) by Cauchy–Schwarz, as in L10). lA′ = max(lA, 0): A ≤ b^{lA′}, 3lA′ < (1 − p_T)ψθ_w.
- σ = min(1/2, (ψ − 2c₁)/(2c₁), s₂/(2D_σ)), s₂ = (1 − p_T)ψθ_w − 3lA′, D_σ = 3lA′/2 + (1 − p_T)ψθ_w.
  α = (1 − σ)θ_w/3, β₁ = lA′(1 + σ/2)/ψ. Then 3ψ(α(1 − p_T) − β₁) = s₂ − σD_σ ≥ s₂/2 > 0, β₁ < α(1 − p_T) ≤ θ_w/3 < 1.
  η₁ = min(σ/2, α(1 − p_T) − β₁, σθ_w, 1 − β₁) > 0; η = η₁c₀/2.

## Step 1 (SqRed)
For p in the range, p > x^{c₀} > b³ − b, so p ∤ r and A^w_{p²} ≤ X_w/p² + τ(r)Σ_{k<r}F_k(p),
F_k(p) = p^{−2}(Σ*_{h<p²}‖f(h/p² + k/r)‖ + Σ_{0<h<p}‖f(h/p + k/r)‖).
Main term: Σ_{p>x^{c₀}} p^{−2} ≤ Σ_{a₀<n} n^{−2} ≤ 1/a₀ ≤ 2x^{−c₀} (a₀ = ⌊x^{c₀}⌋, telescoping 1/n² ≤ 1/(n−1) − 1/n).

## Step 2 (one block [Q, 2Q), Q = 2^i, x^{c₀}/2 < Q ≤ x^{c₁}), lemma Q04_block
j = ⌊log_b Q⌋ − 1 ≥ 1 (Q > b²), b^{j+1} ≤ Q < b^{j+2}, so 2b^{2j+1} ≤ Q² ≤ p², j < N.
K = [1, kK], kK = ⌈(1 + σ/2) log Q/(ψ log b)⌉, kK + 1 ≤ N for N large (by (Q1) and σ). J = [N − j, N).
Pointwise (Palprimes.cut_pointwise with the threshold t = Q^{−α}): ‖f‖ ≤ t^{1−p_T}T_K + t^{−3}‖g_J‖⁴ (‖f‖ ≤ ‖g_J‖,
‖f‖^{p_T} ≤ T_K), and ‖f‖ ≤ ‖f‖^{p_T} ≤ T_K. T_K ≥ 0 extends the h-sums to all residues. SqDiag gives the T_K sums,
SqParseval gives Σ_h‖g_J‖⁴ = p²m_w(4)^j ≤ 4Q²m_w(4)^j, at most Q primes. Hence the block is
≤ Q^{−2}[t^{1−p_T}(4Q³τ₀^{kK} + 4Q²ℓA^{kK}) + t^{−3}4Q³m_w(4)^j + 4Q²τ₀^{kK} + 2QℓA^{kK}], ℓ = log(2Hx)/log Q.

## Step 3 (numerics of a block), lemma Q04_num
τ₀^{kK} ≤ Q^{−(1+σ/2)}, A^{kK} ≤ b^{lA′}Q^{β₁}, m_w(4)^j ≤ b^{2(1+θ_w)}Q^{−(1+θ_w)}, ℓ ≤ L* = log(4bx)/log 2.
The five terms have Q-exponents −(α(1−p_T) + σ/2), −(α(1−p_T) − β₁), −σθ_w (= 3α − θ_w), −(1 + σ/2), −(1 − β₁), all ≤ −η₁.
So block ≤ C_b(1 + L*)Q^{−η₁} ≤ C_b(1 + L*)2^{η₁}x^{−η₁c₀}.

## Step 4 (assembly)
Primes grouped by i = ⌊log₂ p⌋ ∈ [⌊log₂ a₀⌋, ⌊log₂⌊x^{c₁}⌋⌋], at most b(2N+1) blocks; r shifts; τ(r).
Error ≤ τ(r)·r·b(2N+1)·C_b(1 + L*)2^{η₁}x^{−η₁c₀} ≤ [C(N+1)²ρ^N]·x^{−η₁c₀/2} ≤ x^{−η} for N large
(Palprimes.eventually_poly_geom, ρ = b^{−η₁c₀}). ∎
