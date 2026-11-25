# L07 plan (record numerics for every b ≥ 5)

Statement (frozen): given FejerM4Stmt, for every b ≥ 5 there are ψ, lA, θ_w, κ with
τ₀ := recTau b 0 > 0, τ₀ ≤ b^{−ψ}, A := trigMass (recH b) (recTau b) ≤ b^{lA}, M := mw4 b (recGR b) ≤ b^{−(1+θ_w)},
θ_w > 0, κ > 0, (ii*) 0.68 + 2κ < ψ + q(0.68θ_w − 2κ)/3, (iii*) lA + 2κ < q(0.6θ_w − 2κ)/3, (Q1) 0.664 < ψ,
(Q2′) 3lA < qψθ_w, where q = 1 − recP b (q = 1/1024 for b ≤ 15, q = 1/b² for b ≥ 16), so 0 < q ≤ 1.

The statement is true as stated. κ may depend on b, so no uniform κ is needed (κ_b → 0 is harmless).

## 1. Generic real lemma (exponents chosen so that the rpow bounds are equalities)
Given real b > 1, 0 < L₁ ≤ log b ≤ L₂, τ₀ > 0 with τ₀²⁵b¹⁷ < 1, M > 0 with bM < 1, A > 0 with A ≤ 1 + e, e ≥ 0,
0 < q ≤ 1, and the smallness conditions
  (S1) 3e/L₁ < q·(17/25)·(1 − bM)/L₂,   (S2) e/L₁ < q·(3/5)·((1 − bM)/L₂)/3.
Take
- ψ = −log τ₀/log b. Then b^{−ψ} = exp(log b·(−ψ)) = exp(log τ₀) = τ₀. From 25 log τ₀ + 17 log b = log(τ₀²⁵b¹⁷) < 0
  we get ψ > 17/25 = 2θ > 2c₁ = 0.664 (Q1).
- θ_w = −log(bM)/log b. Then b^{−(1+θ_w)} = exp(−log b + log(bM)) = exp(log M) = M. θ_w > 0 since bM < 1, and
  −log(bM) ≥ 1 − bM (log t ≤ t − 1), so θ_w ≥ Θ₀ := (1 − bM)/L₂ > 0.
- lA = max(0, log A/log b). Then b^{lA} ≥ b^{log A/log b} = A, and 0 ≤ lA ≤ e/L₁ (log A ≤ A − 1 ≤ e).
- (Q2′): 3lA ≤ 3e/L₁ < q(17/25)Θ₀ ≤ qψθ_w.
- κ: d₁ := ψ + q·0.68θ_w/3 − 0.68 > 0 (as ψ > 0.68), d₂ := q·0.6θ_w/3 − lA > 0 (by (S2) and θ_w ≥ Θ₀).
  κ := min(d₁, d₂)/4 > 0. Since 2κ + 2qκ/3 ≤ (8/3)κ < 4κ ≤ d_i, (ii*) and (iii*) follow.

## 2. Inputs per base
Fejér bases (b ∉ {6, 8}), m = mB b = ⌊(b+1)/2⌋, so 2m − 1 ≤ b ≤ 2m, m ≥ 3, recH b = m − 1:
- τ₀ = q + (1 − q)/m (fejTau m 0 = 1/m).
- A = 1: τ₀ ≥ 0, τ_u = (1−q)(m−u)/m² ≥ 0 for 1 ≤ u ≤ m−1, Σ_{u=1}^{m−1}(m−u) = m(m−1)/2, so A = q + (1−q)/m + (1−q)(m−1)/m = 1. Hence e = 0,
  L₁ = log b, L₂ = b − 1, and (S1), (S2) read 0 < positive.
- M = (151m⁶ + 70m⁴ + 49m² + 45)/(315m⁷) by FejerM4Stmt: in mw4 the guard `i < b ∧ s − i < b` is redundant because
  fejerW m a = 0 for a ≥ 2m − 1 and 2m − 1 ≤ b; the inner sums vanish for s ≥ 4m − 3 (then i or s − i is ≥ 2m − 1), so the
  outer ranges range(2b − 1) and range(4m) give the same sum (both ⊇ range(4m − 3)).
Finite part b ∈ {5, 7, 9, …, 15} (q = 1/1024): τ₀²⁵b¹⁷ < 1 and b·M(m) < 1 by norm_num (b = 5: τ₀²⁵5¹⁷ ≈ 0.946, 5M(3) = 0.8436).
Uniform part b ≥ 16 (q = 1/b², m ≥ 8):
- τ₀ = 1/b² + (1 − 1/b²)/m ≤ 1/b² + 2/b = (2b + 1)/b² (2m ≥ b), and (2b + 1)²⁵ < b³³ for b ≥ 16 since
  16(2b + 1) ≤ 33b and 33²⁵ < 16³³ ≤ 16²⁵b⁸. So τ₀²⁵b¹⁷ ≤ (2b+1)²⁵/b³³ < 1.
- bM ≤ 2mM = 2(151m⁶ + 70m⁴ + 49m² + 45)/(315m⁶) < 1 ⟺ 140m⁴ + 98m² + 90 < 13m⁶, true for m ≥ 8 (13m⁶ ≥ 832m⁴ ≥ 328m⁴).
LP bases b = 6, 8 (q = 1/1024): exact rationals. τ₀²⁵b¹⁷ ≈ 0.881 (b = 6), 0.361 (b = 8); bM = 0.8221, 0.8507;
A = 1 + 9.99·10⁻⁷ (both) ≤ 1 + e with e = 2·10⁻⁶; L₁ = 1 (exp 1 < 6), L₂ = b − 1; (S1) 6·10⁻⁶ < 2.4·10⁻⁵ (b = 6),
1.4·10⁻⁵ (b = 8); (S2) 2·10⁻⁶ < 6.9·10⁻⁶, 4.2·10⁻⁶.

No kernel computation is needed: the finite part is 11 bases checked by norm_num on rationals.
