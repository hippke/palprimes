# L09 plan (Lemma29wStmt with factor 6)

m = N − j, c'_i = cK b j i (i < j). Then cK b N (m + i) = b^m c'_i, so gJ(α) = P(b^m α), P(γ) = Π_{i<j} G_g(c'_i γ).
1. G_g(t)² = Σ_{s<2b−1} c_s e(st), c_s = (g∗g)(s) (the inner sum of mw4).
2. P(γ)² = Σ_{f : Fin j → Fin (2b−1)} w_f e(Y'(f)γ), w_f = Π c_{f_i}, Y'(f) = Σ f_i c'_i < 2b^{2j+1}
   ((b − 1)Σ c'_i ≤ b^{2j+1} − 1 by the geometric sum).
3. Weighted copy of Palprimes `ls_step` (large_sieve + farey_spacing + twist_bij on points b^m(h/d + β)):
   Σ_d Σ*_h |P(b^m(h/d+β))|⁴ ≤ (4N₁ + 12D² + 2) Σ_n (Σ_{Y'(f)=n} w_f)², N₁ = 2b^{2j+1}.
4. Y' injective (Palprimes sum_cK_eq_zero at L = j, |f_i − f'_i| ≤ 2b − 2), so Σ_n(...)² = Σ_f w_f² = mw4^j.
5. 8b^{2j+1} + 12D² + 2 ≤ 6(4D² + 2b·b^{2j}).
