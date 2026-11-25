# L11 (Lemma SS) sub-blueprint

Statement (frozen, `ItemL11`): `2 ≤ b`, `IsDigitWeight b g`, `0 < θ₀ < θ`, `0 < κ`, `TL1w b g θ κ θ₀ → SSStmt b g θ κ`.

## Verdict on the flag in reports/L11.md
The flag ("TL1w covers only D ∈ (x^θ₀, x^θ], so Lemma K is needed") is wrong. r238 §2.4: for a small D one does not use
the window of the given N but the window of a shorter length N′ ≤ N chosen so that D ∈ (x′^θ₀, x′^θ]. The inner
positions k ≥ m = N − N′ of f_g (length N) form f′_g(b^m ·) of length N′ (c_k = b^m c′_{k−m}), the outer factors have
modulus ≤ 1 (digit weight), and h ↦ b^m h permutes the reduced residues mod d ((d, b) = 1). The statement is true as
written, no extra hypothesis. Lemma K is needed only in L15 (D ≤ exp(ε√log x), where D₀ of SS is not yet reached
uniformly with a power saving that beats 3^ω); SSStmt itself is uniform in N.

## Proof
Fix ε > 0. Put ε′ = min(κ/2, θε) > 0 and take N₀ from TL1w at ε′. Put c = (θ + θ₀)/(2(θ − θ₀)),
N₁ = max(N₀, ⌈c⌉), D₀ = x_{N₁}^θ + 1 (x_n = b^{2n+1}).
Let N, D dyadic, D₀ ≤ D ≤ x_N^θ, β real.
1. N ≥ N₁: otherwise x_N ≤ x_{N₁} and D ≤ x_N^θ ≤ x_{N₁}^θ < D₀.
2. N′ = least n with N₁ ≤ n and D ≤ x_n^θ (exists: N). Then N′ ≤ N, N′ ≠ N₁ (else D ≤ x_{N₁}^θ < D₀),
   so N′ − 1 ≥ N₁ fails: D > x_{N′−1}^θ = b^{(2N′−1)θ}.
3. Since N′ ≥ c, 2N′(θ − θ₀) ≥ θ + θ₀, i.e. (2N′+1)θ₀ ≤ (2N′−1)θ, so x_{N′}^θ₀ ≤ x_{N′−1}^θ < D ≤ x_{N′}^θ, N′ ≥ N₀.
4. Self-similarity. Write N = N′ + m. For j ≤ N′, cK b N (m + j) = b^m cK b N′ j (both branches of cK). With
   range(N+1) = range m ⊔ (m + range(N′+1)) and ‖G_g‖ ≤ 1: ‖f_g^{(N)}(α)‖ ≤ ‖f_g^{(N′)}(b^m α)‖.
5. Periodicity. f_g^{(N′)}(t + n) = f_g^{(N′)}(t) for n ∈ ℕ (integer frequencies). For (d, b) = 1, d ≥ 1,
   h ↦ b^m h mod d is a bijection of redRes d, and b^m h/d = (b^m h mod d)/d + ⌊b^m h/d⌋, so
   Σ*_h ‖f′(b^m(h/d + β))‖ = Σ*_h ‖f′(h/d + b^m β)‖.
6. So block_N(D, β) ≤ block_{N′}(D, b^m β) ≤ D x_{N′}^{−κ+ε′} (TL1w, step 3).
7. x_{N′}^{−κ+ε′} = (x_{N′}^θ)^{(−κ+ε′)/θ} ≤ D^{(−κ+ε′)/θ} (exponent < 0, D ≤ x_{N′}^θ) ≤ D^{−κ/θ+ε} (D ≥ 1,
   ε′ ≤ θε). ∎

Lean: Omega3/Items/L11.lean, helpers prefixed `L11_`.
