# S05 plan (conjunct 6 in the 22:10 form: `3 ≤ ω δ → ∀ q < p(δ), w(q) ≤ φ(δ)`)

t_p = log p / log y, W1 = U − m = 1 − 3m (m = 1/85, U = 1 − 2m).
Conjuncts 1–5: case analysis of `Wf` (0 ≤ W ≤ W1, W = W1 for t ≥ U, W = 0 for t ≤ m, W ≤ t − m for t > m).

Conjuncts 6, 7 from one lemma `key`: δ squarefree, δ ≠ 1, χ(δ/p₁) = 1 (p₁ = p(δ)), u a "phantom" weight with
u ≤ a − m for every a > max(m, t₁), u = 0 if t₁ ≤ m, and u = 0 unless ω δ ≥ 2 and ω δ ≤ 85. Then u + Σ_{p∣δ} w(p) ≤ W1.
Proof: δ' = δ/p₁, F = {p ∣ δ' : t_p > m} (the others have w = 0).
* F = ∅: either t₁ ≤ m (everything 0) or δ' = 1 (δ prime, u = 0, w(p₁) ≤ W1).
* F ≠ ∅, a₀ = min F, (|F| even or |F| ≤ 85): χ(δ') = 1 applied to h = ΠF (h p(h)² < y) gives Σ_F t + 2t_{a₀} < 1;
  w(p₁), u ≤ t_{a₀} − m, Σ_F w ≤ Σ_F t − m, total < 1 − 3m.
* F odd with |F| > 85 (then u = 0): G = F ∖ {a₀} (even), a₁ = min G, same bound with u₁ = w(p₁), u₂ = w(a₀) ≤ t_{a₁} − m.
Conjunct 6: u = 0 (φ ≥ 0) and u = w(q), q < p₁ (needs ω δ ≥ 3 ≥ 2). Conjunct 7: u = 0.
