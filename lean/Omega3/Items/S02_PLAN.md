# S02 plan (Greaves Lemma 2 identity for squarefree A | P(z))

## Statement check
The version frozen before 21:52 (hypothesis 0 < m only) is false for m > 1: then no h with odd ν(h) is constrained in
χ_y, so χ̄(p) = 0 for primes and Σ₂ = Σ₃ = 0, while Λ₂ does not depend on m. Counterexample y = 10, z = 4, m = 2,
W(1) = 1, w = 0, A = 6: Σ(A) = 0 − Λ₂ = −1, Σ₁ + Σ₂ + Σ₃ + Σ₄ = −1 + 0 + 0 + 1 = 0. Lean: `S02_not : ¬ ItemS02old`
(S02_Neg.lean). Fix: add m ≤ 1 (route m = 1/85). The main session applied it at 21:52, so ItemS02 = ItemS02fix.

## Proof with m ≤ 1 (z ≤ y is not needed)
A squarefree, primes < z, so radLt A z = A. I(δ) := innerS = Σ_{t | (A, P(p(δ)))} μ(t)φ(tδ) = val(primes of A below p(δ)),
where val(P) = φ if P = ∅, w(q) if P = {q}, 0 otherwise (powerset/Möbius computation, as in S03).
A. Telescoping: for squarefree d, χ(d) = 1 − Σ_{δ head of d} χ̄(δ), where the heads are the δ | d, δ ≠ 1 with all primes of
   d/δ below p(δ). Induction on d: heads(d) = {d} ⊔ heads(d/p(d)). Exchange of sums (d = tδ) gives
   Σ₁ = Σ_{d|A} μφ − Σ_{δ|A, δ≠1} μ(δ)χ̄(δ)I(δ), and Σ_{d|A} μ(d)φ(d) = Λ{A, W(1), w}.
B. Split δ by ν(δ): ν = 1 (primes, μ = −1), odd 3 ≤ ν ≤ 1/m (= Σ₃), even ≥ 2 (= Σ₄), odd ν > 1/m: χ̄(δ) = 0
   (every constrained h ∋ p(δ), h ≠ δ, is dominated by h′ = (h/p(δ))q ∣ δ/p(δ) with the same ν, q ∤ h).
   So Σ₁ + Σ₂ + Σ₃ + Σ₄ = Λ{A} + Σ_{p|A} χ̄(p)I(p) + Σ₂.
C. Per prime p | A, with a = A/p, PC = primes of a below p, s = √(y/p): χ̄(p) = [y ≤ p³] (needs m ≤ 1).
   χ̄(p) = 0: the Λ₂ set {q < p : y ≤ q²p} is empty. χ̄(p) = 1 (s ≤ p): S(a/q, p) = [PC = {q}], S(a/q, q) = [q = min PC],
   S(a, s) = [s ≤ min PC]; the Λ₂ set is PC ∩ [s, p), the Σ₂ q-set is PC ∩ [0, s), and
   Σ_{q ∈ PC, q ≥ s} [q = min PC] = [s ≤ min PC] − [PC = ∅] closes the identity −Λ₂(p-part) = χ̄(p)I(p) + Σ₂(p-part).
