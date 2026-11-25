# S04 plan (Σ₂ + Σ₃ ≥ −Σ_{δ ∈ 𝒟, δ | A} Λ{(A/δ, P(√(y/δ))), φ(δ), w})

Statement (frozen) as in Statements.lean. True as stated (any m > 0, no z ≤ y needed).
A squarefree with all primes < z, so radLt A z = A and A | P(z). Write val(P) := φ if P = ∅, Σ_{p∈P} w(p) if |P| = 1,
0 otherwise; for a set P of primes LamA(Π P, φ, w) = val(P). χ̄ ∈ {0, 1} on δ ≠ 0, 1 (χ monotone under δ ↦ δ/p(δ)).

1. Inner sum. For δ | A, C = radLt A p(δ) has prime set P_C = {p | A : p < p(δ)}, coprime to δ, so
   φ(tδ) = φ(δ) − Σ_{p|t} w(p) and innerS = Σ_{T ⊆ P_C} (−1)^{|T|}(φ(δ) − Σ_T w) = val(P_C)
   (insert/erase recursion on the powerset: the sum equals w(a)[P_C = {a}] once P_C ∋ a).
2. Monotonicity. If P ⊆ Q, φ ≥ 0, w ≥ 0 and w(q) ≤ φ for q ∈ Q, then val(Q) ≤ val(P) (cases |Q| = 0, 1, ≥ 2).
3. Σ₃ terms (δ | A, ν odd, 3 ≤ ν ≤ 1/m). μ(δ) = −1. χ̄(δ) = 0: term 0 and δ ∉ 𝒟. χ̄(δ) = 1: δ ∈ 𝒟,
   y ≤ δp(δ)² (the violating divisor contains p(δ)), so √(y/δ) ≤ p(δ) and P_B := {q | A/δ : q < √(y/δ)} ⊆ P_C;
   term = −val(P_C) ≥ −val(P_B) = −Λ{B, φ(δ), w} by 2 with the hypotheses φ(δ) ≥ 0 and w(q) ≤ φ(δ) for q < p(δ).
4. Σ₂ terms (p | A). χ̄(p) = 0: term 0, p ∉ 𝒟. χ̄(p) = 1: then p³ ≥ y and 1 ≤ 1/m (the violating divisor is p),
   so p ∈ 𝒟 and √(y/p) ≤ p. With P_B = {q | A/p : q < √(y/p)} (q < √(y/p) ⟺ q²p < y):
   |P_B| = 0: term = −φ(p) = −val. |P_B| = 1 = {q₀}: S(A/p, √(y/p)) = 0, only q₀ can occur in the q-sum, term ≥ −w(q₀).
   |P_B| ≥ 2: S(A/p, √(y/p)) = 0, and for each q in the q-sum another q′ ∈ P_B divides A/(pq) with q′ < p, so S(A/(pq), p) = 0.
5. Sum. {δ ∈ 𝒟 : δ | A} = {p | A prime, p ∈ 𝒟} ⊔ {δ in the Σ₃ range, δ ∈ 𝒟} (ν(δ) odd: = 1 means prime since δ squarefree).
