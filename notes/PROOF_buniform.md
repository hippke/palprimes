# Level 1/4 − ε for palindromes and Ω ≤ 5 in every base

2026-11-20, written in the main chat from r31 §2.1, r32 §7, r35 §1 and r36 (proof r35, adversarial audit r36 with independent code). Second end-to-end audit r38 (15:03–15:20 CET): correct with fixable gaps in exposition and citation, fixes applied below (§5). Notation and numbering follow Tuxanidy–Panario v3 (TP, arXiv 2307.16637v3, IMRN 2024). The local TeX in r01_setup_chat/lit is an older version with shifted numbering (hybrid bound = Prop. 7.1 there).

## 0. Statements
- Notation. b ≥ 2. φ_b(t) = |Σ_{d<b} e(dt)|, ψ(t) = (φ_b(t)/b)² ∈ [0, 1]. For L ≥ 1, c_k = b^k + b^{2L−k} (0 ≤ k < L) and c_L = b^L. For K ⊂ [0, L] write Π_K(α) = Π_{k∈K} ψ(c_k α). TP's product is Φ_N(α) = Π_{1≤n<N} φ_b(α(b^n + b^{2N−n})). P_N is the set of base-b palindromes with 2N+1 digits.
- **Theorem 1.** For every b ≥ 2 and every θ < 1/4, palindromes in base b have level of distribution θ in TP's sense (TP Theorem 1.5 with exponent 1/5 replaced by θ), uniformly in the residue class.
- **Corollary 2.** For every base b ≥ 2 there are infinitely many base-b palindromes with at most 5 prime factors counted with multiplicity.
  - Proof from Theorem 1. TP's Richert set-up (v3 Lemma 11.1) gives Ω ≤ 5 at any level above 1/Δ_5 = 0.2108869. Its extra hypothesis Σ_{D^{1/4} ≤ p ≤ D^{1/u_r}} A_{p²} ≪ X/log³x is supplied by TP v3 Prop. 10.1 (squarefree q ≤ x^{1/4−ε₀}, (q, b³−b) = 1), since D^{1/u_5} < x^{1/4}. Remainders vanish for (d, b³−b) > 1, and even-length palindromes are excluded through TP's set P*. Greaves' weighted sieve (Greaves 1982, Acta Arith. 40, Corollary 1, r27/r28, threshold 0.2050032) is a redundant second route. Both thresholds are below 1/4. TP's Lemma 11.1 is taken as published.
- **Proposition V (r35).** Fix κ ∈ (0, 1). Let Q ∈ [b^{κL}, b^{κL+1}] (r38 issue 3, the proof tolerates this interval at the cost of bounded powers of b and |K2| larger by one), λ = b^L/Q, θ_b = log_b(3b²/(2b²+1)) > 0 and η' = (θ_b/2)·min(κ/(1−κ), 1+θ_b). For every real β,
  S(β) := Σ_{Q≤q≤2Q, (q,b)=1} Σ*_{h mod q} Π_{[0,L−1]}(h/q + β) ≪_{b,κ} Q·τ*^{1/2}·λ^{−η'},
  where τ* = max_{0<|w|<2b^{2L+1}} #{q ∈ [Q, 2Q] : q | w} = b^{o(L)}.
  - The same holds for Π_{[0,L]} (with the middle digit). Here the product without the middle digit is used, since that is what TP's Φ_N produces (r36 issue 1).
  - η' at κ ≥ 0.6 is 0.294 (b = 2), 0.211 (b = 3), 0.102 (b = 10), 0.048 (b = 100), ≈ 0.20/ln b for large b.

## 1. Injectivity lemma
- **Lemma 3.** Let t_0, …, t_{2L} be integers with |t_j| ≤ 2b − 2 and t_j = t_{2L−j} for all j. If Σ_j t_j b^j = 0, then t = 0.
- Proof. Put P_j = Σ_{i≤j} t_i b^i. Then |P_j| ≤ 2b^{j+1} − 2, and P_j = −Σ_{i>j} t_i b^i is divisible by b^{j+1}. So C_j = P_j/b^{j+1} ∈ {−1, 0, 1}, C_{−1} = C_{2L} = 0 and t_j = bC_j − C_{j−1}. With D_j = C_{2L−1−j} one has t_{2L−j} = bD_{j−1} − D_j. The symmetry t_j = t_{2L−j} becomes bC_j + D_j = bD_{j−1} + C_{j−1}. If C_{j−1} = D_{j−1} = 0, then bC_j + D_j = 0 with |C_j|, |D_j| ≤ 1 and b ≥ 2, so C_j = D_j = 0. Induction over j = 0, …, L−1 gives C_j = 0 for all j, hence t = 0. □
- The bound 2b − 2 is sharp for b = 2 (r36 issue 3). Checked exactly by meet in the middle for b ≤ 23 and small L (r36 `inj_mitm.log`).
- **Consequence.** Let K1, K2 ⊂ [0, L] be disjoint, and let d_k, d'_k be independent uniform digits. Put Y = Σ_{K1}(d_k + d'_k)c_k + Σ_{K2} d_k c_k. The difference of two independent copies of Y is Σ_k t_k c_k = Σ_j t̃_j b^j, with t̃ palindromic and |t̃_j| ≤ 2b − 2. So Y = Y' exactly when the digit sums on K1 and the digits on K2 agree. With g = (2b²+1)/(3b²) = b^{−θ_b},
  ‖law(Y)‖₂² = Pr(Y = Y') = (g/b)^{|K1|} b^{−|K2|}.

## 2. Proof of Proposition V (r35 §1.3, with the middle-digit fix of r36)
- Choose m = ⌈(1−κ)L⌉ and K3 = [0, m). Split the inner block [m, L−1] = K1 ⊔ K2 with |K2| = max(0, ⌈κL − (1+θ_b)m⌉).
- Cauchy–Schwarz. Termwise Π_{[0,L−1]} = (Π_{K1}Π_{K2}^{1/2})(Π_{K3}Π_{K2}^{1/2}), and ψ ≥ 0. Hence S ≤ A1^{1/2}A3^{1/2} with A1 = Σ Π_{K1}²Π_{K2} and A3 = Σ Π_{K3}²Π_{K2}, both over the same pairs (q, h) and the same β.
- A1, large sieve. Π_{K1}²Π_{K2}(α) = |f̂1(α)|², with f1 the law of Y above.
  - Every c_k with k ≥ m is divisible by b^m. So f̂1(α) = f̃1^(b^m α), with f̃1 the law of Y/b^m, supported in [0, 2b^{2(L−m)+1}).
  - For (q, b) = 1, h ↦ b^m h permutes the reduced residues mod q. The points b^m(h/q + β) are therefore the reduced fractions with denominators in [Q, 2Q], translated by b^m β. They are 1/(4Q²)-spaced.
  - The large sieve gives A1 ≤ (2b^{2(L−m)+1} + 4Q²)‖f1‖₂².
  - L − m ≤ κL gives 2b^{2(L−m)+1} ≤ 2bQ². |K1| + |K2| = L − m ≥ κL − 1 gives b^{−|K1|−|K2|} ≤ b/Q.
  - So A1 ≤ (2b + 4)·b·Q·g^{|K1|}.
- A3, divisor bound (TP's L² lemma). Let f3 be the law of Z = Σ_{K3}(d_k + d'_k)c_k + Σ_{K2} d_k c_k.
  - For every real β, Σ_{h mod q}|f̂3(h/q+β)|² = q Σ_{z≡z' (q)} f3(z)f3(z')e((z−z')β) ≤ q·Pr(Z ≡ Z' mod q).
  - Summing over q ∈ [Q, 2Q] gives A3 ≤ 2Q(#q·‖f3‖₂² + τ*), since |Z − Z'| < 2b^{2L+1}.
  - Lemma 3 gives ‖f3‖₂² = (g/b)^m b^{−|K2|}. The choice of |K2| gives Q‖f3‖₂² ≤ 1, so A3 ≤ 2Q(2 + τ*).
- Conclusion. |K1| = L − m − |K2| ≥ min(κ, (1+θ_b)(1−κ))L − 1. So S ≤ ((2b+4)b·Q·g^{|K1|}·2Q(2+τ*))^{1/2} ≪_b Q τ*^{1/2} λ^{−η'}. □
- Checked numerically on all moduli (prime and composite) in a dyadic range, for b ∈ {2, 3, 5, 10}, κ ∈ [0.6, 0.9] and rational and irrational β, with and without the middle digit (r35 `cs_chain.log`, r36 `chain_*.log`).

## 3. From V to TP's Farey bound (r31 §2.1, r32 §7, r36 §2)
- Fix κ ∈ (0, 1) and δ < κ/(1+κ). Set μ = δ/κ, so δ + μ < 1. Put Q = b^{δN}.
- Split TP's index range [1, N−1] into V = [1, δN] (shallow), U = [N − μN, N − 1] (inner) and the rest A.
- Cauchy–Schwarz and the sup norm on A give Σ_{q~Q}Σ*_h Φ_N(h/q+β) ≤ b^{|A|}(Σ Φ_V²)^{1/2}(Σ Φ_U²)^{1/2}.
  - V. TP's L² lemma gives Σ Φ_V² ≪ Q² b^{δN} b^{o(N)}, uniformly in β. Positivity handles the restrictions on q and h.
  - U. The twist h ↦ h b^{N−μN} (a bijection on reduced residues, (q, b) = 1) turns Φ_U into b^{L}·Π_{[0,L−1]}^{1/2} with L = μN, at the shift β b^{N−μN}. So Σ Φ_U² = b^{2L} S, and Proposition V at κ gives Σ Φ_U² ≪ Q b^{2μN} λ^{−η'} b^{o(N)} with λ = b^{(μ−δ)N}.
  - Product: Q b^N λ^{−η'/2} b^{o(N)}, a power saving over TP's break-even Q b^N.
- TP's Proposition 8.1 (read in r36 §2) needs two things. (i) For Q ≥ b^{δN}, Σ ≪ Q² b^{N(1−δ−σ)}. (ii) For Q ≤ b^{δN}, Σ ≪ Q^{1−σ/δ} b^N.
  - (i), large Q ≥ b^{(δ+σ+γ)N}. Two TP L² halves of length N/2 give the bound when δ + σ + γ ≤ 1/2.
  - (i), the window b^{δN} ≤ Q ≤ b^{(δ+σ+γ)N}. The scheme above at Q gives it once σ is small and δ + σ + γ < κ/(1+κ).
  - (ii) is TP's own reduction (Col's L^∞ bound on the outer digits and (i) at a shorter length). It uses V at the shorter length L' = log_b Q'/κ, where τ*^{1/2} = b^{o(L')} is beaten by λ'^{η'} (r36 issue 2).
  - TP's restriction 1/3 ≤ δ ≤ 2/5 − ε serves only their own Hölder step and is not needed.
- All dyadic sub-ranges (r38 issue 2). TP's (8.1) sums over all q ≤ Q. Run the scheme at each dyadic R ≤ Q. This gives ≪ R b^{N+o(N)} R^{−(1/κ−1)η'/2} with o(N) uniform in R. For R ≤ Q^{1−c} use the bound R b^{N+o(N)}. For R ≥ Q^{1−c} one has log R ≍ N, and the saving beats b^{o(N)}. The total is ≪ Q^{1−c'} b^{N+o(N)}, which is below Q² b^{N(1−δ−σ)} for small σ.
- Form (8.2) (r38 issue 4). TP §9 uses (8.2), with q ≥ 2, (q, b³−b) = 1 and the factor e^{−σ_∞N/log Q}. For Q ≥ b^{δN}, (8.2) follows from (8.1) by positivity, since the factor is ≍ 1. For Q ≤ b^{δN}, TP's own reduction (Col's bound, then (8.1) at length N − M) produces the factor and needs only a fixed δ > 0.
- TP §9 then gives E ≪ Q x^{(1−δ)/2+ε} + √x e^{−c√log x}, i.e. level δ/2. Letting κ → 1 gives every level below 1/4. This proves Theorem 1.
- The shifts kb^t/(b³−b) in TP's argument are real numbers, and V holds for every real β.

## 4. Remarks
- Barrier B8. Level 1/4 is the square-root cap of absolute-value Fourier methods for a set of size x^{1/2}. The argument reaches exactly this cap and cannot pass it. Ω ≤ 4 needs level above 0.2575 (Greaves) and stays open.
- What is new. The doubling of digits on part of the inner block (Lemma 3 makes its collision probability exact) together with a partner sum that is needed only at break-even. The divisor bound gives break-even at any span. The twisted inner block with the large sieve at break-even is already in Tuxanidy 2603.02549. The doubling step, a level above 1/5 for palindromes, and Ω ≤ 5 in every base were not found in 29 + 32 queries and a full-text grep of 2023–2026 (r35, r36). Status "not found", not "new". Closest idea in the literature is Eberhard–Varjú 2003.08117 (§8, case a = 4).
- Effective range. With the explicit constants the bound in V becomes non-trivial only from L of order 100 for b = 3, 10 (r35 `eta_table.log`). The theorem is asymptotic in N, so this is harmless.
- Supersedes the base-by-base results (Ω ≤ 5 for 2 ≤ b ≤ 40 via the r10/r21 schemes and Greaves), which remain correct.

## 5. Audit trail
- r36 (14:45–15:01 CET, adversarial, own code). Proof of V correct. Middle-digit interface fix (used above).
- r38 (15:03–15:20 CET, end-to-end referee audit, own code, TP v3 read on arxiv.org). Correct with fixable gaps. Issues 1–4 (TP v3 numbering and the square-divisor hypothesis of Lemma 11.1, dyadic sub-ranges, Q in an interval, (8.1) versus (8.2)) are fixed in §0 and §3. Remarks: r36's constant (2b+4) drops a factor b and its "no −1 loss" fails when K2 = ∅, while this write-up has both right. Lemma 3 is sharp in base 2. Numerics confirm every explicit inequality (Proposition V chain on 14 configurations × 6 shifts, all moduli, and the L¹ Farey bound of §3 with TP's exact Φ_N for (b, N) = (2, 34), (2, 28), (3, 20), (5, 12), (10, 9)). Small cases cannot confirm the exponent η' or the o(N) losses. These rest on the hand proof.
