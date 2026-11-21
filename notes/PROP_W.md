# Prime-square divisors of palindromes without Baier–Zhao (S0, 2026-11-20)

Goal: replace TP v3 Prop. 10.1 (which uses the Baier–Zhao large sieve for square moduli) by an argument built from the tools of the b-uniform proof (Lemma 3, an elementary large sieve, a trivial divisor count). Only the input that TP's Lemma 11.1 and our crude sieve need is proved: sums over prime squares p², not all squarefree q².

## Setting
- Base b ≥ 2. Palindromes of length 2M (the odd length 2M+1 of TP's P* only adds the middle digit c = b^M, which goes into K1 or is bounded by 1). x = b^{2M}, X = b^M.
- n = Σ_{j<M} d_j c_j with c_j = b^j + b^{2M−1−j}. S(α) = Σ_n e(nα), |S(α)| = X·Π_j ψ(c_j α)^{1/2} with ψ(t) = (φ_b(t)/b)².
- A_q = #{n : q | n}. Fourier: A_{p²} = p^{−2} Σ_{h mod p²} S(h/p²) ≤ X/p² + p^{−2} Σ_{h ≠ 0} |S(h/p²)|.
- Points: 𝒫(P) = {h/p² : P ≤ p < 2P prime, h mod p²}, about P³/log P points.
- θ_b = log_b(3b²/(2b²+1)) and g = b^{−θ_b} = (2b²+1)/(3b²), as in PROOF_buniform.md.

## Proposition W
For every b ≥ 2 and every c < 1/4 there is δ = δ(b, c) > 0 such that for x^{ε} ≤ P ≤ x^c
  Σ_{P ≤ p < 2P} A_{p²} ≪_{b,c} X/P + X·P^{−δ}.
Explicitly δ = θ_b·a/4 with a = min(1, (1+θ_b)(1/(2c) − 2)) (any smaller a > 0 also works). Summed over dyadic P ∈ [x^α, x^c] this gives Σ_{x^α ≤ p ≤ x^c} A_{p²} ≪ X x^{−αδ}, which covers TP Lemma 11.1's hypothesis Σ_{D^{1/4} ≤ p ≤ D^{1/u_r}} A_{p²} ≪ X/log³x (u_r = 1 + 3^{−r}, so D^{1/u_5} = D^{243/244} < D < x^{1/4}; at D = x^{0.22} Prop. W is needed at c ≈ 0.22, δ ≈ 0.042 for b = 2 and ≈ 0.014 for b = 10).

## Proof
Write everything in units of ℓ = log_b P. Choose disjoint position blocks, from the middle outwards: K1 (innermost, length aℓ), K2 (length (1−a)ℓ), K3 (length aℓ/(1+θ_b)), and V (outermost, length ℓ). Total length (2 + a/(1+θ_b))ℓ ≤ M, which is the condition P ≤ x^c with the stated a. Rounding to integers costs bounded powers of b.

1. First Cauchy–Schwarz. Π_all ψ^{1/2} ≤ Π_V ψ^{1/2}·Π_U ψ^{1/2} with U = K1 ∪ K2 ∪ K3. So
   Σ_𝒫 |S|/X ≤ (Σ_𝒫 Π_V ψ)^{1/2}·(Σ_𝒫 Π_U ψ)^{1/2}.
2. Outer block. Π_V ψ(α) = |f̂_V(α)|², f_V the law of Z = Σ_V d_j c_j. For each p, Σ_{h mod p²} |f̂_V(h/p²)|² = p² Pr(Z ≡ Z' mod p²). Z − Z' is 0 with probability b^{−|V|} = 1/P, and otherwise a nonzero integer of size < x, divisible by p² for at most log x/(2 log P) ≤ 1/(2ε) primes p ≥ P. Hence Σ_𝒫 Π_V ψ ≤ 4P²(π(2P)/P + 1/(2ε)) ≪ P².
3. Second Cauchy–Schwarz (as in Prop. V). Π_U ψ = (Π_{K1}ψ Π_{K2}ψ^{1/2})(Π_{K3}ψ Π_{K2}ψ^{1/2}), so Σ Π_U ψ ≤ (A1)^{1/2}(A3)^{1/2} with A1 = Σ Π_{K1}ψ² Π_{K2}ψ and A3 = Σ Π_{K3}ψ² Π_{K2}ψ.
4. A3. Π_{K3}ψ²Π_{K2}ψ = |f̂_3|² with f_3 the law of Σ_{K3}(d+d')c + Σ_{K2} d c. By Lemma 3, ‖f_3‖² = (g/b)^{|K3|} b^{−|K2|} = P^{−(1+θ_b)a/(1+θ_b) − (1−a)} = 1/P. The same divisor count as in step 2 gives A3 ≪ P².
5. A1, elementary large sieve for prime-square moduli. Π_{K1}ψ²Π_{K2}ψ = |f̂_1|², f_1 the law of Y = Σ_{K1}(d+d')c + Σ_{K2} d c.
   - All c_j with j ∈ K1 ∪ K2 are divisible by b^m (m = M − |K1| − |K2|), and Y/b^m < 2b^{2(|K1|+|K2|)+1} =: N1 ≍_b P². For (p, b) = 1 the twist h ↦ b^m h permutes Z/p², so the points become b^m·𝒫, again all h/p².
   - Local count. Any interval of length 1/N1 contains at most Σ_p (2p²/N1 + 1) ≪ P³/N1 + P points of 𝒫.
   - Collision count (audit r-W issue 5, replaces the large sieve). Σ_{h mod p²}|f̂_1(h/p²)|² = p² Pr(p² | W) with W = Y − Y', |W| < N1 after dividing by b^m, and Pr(W = w) ≤ ‖f_1‖² by Cauchy–Schwarz. So Pr(p² | W) ≤ (2N1/p² + 1)‖f_1‖² and Σ_𝒫 |f̂_1|² ≤ Σ_p (p² + 2N1)‖f_1‖² ≪ P³‖f_1‖². No large sieve, no twist needed. (The large sieve with the local count P³/N1 + P gives the same bound.)
   - Lemma 3: ‖f_1‖² = (g/b)^{|K1|} b^{−|K2|} = P^{−(1+θ_b)a − (1−a)} = P^{−1−θ_b a}. So A1 ≪ P^{2 − θ_b a}.
6. Conclusion. Σ Π_U ψ ≪ (P^{2−θ_b a}·P²)^{1/2} = P^{2−θ_b a/2}, and Σ_𝒫 |S| ≪ X (P²)^{1/2}(P^{2−θ_b a/2})^{1/2} = X P^{2−θ_b a/4}. Dividing by p² ≍ P² gives the claim. □

## Interface with TP Lemma 11.1 (audit issue 1)
- TP's A_d counts n ∈ P*_b(x): odd-length palindromes ≤ x coprime to b³ − b. Coprimality only removes elements, so drop it. Odd length 2M+1 is the main case (Lemma 3 as written is the odd-length version, the middle digit goes into K1).
- Shorter lengths and the top block cut at x: P*_b(x) is a union of O(b·log x) cylinders. In each cylinder some outer digits are fixed and the free digits form an inner interval of positions, plus O(1) tie cases. Steps 2–5 only need that, the fixed digits add a phase that the absolute values remove.
- Run Prop. W at c < c″ < 1/4. Cylinders with fewer than ℓ/(2c″) free digit pairs have ≤ b·X^{c/c″} elements, a power saving after summing O(log x) of them. Prop. W at c″ covers the rest.
- Audit report: `AUDIT_W.md`, code `audit/audit_w.py` (exact laws, odd length, b = 2, 3, 5: Lemma 3 exhaustive, norms, Fourier = residue side, A1 ≤ collision bound ≤ large-sieve bound).

## Remarks
- Uniform in b in the same sense as Theorem 1 (constants and δ depend on b, δ ≈ 0.10·a/ln b for large b). The reach c < 1/4 is the square-root cap for these P³ points (average |S| ≈ X/P must exceed √X).
- Without K2 (a = 1, block lengths ℓ, ℓ, ℓ/(1+θ_b)) the reach is only x^{1/(2(2+1/(1+θ_b)))} → x^{1/6}. This was the back-of-envelope figure in PLAN_LEAN.md §3 before S0. K2 is what Prop. V also uses.
- Tools used: Lemma 3, the identity Σ_{h mod q}|f̂(h/q)|² = q Pr(Z ≡ Z' mod q), Pr(W = w) ≤ ‖f‖², a count of prime-square divisors of a nonzero integer. No large sieve, no divisor bound τ(n) ≪ n^ε, no Poisson summation, no Baier–Zhao.
- Small-case check of each inequality in the chain: `chain.py`, `chain.log` (b = 2, 3, 5, 10). Small cases cannot test the exponent.

## Prime cubes (optional simplification)
- A_{p³} ≤ 2b^{3/2} X p^{−3/2}. Proof: fix all digits outside a middle block of k free digits with b^{2k+1} ≤ p³. The block contributes b^{M−k}·m(v) with m(v) distinct integers below b^{2k+1}, so at most one v fits a residue class mod p³ (needs p ≤ x^{1/3}, true in the sieve range). Hence Σ_{p ≥ x^α} A_{p³} ≪ X x^{−α/2}.
- With cubes excluded this way, the sieve only needs square control up to c0 ≈ 0.167 at θ = 0.249 (crude W/XV = +0.041) or c0 ≈ 0.175 at θ = 0.24 (+0.009), instead of 0.19 (`plan/feas_cubes*.log`). With Prop. W reaching any c < 1/4 this is optional. It still raises δ and gives margin.
