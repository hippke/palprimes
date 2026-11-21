# Audit of Proposition W (PROP_W.md), adversarial referee, 2026-11-20

## Verdict
CORRECT, WITH ONE FIXABLE GAP AT THE INTERFACE. Steps 1 to 6 hold as written, and the exponent δ = θ_b a/4 is right. The gap: Prop. W is proved for one complete length block. TP Lemma 11.1 uses 𝒜 = P*_b(x), which is all odd-length palindromes ≤ x coprime to b³ − b. That set has shorter lengths and a truncated top block. A slack argument of a few lines closes the gap (issue 1). The prime-cube lemma is correct.

TP v3 statements were read on arxiv.org/html/2307.16637v3. Lemma 11.1 has u_r = 1 + 3^{−r}, the hypothesis Σ_{D^{1/4}≤p≤D^{1/u_r}} A_{p²} ≪ X/log³x, and A_d = #{n ∈ P*_b(x) : d | n}. P*_b = {n ∈ P_b : (n, b³−b) = 1}, and P_b^0(x) is the odd-length palindromes ≤ x.

## Checks performed (own derivation, then code)
- Step 1. |S| = X Π ψ^{1/2}. Dropping the unused positions (ψ ≤ 1), and termwise Cauchy–Schwarz, are correct. Including h = 0 and the trivial points only enlarges the sum.
- Step 2. Σ_h |f̂(h/q)|² = q Pr(Z ≡ Z′ mod q) holds exactly. For p ≥ P, Z = Z′ has probability b^{−ℓ} = 1/P by Lemma 3 with single digits. The prime-square count is right: Π p² | w with |w| < 2x gives at most log(2x)/(2 log P) such primes. So Σ ≤ 4P²(π(2P)/P + O(1/ε)) ≪ P².
- Step 3. The factorisation and the Cauchy–Schwarz step are correct.
- Steps 4 and 5. Lemma 3 gives ‖f₃‖² = (g/b)^{aℓ/(1+θ)} b^{−(1−a)ℓ} = P^{−1} and ‖f₁‖² = P^{−1−θa}. The function f̂ is evaluated at c_j α mod 1, and |f̂₁|² = Π_{K1}ψ² Π_{K2}ψ.
  - The K1 ∪ K2 positions are the innermost ℓ positions, so Y/b^m < 2b^{2ℓ+1} ≍ P² (odd length; 2b^{2ℓ} for even length).
  - The twist h ↦ b^m h permutes all of Z/p² (p > b).
  - The local count Σ_p(p²·2/N₁ + 1) ≪ P is right for all h, reduced or not. With multiplicity, the point 0 appears once per prime.
  - The large sieve with local count K(δ) is a standard inequality: Σ ≤ (N + δ^{−1})·O(K(δ))·‖a‖². Split the sorted points into O(K) classes that are each δ-spaced.
  - The result is A₁ ≪ P³‖f₁‖² = P^{2−θa}.
- Step 6. (P² · (P^{2−θa}P²)^{1/2})^{1/2} = P^{2−θa/4}. Dividing by p² gives X P^{−θa/4}.
- Budget. 2 + a/(1+θ) = 1/(2c) exactly, so the block lengths fit into M iff ℓ ≤ 2cM, i.e. P ≤ x^c.
- Code: `audit/audit_w.py` and `audit/audit_w.log`. It uses odd length 2M+1 (TP's Π_b(2M)) and exact laws.
  - Lemma 3 holds for even and odd lengths (exhaustive search, b = 2, 3, 4).
  - ‖f₁‖², ‖f₃‖² and ‖f_V‖² equal the Lemma 3 values exactly.
  - The Fourier side equals the residue side.
  - A₁ ≤ collision bound ≤ local-count LS bound in 5 configurations (b = 2, 3, 5).
  - Small cases cannot test the exponent.

## Issues
1. **FIXABLE (interface with TP Lemma 11.1).** A_{p²} counts n ∈ P*_b(x). This covers all odd lengths 2N′+1 ≤ log_b x + 1 and a top block truncated at x. Prop. W treats one full block only. Fix as follows.
   - Coprimality only removes elements (positivity).
   - The truncated block is a union of at most b·M cylinders plus O(1) ties. In a cylinder the leading k digits are fixed, and with them the trailing k. The free positions form an inner interval, which is what steps 2 to 5 need, since V and K3 may sit anywhere. The fixed part only adds a phase e(n₀h/p²), which the absolute values remove. So the proof runs with X_cyl = b^{#free} and the same size bound |W| < 2x.
   - Take c < c″ < 1/4 and run Prop. W at c″. If a block or cylinder has fewer free digits than the budget ℓ/(2c″), it has at most b·P^{1/(2c″)} ≤ b·X^{c/c″} elements. Summed over O(log x) of them, this is a power saving. All other pieces are covered by Prop. W, and Σ X_cyl ≪ X.
2. **COSMETIC (parameter a).** a = (1+θ)(1/(2c) − 2) exceeds 1 for c < 1/(2(2 + 1/(1+θ))), and then |K2| < 0. State a = min(1, (1+θ)(1/(2c) − 2)).
3. **COSMETIC (wrong number).** "D^{1/u_5} ≈ x^{0.19}" is wrong. Lemma 11.1 at r = 5 needs D ≥ x^{1/Δ_5+ε} with 1/Δ_5 = 0.2109, and D^{1/u_5} = D^{243/244}. Example: D = x^{0.22} gives x^{0.219}, so Prop. W is needed at c ≈ 0.22, where δ ≈ 0.042 (b = 2) and ≈ 0.014 (b = 10). The figure 0.19 may belong to the crude sieve.
4. **COSMETIC (setting).** Use odd length 2M+1 as the main case, because P* has no even lengths: they are divisible by b+1. Lemma 3 as written in PROOF_buniform is for odd length. The even-length analogue holds by the same induction (checked), but it is not needed. Palindromes with leading zeros form a superset, which is fine by positivity.
5. **COSMETIC (simplification of step 5).** No large sieve is needed. A₁ = Σ_p p² Pr(p² | W) with W = (Y − Y′)/b^m and |W| < N₁. Also Pr(W = w) ≤ ‖f₁‖² by Cauchy–Schwarz. So A₁ ≤ Σ_p(p² + 2N₁)‖f₁‖² ≪ P³‖f₁‖²/log P. This is the same bound with a fully elementary proof, which also suits the Lean plan. The "BZ 2008 Lemma 1" citation for the local-count large sieve was not checked; this route makes it unnecessary.
6. **COSMETIC (prime cubes).** The proof is correct. The m(v) are distinct, being single digits without carries, and lie in [0, b^{2k}) ⊂ [0, p³/b). So at most one v falls in each class, not two. The bound needs p ≤ x^{1/3}, which holds in the sieve range. Cylinders handle the truncated block as in issue 1. The claim about square control up to c₀ ≈ 1/6 concerns the crude sieve (`feas_cubes*.log`), which I did not audit.
7. **REMARK.** Every step is a collision count over complete residue systems h mod p². Nothing uses τ(n) ≪ n^ε, Poisson summation or Baier–Zhao, as claimed. With issue 1 fixed, Prop. W supplies the square-divisor hypothesis of TP Lemma 11.1 with a power saving X x^{−αδ}, which replaces TP Prop. 10.1 for this purpose.
