# κ-palindromic primes for every κ < 9/20 in every base. A hybrid Heath-Brown–Iwaniec argument

Version 6 (r66, 2026-11-20). Version 4 was accepted by the audits r70 and r71, version 5 applies r70's cosmetic points, and version 6 applies points 1 and 2 of the referee check r73. Self-contained except for the cited results, which the auditor needs. The main one is HBI = D. R. Heath-Brown and H. Iwaniec, On the difference between consecutive primes, Invent. Math. 55 (1979) 49–69. Page numbers below refer to it.

Source markers for every cited statement.
- [P] primary source read in full or at the statement.
- [S] statement known to us only through a secondary source (named).
- [M] standard result quoted from memory, not re-read.
- [O] proved here (sketch level unless said otherwise).

## 0. Status
- Changes from version 1 (r63 audit issues 1–5).
  - Issue 1. Smooth minorant weight (Repair A, §3.2). All Mellin integrals are exact, contour shifts have no horizontal errors, and per character only zeros and points with |t| ≤ T_w ≤ T/q matter. So the conductor-height of everything used is ≤ T, HBI's height.
  - Issue 2. Tools T1–T3 are stated for the full family (χ mod q, |t| ≤ T/q), whose bound q·T/q = T is HBI's T. HBI's F (p. 56) is written with T. T2 is proved for the full family by a coset subdivision (r67 issue 1).
  - Issue 3. Lemma 5.1(e) bookkeeping corrected (no N^{ε″} loss).
  - Issue 4. Hypothesis q²X ≤ x^{1−η−2δ} added to Theorem 3.1 and checked in §2.
  - Issue 5. Truncation term and zeros of imprimitive characters corrected.
- Complete in this file. Statement (Thm 1.1), block reduction and tiling (§2), hybrid setting with the smooth weight (§3), tools with sources (§4), Lemma I5 (§5), hybrid Lemma 1 and Lemma 2 (§6–7), Σ₁ and Σ₄ (§8–9), Lemmas 4–7 with the density substitutions (§10), Σ₃, Σ₂, Σ₅ (§11), numerology (§12), checkpoints (§13).
- Not re-derived. HBI's exponent case analysis in Lemma 2 (pp. 56–57), the proofs of Lemmas 6, 7, and the polygon conditions (11)–(15) of §6 are used verbatim (justification in §3.4). The tools marked [S] and [M] are not re-read.

## 1. Statement

Notation. b ≥ 2 is the base, L ≥ 1, 0 < κ < 1, k = ⌊κL/2⌋. An integer n with b^{L−1} ≤ n < b^L is κ-palindromic if its first k digits mirror its last k digits. Equivalently n = t·b^{L−k} + m·b^k + rev_k(t) with t ∈ [b^{k−1}, b^k), 0 ≤ m < b^{L−2k}. Here rev_k reverses the k-digit string of t. Let A_κ(L) be the set of these n, so #A_κ(L) = (b−1)b^{L−k−1}.

Theorem 1.1. Let b ≥ 2 and 0 < κ < 9/20. There are c = c(b, κ) > 0 and L₀(b, κ) such that for L ≥ L₀ the number of primes in A_κ(L) is at least c·#A_κ(L)/L. More precisely, for every top block t whose leading digit is prime to b, the block {n ∈ A_κ(L) | ⌊n/b^{L−k}⌋ = t} contains ≥ c·b^{L−2k}·(b/φ(b))/(L log b) primes. Blocks whose leading digit shares a factor with b contain no primes once n > b, since the last digit of n equals the leading digit of t.

Remarks. For κ < 5/12 the theorem with an asymptotic follows from Thorner–Zaman 2108.10878 Cor. 3.2 [P]. The new range is 5/12 ≤ κ < 9/20, which includes κ ∈ (4/9, 9/20) beyond the second-moment rung 4/9. This is a lower bound, not an asymptotic.

## 2. Reduction to blocks and tiling [O]
- Fix t with leading digit d, (d, b) = 1, and put q = b^k, a = rev_k(t), which is prime to b (last digit d). The block is A_t = {n ∈ [tY, (t+1)Y) | n ≡ a mod q} with Y = b^{L−k}. Its size is X_t = Y/q = b^{L−2k}.
- Put x = b^L. Then x/b ≤ tY < (t+1)Y ≤ x, and X_t = x^{1−κ+O(1/L)}.
- Tiling. First fix Θ₁ ∈ (11/20, min(0.555, 1 − κ)), possible since κ < 9/20. Then fix η, δ > 0 so small that 2η < Θ₁ − 11/20, 12η < Θ₁ − 1/2 and η + 2δ < 1 − κ − Θ₁. Let X′ = ⌊x^{Θ₁}⌋. Then q²X′ = x^{κ+Θ₁+O(1/L)} ≤ x^{1−η−2δ}, which is the size hypothesis of Theorem 3.1. Cut [tY, (t+1)Y) into ⌊X_t/X′⌋ disjoint intervals J of length qX′ (and a remainder). Each piece A_J = {n ∈ J | n ≡ a mod q} has X′ + O(1) elements. Theorem 3.1 below gives ≥ c₁ X′(b/φ(b))/log x primes in each A_J, uniformly in J and a. Summing gives ≥ (c₁/2) X_t (b/φ(b))/log x primes in A_t. There are φ(b)b^{k−1} admissible t, so the total is ≥ (c₁/2)(b/φ(b))X_t φ(b)b^{k−1}/log x = (c₁/2)b^{L−k}/log x ≫ #A_κ(L)/L. This is Theorem 1.1.
- So it suffices to prove Theorem 3.1 for one interval of length qX′ in one class mod q, with X′ = x^{Θ}, Θ ∈ (11/20, 5/9) close to 11/20.

## 3. Hybrid setting

### 3.1 The weighted set
Let x be large, q = b^k, a with (a, b) = 1, Θ ∈ (11/20, 5/9), x′ ∈ [x/b, x], X = x^{Θ}, and fix a small δ ∈ (0, 1/10). Let I = (x′ − qX, x′] and let w be a smooth function with 0 ≤ w ≤ 1, supported in I, equal to 1 on (x′ − qX + δqX, x′ − δqX], with w^{(j)} ≪_j (δqX)^{−j}. Define the weighted sequence a_n = w(n)·1_{n ≡ a mod q}·1_{(n,b)=1}, and for (d, b) = 1 put |𝒜_d| = Σ_{d|n} a_n. Let X_w = q^{−1}∫w(u) du, so (1 − 2δ)X ≤ X_w ≤ X.
- Remainder. For (d, b) = 1, Σ_{n ≡ c mod qd} w(n) = (qd)^{−1}∫w + O(var w) with var w ≤ 2, so |𝒜_d| = X_w/d + r(𝒜, d) with |r(𝒜, d)| ≤ 2. For (d, b) > 1, |𝒜_d| = 0. The sifting density is g(p) = 1/p for p ∤ b and 0 for p | b [O].
- Primes. #{p prime, p ∈ I, p ≡ a mod q} ≥ Σ_p a_p = S(𝒜, x^{1/2}), since every n in the support exceeds x/(2b) > x^{1/2}.

Theorem 3.1. Let 11/20 < Θ < 0.555, and assume q²X ≤ x^{1−η−2δ} with η, δ small and fixed. Then S(𝒜, x^{1/2}) ≥ (C(Θ) − cη − cδ − o(1)) X(b/φ(b))/log x, uniformly in q = b^k with k ≥ k₀(b), in a and in x′. Here C(Θ) is HBI's constant, with C(11/20) = 0.004735 (HBI p. 69), C increasing near 11/20, and C(Θ) > 0 on (11/20, 0.555) [checked by the r63 audit].
Note. k ≥ k₀(b) is needed only to exclude exceptional zeros (T8). In the application q = b^k ≥ x^{κ/2−o(1)}.

### 3.2 Mellin transform of the weight, no truncation [O]
Let ŵ(s) = ∫₀^∞ w(u) u^{s−1} du. For σ = Re s ∈ [−1, 2] and every j ≥ 0, integration by parts gives
|ŵ(s)| ≪_j qX x^{σ−1} (x/(δqX(1+|t|)))^j.
So |ŵ(s)| ≪_A x^{−A} for |t| ≥ T_w := x^{1+ε}/(δqX). With T = x^{1+2η}/X (HBI's height, §3.3) one has q·T_w = x^{1+ε}/(δX) ≤ T for ε < 2η and x large.
For any coefficients c_n (|c_n| ≤ x^{o(1)}) and χ mod q,
Σ_n c_n χ(n) w(n) = (2πi)^{−1}∫_{(σ₀)} C_χ(s) ŵ(s) ds exactly (σ₀ = 1 + 1/log x),
and Σ_n c_n w(n)1_{n≡a (q)} = φ(q)^{−1}Σ_χ χ̄(a)(…) for n prime to b. Moving the line to Re s = 1/2 (for polynomials C_χ) or using the explicit formula (for Λ-sums) produces no horizontal error, since ŵ decays faster than any power beyond T_w. Every integral and zero sum is therefore restricted to |t| ≤ T_w, |γ| ≤ T_w, up to O(x^{−A}) per character, i.e. O(x^{−A}) in total.
Explicit formula for a smooth weight [M]. For χ mod q induced by χ* primitive, Σ_n Λ(n)χ(n)w(n) = 1_{χ principal}ŵ(1) − Σ_ρ ŵ(ρ) + O(x^{−A} + log q·log x). Here ρ runs over the non-trivial zeros of L(s, χ*) and the O-term covers trivial zeros (|ŵ(−m)| ≪ qX x^{−m−1}) and prime powers p | b. The zeros of the Euler factors at p | b on Re s = 0 do not occur (Λ-sums over n prime to b use L(s, χ*) with those primes removed, which only changes O(log q log x)).

### 3.3 Dictionary [O]
HBI work with y = x^{Θ}, T = x^{1+2η}y^{−1} (p. 51), z = T^{16/5}x^{−1}, D = x^{2−2η}T^{−12/5}, 0 < 2η < Θ − 11/20, 11/20 < Θ < 5/9. We take the same Θ, η, T = x^{1+2η}/X, z, D. The hybrid family is F_h = {(χ, t) | χ mod q, |t| ≤ T/q}. Its points have conductor-height ≤ q(1 + T/q) ≤ 2T, and its large-sieve constant is φ(q)·T/q + N ≍ T + N, the role of HBI's T + N. HBI's y corresponds to X_w·(q/φ(q)) = X_w b/φ(b) in main terms and to X_w in r(𝒜, d).

### 3.4 Principle of the transcription [O]
After §3.2, HBI's height T enters only through (i) the range of integration or of zeros, now |t| ≤ T_w ≤ T/q per character with no truncation error, and (ii) the estimates T1–T6 of §4. Each of these holds for the hybrid family F_h with HBI's T. Hence every inequality of HBI between powers of x, T, M, N, L, U, V, W stays true with the same exponents. Extra log x and x^{o(1)} factors are absorbed by HBI's power savings, and the (qτ)^{o(1)(1−σ)} losses of T5 by the slack x^{−η(1−σ)} of §11.

## 4. Tools (hybrid versions) and sources
A set of points (χ_r, t_r) is well spaced if |t_r − t_s| ≥ 1 whenever χ_r = χ_s.
- T1. Hybrid mean value. For well-spaced points (χ_r, t_r) ∈ F_h (|t_r − t_s| ≥ 1 when χ_r = χ_s), Σ_r |Σ_{m∼M} a_m χ_r(m) m^{−it_r}|² ≪ (M + T) log x Σ|a_m|². [M: single-modulus hybrid large sieve, Gallagher. HBI use Montgomery Topics Thm 7.3 with Q = 1 (p. 55) [S: HBI]]
- T2. Halász–Montgomery–Huxley large values. For well-spaced points in F_h with |Σ_{m∼M} a_m χ_r(m) m^{−it_r}| ≥ V′ (|a_m| ≤ 1), R ≪ (M²V′^{−2} + T·M⁴V′^{−6})(log x)^c, for every M ≥ 1. In HBI's normalisation this is |S| ≪ (V^{−2}M + V^{−6}MT)(log x)^c (p. 55). H3′ (U^{−4}L² + U^{−12}L²T) follows by applying it to L_χ².
  Proof [O, standard pattern]. The single-modulus hybrid form is quoted by Chen 2507.08296 eq. (hmhlve) from Huxley 1975 [S], but in a setting with M ≥ (qT′)^{3/4} > q. The short range M < 4q is not covered by that citation, so the argument is given here.
  - Halász–Montgomery inequality. Let S′ be a set of R′ well-spaced points with |A_r| ≥ V′, A_r = Σ_{m∼M} a_m χ_r(m) m^{−it_r}. Duality and Cauchy–Schwarz with the smooth majorant e^{1−m/M} of 1_{m∼M} give R′²V′² ≤ (Σ_r |A_r|)² ≤ e‖a‖² Σ_{r,s} |K_{rs}| with K_{rs} = Σ_m χ_rχ̄_s(m) m^{−i(t_r−t_s)} e^{−m/M}, and ‖a‖² ≤ M.
  - Off-diagonal bound. By Mellin inversion, K_{rs} = (2πi)^{−1}∫_{(1)} L(s + i(t_r−t_s), χ_rχ̄_s)Γ(s)M^s ds. Moving the line to Re s = 0 and using |L(iu, ψ)| ≪ (cond ψ (1+|u|))^{1/2} log (T6, Euler factors at p | b bounded by 2^{ω(b)}) gives |K_{rs}| ≪ (cond(χ_rχ̄_s)(1+|t_r−t_s|))^{1/2} log x. When χ_r = χ_s there is the pole term M Γ(1 − i(t_r−t_s)) ≪ M(1+|t_r−t_s|)^{1/2}e^{−π|t_r−t_s|/2}. Summed over well-spaced s it is ≪ M for each r, so it adds O(R′M) to Σ_{r,s}|K_{rs}|, the same order as the diagonal R′M.
  - Boxes. Fix Y₀ ≥ 1. Choose j₀ with b^{j₀} ≤ Y₀ < b^{j₀+1} if Y₀ < q, else j₀ = k, and T₀ = Y₀/b^{j₀} ≥ 1. A box is a coset of the group H_{j₀} of characters mod q of conductor dividing b^{j₀}, times a t-interval of length T₀. For two points in one box, χ_rχ̄_s ∈ H_{j₀}, so cond(χ_rχ̄_s)(1 + |t_r − t_s|) ≤ b^{j₀}(1 + T₀) ≤ 2b·Y₀, and |K_{rs}| ≪ Y₀^{1/2} log x.
  - Count. F_h is covered by (φ(q)/|H_{j₀}|)·(2T/(qT₀) + 1) ≪ (q/b^{j₀})(T/(qT₀) + 1) ≪ T/Y₀ + q/b^{j₀} ≪ T/Y₀ + 1 boxes, using |H_{j₀}| ≍ b^{j₀}, q/b^{j₀} ≤ b·q/Y₀ ≤ b·T/Y₀ (q ≤ T) when Y₀ < q, and q/b^{j₀} = 1 otherwise.
  - Huxley's choice. In one box, R′²V′² ≪ M(R′M + R′²Y₀^{1/2} log x), i.e. R′(V′² − cMY₀^{1/2}log x) ≪ M². With Y₀ = V′⁴/(4c²M²(log x)²) this gives R′ ≪ M²V′^{−2}. Summing over ≪ T/Y₀ + 1 boxes gives R ≪ M²V′^{−2}(1 + T M²(log x)²V′^{−4}) = M²V′^{−2} + T M⁴V′^{−6}(log x)². If this Y₀ is < 1, then V′⁴ ≪ M²(log x)², and T1 gives R ≪ (M + T)M V′^{−2} ≪ M²V′^{−2} + TM⁴V′^{−6}(log x)².
  - No condition on M relative to q is needed.
- T3. Fourth moments. Σ_{χ mod q}∫_{|t|≤2T/q} |L(1/2+it, χ)|⁴ dt ≪ T log⁴ x, and the same for L′. [M: Montgomery Topics Thm 10.1, single-modulus hybrid. Own sketch: approximate functional equation for L(s,χ)² of length ≍ q(1+|t|) and T1.] HBI's form Σ_r∫|ζ(1/2+iτ)|⁴ dτ/(1+|τ−t_r|) (p. 55–56) follows with Σ_r over well-spaced points of F_h.
- T4. Short smooth character sums (= I5, §5). [O, from P statements] HBI's "van der Corput" bound U ≪ L^{1/2}x^{−δ₁} (p. 56).
- T5. Zero density for the hybrid family. Here N(σ, τ) = Σ_{χ mod q} N(σ, τ, χ).
  - (a) Ingham. N(σ, τ) ≪ (qτ)^{3(1−σ)/(2−σ)} x^{o(1)}, 1/2 ≤ σ ≤ 3/4. [S: Chen eq. (Inghaqt). Montgomery Topics Thm 12.1 with log powers [M]]
  - (b) Huxley. N(σ, τ) ≪ (qτ)^{3(1−σ)/(3σ−1)} x^{o(1)}, 3/4 ≤ σ ≤ 4/5. [S: Chen eq. (zeeshmh)]
  - (c) Jutila. N(σ, τ) ≪ (q²τ²)^{(1+ε)(1−σ)}, 4/5 ≤ σ ≤ 1. [S: Pintz 1804.05552 eq. (2.6) with Jutila's c₁ = c₂ = 2]
- T6. Mean values at zeros. Σ over zeros ρ of L(s, χ*), χ mod q, β ≥ σ, |γ| ≤ τ, of |M(ρ, χ)|² ≪ M^{1−2σ}(M + min(qτ, (qτ)^{1/2}N(σ, τ))) (log x)². By T1 at well-spaced zeros (O(log x) subsets) and the Halász–Montgomery inequality, whose off-diagonal terms use |L(iu, ψ)| ≪ (cond ψ(1+|u|))^{1/2} log on Re s = 0 (Euler factors at p | b bounded by 2^{ω(b)}). [S: HBI cite Montgomery Thms 7.3, 8.2. Single-modulus hybrid form [M]]
- T7. Vaughan's identity (HBI Lemma 3) [P].
- T8. Zero-free region. L(s,χ) ≠ 0 for χ mod q and σ ≥ 1 − c/(log rad(b) + (log q(|t|+2))^{3/4}(log⁺log q(|t|+2))^{3/4}). No exceptional zero for k ≥ k₀(b), since real characters mod b^k have conductor dividing 8 rad(b), so there are finitely many such L-functions. [S: Thorner–Zaman 2108.10878 eq. (iwaniec), quoting Iwaniec, Invent. Math. 23 (1974).] HBI need only width (log T)^{−4/5} (p. 65), which is weaker.
- T9. Brun–Titchmarsh in short intervals of progressions. π(J; q, c) ≤ 2|J|/(φ(q) log(|J|/q)) for an interval J with |J| > q [M: Montgomery–Vaughan]. HBI use π(x/p) − π((x−y)/p) ≪ y/(p log(y/p)) (p. 65).
- Also used. Iwaniec's linear sieve (HBI Lemma 1) [P: statement in HBI], Postnikov–Iwaniec lemma and Banks–Shparlinski Thm 2.1 [P: statements in 1605.07553], Vinogradov–Korobov [M].

## 5. Lemma I5 (T4) [O, sketch from P statements]
Lemma 5.1. Fix b ≥ 2 and c₀ ∈ (0, 1/2). There is δ₁ = δ₁(b, c₀) > 0 with the following property for large x. Let q = b^k ≤ x^{1/2}, χ mod q, t ∈ R with Q_h = cond(χ)(1+|t|) ≤ x^{1/2+3η}, N ∈ [x^{c₀}, x] and N < M ≤ 2N. Then |Σ_{N<n≤M} χ(n) n^{−it}| ≪ N^{1−δ₁}, unless χ is principal and |t| ≤ N^{δ₁}.

Proof.
- (a) Write χ = χ*·1_{(n,b)=1}, χ* primitive mod q* | q. Then Σ_n χ(n) n^{−it} = Σ_{d | rad(b)} μ(d) χ*(d) d^{−it} Σ_{N/d<m≤M/d} χ*(m) m^{−it}. So it suffices to treat χ* on [N/d, M/d], d ≤ b.
- (b) Period case. Let χ* ≠ 1 and Q_h ≤ N^{1−3δ}. Split into complete periods of length q*. Over one period Σ χ*(n) = 0, so the period sum is Σ χ*(n)(n^{−it} − n₀^{−it}), of size ≤ q*·|t|q*/N. With N/q* periods and one partial period, the total is ≤ 2Q_h + q* ≤ 3N^{1−3δ}.
- (c) Principal χ* = 1 with |t| ≥ N^{δ₁}. Kusmin–Landau gives ≪ N/|t| for |t| ≤ πN. For πN < |t| ≤ x, Vinogradov–Korobov gives ≪ N exp(−c(log N)³/(log|t|)²) = N^{1−c/ρ²} with ρ = log|t|/log N ≤ 1/c₀ [M].
- (d) χ* ≠ 1, Q_h > N^{1−3δ}, q* ≤ N^{1/2}. Then 1 + |t| ≥ N^{1/2−3δ}. Writing n = a′ + q*m,
  Σ = Σ_{a′ mod q*} χ*(a′) q*^{−it} Σ_m (m + a′/q*)^{−it},
  where the inner sums run over intervals of length ≍ N/q* ≥ N^{1/2}. If |t| ≤ πN/q*, Kusmin–Landau gives ≪ N/(q*|t|) per inner sum, ≪ N/|t| ≤ N^{1/2+3δ} in total. Otherwise, the shift-uniform Vinogradov–Korobov bound for Σ_m (m+u)^{−it} (u ∈ [0,1)) gives (N/q*)^{1−c/ρ′²} with ρ′ = log|t|/log(N/q*) ≤ 2/c₀ [M: the Vinogradov method applies to f(m) = (t/2π)log(m+u) uniformly in u, as in the proof of the Vinogradov–Korobov region for Dirichlet L-functions].
- (e) q* > N^{1/2}. Factor q* = ∏_p p^{e_p} and let p*^{e*} be the largest prime-power factor, so p*^{e*} ≥ q*^{1/ω(b)} > N^{1/(2ω(b))} ≥ x^{c₀/(2ω(b))}, and e* → ∞ as x → ∞ (p* ≤ b). Let q_R = q*/p*^{e*}, 𝔮_R = rad(q_R), τ = 2 if 4 | q_R, else τ = 1, and D = (τ𝔮_R)^s with s maximal such that D ≤ N^{ε″}. Here ε″ is small, fixed in terms of c₀.
  - On a class n ≡ n₀ mod D with (n₀, q_R) = 1, the Postnikov–Iwaniec lemma [P: BS 1605.07553 Lemma "iwaniec", valid for every primitive character and every modulus] gives χ_R(n₀ + Dy) = χ_R(n₀) e(f(y)). Here f is a polynomial with rational coefficients. Its terms of degree j vanish mod 1 once (τ𝔮_R)^{sj} is divisible by q_R times the denominators of the logarithm series, so the effective degree is ≤ J ≪ max_p e_p/s + 1. Since max_p e_p · log 𝔮_R ≤ (log q_R/log 2) log rad(b), J ≪_b log q_R/log D ≤ 1/(c₀ε″).
  - Since (D, p*) = 1, χ_{p*}(n₀ + Dy) = χ_{p*}(D) χ_{p*}(y + c) for some integer c, so the p*-component remains a character in consecutive y.
  - Cut the range of n into pieces of length H = min(p*^{0.99e*}, N^{1−ε}). On each piece, (n₀ + Dy)^{−it} = e(G₀(y)) + O(N^{−1}), with G₀ the Taylor polynomial of −(t/2π)log(n₀ + Dy) around the centre. Its degree is ≪ log(2+|t|)/(ε log N) ≤ 1/(εc₀).
  - Each piece sum is χ_R(n₀)χ_{p*}(D) Σ_y χ_{p*}(y + c) e(G(y)) with G = f + G₀ real, deg G ≤ C₀(b, c₀), over ≍ H/D consecutive y. Banks–Shparlinski Thm 2.1 [P: statement] applies to the primitive character χ_{p*} mod p*^{e*}. The prime-power modulus satisfies their condition min v_p ≥ 0.7 max v_p trivially, and e* ≥ γ₀. Also p*^{e*} ≥ H/D ≥ p*^{γ₀} and deg G ≤ C₀ ≤ C₀ρ with ρ = log p*^{e*}/log(H/D). Here H/D ≥ N^{1/(3ω(b))} for ε, ε″ small (from p*^{e*} > N^{1/(2ω(b))} and N^{1−ε} ≥ N^{1/(2ω(b))}), and p*^{e*} ≤ q* ≤ x^{1/2+3η} ≤ N^{(1/2+3η)/c₀}, so ρ ∈ [1, 3ω(b)(1/2+3η)/c₀] ⊂ [1, 3ω(b)/c₀]. It gives ≪ (H/D)^{1−ξ₀/ρ²}, with ξ₀ depending on C₀.
  - Summing over the D classes n₀ and over ≪ N/H pieces gives ≪ D·(N/H)·(H/D)^{1−ξ₀/ρ²} = N (H/D)^{−ξ₀/ρ²} ≤ N^{1−ξ₀/(3ω(b)ρ²)}, since H/D ≥ N^{1/(3ω(b))}. No loss in ε″ occurs.
- δ₁ is the minimum of the savings in (b)–(e) with ε″, ε, δ small.
Remarks. BS state their Theorem 2.1 for moduli with min v_p ≥ 0.7 max v_p. Step (e) uses it only for a prime power, which is why composite b with unbalanced conductors (b = 12, or 2^a 5^c with c ≪ a for b = 10) cause no difficulty. Numerical check (r59, logs/i5_*.txt). All characters mod 4096, 10³, 10⁴, 1728, 20736, N ≤ 4096, |t| ≤ q. The max of |S|/N for non-principal χ with Q_h ≥ N falls like the random-coefficient control (0.28 to 0.03). Principal χ with |t| ≤ 2 gives φ(b)/b. This checks uniformity, not the exponent.

## 6. Hybrid Lemma 1 (linear sieve) [P: HBI Lemma 1, p. 51–52]
Lemma 6.1. Let z ≥ 2, D ≥ z², ε > 0, s = log D/log z. Then
- S(𝒜, z) ≤ X_w V_b(z){F(s) + E} + R⁺,
- W⁻(𝒜, z, D) ≥ X_w V_b(z){f(s) − E} − R⁻,
where V_b(z) = ∏_{p<z, p∤b}(1 − 1/p), E = cε + O((log D)^{−1/3}), and W⁻(𝒜, z, D) = S(𝒜, z) − Σ_{(D/p)^{1/3} ≤ q < p < z} S(𝒜_{qp}, q). The R^± are as in HBI (5), with r(𝒜, ·) of §3.1. They are sums over sequences D₁ ≥ ⋯ ≥ D_r of the well-factorable form Σ′ c^±(v, ε) r(𝒜, v p₁⋯p_r), v | P(D^{ε²}), |c| ≤ 1.
Proof. Iwaniec's linear sieve applies to any non-negative sequence with |𝒜_d| = X_w g(d) + r(𝒜, d) [M: Iwaniec's sieve is stated for sequences]. The density g has g(p) = 0 for the finitely many p | b and g(p) = 1/p otherwise, which satisfies the linear-sieve dimension condition. V_b(z) = (b/φ(b))V(z)(1 + o(1)).

## 7. Hybrid Lemma 2 (bilinear remainder) [O transcription of HBI §4, pp. 52–57]
Lemma 7.1. Let 11/20 + 2η < Θ ≤ 5/9, q²X ≤ x^{1−η−2δ}, 0 ≤ φ ≤ (6Θ−1)/5 − 3η, 1 ≤ M, N < x^{φ}, |a_m|, |b_n| ≤ 1 supported on integers prime to b. Then
R(𝒜; M, N) := Σ_{M<m≤2M, N<n≤2N} a_m b_n r(𝒜, mn) ≪ X x^{−δ′}, δ′ = δ′(η, b) > 0,
uniformly in q, a, x′.
Proof.
- Step 0 (trivial case, HBI p. 53). If MN < X x^{−η}, then |r(𝒜, mn)| ≤ 2 gives R ≤ 2·4MN ≪ X x^{−η}. So assume MN ≥ X x^{−η}, hence L = x′/(2MN) ≤ x^{1+η}/X and T₀ = L^{1/2} ≤ x^{(1−Θ+η)/2}.
- Step 1 (HBI p. 53). Put L = x′/(2MN) and L_χ(s) = Σ_{L/4<l≤3L, (l,b)=1} χ(l) l^{−s}, M_χ, N_χ similarly. Then Σ a_m b_n |𝒜_{mn}| = Σ_{l,m,n} a_m b_n w(lmn)1_{lmn≡a}, since lmn in the support of w ⊂ (x′ − qX, x′] with M < m ≤ 2M, N < n ≤ 2N forces (x′ − qX)/(4MN) < l ≤ x′/(MN), i.e. L/2·(1 − o(1)) < l ≤ 2L, which lies in (L/4, 3L] and is separated from both ends by a constant factor (qX = o(x′)). This separation is what gives the O(X/T₀) truncation error below. By §3.2 this equals φ(q)^{−1}Σ_χ χ̄(a)(2πi)^{−1}∫_{(c)} L_χM_χN_χ(s)ŵ(s) ds. The part with |t| > T_w is O(x^{−A}).
  - Main term. For χ principal and |t| ≤ T₀ = L^{1/2} (HBI p. 54, "on choosing T₀ = L^{1/2}", L ≥ x^{1/15}), use L_{χ₀}(c+it) = (φ(b)/b)((3L)^{1−s} − (L/4)^{1−s})/(1−s) + O(L^{−c}) (HBI p. 53, Titchmarsh 4.11, Euler factor at p | b). The O(L^{−c}) part gives ≪ φ(q)^{−1}T₀ L^{−c}(MN)^{1−c}|ŵ(c)| ≪ X T₀ L^{−1} = X L^{−1/2}. Termwise integration of the main part gives φ(q)^{−1}(φ(b)/b)∫w·Σ a_m b_n/(mn) + O(X T₀^{−1}) = X_w Σ a_m b_n/(mn) + O(X L^{−1/2}). This cancels the X_w/(mn) part of r(𝒜, mn). The size hypothesis q²X ≤ x^{1−η−2δ} gives T₀ ≤ x^{(1−Θ+η)/2} ≤ T/q, so the main-term region lies inside F_h (as needed for HBI's E₁, E₂ bookkeeping, r63 issue 4).
- Step 2 (HBI p. 54). The remaining points (χ, t) ∈ F_h, |t| ≤ T_w, χ non-principal or |t| ≥ T₀, are discretised into O(log x) well-spaced sets as in HBI. Points where |L|, |M| or |N| ≤ x^{−2} contribute ≪ X x^{−η}. The rest go into (4 log x)³ sets S(U, V, W) defined by U ≤ L^{c−1/2}|L_χ(c+it_r)| < 2U etc. Since |ŵ(c+it)| ≪ qX x^{c−1}, R ≪ X x^{−η} + (log x)^5 (X q/φ(q)) x^{−1/2} UVW |S(U,V,W)|. It suffices to show HBI's (8), UVW·F ≪ x^{1/2−2δ₀}, where F is the minimum of the seven bounds below.
- Step 3, the seven bounds (HBI p. 55–56, with T as in HBI).
  - |S| ≪ V^{−2}(M + T) log x and |S| ≪ W^{−2}(N + T) log x (T1).
  - |S| ≪ (V^{−2}M + V^{−6}MT) x^{o(1)} and the same with W, N (T2).
  - |S| ≪ (U^{−4}L² + U^{−12}L²T) x^{o(1)} (T2 applied to L_χ²).
  - |S| ≪ U^{−4}T(log x)^9 (T3). As in HBI p. 55, for each point (χ_r, t_r) use
    L_χ(c+it_r) = (2πi)^{−1}∫_{|Im z| ≤ H_r} L(c+it_r+z, χ)((3L)^z − (L/4)^z) dz/z + O(L^{1/2−c} log x), z on Re(c + z) = 1/2,
    with truncation height H_r = max(2|t_r|, L^{1/2}) ≥ L^{1/2}, which gives HBI's error L^{1/2−c} log x. There is a pole term only for χ principal, and then |t_r| ≥ T₀. All L-values lie at heights ≤ |t_r| + H_r ≤ 3 max(|t_r|, L^{1/2}). This stays inside height 3T/q, and T3 holds with 3T/q in place of 2T/q (same bound, constant changed). By Step 0, L ≤ x^{1+η}/X, and qL^{1/2} ≤ q(x^{1+η}/X)^{1/2} ≤ x/X = T x^{−2η} is equivalent to q²X ≤ x^{1−η}, which the hypothesis q²X ≤ x^{1−η−2δ} implies. So L^{1/2} ≤ T x^{−2η}/q. Hölder and T3 over the full family then give U⁴|S| ≪ T(log x)^8 + |S|(log x)^4, as in HBI.
  - U ≪ L^{1/2}x^{−δ₁} at every point of S (Lemma 5.1, used in HBI's Case 1 only, p. 56). Non-principal χ with Q_h ≥ x^{η} are covered by Lemma 5.1 with c₀ = 1/15, since L ≥ x^{1−2φ} ≥ x^{(7−12Θ)/5} ≥ x^{1/15} for Θ ≤ 5/9. Non-principal χ with Q_h < x^{η} are covered by Lemma 5.1(b) and partial summation, U ≪ L^{−1/2}·3Q_h ≤ 3L^{1/2}x^{η−1/15} (η < 1/30). Principal χ with |t| ≥ T₀ = L^{1/2} ≥ x^{1/30} ≥ x^{η} are covered by Lemma 5.1(c).
  - HBI's F (p. 56) is formed with T, not with a dyadic T₁. Their T₁ enters only through the van der Corput condition T₁ ≥ x^{η} of Case 1, which Lemma 5.1 replaces.
- Step 4 (HBI pp. 56–57, Cases 1–4). Purely algebraic in U, V, W, L, M, N, T under LMN ≍ x. Identical to HBI, taken over without change. The x^{o(1)} losses in T2 are absorbed by the power saving 2δ₀. This is checkpoint C1.

## 8. Σ₁ [HBI p. 57–59]
Decomposition (HBI (4)). The weighted prime count is S(𝒜, x^{1/2}) (§3.1). Below, A stands for the weighted sequence 𝒜, every count is weighted by w, and X stands for X_w in main terms (X_w = (1 − O(δ))X). Buchstab's identity holds for weighted sequences and gives
S(𝒜, x^{1/2}) = Σ₁ + Σ₂ − Σ₃ − Σ₄ + Σ₅,
- Σ₁ = W⁻(A, z, D),
- Σ₂ = Σ_{(D/p)^{1/3} ≤ q < p < z} S(A_{qp}, q),
- Σ₃ = Σ_{z ≤ p < D^{1/2}} S(A_p, p),
- Σ₄ = Σ_{D^{1/2} ≤ p < x^{1/2}} S(A_p, (D/p)^{1/3}),
- Σ₅ = Σ_{D^{1/2} ≤ p < x^{1/2}, (D/p)^{1/3} ≤ q < p} S(A_{qp}, q).
p, q are primes, automatically > z > b, so (pq, b) = 1. Here 2 < z < D^{1/2} < x^{1/2}, D < z⁴, and x^{1/3} < z.

Lower bound for Σ₁. Lemma 6.1 with M = N = D^{1/2}. As in HBI p. 57–58, R⁻ = Σ_{(D)}Σ r(A, jn) c_j b_n with M^{1+ε⁷}D^{ε}, N^{1+ε⁷} < x^{φ} and φ = (6Θ−1)/5 + 2ε − 16η/5 ≤ (6Θ−1)/5 − 3η for ε < η/10. Lemma 7.1 gives R⁻ ≪ X x^{−δ′+2ε} ≪ X(log x)^{−2}. With V(z) = e^{−γ}(log z)^{−1}(1 + O((log z)^{−2})), (log z)^{−1} ≥ (5/(11−16Θ) − cη)(log x)^{−1}, and f(s) = 2e^{γ}s^{−1}log(s−1) for 2 ≤ s ≤ 4,
Σ₁ ≥ (X b/φ(b)/log x)(C₁ − cη + O((log x)^{−1/3})), C₁ = (5/(6Θ−1)) log((28Θ−13)/(11−16Θ)).

## 9. Σ₄ [HBI p. 59–62]
- Smooth partition [O]. Let P run over D^{1/2}2^j (j ≥ 0), and let ψ_P be smooth, 0 ≤ ψ_P ≤ 1, ψ_P^{(i)} ≪_i P^{−i}, with Σ_P ψ_P(u) = 1 on [D^{1/2}, x^{1/2}], supp ψ_P ⊂ [P/2, 2P] for j ≥ 1 and supp ψ_{D^{1/2}} ⊂ [D^{1/2}/2, 2D^{1/2}]. Then Vaughan's parameter u = PD^{−1/2} ≥ 1 (HBI Lemma 3 needs u ≥ 1). The extra range [D^{1/2}/2, D^{1/2}) of the first bump only adds non-negative terms and changes the final Λ-sum (and C₄) by O(1/log x), so that sum is taken over D^{1/2}/2 ≤ n < 2x^{1/2}. Since S(A_p, Z) is non-increasing in Z and (D/p)^{1/3} ≥ (D/4P)^{1/3} on supp ψ_P,
  Σ₄ ≤ Σ_P Σ_p ψ_P(p) S(A_p, (D/4P)^{1/3}) ≤ Σ_P (log(P/2))^{−1} Σ_n Λ(n)ψ_P(n) S(A_n, (D/4P)^{1/3}).
  Overcounting at the two ends and the prime powers only add non-negative terms, which is allowed since Σ₄ is subtracted and needs only an upper bound (HBI p. 59). This replaces HBI's sharp split P ≤ p < 2P and their sifting limit (D/2P)^{1/3}.
- Lemma 6.1 (upper bound) with s = log(D/4P)/log((D/4P)^{1/3}) = 3, F(3)V_b = (b/φ(b))2e^{γ}/(3·e^{γ}log((D/4P)^{1/3})), gives
  S(A_n, (D/4P)^{1/3}) ≤ (2X_w/(n log(D/n)))(b/φ(b))(1 + cε + O((log x)^{−1/3})) + R_n⁺,
  with R_n⁺ = Σ_{(D)}Σ′ c⁺ H_{(D)}(vn), H_{(D)}(vn) = Σ′ r(𝒜, vnp₁⋯p_r) (log(D/4P) = log(D/n) + O(1) on the support).
- Σ_n Λ(n)ψ_P(n) H_{(D)}(vn) is split by Vaughan's identity (T7) with u = PD^{−1/2} into S₁, S₂ (HBI p. 60) and S₃. The weight ψ_P(km) is carried along.
- S₁, S₂ (heights) [O]. HBI write the inner polynomial B(s) = Σ_{P≤km<2P} c_k(log m)^{2−i}(km)^{−s} as a sharp Perron integral in z over |Im z| ≤ P (p. 60). In the hybrid family that would evaluate L(s + z, χ) at heights up to T/q + P, i.e. conductor-height up to qP > T, and the fourth moment would cost T + qP. With the smooth weight instead,
  B_χ(s) = Σ_{k≤u², m} c_k χ(km)(log m)^{2−i}ψ_P(km)(km)^{−s} = (2πi)^{−1}∫_{Re z = 0} A_χ(s+z) Z_χ(s+z) ψ̂_P(z) dz + (pole term),
  with Z_χ = L(·, χ) or −L′(·, χ), A_χ(w) = Σ_{k≤u²} c_k χ(k)k^{−w}, and ψ̂_P(z) = ∫ψ_P(v)v^{z−1}dv. The identity holds first on Re z = 1 and is moved to Re z = 0. The X_w/d part of r(𝒜, ·) is cancelled by the outer pole of L(s, χ₀) at s = 1, crossed when the outer line is moved from Re s = c to Re s = 1/2 while B_χ(s) is still a Dirichlet polynomial, exactly as the pole of ζ(s) at s = 1 in HBI (p. 60). The inner pole of Z_{χ₀} at s + z = 1 (s on Re s = 1/2) has a residue involving A_{χ₀}(1), A′_{χ₀}(1), ψ̂_P(1−s), ψ̂_P′(1−s), which are ≪ P^{1/2+ε}(1+|t|)^{−2}. With |C(1/2+it)| ≪ (D/P)^{1/2}, |ŵ| ≪ qXx^{−1/2} and the factor φ(q)^{−1}, it contributes ≪ X(D/x)^{1/2}x^{ε} ≪ X x^{−1/25} (D ≈ x^{0.92}).
  - Since ψ_P is smooth on scale P, |ψ̂_P(iy)| ≪_j (1+|y|)^{−j}, uniformly in P. The z-integral is restricted to |Im z| ≤ x^{ε} up to O(x^{−A}), with ∫|ψ̂_P(iy)|dy ≪ 1.
  - The outer integral over s runs over Re s = 1/2, |t| ≤ T_w ≤ T/q (§3.2, exact shift, no horizontal segments). All L-values are therefore at heights ≤ T/q + x^{ε}.
  - Hölder as in HBI p. 61 now gives the fourth-moment factor (Σ_χ∫_{|t|≤T/q}|Z_χ(1/2+it+iy)|⁴dt)^{1/4} ≪ (T + qx^{ε})^{1/4}(log x) ≪ T^{1/4}x^{ε}, uniformly in |y| ≤ x^{ε} (T3, q ≤ T/q). HBI have (T + P)^{1/4} ≥ T^{1/4} here, so the hybrid bound is at least as good. The same holds for A_χ(1/2+it+iy)C_χ(1/2+it) with T1 (heights ≤ T/q + x^{ε}).
  - Result. S_j ≪ X x^{η−1/2+2ε} T^{1/2}(T + u²(D/P)^{1+ε})^{1/2} ≪ X x^{−η}, under HBI's condition 12η < Θ − 1/2 (their bound with (T+P)^{1/4} replaced by T^{1/4}). HBI's second term from the inner truncation error O(x^{η}) does not occur, since ψ̂_P gives no truncation error.
- S₃ is HBI's S₃ (S₄ after splitting k, m into dyadic ranges). The weight ψ_P(km) is separated by ψ_P(km) = (2πi)^{−1}∫_{Re z=0}ψ̂_P(z)(km)^{−z}dz over |Im z| ≤ x^{ε}, which twists the coefficients by unimodular factors k^{−z}, m^{−z}. Lemma 7.1 is uniform in the coefficients, and ∫|ψ̂_P| ≪ 1 (HBI use a sharp Perron in u for the same purpose, p. 61). It is a sum of Lemma 7.1 terms with 2KG^{1+ε}v, 2MH^{1+ε} < x^{φ}, φ = (6Θ−1)/5 + 2ε − 17η/5. So S₃ ≪ X x^{−δ′+4ε}.
- Summing, Σ_n Λ(n)ψ_P(n)R_n⁺ ≪ X x^{−η/2+5ε} + X x^{−δ′+5ε} ≪ X(log x)^{−2}. With 2Σ_{D^{1/2}/2≤n<2x^{1/2}} Λ(n)/(n log n log(D/n)) ≤ (C₄ + cη)(log x)^{−1},
Σ₄ ≤ (X b/φ(b)/log x)(C₄ + cη + O((log x)^{−1/3})), C₄ = (5/(6Θ−1)) log(5/(3(8Θ−3))).

## 10. Lemmas 4–7 (weighted zero density) [HBI §5, p. 62–64, transcribed]
Here zeros are the non-trivial zeros of L(s, χ*), χ* the primitive character inducing χ mod q, ρ = β + iγ with |γ| ≤ τ := T/q. The conductor-height bound is qτ = T, and HBI's range X_5^{4/9} ≤ T ≤ X_5^{1/2} holds (X_5 = x^{1−η}, T = x^{1−Θ+2η}). HBI write X for X_5 and τ for T. M(s) = M_χ(s) = Σ_{M<m≤2M} a_m χ(m) m^{−s}, N_χ similarly, |a_m|, |b_n| ≤ 1. The sums Σ_{β≥σ} below run over (χ, ρ).
- Lemma 10.1 (HBI Lemma 4). Under HBI's range for M (with τ → qτ), Σ_{β≥σ} |M(ρ)| ≪ X_5^{1−σ}(log X_5)^c uniformly in 0 ≤ σ ≤ 1.
- Lemma 10.2 (HBI Lemma 5). Under HBI's ranges for MN and M/N, Σ_{β≥σ} |M(ρ)N(ρ)| ≪ X_5^{1−σ}(log X_5)^c.
- Lemmas 10.3, 10.4 (HBI Lemmas 6, 7). The same under HBI's ranges.
Proof (HBI p. 63–64, with substitutions).
- Hölder as in HBI. Σ|M| ≤ N(σ)^{1/2}(Σ|M|²)^{1/2}, Σ|MN| ≤ N(σ)^{1/4}(Σ|M|²)^{1/2}(Σ|N|⁴)^{1/4}, Σ|MN| ≤ (Σ|M|²)^{1/2}(Σ|N|²)^{1/2}, Σ|MN| ≤ N(σ)^{1/3}(Σ|M|²)^{1/2}(Σ|N|⁶)^{1/6}.
- T6 for each mean value, with N(σ) = N(σ, τ) from T5. As in HBI, it suffices that F^{1/(1−σ)} ≤ X_5, where F = (qτ)^{a(1−σ)v(σ)}(MN)^{1−σ}E^{k}B^{−1} with E = min(qτ, (qτ)^{1/2+(1−σ)v(σ)}). The parameters (a, k, B) are those of HBI for each lemma.
- Density exponents (checkpoint C3).
  - On [1/2, 3/4] and [3/4, 4/5] use T5(a), T5(b) with v(σ) = 3/(2−σ), 3/(3σ−1). Their x^{o(1)} losses equal (qτ)^{o(1)(1−σ)} there, since 1 − σ ≥ 1/5.
  - On [4/5, 1] use T5(c), v′ = 2 + 2ε. HBI's maximising points stay at σ = 3/4 or 7/9 (p. 64). On [7/9, 1] the expression log F/((1−σ)log qτ) = (a+k)v + l + (k/2 − b′)/(1−σ) (MN = (qτ)^l, B = (qτ)^{b′}) has a, k ≥ 0 and k/2 − b′ ≤ 0, the condition HBI need for uniformity up to σ = 1. It is therefore non-increasing when v is replaced by any v′ ≤ v(7/9) = 9/4 that keeps (1−σ)v′ ≤ 1/2. Both hold for 2 + 2ε on [4/5, 1].
  - Below σ = 1/2 use N(σ) ≤ N(1/2).
- The losses (qτ)^{O(ε)(1−σ)} are absorbed in §11 by the slack (X_5/x)^{1−σ} = x^{−η(1−σ)}. Lemma 10.1–10.4 therefore hold with X_5^{1−σ} replaced by (X_5 x^{ε′})^{1−σ}, ε′ < η/2, which is what §11 uses.
Status. The case analysis for Lemmas 6, 7 (HBI "the other cases being similar") is not re-derived here, as in HBI.

## 11. Σ₃, Σ₂, Σ₅ [HBI §6, p. 64–68]
Zero heights. By §3.2 every zero sum below runs over |γ| ≤ T_w ≤ T/q = τ, up to O(x^{−A}). Lemmas 10.1–10.4 are applied with τ = T/q, i.e. conductor-height T, exactly HBI's τ = T.
- Σ₃. For z ≤ p < D^{1/2}, S(𝒜_p, p) = Σ_{m prime, m ≡ a p̄ (q)} w(pm), since the cofactor m ≤ x/z < z² < p² has no prime factor below p. Prime powers and the replacement of 1_prime(m) by Λ(m)/log(x′/p) cost O(X/(log x)²) (log m varies by O(qX/x) on the support). For z x^{η} ≤ P < D^{1/2}, by the explicit formula of §3.2 applied to w_p(u) = w(pu),
  Σ_{P<p≤2P} Σ_m Λ(m)1_{m≡ap̄}w(pm) = φ(q)^{−1}Σ_χ χ̄(a)[1_{χ principal}ŵ(1)Σ_p χ(p)/p − Σ_{|γ|≤T_w} P_χ(ρ)ŵ(ρ)] + O(P log x + X x^{−A}),
  with P_χ(s) = Σ_{P<p≤2P} χ(p)p^{−s} and |ŵ(ρ)| ≪ qX x^{β−1}. The explicit formula has an O(log b + log x) error per prime p (prime powers of p | b, trivial zeros), summed over P < p ≤ 2P. This is ≪ X(log x)^{−2}, since P < D^{1/2} ≤ x^{0.46} < X x^{−δ}.
  - Split β into [log x] slices l/L₀ ≤ β < (l+1)/L₀. Lemma 10.1 with M = P gives ≪ (q/φ(q))X Σ_l x^{(l+1)/L₀−1}(X_5x^{ε′})^{1−l/L₀}(log x)^c.
  - Slices with l/L₀ ≥ 1 − (log T)^{−4/5} are empty by T8. Since x^{β−1}(X_5x^{ε′})^{1−β} = x^{−(η−ε′)(1−β)}, the rest give ≪ X exp(−(η−ε′)(log x)(log T)^{−4/5})(log x)^{c+1} ≪ X(log x)^{−2}.
  - For P < z x^{η}, use T9 for the weighted count (w ≤ 1). With Σ_{z≤p<D^{1/2}}(p log(x/p))^{−1} = C₃/log x + O(η) this gives
  |Σ₃ − C₃ X_w(b/φ(b))/log x| ≤ c(η + δ) X/log x, C₃ = log((6Θ−1)(8Θ−3)/(3(1−Θ)(11−16Θ))).
- Σ₂. As in HBI p. 66–67, Σ₂ counts (with weight w) pqr ∈ 𝒜 with r ≥ q prime. The weighted sums Σ_{Q<q≤2Q, R<r≤2R} Σ Λ(·)w(qr·) and the (p, r) analogue are evaluated by the same explicit formula with P_χ replaced by the products of the q- and r-polynomials, and Lemmas 10.2, 10.3 with X_5 = x^{1−η} and τ = T/q. This is under HBI's conditions (11)–(15) on P, Q, R, which are unchanged (functions of x and T only). The polygon integrals give
  Σ₂ ≥ (X_w b/φ(b)/log x)(C₂₁ + C₂₂ − cη), C₂ᵢ = ∬_{M₂ᵢ} dα dβ/(αβ(1−α−β)),
  with M₂₁, M₂₂ HBI's polygons (functions of Θ only).
  - Explicit-formula error in Σ₂ (and Σ₅) after averaging over χ. For one pair (q, r) the character sum carries the twist χ(qr), and the imprimitive correction is Σ_{p|b, j≥1} log p·w(qrp^j)·φ(q)^{−1}Σ_χ χ̄(a)χ(qr)χ*(p^j). By orthogonality this equals (φ(q′)/φ(q))1_{qrp^j ≡ a (q′)} log p·w(qrp^j), q′ the p-free part of q. Counting pairs with qrp^j in the support and in that class mod q′ gives ≪ ω(b)(q/φ(q))X(QR/x) log x ≪ X x^{−η} (QR ≤ x^{1−η}). The trivial-zero and left-line terms are ≪ qX/x per pair after orthogonality (the average over even χ restricts qr to ±a mod q). Summed over pairs they give ≪ (q/φ(q))X·QR/x ≪ X x^{−η}.
- Σ₅. As in HBI p. 68, Lemmas 10.2 and 10.4 with M = P, N = Q give Σ₅ ≥ (X_w b/φ(b)/log x)(C₅₁ + C₅₂ − cη) with HBI's polygons M₅₁, M₅₂.
- Weights. In Σ₂, Σ₅ only lower bounds are needed, and w ≥ 0, so restricting to the asymptotic subranges is legitimate as in HBI. Σ₃ (subtracted) is an asymptotic with error c(η + δ). Σ₄ (subtracted) is an upper bound from §9.

## 12. Numerology [P: HBI p. 69, checked in r58 and by the r63 audit]
- Collecting §8, §9, §11, S(𝒜, x^{1/2}) ≥ (X_w b/φ(b)/log x)(C(Θ) − cη − cδ − A_{ε,η}(log x)^{−1/3}) with C(Θ) = C₁ + C₂₁ + C₂₂ − C₃ − C₄ + C₅₁ + C₅₂.
- At Θ = 11/20, HBI give C₁ = 0.189155, C₂₁ = 0.175089, C₂₂ = 0.020297, C₃ = 0.080819, C₄ = 0.379029, C₅₁ = 0.062568, C₅₂ = 0.017473, so C(11/20) = 0.004735 > 1/212.
- Value used. We use HBI's printed values, so C(11/20) = 0.004735. The r63 audit recomputed all constants. It agrees to 10⁻⁶ except C₅₁ = 0.062751 (its reading of M₅₁ with β ≤ α, +1.8·10⁻⁴), giving C(11/20) = 0.004918. HBI's value is the smaller one, so it is the conservative choice, and the sign is the same either way.
- Control (r63). C(0.549) = −0.043 and C(0.548) = −0.093, while C(0.552) = +0.096 and C(0.555) = +0.214. So the constant fails below 11/20, as it must (HBI's Case 2 term needs 1/20 + (1−Θ) < 1/2), and C is increasing near 11/20.
- Conclusion. For Θ ∈ (11/20, 0.555), C(Θ) > C(11/20) > 0. With η, δ small and ε = ε(η), Theorem 3.1 follows, with X_w ≥ (1 − 2δ)X.
- In terms of κ, Θ_eff = 1 − κ + o(1). The tiling of §2 needs Θ₁ ∈ (11/20, 0.555) with Θ₁ < 1 − κ − η − 2δ, i.e. κ < 9/20.

## 13. Checkpoints and audit list
- C1. Lemma 7.1 Step 4 (HBI Cases 1–4) is taken over unchanged with HBI's T. To confirm, no step uses a property of T other than T1–T4 and the integration range, which §3.2 handles.
- C2. T2 for the full family F_h, proved in §4 by a coset subdivision for every M ≥ 1 [O]. Chen's quotation of Huxley 1975 [S] covers only M ≥ (qT′)^{3/4}.
- C3. T5 substitutions in Lemmas 10.1–10.4 (§10) [O, confirmed by r63]. Chen's quoted Ingham and Huxley bounds [S] and Jutila via Pintz [S].
- C4. T3 for the full family [M: Montgomery Topics Thm 10.1].
- I5. Lemma 5.1, step (e) corrected (r63 issue 3). Step (d) needs only a k-th derivative test uniform in the shift for bounded ρ′ [M].
- New in version 2 (to audit). §3.2 (Mellin bound for w, exact contour shifts, explicit formula for smooth weights [M]). The weighted remainder |r| ≤ 2 and Iwaniec's sieve for weighted sequences [M]. The size hypothesis q²X ≤ x^{1−η−2δ} in Theorem 3.1 and its check in §2. The main term (1 − O(δ))X.
- Secondary only [S]. Huxley 1975 (T5(b), and T2 only as a cross-check), Ingham single-modulus hybrid (T5(a)), Jutila (T5(c)), Iwaniec 1974 (T8), Montgomery Thms 7.3, 8.2 (T1, T6, through HBI).
- Memory only [M]. Gallagher's hybrid large sieve, the single-modulus hybrid fourth moment, Vinogradov–Korobov and van der Corput (also shifted), Montgomery–Vaughan Brun–Titchmarsh, the explicit formula for smooth weights, Iwaniec's sieve for weighted sequences.
