import Mathlib

/-!
# Lemma R of omega-2/PROOF_K2.md (no resonance between the mirrored block and the free block)

Polynomial form. For `t : ℤ[X]` the base-`b` value is `t.eval b`, and the reversed value
`t*(b) = Σ tᵢ b^{m-1-i}` is `(t.reflect (m-1)).eval b`.
-/

open Polynomial

namespace KappaOmega2

/-- A polynomial with coefficients bounded by `b - 1` in absolute value and value `0` at `b ≥ 2`
is zero (uniqueness of balanced base-`b` digits). -/
theorem eq_zero_of_eval_eq_zero_of_digits (b : ℤ) (hb : 2 ≤ b) :
    ∀ (n : ℕ) (p : ℤ[X]), p.natDegree ≤ n → (∀ i, |p.coeff i| ≤ b - 1) → p.eval b = 0 → p = 0 := by
  intro n
  induction n with
  | zero =>
    intro p hdeg _ hev
    rw [Polynomial.eq_C_of_natDegree_le_zero hdeg] at hev ⊢
    simp at hev
    simp [hev]
  | succ n ih =>
    intro p hdeg hbox hev
    -- p = X * divX p + C (coeff 0)
    have hsplit : p = X * p.divX + C (p.coeff 0) := (Polynomial.X_mul_divX_add p).symm
    have hev2 : b * (p.divX).eval b + p.coeff 0 = 0 := by
      have := congrArg (Polynomial.eval b) hsplit
      simp [Polynomial.eval_add, Polynomial.eval_mul] at this
      linarith [this, hev]
    -- b divides coeff 0, hence coeff 0 = 0
    have hdvd : b ∣ p.coeff 0 := ⟨-(p.divX.eval b), by linarith⟩
    have hc0 : p.coeff 0 = 0 := by
      obtain ⟨c, hc⟩ := hdvd
      have h1 := hbox 0
      rw [hc] at h1 ⊢
      rcases lt_trichotomy c 0 with h | h | h
      · exfalso
        have : |b * c| = b * |c| := by rw [abs_mul, abs_of_pos (by linarith)]
        rw [this] at h1
        have : (1:ℤ) ≤ |c| := by rw [abs_of_neg h]; linarith
        nlinarith
      · simp [h]
      · exfalso
        have : |b * c| = b * |c| := by rw [abs_mul, abs_of_pos (by linarith)]
        rw [this] at h1
        have : (1:ℤ) ≤ |c| := by rw [abs_of_pos h]; linarith
        nlinarith
    have hq : p.divX = 0 := by
      apply ih
      · rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one]; omega
      · intro i; rw [Polynomial.coeff_divX]; exact hbox (i + 1)
      · rw [hc0] at hev2
        have hb0 : b ≠ 0 := by linarith
        have : b * (p.divX).eval b = 0 := by linarith
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h hb0
        · exact h
    rw [hsplit, hq, hc0]; simp


/-- Coefficient bound for the quotient by `X - C b`: if `t' = (X - C b) * q` and every coefficient of `t'`
is at most `b(b-1)` in absolute value, every coefficient of `q` is at most `b - 1`. -/
theorem quot_coeff_bound (b : ℤ) (hb : 2 ≤ b) (t' q : ℤ[X]) (h : t' = (X - C b) * q)
    (hbox : ∀ i, |t'.coeff i| ≤ b * (b - 1)) : ∀ i, |q.coeff i| ≤ b - 1 := by
  have hbpos : 0 < b := by linarith
  -- key step: b * |c| ≤ (b-1)(b+1) forces |c| ≤ b - 1
  have key : ∀ c : ℤ, b * |c| ≤ (b - 1) * (b + 1) → |c| ≤ b - 1 := by
    intro c hc
    by_contra hcon
    push Not at hcon
    have : b ≤ |c| := by linarith
    nlinarith
  intro i
  induction i with
  | zero =>
    have h0 : t'.coeff 0 = -b * q.coeff 0 := by
      rw [h, Polynomial.mul_coeff_zero]; simp
    apply key
    have := hbox 0
    rw [h0, abs_mul, abs_neg, abs_of_pos hbpos] at this
    nlinarith
  | succ n ih =>
    have h1 : t'.coeff (n + 1) = q.coeff n - b * q.coeff (n + 1) := by
      rw [h, Polynomial.coeff_X_sub_C_mul]
    apply key
    have hb1 := hbox (n + 1)
    rw [h1] at hb1
    have : b * |q.coeff (n + 1)| ≤ |q.coeff n| + |q.coeff n - b * q.coeff (n + 1)| := by
      have e : b * q.coeff (n + 1) = q.coeff n - (q.coeff n - b * q.coeff (n + 1)) := by ring
      calc b * |q.coeff (n + 1)| = |b * q.coeff (n + 1)| := by
            rw [abs_mul, abs_of_pos hbpos]
        _ = |q.coeff n - (q.coeff n - b * q.coeff (n + 1))| := by rw [← e]
        _ ≤ |q.coeff n| + |q.coeff n - b * q.coeff (n + 1)| := abs_sub _ _
    nlinarith

/-- The reversed value as a value at `1/b` over `ℚ`. -/
theorem reflect_eval_cast (b : ℤ) (hb : b ≠ 0) (N : ℕ) (p : ℤ[X]) (hp : p.natDegree ≤ N) :
    (((p.reflect N).eval b : ℤ) : ℚ) = (b : ℚ) ^ N * (p.map (Int.castRingHom ℚ)).eval (1 / (b : ℚ)) := by
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  let _ : Invertible (1 / (b : ℚ)) := invertibleOfNonzero (by simpa using hbq)
  have key := eval₂_reflect_mul_pow (Int.castRingHom ℚ) (1 / (b : ℚ)) N p hp
  have hinv : ⅟(1 / (b : ℚ)) = (b : ℚ) := by rw [invOf_eq_inv]; simp
  rw [hinv] at key
  have e1 : eval₂ (Int.castRingHom ℚ) (b : ℚ) (p.reflect N) = (((p.reflect N).eval b : ℤ) : ℚ) := by
    have := Polynomial.eval₂_hom (p := p.reflect N) (Int.castRingHom ℚ) b
    simpa using this
  rw [e1] at key
  rw [Polynomial.eval_map]
  have hpow : ((1 : ℚ) / b) ^ N * (b : ℚ) ^ N = 1 := by
    rw [← mul_pow, one_div_mul_cancel hbq, one_pow]
  rw [← key, mul_comm ((b : ℚ) ^ N), mul_assoc, hpow, mul_one]

/-- Lemma R, polynomial form (b ≥ 3). -/
theorem lemmaR_poly (b k : ℤ) (hb : 3 ≤ b) (m : ℕ) (hm : 1 ≤ m) (t : ℤ[X])
    (hdeg : t.natDegree < m) (hbox : ∀ i, |t.coeff i| ≤ b * (b - 1)) (hk : |k| ≤ b - 1)
    (hval : t.eval b = k * b ^ m) (hrev : |(t.reflect (m - 1)).eval b| ≤ 1) : t = 0 ∧ k = 0 := by
  have hb0 : b ≠ 0 := by linarith
  set t' : ℤ[X] := t - C k * X ^ m with ht'
  have hroot : IsRoot t' b := by
    simp [ht', IsRoot, hval]
  set q : ℤ[X] := t' /ₘ (X - C b) with hq
  have hmul : (X - C b) * q = t' := (mul_divByMonic_eq_iff_isRoot).mpr hroot
  have hdegt' : t'.natDegree ≤ m := by
    apply (natDegree_sub_le _ _).trans
    exact max_le (by omega) (natDegree_C_mul_X_pow_le _ _)
  have hdegq : q.natDegree ≤ m - 1 := by
    rw [hq, natDegree_divByMonic _ (monic_X_sub_C b), natDegree_X_sub_C]; omega
  -- box for t'
  have hbox' : ∀ i, |t'.coeff i| ≤ b * (b - 1) := by
    intro i
    simp only [ht', coeff_sub, coeff_C_mul, coeff_X_pow]
    by_cases hi : i = m
    · subst hi
      have : t.coeff i = 0 := coeff_eq_zero_of_natDegree_lt hdeg
      simp [this]
      nlinarith [abs_nonneg k]
    · simp [hi]; exact hbox i
  have hqb := quot_coeff_bound b (by linarith) t' q hmul.symm hbox'
  -- the identity b T - k = (1 - b^2) Y
  set T : ℤ := (t.reflect (m - 1)).eval b with hT
  set Y : ℤ := (q.reflect (m - 1)).eval b with hY
  have hid : b * T - k = (1 - b ^ 2) * Y := by
    have hTq := reflect_eval_cast b hb0 (m - 1) t (by omega)
    have hYq := reflect_eval_cast b hb0 (m - 1) q hdegq
    have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb0
    have heval : (t'.map (Int.castRingHom ℚ)).eval (1 / (b : ℚ))
        = (1 / (b : ℚ) - b) * (q.map (Int.castRingHom ℚ)).eval (1 / (b : ℚ)) := by
      rw [← hmul]; simp [Polynomial.map_mul]
    have ht'ev : (t'.map (Int.castRingHom ℚ)).eval (1 / (b : ℚ))
        = (t.map (Int.castRingHom ℚ)).eval (1 / (b : ℚ)) - (k : ℚ) * (1 / (b : ℚ)) ^ m := by
      simp [ht', Polynomial.map_sub]
    obtain ⟨n, hn⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    have hmn : m - 1 = n := by omega
    rw [hmn] at hTq hYq
    have hTq' : (T : ℚ) = (b : ℚ) ^ n * (t.map (Int.castRingHom ℚ)).eval (1 / (b : ℚ)) := by
      rw [hT, hmn]; exact hTq
    have hYq' : (Y : ℚ) = (b : ℚ) ^ n * (q.map (Int.castRingHom ℚ)).eval (1 / (b : ℚ)) := by
      rw [hY, hmn]; exact hYq
    have : ((b * T - k : ℤ) : ℚ) = (((1 - b ^ 2) * Y : ℤ) : ℚ) := by
      push_cast
      rw [hTq', hYq']
      have e := heval
      rw [ht'ev] at e
      have e2 : (t.map (Int.castRingHom ℚ)).eval (1 / (b : ℚ))
          = (1 / (b : ℚ) - b) * (q.map (Int.castRingHom ℚ)).eval (1 / (b : ℚ)) + (k : ℚ) * (1 / (b : ℚ)) ^ m := by
        linarith
      rw [e2, hn, pow_succ]
      have hpow : (b : ℚ) ^ n * (1 / (b : ℚ)) ^ n = 1 := by
        rw [← mul_pow, mul_one_div_cancel hbq, one_pow]
      set Q := (q.map (Int.castRingHom ℚ)).eval (1 / (b : ℚ))
      have hb1 : (b : ℚ) * (1 / (b : ℚ)) = 1 := mul_one_div_cancel hbq
      have hpow' : (b : ℚ) ^ n * ((b : ℚ)⁻¹) ^ n = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ hbq, one_pow]
      field_simp
      linear_combination (k : ℚ) * hpow'
    exact_mod_cast this
  -- integer conclusion
  have hY0 : Y = 0 := by
    by_contra hY0
    have h1 : 1 ≤ |Y| := Int.one_le_abs hY0
    have h2 : |(1 - b ^ 2) * Y| = (b ^ 2 - 1) * |Y| := by
      rw [abs_mul]; congr 1; rw [abs_of_neg (by nlinarith)]; ring
    have h3 : |b * T - k| ≤ 2 * b - 1 := by
      have : |b * T| ≤ b := by rw [abs_mul, abs_of_pos (by linarith)]; nlinarith
      calc |b * T - k| ≤ |b * T| + |k| := abs_sub _ _
        _ ≤ 2 * b - 1 := by linarith
    rw [hid, h2] at h3
    have h4 : (b ^ 2 - 1) * 1 ≤ (b ^ 2 - 1) * |Y| :=
      mul_le_mul_of_nonneg_left h1 (by nlinarith)
    nlinarith
  have hkT : k = b * T := by rw [hY0] at hid; linarith
  have hT0 : T = 0 := by
    by_contra hT0
    have h1 : 1 ≤ |T| := Int.one_le_abs hT0
    have : b ≤ |k| := by rw [hkT, abs_mul, abs_of_pos (by linarith)]; nlinarith
    linarith
  have hk0 : k = 0 := by rw [hkT, hT0]; ring
  -- Y = 0 forces q = 0 by balanced digits
  have hrq : q.reflect (m - 1) = 0 := by
    apply eq_zero_of_eval_eq_zero_of_digits b (by linarith) (m - 1)
    · exact natDegree_reflect_le.trans (max_le le_rfl hdegq)
    · intro i; rw [coeff_reflect]; exact hqb _
    · exact hY0
  have hq0 : q = 0 := reflect_eq_zero_iff.mp hrq
  have ht'0 : t' = 0 := by rw [← hmul, hq0, mul_zero]
  refine ⟨?_, hk0⟩
  have : t = t' + C k * X ^ m := by rw [ht']; ring
  rw [this, ht'0, hk0]; simp

/-- The polynomial `Σ_{i<m} tᵢ Xⁱ` attached to a digit-difference vector. -/
noncomputable def polyOf (m : ℕ) (t : ℕ → ℤ) : ℤ[X] := ∑ i ∈ Finset.range m, C (t i) * X ^ i

theorem polyOf_coeff (m : ℕ) (t : ℕ → ℤ) (n : ℕ) :
    (polyOf m t).coeff n = if n < m then t n else 0 := by
  rw [polyOf, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single n]
    · simp
    · intro j _ hj; simp [Ne.symm hj]
    · intro hn; exact absurd (Finset.mem_range.mpr h) hn
  · apply Finset.sum_eq_zero
    intro j hj
    have : n ≠ j := by intro e; subst e; exact h (Finset.mem_range.mp hj)
    simp [this]

theorem polyOf_natDegree (m : ℕ) (hm : 1 ≤ m) (t : ℕ → ℤ) : (polyOf m t).natDegree < m := by
  have : (polyOf m t).natDegree ≤ m - 1 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [polyOf_coeff]; simp; omega
  omega

theorem polyOf_eval (m : ℕ) (t : ℕ → ℤ) (b : ℤ) :
    (polyOf m t).eval b = ∑ i ∈ Finset.range m, t i * b ^ i := by
  simp [polyOf, eval_finsetSum]

theorem polyOf_reflect_eval (m : ℕ) (hm : 1 ≤ m) (t : ℕ → ℤ) (b : ℤ) (hb : b ≠ 0) :
    ((polyOf m t).reflect (m - 1)).eval b = ∑ i ∈ Finset.range m, t i * b ^ (m - 1 - i) := by
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  have h := reflect_eval_cast b hb (m - 1) (polyOf m t) (by have := polyOf_natDegree m hm t; omega)
  apply Int.cast_injective (α := ℚ)
  rw [h]
  simp only [polyOf, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow, map_C, map_X,
    eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, Int.cast_sum, Int.cast_mul, Int.cast_pow,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ m - 1 := by have := Finset.mem_range.mp hi; omega
  have e : (b : ℚ) ^ (m - 1) = (b : ℚ) ^ (m - 1 - i) * (b : ℚ) ^ i := by
    rw [← pow_add]; congr 1; omega
  rw [e]
  have hpow : (b : ℚ) ^ i * (1 / (b : ℚ)) ^ i = 1 := by
    rw [← mul_pow, mul_one_div_cancel hbq, one_pow]
  calc (b : ℚ) ^ (m - 1 - i) * (b : ℚ) ^ i * ((t i : ℚ) * (1 / (b : ℚ)) ^ i)
      = (t i : ℚ) * (b : ℚ) ^ (m - 1 - i) * ((b : ℚ) ^ i * (1 / (b : ℚ)) ^ i) := by ring
    _ = (t i : ℚ) * (b : ℚ) ^ (m - 1 - i) := by rw [hpow, mul_one]

/-- Geometric bound `Σ_{i<m} H bⁱ = H (bᵐ - 1)/(b - 1)`, in the form `(b-1) Σ = H (bᵐ - 1)`. -/
theorem abs_sum_le (m : ℕ) (t : ℕ → ℤ) (b H : ℤ) (hb : 2 ≤ b) (hbox : ∀ i, |t i| ≤ H) :
    (b - 1) * |∑ i ∈ Finset.range m, t i * b ^ i| ≤ H * (b ^ m - 1) := by
  have h1 : |∑ i ∈ Finset.range m, t i * b ^ i| ≤ ∑ i ∈ Finset.range m, H * b ^ i := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [abs_mul, abs_of_pos (by positivity : (0:ℤ) < b ^ i)]
    exact mul_le_mul_of_nonneg_right (hbox i) (by positivity)
  have h2 : (b - 1) * ∑ i ∈ Finset.range m, H * b ^ i = H * (b ^ m - 1) := by
    rw [← Finset.mul_sum, show (b - 1) * (H * ∑ i ∈ Finset.range m, b ^ i)
      = H * ((∑ i ∈ Finset.range m, b ^ i) * (b - 1)) by ring, geom_sum_mul]
  calc (b - 1) * |∑ i ∈ Finset.range m, t i * b ^ i|
      ≤ (b - 1) * ∑ i ∈ Finset.range m, H * b ^ i := mul_le_mul_of_nonneg_left h1 (by linarith)
    _ = H * (b ^ m - 1) := h2

/-- The equation of Lemma R splits into the bottom value `F = Σ tᵢ bⁱ`, the reversed value
`T = Σ tᵢ b^{m-1-i}` and the middle term: `F + b^{L-m} T + s bᵐ = 0`. -/
theorem split_eq (m L : ℕ) (hL : m ≤ L) (t : ℕ → ℤ) (b s : ℤ) :
    (∑ i ∈ Finset.range m, t i * (b ^ (L - 1 - i) + b ^ i)) + s * b ^ m
      = (∑ i ∈ Finset.range m, t i * b ^ i)
        + b ^ (L - m) * (∑ i ∈ Finset.range m, t i * b ^ (m - 1 - i)) + s * b ^ m := by
  have : ∀ i ∈ Finset.range m, t i * (b ^ (L - 1 - i) + b ^ i)
      = t i * b ^ i + b ^ (L - m) * (t i * b ^ (m - 1 - i)) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have e : b ^ (L - 1 - i) = b ^ (L - m) * b ^ (m - 1 - i) := by rw [← pow_add]; congr 1; omega
    rw [e]; ring
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- Lemma R of PROOF_K2 (b ≥ 3, box b(b-1), |s| ≤ W = b^{L-2m}, W ≥ b). -/
theorem lemmaR (b : ℤ) (hb : 3 ≤ b) (m L : ℕ) (hm : 1 ≤ m) (hL : 2 * m + 1 ≤ L)
    (t : ℕ → ℤ) (s : ℤ) (hbox : ∀ i, |t i| ≤ b * (b - 1)) (hs : |s| ≤ b ^ (L - 2 * m))
    (hW : b ≤ b ^ (L - 2 * m))
    (heq : (∑ i ∈ Finset.range m, t i * (b ^ (L - 1 - i) + b ^ i)) + s * b ^ m = 0) :
    (∀ i < m, t i = 0) ∧ s = 0 := by
  have hb0 : b ≠ 0 := by linarith
  have hbpos : 0 < b := by linarith
  set W : ℤ := b ^ (L - 2 * m) with hWdef
  set F := ∑ i ∈ Finset.range m, t i * b ^ i with hF
  set T := ∑ i ∈ Finset.range m, t i * b ^ (m - 1 - i) with hT
  rw [split_eq m L (by omega) t b s] at heq
  have hLm : b ^ (L - m) = W * b ^ m := by rw [hWdef, ← pow_add]; congr 1; omega
  set k : ℤ := -(W * T + s) with hk
  have hFk : F = k * b ^ m := by rw [hLm] at heq; rw [hk]; linarith
  have hbm : 0 < b ^ m := by positivity
  -- |k| ≤ b - 1
  have hkb : |k| ≤ b - 1 := by
    have h := abs_sum_le m t b (b * (b - 1)) (by linarith) hbox
    rw [← hF, hFk, abs_mul, abs_of_pos hbm] at h
    -- (b-1) |k| b^m ≤ b(b-1)(b^m - 1) < (b-1) b b^m
    have h2 : |k| * b ^ m < b * b ^ m := by nlinarith
    have h3 : |k| < b := lt_of_mul_lt_mul_right h2 hbm.le
    linarith
  -- |T| ≤ 1
  have hT1 : |T| ≤ 1 := by
    have hWT : W * T = -k - s := by rw [hk]; ring
    have hWpos : 0 < W := by linarith
    have h1 : W * |T| ≤ |k| + |s| := by
      calc W * |T| = |W * T| := by rw [abs_mul, abs_of_pos hWpos]
        _ = |-k - s| := by rw [hWT]
        _ = |k + s| := by rw [show -k - s = -(k + s) by ring, abs_neg]
        _ ≤ |k| + |s| := abs_add_le _ _
    by_contra hcon
    push Not at hcon
    have : 2 ≤ |T| := by omega
    nlinarith
  -- apply the polynomial form
  have hP := lemmaR_poly b k hb m hm (polyOf m t) (polyOf_natDegree m hm t)
    (by intro i; rw [polyOf_coeff]; split_ifs
        · exact hbox i
        · simp; nlinarith)
    hkb (by rw [polyOf_eval]; exact hFk)
    (by rw [polyOf_reflect_eval m hm t b hb0]; exact hT1)
  obtain ⟨hP0, hk0⟩ := hP
  have ht : ∀ i < m, t i = 0 := by
    intro i hi
    have := congrArg (fun p : ℤ[X] => p.coeff i) hP0
    simp only [polyOf_coeff, coeff_zero, if_pos hi] at this
    exact this
  refine ⟨ht, ?_⟩
  have hT0 : T = 0 := by
    rw [hT]; apply Finset.sum_eq_zero; intro i hi; rw [ht i (Finset.mem_range.mp hi)]; ring
  have : W * T + s = 0 := by have := hk0; rw [hk] at this; linarith
  rw [hT0] at this; linarith

/-- Lemma E of PROOF_K2 (b ≥ 3, fourfold digit differences |tᵢ| ≤ 2b-2, middle differences
|s| ≤ 2W - 2): the only additive coincidences are diagonal. -/
theorem lemmaE (b : ℤ) (hb : 3 ≤ b) (m L : ℕ) (hm : 1 ≤ m) (hL : 2 * m + 1 ≤ L)
    (t : ℕ → ℤ) (s : ℤ) (hbox : ∀ i, |t i| ≤ 2 * b - 2) (hs : |s| ≤ 2 * b ^ (L - 2 * m) - 2)
    (heq : (∑ i ∈ Finset.range m, t i * (b ^ (L - 1 - i) + b ^ i)) + s * b ^ m = 0) :
    (∀ i < m, t i = 0) ∧ s = 0 := by
  have hb0 : b ≠ 0 := by linarith
  set W : ℤ := b ^ (L - 2 * m) with hWdef
  have hWpos : 0 < W := by positivity
  set F := ∑ i ∈ Finset.range m, t i * b ^ i with hF
  set T := ∑ i ∈ Finset.range m, t i * b ^ (m - 1 - i) with hT
  rw [split_eq m L (by omega) t b s] at heq
  have hLm : b ^ (L - m) = W * b ^ m := by rw [hWdef, ← pow_add]; congr 1; omega
  set k : ℤ := -(W * T + s) with hk
  have hFk : F = k * b ^ m := by rw [hLm] at heq; rw [hk]; linarith
  have hbm : 0 < b ^ m := by positivity
  have hk1 : |k| ≤ 1 := by
    have h := abs_sum_le m t b (2 * b - 2) (by linarith) hbox
    rw [← hF, hFk, abs_mul, abs_of_pos hbm] at h
    have h2 : |k| * b ^ m < 2 * b ^ m := by nlinarith
    have h3 : |k| < 2 := lt_of_mul_lt_mul_right h2 hbm.le
    omega
  have hT1 : |T| ≤ 1 := by
    have hWT : W * T = -k - s := by rw [hk]; ring
    have h1 : W * |T| ≤ |k| + |s| := by
      calc W * |T| = |W * T| := by rw [abs_mul, abs_of_pos hWpos]
        _ = |-k - s| := by rw [hWT]
        _ = |k + s| := by rw [show -k - s = -(k + s) by ring, abs_neg]
        _ ≤ |k| + |s| := abs_add_le _ _
    by_contra hcon
    push Not at hcon
    have : 2 ≤ |T| := by omega
    nlinarith
  have hP := lemmaR_poly b k hb m hm (polyOf m t) (polyOf_natDegree m hm t)
    (by intro i; rw [polyOf_coeff]; split_ifs
        · exact (hbox i).trans (by nlinarith)
        · simp; nlinarith)
    (by linarith) (by rw [polyOf_eval]; exact hFk)
    (by rw [polyOf_reflect_eval m hm t b hb0]; exact hT1)
  obtain ⟨hP0, hk0⟩ := hP
  have ht : ∀ i < m, t i = 0 := by
    intro i hi
    have := congrArg (fun p : ℤ[X] => p.coeff i) hP0
    simp only [polyOf_coeff, coeff_zero, if_pos hi] at this
    exact this
  refine ⟨ht, ?_⟩
  have hT0 : T = 0 := by
    rw [hT]; apply Finset.sum_eq_zero; intro i hi; rw [ht i (Finset.mem_range.mp hi)]; ring
  have : W * T + s = 0 := by have := hk0; rw [hk] at this; linarith
  rw [hT0] at this; linarith

end KappaOmega2
