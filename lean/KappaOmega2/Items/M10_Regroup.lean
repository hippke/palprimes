import KappaOmega2.Items.M10_X

/-!
# M10 helper: the regrouping `S_p − E_p = X_p` (`M10_PLAN.md` §4.1 (ii), Greaves p. 94 + Lemma 10)
-/

set_option linter.style.longLine false

open Finset Real
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius

namespace KappaOmega2

open Palprimes Palprimes.Greaves

namespace M10

open Classical

theorem chiProp_iff (y m : ℝ) (d : ℕ) : chiProp y m d ↔ chiMinusProp y d ∧ chiStarProp y m d := by
  constructor
  · intro h
    exact ⟨fun h' hh h1 hev => h h' hh h1 (Or.inl hev), fun h' hh h1 _ hm => h h' hh h1 (Or.inr hm)⟩
  · rintro ⟨h1, h2⟩ h' hh hne hc
    by_cases hev : Even (ω h')
    · exact h1 h' hh hne hev
    · rcases hc with hc | hc
      · exact absurd hc hev
      · exact h2 h' hh hne (Nat.not_even_iff_odd.1 hev) hc

theorem chiMinus_of_dvd {y : ℝ} {d e : ℕ} (he : e ≠ 0) (hde : d ∣ e) (h : chiMinusProp y e) : chiMinusProp y d :=
  fun h' hh h1 hev => h h' (Nat.mem_divisors.2 ⟨(Nat.dvd_of_mem_divisors hh).trans hde, he⟩) h1 hev

theorem minFac_mul_prime_below {h₁ p : ℕ} (hp : p.Prime) (hh₁ : h₁ ≠ 0) (hlt : ∀ q ∈ h₁.primeFactors, p < q) :
    (h₁ * p).minFac = p := by
  have hne : h₁ * p ≠ 1 := by
    intro h; exact hp.one_lt.ne' (Nat.eq_one_of_mul_eq_one_left h)
  apply le_antisymm
  · exact Nat.minFac_le_of_dvd hp.two_le (dvd_mul_left p h₁)
  · have hmp := Nat.minFac_prime hne
    rcases (Nat.Prime.dvd_mul hmp).1 (Nat.minFac_dvd (h₁ * p)) with h | h
    · exact (hlt _ (Nat.mem_primeFactors.2 ⟨hmp, h, hh₁⟩)).le
    · exact (Nat.prime_dvd_prime_iff_eq hmp hp).1 h |>.ge

/-- `χ⁻_y(d p)` from `χ⁻_y(d)` and the conditions `h₁ p³ < y` for odd `h₁ ∣ d` (`p` below the primes of `d`). -/
theorem chiMinus_mul_of {y : ℝ} {d p : ℕ} (hp : p.Prime) (hd : d ≠ 0) (hlt : ∀ q ∈ d.primeFactors, p < q)
    (hχ : chiMinusProp y d) (hodd : ∀ h₁ ∈ d.divisors, Odd (ω h₁) → (h₁ : ℝ) * (p : ℝ) ^ 3 < y) :
    chiMinusProp y (d * p) := by
  intro h hh h1 hev
  have hdp0 : d * p ≠ 0 := mul_ne_zero hd hp.ne_zero
  have hhdp := Nat.dvd_of_mem_divisors hh
  have hpd : ¬ p ∣ d := by
    intro hpd
    exact lt_irrefl p (hlt p (Nat.mem_primeFactors.2 ⟨hp, hpd, hd⟩))
  by_cases hph : p ∣ h
  · obtain ⟨h₁, rfl⟩ := hph
    have hh₁0 : h₁ ≠ 0 := by rintro rfl; simp at hh; tauto
    have hh₁d : h₁ ∣ d := by
      have : p * h₁ ∣ p * d := by rw [mul_comm p d]; exact hhdp
      exact Nat.dvd_of_mul_dvd_mul_left hp.pos this
    have hpcop : Nat.Coprime p h₁ := (Nat.Prime.coprime_iff_not_dvd hp).2 (fun h' => hpd (h'.trans hh₁d))
    have hω : ω (p * h₁) = ω h₁ + 1 := by
      rw [ArithmeticFunction.cardDistinctFactors_mul hpcop, ArithmeticFunction.cardDistinctFactors_apply_prime hp]; ring
    have hodd₁ : Odd (ω h₁) := by
      rw [hω] at hev
      rcases Nat.even_or_odd (ω h₁) with he | ho
      · exact absurd hev (by rw [Nat.even_add_one]; exact not_not.2 he)
      · exact ho
    have hlt₁ : ∀ q ∈ h₁.primeFactors, p < q := fun q hq => hlt q (Nat.primeFactors_mono hh₁d hd hq)
    rw [mul_comm p h₁, minFac_mul_prime_below hp hh₁0 hlt₁]
    have := hodd h₁ (Nat.mem_divisors.2 ⟨hh₁d, hd⟩) hodd₁
    push_cast; nlinarith
  · have hhd : h ∣ d := by
      have hcop : Nat.Coprime h p := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 hph)
      exact hcop.dvd_of_dvd_mul_right hhdp
    exact hχ h (Nat.mem_divisors.2 ⟨hhd, hd⟩) h1 hev

theorem squarefree_of_mem_divisors_primorial {z : ℝ} {n : ℕ} (hn : n ∈ (primorialLt z).divisors) : Squarefree n := by
  have hsq : Squarefree (primorialLt z) := by
    unfold primorialLt; exact SelbergPort.prod_primes_squarefree _ (primes_PB z)
  exact hsq.squarefree_of_dvd (Nat.dvd_of_mem_divisors hn)

theorem dvd_primorial_of {d : ℕ} {z : ℝ} (hsq : Squarefree d) (hlt : ∀ q ∈ d.primeFactors, (q : ℝ) < z) :
    d ∣ primorialLt z := by
  rw [← Nat.prod_primeFactors_of_squarefree hsq]
  unfold primorialLt
  apply prod_dvd_prod_of_subset
  intro q hq
  rw [mem_primesBelow]; exact ⟨Nat.prime_of_mem_primeFactors hq, hlt q hq⟩

theorem coprime_div_of_squarefree {n d : ℕ} (hsq : Squarefree n) (hd : d ∣ n) : Nat.Coprime d (n / d) := by
  apply Nat.coprime_of_dvd
  intro k hk hkd hkt
  have : k * k ∣ n := by
    rw [← Nat.mul_div_cancel' hd]; exact Nat.mul_dvd_mul hkd hkt
  exact hk.one_lt.ne' (Nat.isUnit_iff.1 (hsq k this))

theorem omega_div_add {n d : ℕ} (hn : n ≠ 0) (hsq : Squarefree n) (hd : d ∣ n) : ω d + ω (n / d) = ω n := by
  have hcop := coprime_div_of_squarefree hsq hd
  conv_rhs => rw [← Nat.mul_div_cancel' hd]
  rw [ArithmeticFunction.cardDistinctFactors_mul hcop]

/-- P4: for even `ν(d)` with primes above `p`, `χ⁻_y(d)` gives every `h₁ p³ < y`, `h₁ ∣ d` odd. -/
theorem P4 {y : ℝ} {d p : ℕ} (hp : p.Prime) (hd : d ≠ 0) (hsq : Squarefree d) (hlt : ∀ q ∈ d.primeFactors, p < q)
    (hev : Even (ω d)) (hχ : chiMinusProp y d) :
    ∀ h₁ ∈ d.divisors, Odd (ω h₁) → (h₁ : ℝ) * (p : ℝ) ^ 3 < y := by
  intro h₁ hh₁ hodd
  have hh₁d := Nat.dvd_of_mem_divisors hh₁
  have hh₁0 : h₁ ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hh₁)
  -- a prime of d outside h₁
  have hex : ∃ r ∈ d.primeFactors, ¬ r ∣ h₁ := by
    by_contra hcon
    push_neg at hcon
    have hsub : d.primeFactors ⊆ h₁.primeFactors := fun r hr =>
      Nat.mem_primeFactors.2 ⟨Nat.prime_of_mem_primeFactors hr, hcon r hr, hh₁0⟩
    have hsub' : h₁.primeFactors ⊆ d.primeFactors := Nat.primeFactors_mono hh₁d hd
    have heq : ω h₁ = ω d := by
      rw [ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors,
        ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors, le_antisymm hsub' hsub]
    rw [heq] at hodd
    exact (Nat.not_even_iff_odd.2 hodd) hev
  obtain ⟨r, hrd, hrh⟩ := hex
  have hr := Nat.prime_of_mem_primeFactors hrd
  have hcop : Nat.Coprime h₁ r := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hr).2 hrh)
  have hh'd : h₁ * r ∣ d := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hh₁d (Nat.dvd_of_mem_primeFactors hrd)
  have hω : ω (h₁ * r) = ω h₁ + 1 := by
    rw [ArithmeticFunction.cardDistinctFactors_mul hcop, ArithmeticFunction.cardDistinctFactors_apply_prime hr]
  have hne1 : h₁ * r ≠ 1 := fun h => hr.one_lt.ne' (Nat.eq_one_of_dvd_one ⟨h₁, by rw [mul_comm]; exact h.symm⟩)
  have h1 := hχ (h₁ * r) (Nat.mem_divisors.2 ⟨hh'd, hd⟩) hne1 (by rw [hω]; exact hodd.add_one)
  have hmf : p < (h₁ * r).minFac := by
    apply hlt
    exact Nat.mem_primeFactors.2 ⟨Nat.minFac_prime hne1, (Nat.minFac_dvd _).trans hh'd, hd⟩
  have hpr : p < r := hlt r hrd
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hmf' : (p : ℝ) < ((h₁ * r).minFac : ℝ) := by exact_mod_cast hmf
  have hpr' : (p : ℝ) < r := by exact_mod_cast hpr
  have hh₁' : (0 : ℝ) < h₁ := by exact_mod_cast Nat.pos_of_ne_zero hh₁0
  push_cast at h1
  have : (h₁ : ℝ) * p * p ^ 2 < h₁ * r * ((h₁ * r).minFac : ℝ) ^ 2 := by
    have a1 : (p : ℝ) ^ 2 < ((h₁ * r).minFac : ℝ) ^ 2 := by nlinarith
    have a2 : (h₁ : ℝ) * p < h₁ * r := by nlinarith
    exact mul_lt_mul a2 a1.le (by positivity) (by positivity)
  nlinarith

/-- The set `D'(n)` of the regrouping. -/
noncomputable def Dprime (y : ℝ) (p n : ℕ) : Finset ℕ :=
  n.divisors.filter (fun d : ℕ => d ∈ D1set y p ∧ n / d ∈ S9 (y / (p * d)) p (decide (Even (ω d))) ∧
    Nat.Coprime d (n / d))

/-- Coefficientwise comparison with Lemma 10's `b(n)`. -/
theorem coef_eq {y : ℝ} (hy : 16 ≤ y) {p : ℕ} (hp : p.Prime) (h4 : (p : ℝ) < y ^ ((1 : ℝ) / 4)) {n : ℕ}
    (hn : n ∈ (primorialLt y).divisors) (hnp : ∀ q ∈ n.primeFactors, p < q) (hev : Even (ω n))
    {d : ℕ} (hd : d ∈ n.divisors) :
    (if d ∈ Dprime y p n then (μ d : ℝ) * (if chiStarProp y mm d then 1 else 0) * (if chiMinusProp y (d * p) then 1 else 0) else 0) =
      (if (qmax (n / d) : ℝ) < y / (p * n) then (μ d : ℝ) * chi y mm d else 0) := by
  have hy1 : (1 : ℝ) < y := by linarith
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpy : (p : ℝ) < y := lt_of_lt_of_le h4 (Real.rpow_le_self_of_one_le hy1.le (by norm_num))
  have hn0 : n ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hn)
  have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
  have hd0 : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
  have hsqn := squarefree_of_mem_divisors_primorial hn
  have hsqd : Squarefree d := hsqn.squarefree_of_dvd hdn
  set t := n / d with ht
  have hnt : n = d * t := (Nat.mul_div_cancel' hdn).symm
  have ht0 : t ≠ 0 := by rintro h0; rw [h0, mul_zero] at hnt; exact hn0 hnt
  have hsqt : Squarefree t := hsqn.squarefree_of_dvd (Nat.div_dvd_of_dvd hdn)
  have hcop : Nat.Coprime d t := coprime_div_of_squarefree hsqn hdn
  have hdp : ∀ q ∈ d.primeFactors, p < q := fun q hq => hnp q (Nat.primeFactors_mono hdn hn0 hq)
  have htp : ∀ q ∈ t.primeFactors, p < q := fun q hq => hnp q (Nat.primeFactors_mono (Nat.div_dvd_of_dvd hdn) hn0 hq)
  have hωsum : ω d + ω t = ω n := omega_div_add hn0 hsqn hdn
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.pos_of_ne_zero hd0
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast Nat.pos_of_ne_zero ht0
  have hnR : (n : ℝ) = d * t := by rw [hnt]; push_cast; ring
  set η := y / (p * d) with hη
  have hη0 : 0 < η := div_pos (by linarith) (by positivity)
  have hX : η / t = y / (p * n) := by rw [hη, hnR]; field_simp
  set X := y / (p * n) with hXdef
  have hXη : X ≤ η := by rw [← hX]; exact div_le_self hη0.le ht1
  -- S9 membership of t
  have hS9 : t ∈ S9 η p (decide (Even (ω d))) ↔ ∀ q ∈ t.primeFactors, (q : ℝ) < X := by
    unfold S9
    rw [mem_filter, hX]
    constructor
    · rintro ⟨_, _, h, _⟩; exact h
    · intro h
      refine ⟨Nat.mem_divisors.2 ⟨dvd_primorial_of hsqt (fun q hq => lt_of_lt_of_le (h q hq) hXη),
        (primorialLt_pos' _).ne'⟩, fun q hq => by exact_mod_cast htp q hq, h, ?_⟩
      by_cases he : Even (ω d)
      · simp only [he, decide_true, if_true]
        have := hev; rw [← hωsum] at this; exact (Nat.even_add.1 this).1 he
      · simp only [he, decide_false]
        simp only [Bool.false_eq_true, if_false]
        have := hev; rw [← hωsum] at this
        exact Nat.not_even_iff_odd.1 (fun h' => he ((Nat.even_add.1 this).2 h'))
  by_cases hχ : chiProp y mm d
  · have hchi : chi y mm d = 1 := by unfold chi; rw [if_pos hχ]
    obtain ⟨hχm, hχs⟩ := (chiProp_iff y mm d).1 hχ
    have hD1 : d ∈ D1set y p := by
      unfold D1set
      rw [mem_filter]
      refine ⟨Nat.mem_divisors.2 ⟨dvd_primorial_of hsqd (fun q hq => ?_), (primorialLt_pos' _).ne'⟩, hdp⟩
      have hqp := Nat.prime_of_mem_primeFactors hq
      have h1 := hχ q (Nat.mem_divisors.2 ⟨Nat.dvd_of_mem_primeFactors hq, hd0⟩) hqp.ne_one (Or.inr (by
        rw [ArithmeticFunction.cardDistinctFactors_apply_prime hqp]; norm_num [mm]))
      rw [Nat.Prime.minFac_eq hqp] at h1
      have h2 := lt_cbrt_of_cube_lt (Nat.cast_nonneg q) (by linarith) h1
      exact lt_of_lt_of_le h2 (Real.rpow_le_rpow_of_exponent_le hy1.le (by norm_num [UU]))
    have hmemD : d ∈ Dprime y p n ↔ ∀ q ∈ t.primeFactors, (q : ℝ) < X := by
      unfold Dprime
      rw [mem_filter, ← hS9]
      constructor
      · rintro ⟨_, _, h, _⟩; exact h
      · intro h; exact ⟨hd, hD1, h, hcop⟩
    rw [hchi, if_pos hχs, mul_one]
    by_cases ht1' : t = 1
    · -- t = 1: d = n
      have hdn' : d = n := by rw [hnt, ht1', mul_one]
      have hA : ∀ q ∈ t.primeFactors, (q : ℝ) < X := by rw [ht1']; simp
      rw [if_pos (hmemD.2 hA)]
      have hevd : Even (ω d) := by rw [hdn']; exact hev
      have hχdp : chiMinusProp y (d * p) :=
        chiMinus_mul_of hp hd0 hdp hχm (P4 hp hd0 hsqd hdp hevd hχm)
      rw [if_pos hχdp, mul_one]
      have hq1 : (qmax t : ℝ) < X := by
        rw [ht1']
        have : qmax 1 = 1 := by simp [qmax]
        rw [this, Nat.cast_one, hXdef, lt_div_iff₀ (by positivity), one_mul]
        by_cases hn1 : n = 1
        · rw [hn1, Nat.cast_one, mul_one]; exact hpy
        · have hχn : chiMinusProp y n := by rw [← hdn']; exact hχm
          have h1 := hχn n (Nat.mem_divisors_self n hn0) hn1 hev
          have hmf : p < n.minFac := hnp _ (Nat.mem_primeFactors.2 ⟨Nat.minFac_prime hn1, Nat.minFac_dvd n, hn0⟩)
          have hmf' : (p : ℝ) < n.minFac := by exact_mod_cast hmf
          have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero hn0
          have hmf1 : (1 : ℝ) ≤ n.minFac := by exact_mod_cast (Nat.minFac_prime hn1).one_lt.le
          have : (p : ℝ) ≤ (n.minFac : ℝ) ^ 2 := by nlinarith
          nlinarith
      rw [if_pos hq1]
    · -- t ≠ 1
      have hne : t.primeFactors.Nonempty := by
        rw [Nat.nonempty_primeFactors]; exact Nat.one_lt_iff_ne_zero_and_ne_one.2 ⟨ht0, ht1'⟩
      obtain ⟨s0, hs0, hs0max⟩ := Finset.exists_max_image t.primeFactors id hne
      have hqmax : qmax t = s0 := by
        unfold qmax
        have hsup : t.primeFactors.sup id = s0 := le_antisymm (Finset.sup_le hs0max) (Finset.le_sup (f := id) hs0)
        rw [hsup]
        exact max_eq_left (Nat.prime_of_mem_primeFactors hs0).one_lt.le
      have hAiff : (∀ q ∈ t.primeFactors, (q : ℝ) < X) ↔ (qmax t : ℝ) < X := by
        rw [hqmax]
        constructor
        · intro h; exact h s0 hs0
        · intro h q hq
          exact lt_of_le_of_lt (by exact_mod_cast hs0max q hq) h
      by_cases hA : ∀ q ∈ t.primeFactors, (q : ℝ) < X
      · rw [if_pos (hmemD.2 hA), if_pos (hAiff.1 hA)]
        have hχdp : chiMinusProp y (d * p) := by
          apply chiMinus_mul_of hp hd0 hdp hχm
          intro h₁ hh₁ _
          have hr := hA s0 hs0
          have hrp : p < s0 := htp s0 hs0
          have hrp' : (p : ℝ) < s0 := by exact_mod_cast hrp
          have hrt : (s0 : ℝ) ≤ t := by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero ht0) (Nat.dvd_of_mem_primeFactors hs0)
          have hh₁d : (h₁ : ℝ) ≤ d := by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) (Nat.dvd_of_mem_divisors hh₁)
          rw [hXdef, lt_div_iff₀ (by positivity), hnR] at hr
          have h0 : (0 : ℝ) ≤ h₁ := Nat.cast_nonneg _
          have e1 : (h₁ : ℝ) * p ^ 3 ≤ d * p ^ 3 := mul_le_mul_of_nonneg_right hh₁d (by positivity)
          have e2 : (d : ℝ) * p ^ 3 < d * p * s0 ^ 2 := by
            have : (p : ℝ) ^ 2 < (s0 : ℝ) ^ 2 := by nlinarith
            have hdp0 : (0 : ℝ) < (d : ℝ) * (p : ℝ) := by positivity
            calc (d : ℝ) * (p : ℝ) ^ 3 = ((d : ℝ) * (p : ℝ)) * (p : ℝ) ^ 2 := by ring
              _ < ((d : ℝ) * (p : ℝ)) * (s0 : ℝ) ^ 2 := mul_lt_mul_of_pos_left this hdp0
          have e3 : (d : ℝ) * p * s0 ^ 2 ≤ s0 * (p * (d * t)) := by
            have hs00 : (0 : ℝ) ≤ s0 := Nat.cast_nonneg _
            calc (d : ℝ) * (p : ℝ) * (s0 : ℝ) ^ 2 = ((s0 : ℝ) * ((p : ℝ) * (d : ℝ))) * (s0 : ℝ) := by ring
              _ ≤ ((s0 : ℝ) * ((p : ℝ) * (d : ℝ))) * (t : ℝ) := mul_le_mul_of_nonneg_left hrt (by positivity)
              _ = (s0 : ℝ) * ((p : ℝ) * ((d : ℝ) * (t : ℝ))) := by ring
          linarith
        rw [if_pos hχdp, mul_one]
      · rw [if_neg (fun h => hA (hmemD.1 h)), if_neg (fun h => hA (hAiff.2 h))]
  · have hchi : chi y mm d = 0 := by unfold chi; rw [if_neg hχ]
    rw [hchi, mul_zero]
    by_cases h2 : chiStarProp y mm d
    · by_cases h3 : chiMinusProp y (d * p)
      · exfalso; exact hχ ((chiProp_iff y mm d).2 ⟨chiMinus_of_dvd (mul_ne_zero hd0 hp.ne_zero) (dvd_mul_right d p) h3, h2⟩)
      · simp [h3]
    · simp [h2]

/-- `N'`: divisors of `P(y)` with all primes above `p` and `ν` even. -/
noncomputable def Nprime (y : ℝ) (p : ℕ) : Finset ℕ :=
  (primorialLt y).divisors.filter (fun n : ℕ => (∀ q ∈ n.primeFactors, p < q) ∧ Even (ω n))

/-- Reindexing the coprime pairs `(d₁, t)` by `n = d₁ t`. -/
theorem reindex {y : ℝ} (hy : 1 ≤ y) {p : ℕ} (hp : p.Prime) (F : ℕ → ℕ → ℝ) :
    ∑ d ∈ D1set y p, ∑ t ∈ (S9 (y / (p * d)) p (decide (Even (ω d)))).filter (fun t : ℕ => Nat.Coprime d t), F d t =
      ∑ n ∈ Nprime y p, ∑ d ∈ Dprime y p n, F d (n / d) := by
  have step1 : ∀ d ∈ D1set y p,
      ∑ t ∈ (S9 (y / (p * d)) p (decide (Even (ω d)))).filter (fun t : ℕ => Nat.Coprime d t), F d t =
      ∑ n ∈ ((S9 (y / (p * d)) p (decide (Even (ω d)))).filter (fun t : ℕ => Nat.Coprime d t)).image (d * ·),
        F d (n / d) := by
    intro d hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors (mem_filter.1 hd).1
    rw [sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hd0 h)]
    apply sum_congr rfl; intro t _
    rw [Nat.mul_div_cancel_left t hd0]
  rw [sum_congr rfl step1]
  apply Finset.sum_comm'
  intro d n
  constructor
  · rintro ⟨hd, hn⟩
    obtain ⟨t, ht, rfl⟩ := mem_image.1 hn
    have hdD := mem_filter.1 hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hdD.1
    have htf := mem_filter.1 ht
    have htS := mem_filter.1 htf.1
    have ht0 : 0 < t := Nat.pos_of_mem_divisors htS.1
    have hcop : Nat.Coprime d t := htf.2
    have hdt0 : d * t ≠ 0 := Nat.mul_ne_zero hd0.ne' ht0.ne'
    have hdiv : d * t / d = t := Nat.mul_div_cancel_left t hd0
    refine ⟨?_, ?_⟩
    · unfold Dprime
      rw [mem_filter, hdiv]
      exact ⟨Nat.mem_divisors.2 ⟨dvd_mul_right d t, hdt0⟩, hd, htf.1, hcop⟩
    · unfold Nprime
      rw [mem_filter]
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.pos
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd0
      have hηy : y / (p * d) ≤ y := div_le_self (by linarith) (by nlinarith)
      have hdP : d ∣ primorialLt y :=
        (Nat.dvd_of_mem_divisors hdD.1).trans (primorialLt_dvd (Real.rpow_le_self_of_one_le hy (by norm_num [UU])))
      have htP : t ∣ primorialLt y := (Nat.dvd_of_mem_divisors htS.1).trans (primorialLt_dvd hηy)
      refine ⟨Nat.mem_divisors.2 ⟨Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hdP htP, (primorialLt_pos' y).ne'⟩, ?_, ?_⟩
      · intro q hq
        rw [Nat.primeFactors_mul hd0.ne' ht0.ne', mem_union] at hq
        rcases hq with hq | hq
        · exact hdD.2 q hq
        · have := htS.2.1 q hq; exact_mod_cast this
      · rw [ArithmeticFunction.cardDistinctFactors_mul hcop]
        have hpar := htS.2.2.2
        by_cases he : Even (ω d)
        · simp only [he, decide_true, if_true] at hpar
          exact he.add hpar
        · simp only [he, decide_false, Bool.false_eq_true, if_false] at hpar
          exact (Nat.not_even_iff_odd.1 he).add_odd hpar
  · rintro ⟨hd, hn⟩
    unfold Dprime at hd
    rw [mem_filter] at hd
    obtain ⟨hdn, hdD, htS, hcop⟩ := hd
    refine ⟨hdD, mem_image.2 ⟨n / d, mem_filter.2 ⟨htS, hcop⟩, Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hdn)⟩⟩

theorem G_mul_div (b : ℕ) {n d : ℕ} (hd : d ∣ n) (hd0 : d ≠ 0) :
    rhoB b d / (d : ℝ) * (rhoB b (n / d) / ((n / d : ℕ) : ℝ)) = rhoB b n / (n : ℝ) := by
  have hn : n = d * (n / d) := (Nat.mul_div_cancel' hd).symm
  conv_rhs => rw [hn, rhoB_mul]
  rw [div_mul_div_comm]
  congr 1
  rw [← Nat.cast_mul, ← hn]

theorem Nprime_erase_filter {y : ℝ} {p : ℕ} :
    ((Nprime y p).erase 1).filter (fun n : ℕ => (n : ℝ) * n.minFac < y / p) = Nset y p := by
  ext n
  unfold Nprime Nset
  simp only [mem_filter, mem_erase]
  constructor
  · rintro ⟨⟨hn1, hn, hnp, hev⟩, hlt⟩
    have hn0 : n ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hn)
    exact ⟨hn, hn1, hev, hnp _ (Nat.mem_primeFactors.2 ⟨Nat.minFac_prime hn1, Nat.minFac_dvd n, hn0⟩), hlt⟩
  · rintro ⟨hn, hn1, hev, hpm, hlt⟩
    refine ⟨⟨hn1, hn, fun q hq => lt_of_lt_of_le hpm (Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactors hq).two_le
      (Nat.dvd_of_mem_primeFactors hq)), hev⟩, hlt⟩

end M10

/-- §4.1 (ii): regrouping `n = d₁ t` of the coprime pairs and Lemma 10 (at `p < y^{1/4} < y`). -/
theorem regroup (b : ℕ) (h10 : Lemma10LtStmt) {y : ℝ} (hy : 16 ≤ y) {p : ℕ} (hp : p.Prime)
    (h4 : (p : ℝ) < y ^ ((1 : ℝ) / 4)) : Sp b y p - Ep b y p = Xd b y p := by
  classical
  have hy1 : (1 : ℝ) < y := by linarith
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpy : (p : ℝ) < y := lt_of_lt_of_le h4 (Real.rpow_le_self_of_one_le hy1.le (by norm_num))
  set A : ℕ → ℝ := fun d => (μ d : ℝ) * rhoB b d / d * (if chiStarProp y mm d then 1 else 0) *
    (if chiMinusProp y (d * p) then 1 else 0) with hA
  set c : ℕ → ℝ := fun d => (μ d : ℝ) * (if chiStarProp y mm d then 1 else 0) *
    (if chiMinusProp y (d * p) then 1 else 0) with hc
  -- Claim C
  have hC : ∑ d ∈ D1set y p, A d * ∑ t ∈ (S9 (y / (p * d)) p (decide (Even (ω d)))).filter (fun t : ℕ => Nat.Coprime d t),
      rhoB b t / t * sigmaP b (y / (p * d) / t) =
      sigmaP b (y / p) - ∑ n ∈ Nset y p, chibar y mm n * rhoB b n / n * sigmaP b (y / (p * n)) := by
    have e1 : ∑ d ∈ D1set y p, A d * ∑ t ∈ (S9 (y / (p * d)) p (decide (Even (ω d)))).filter (fun t : ℕ => Nat.Coprime d t),
        rhoB b t / t * sigmaP b (y / (p * d) / t) =
        ∑ d ∈ D1set y p, ∑ t ∈ (S9 (y / (p * d)) p (decide (Even (ω d)))).filter (fun t : ℕ => Nat.Coprime d t),
        A d * (rhoB b t / t * sigmaP b (y / (p * d) / t)) := by
      apply sum_congr rfl; intro d _; rw [mul_sum]
    rw [e1, M10.reindex hy1.le hp (fun d t => A d * (rhoB b t / t * sigmaP b (y / (p * d) / t)))]
    -- per n
    have e2 : ∀ n ∈ M10.Nprime y p, ∑ d ∈ M10.Dprime y p n, A d * (rhoB b (n / d) / ((n / d : ℕ) : ℝ) *
        sigmaP b (y / (p * d) / ((n / d : ℕ) : ℝ))) =
        rhoB b n / n * sigmaP b (y / (p * n)) * (if n = 1 then 1 else if (n : ℝ) * n.minFac < y / p then -chibar y mm n else 0) := by
      intro n hn
      have hnm := mem_filter.1 hn
      have hn0 : n ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hnm.1)
      have e3 : ∀ d ∈ M10.Dprime y p n, A d * (rhoB b (n / d) / ((n / d : ℕ) : ℝ) *
          sigmaP b (y / (p * d) / ((n / d : ℕ) : ℝ))) = rhoB b n / n * sigmaP b (y / (p * n)) * c d := by
        intro d hd
        have hdn := Nat.dvd_of_mem_divisors (mem_filter.1 hd).1
        have hd0 : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors (mem_filter.1 hd).1)
        have hcast : ((n / d : ℕ) : ℝ) = (n : ℝ) / d := Nat.cast_div hdn (by exact_mod_cast hd0)
        have hd' : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd0
        have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
        have harg : y / (p * d) / ((n / d : ℕ) : ℝ) = y / (p * n) := by
          rw [hcast]; field_simp
        have hG := M10.G_mul_div b hdn hd0
        rw [harg, hA, hc]
        dsimp only
        rw [← hG]; ring
      rw [sum_congr rfl e3, ← mul_sum]
      congr 1
      -- the coefficient sum is Lemma 10's b(n)
      have hsub : M10.Dprime y p n ⊆ n.divisors := filter_subset _ _
      have e4 : ∑ d ∈ M10.Dprime y p n, c d = ∑ d ∈ n.divisors, (if d ∈ M10.Dprime y p n then c d else 0) := by
        rw [← sum_filter]; congr 1; ext d; simp only [mem_filter]
        exact ⟨fun h => ⟨hsub h, h⟩, fun h => h.2⟩
      rw [e4, sum_congr rfl (fun d hd => M10.coef_eq hy hp h4 hnm.1 hnm.2.1 hnm.2.2 hd)]
      rw [← sum_filter]
      have hb : bfun y mm p n = ∑ d ∈ n.divisors.filter (fun d : ℕ => (qmax (n / d) : ℝ) < y / (p * n)),
          (μ d : ℝ) * chi y mm d := rfl
      rw [← hb]
      have hsqn := M10.squarefree_of_mem_divisors_primorial hnm.1
      exact h10 y mm p n (by norm_num [mm]) (by linarith) hp hpy hsqn hnm.2.1
        (fun q hq => ((mem_primesBelow y q).1 (M10.mem_PB_of_dvd (Nat.prime_of_mem_primeFactors hq)
          ((Nat.dvd_of_mem_primeFactors hq).trans (Nat.dvd_of_mem_divisors hnm.1)))).2) hnm.2.2
    rw [sum_congr rfl e2]
    have h1mem : 1 ∈ M10.Nprime y p := by
      unfold M10.Nprime; rw [mem_filter]
      refine ⟨Nat.mem_divisors.2 ⟨one_dvd _, (M10.primorialLt_pos' y).ne'⟩, by simp, by simp⟩
    rw [← add_sum_erase _ _ h1mem]
    have hρ1 : rhoB b 1 = 1 := by unfold rhoB; simp
    rw [if_pos rfl, hρ1, Nat.cast_one, div_one, one_mul, mul_one, mul_one]
    have e5 : ∑ n ∈ (M10.Nprime y p).erase 1, rhoB b n / n * sigmaP b (y / (p * n)) *
        (if n = 1 then 1 else if (n : ℝ) * n.minFac < y / p then -chibar y mm n else 0) =
        -∑ n ∈ ((M10.Nprime y p).erase 1).filter (fun n : ℕ => (n : ℝ) * n.minFac < y / p),
          chibar y mm n * rhoB b n / n * sigmaP b (y / (p * n)) := by
      rw [sum_filter, ← sum_neg_distrib]
      apply sum_congr rfl; intro n hn
      rw [if_neg (ne_of_mem_erase hn)]
      split_ifs <;> ring
    rw [e5, M10.Nprime_erase_filter]; ring
  -- assemble
  unfold Sp Xd Rpm
  have e6 : ∀ d ∈ D1set y p, A d * ∑ t ∈ S9 (y / (p * d)) p (decide (Even (ω d))), rhoB b t / t * sigmaP b (y / (p * d) / t) =
      A d * ∑ t ∈ (S9 (y / (p * d)) p (decide (Even (ω d)))).filter (fun t : ℕ => Nat.Coprime d t),
        rhoB b t / t * sigmaP b (y / (p * d) / t) +
      A d * ∑ t ∈ (S9 (y / (p * d)) p (decide (Even (ω d)))).filter (fun t : ℕ => ¬ Nat.Coprime d t),
        rhoB b t / t * sigmaP b (y / (p * d) / t) := by
    intro d _; rw [← mul_add, sum_filter_add_sum_filter_not]
  have e7 := sum_congr rfl e6
  rw [sum_add_distrib, hC] at e7
  simp only [hA] at e7
  rw [e7]
  unfold Ep
  ring

end KappaOmega2
