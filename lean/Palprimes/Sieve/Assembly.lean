import Palprimes.Sieve.Intervals

/-! # Assembly helpers for the weighted sieve (M13) -/

open Finset Real

namespace Palprimes

theorem PB_succ (B t : ℕ) : PB B (t + 1) =
    if t.Prime ∧ ¬ t ∣ B then insert t (PB B t) else PB B t := by
  unfold PB; rw [Finset.range_add_one, Finset.filter_insert]

theorem PB_sdiff (B W Z : ℕ) (hWZ : W ≤ Z) :
    PB B Z \ PB B W = (Ico W Z).filter (fun p => p.Prime ∧ ¬ p ∣ B) := by
  ext q
  simp only [PB, mem_sdiff, mem_filter, mem_range, mem_Ico]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨by by_contra h; exact h3 ⟨by omega, h2⟩, h1⟩, h2⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h2, h3⟩, fun h => by omega⟩

/-- **Telescoping** `V(W) − V(Z) = Σ_{W ≤ p < Z} V(p)/p`. -/
theorem telescope_V (B W Z : ℕ) (hWZ : W ≤ Z) :
    ∏ q ∈ PB B W, (1 - 1 / (q : ℝ)) - ∏ q ∈ PB B Z, (1 - 1 / (q : ℝ)) =
      ∑ p ∈ (Ico W Z).filter (fun p => p.Prime ∧ ¬ p ∣ B), (∏ q ∈ PB B p, (1 - 1 / (q : ℝ))) / p := by
  induction Z, hWZ using Nat.le_induction with
  | base => simp
  | succ Z hWZ ih =>
    rw [PB_succ]
    have hIco : (Ico W (Z + 1)).filter (fun p => p.Prime ∧ ¬ p ∣ B) =
        if Z.Prime ∧ ¬ Z ∣ B then insert Z ((Ico W Z).filter (fun p => p.Prime ∧ ¬ p ∣ B))
        else (Ico W Z).filter (fun p => p.Prime ∧ ¬ p ∣ B) := by
      rw [← Finset.insert_Ico_right_eq_Ico_add_one hWZ, Finset.filter_insert]
    rw [hIco]
    split_ifs with h
    · have hZ : Z ∉ PB B Z := by simp [PB]
      have hZ' : Z ∉ (Ico W Z).filter (fun p => p.Prime ∧ ¬ p ∣ B) := by simp
      rw [Finset.prod_insert hZ, Finset.sum_insert hZ', ← ih]
      ring
    · exact ih

theorem prod_PB_le (B W : ℕ) : ∏ q ∈ PB B W, q ≤ 4 ^ W := by
  refine le_trans ?_ (primorial_le_four_pow W)
  unfold primorial
  apply Finset.prod_le_prod_of_subset_of_one_le
  · intro q hq
    simp only [PB, mem_filter, mem_range] at hq
    simp only [mem_filter, mem_range]; exact ⟨by omega, hq.2.1⟩
  · intro q hq _
    simp only [mem_filter] at hq; exact hq.2.one_lt.le

/-- `(p, d) ↦ p d` is injective when all prime factors of `d` are below `p`. -/
theorem sum_sigma_mul_le (Ps : Finset ℕ) (hPs : ∀ p ∈ Ps, p.Prime) (Dd : ℕ → Finset ℕ)
    (hD : ∀ p ∈ Ps, ∀ d ∈ Dd p, ∀ q : ℕ, q.Prime → q ∣ d → q < p)
    (Q : Finset ℕ) (hQ : ∀ p ∈ Ps, ∀ d ∈ Dd p, p * d ∈ Q) (g : ℕ → ℝ) (hg : ∀ q ∈ Q, 0 ≤ g q) :
    ∑ p ∈ Ps, ∑ d ∈ Dd p, g (p * d) ≤ ∑ q ∈ Q, g q := by
  classical
  rw [Finset.sum_sigma']
  have hinj : Set.InjOn (fun x : (_ : ℕ) × ℕ => x.1 * x.2) (Ps.sigma Dd : Set ((_ : ℕ) × ℕ)) := by
    rintro ⟨p, d⟩ hx ⟨p', d'⟩ hy h
    simp only [coe_sigma, Set.mem_sigma_iff, mem_coe] at hx hy
    simp only at h
    have hp := hPs p hx.1
    have hp' := hPs p' hy.1
    have hpp : p = p' := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · -- `p' | p d`, so `p' | d`, but primes of `d` are below `p < p'`
        have h1 : p' ∣ p * d := ⟨d', h⟩
        rcases (Nat.Prime.dvd_mul hp').1 h1 with h2 | h2
        · exact hne ((Nat.prime_dvd_prime_iff_eq hp' hp).1 h2).symm
        · exact absurd (hD p hx.1 d hx.2 p' hp' h2) (by omega)
      · have h1 : p ∣ p' * d' := ⟨d, h.symm⟩
        rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
        · exact hne ((Nat.prime_dvd_prime_iff_eq hp hp').1 h2)
        · exact absurd (hD p' hy.1 d' hy.2 p hp h2) (by omega)
    subst hpp
    have hdd : d = d' := Nat.eq_of_mul_eq_mul_left hp.pos h
    subst hdd; rfl
  rw [← Finset.sum_image (f := g) hinj]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro q hq
    rw [mem_image] at hq
    obtain ⟨⟨p, d⟩, hx, rfl⟩ := hq
    rw [mem_sigma] at hx
    exact hQ p hx.1 d hx.2
  · intro q hq _; exact hg q hq

theorem coprime_of_dvd_prod_PB (Pset : Finset ℕ) (B : ℕ) (hP : ∀ q ∈ Pset, q.Prime ∧ ¬ q ∣ B)
    (d : ℕ) (hd : d ∣ ∏ q ∈ Pset, q) : Nat.Coprime d B := by
  have : Nat.Coprime (∏ q ∈ Pset, q) B :=
    Nat.Coprime.prod_left (fun q hq => (Nat.Prime.coprime_iff_not_dvd (hP q hq).1).2 (hP q hq).2)
  exact Nat.Coprime.coprime_dvd_left hd this

/-- The remainder terms of all Selberg applications together are at most the level sum. -/
theorem err_sum_le (A : Finset ℕ) (B : ℕ) (X D : ℝ) (Ps : Finset ℕ) (Pset : ℕ → Finset ℕ)
    (hPs : ∀ p ∈ Ps, p.Prime ∧ ¬ p ∣ B)
    (hPset : ∀ p ∈ Ps, ∀ q ∈ Pset p, q.Prime ∧ ¬ q ∣ B ∧ q < p) :
    ∑ p ∈ Ps, ∑ d ∈ (∏ q ∈ Pset p, q).divisors with (((d : ℕ) : ℝ) ≤ D / p),
        (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors d) *
          |(#((A.filter (p ∣ ·)).filter (d ∣ ·)) : ℝ) - X / p / d| ≤
      ∑ q ∈ (Icc 1 ⌊D⌋₊).filter (fun q => Nat.Coprime q B),
        (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors q) * |(countDvd A q : ℝ) - X / q| := by
  classical
  set g : ℕ → ℝ := fun q => (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors q) *
    |(countDvd A q : ℝ) - X / q|
  have hterm : ∀ p ∈ Ps, ∀ d ∈ (∏ q ∈ Pset p, q).divisors.filter (fun d : ℕ => ((d : ℕ) : ℝ) ≤ D / p),
      (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors d) *
        |(#((A.filter (p ∣ ·)).filter (d ∣ ·)) : ℝ) - X / p / d| ≤ g (p * d) := by
    intro p hp d hd
    simp only [mem_filter, Nat.mem_divisors] at hd
    have hpp := (hPs p hp).1
    have hpd : ¬ p ∣ d := by
      intro h
      have := Nat.dvd_trans h hd.1.1
      obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hpp.prime _).1 this
      have hq' := hPset p hp q hq
      have := (Nat.prime_dvd_prime_iff_eq hpp hq'.1).1 hpq
      omega
    have hcop : Nat.Coprime p d := (Nat.Prime.coprime_iff_not_dvd hpp).2 hpd
    have hcard : (A.filter (p ∣ ·)).filter (d ∣ ·) = A.filter ((p * d) ∣ ·) := by
      rw [Finset.filter_filter]
      apply Finset.filter_congr; intro n _
      exact ⟨fun h => Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h.1 h.2,
        fun h => ⟨dvd_trans (dvd_mul_right p d) h, dvd_trans (dvd_mul_left d p) h⟩⟩
    have hω : ArithmeticFunction.cardDistinctFactors d ≤ ArithmeticFunction.cardDistinctFactors (p * d) := by
      rw [ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors,
        ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors]
      apply Finset.card_le_card
      exact Nat.primeFactors_mono (dvd_mul_left d p) (Nat.mul_ne_zero hpp.ne_zero hd.1.2 |> fun h => by
        intro h0; rcases Nat.mul_eq_zero.1 h0 with h1 | h1
        · exact hpp.ne_zero h1
        · exact (Nat.pos_of_dvd_of_pos hd.1.1 (Nat.pos_of_ne_zero hd.1.2)).ne' h1)
    simp only [g, countDvd]
    rw [hcard, show X / p / d = X / ((p * d : ℕ) : ℝ) by push_cast; ring]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    exact pow_le_pow_right₀ (by norm_num) hω
  calc _ ≤ ∑ p ∈ Ps, ∑ d ∈ (∏ q ∈ Pset p, q).divisors.filter (fun d : ℕ => ((d : ℕ) : ℝ) ≤ D / p),
        g (p * d) := Finset.sum_le_sum (fun p hp => Finset.sum_le_sum (fun d hd => hterm p hp d hd))
    _ ≤ _ := by
      apply sum_sigma_mul_le Ps (fun p hp => (hPs p hp).1) _
      · intro p hp d hd q hq hqd
        simp only [mem_filter, Nat.mem_divisors] at hd
        obtain ⟨r, hr, hqr⟩ := (Prime.dvd_finsetProd_iff hq.prime _).1 (Nat.dvd_trans hqd hd.1.1)
        have hr' := hPset p hp r hr
        rw [(Nat.prime_dvd_prime_iff_eq hq hr'.1).1 hqr]; exact hr'.2.2
      · intro p hp d hd
        simp only [mem_filter, Nat.mem_divisors] at hd
        have hpp := (hPs p hp).1
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
        have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd.1.1 (Nat.pos_of_ne_zero hd.1.2)
        simp only [mem_filter, mem_Icc]
        refine ⟨⟨Nat.mul_pos hpp.pos hd0, ?_⟩, ?_⟩
        · apply Nat.le_floor; push_cast
          have := hd.2; rw [le_div_iff₀ hp0] at this; linarith
        · exact Nat.Coprime.mul_left ((Nat.Prime.coprime_iff_not_dvd hpp).2 (hPs p hp).2)
            (coprime_of_dvd_prod_PB (Pset p) B (fun q hq => ⟨(hPset p hp q hq).1, (hPset p hp q hq).2.1⟩)
              d hd.1.1)
      · intro q _; simp only [g]; positivity

/-- The level sum `R`. -/
noncomputable def levelSum (A : Finset ℕ) (B : ℕ) (D : ℝ) : ℝ :=
  ∑ q ∈ (Icc 1 ⌊D⌋₊).filter (fun q => Nat.Coprime q B),
    (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors q) * |(countDvd A q : ℝ) - (#A : ℝ) / q|

theorem levelSum_nonneg (A : Finset ℕ) (B : ℕ) (D : ℝ) : 0 ≤ levelSum A B D :=
  Finset.sum_nonneg (fun q _ => by positivity)

/-- Selberg for `A_p` with sifting set `Pset`, written with `selS`. -/
theorem selberg_Ap (A : Finset ℕ) (p : ℕ) (Pset : Finset ℕ) (hP : ∀ q ∈ Pset, q.Prime) (X D : ℝ)
    (hy : 1 ≤ D / p) :
    (#((A.filter (p ∣ ·)).filter (fun n => ∀ q ∈ Pset, ¬ q ∣ n)) : ℝ) ≤
      X / p / selS Pset (D / p) +
      ∑ d ∈ (∏ q ∈ Pset, q).divisors with (((d : ℕ) : ℝ) ≤ D / p),
        (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors d) *
          |(#((A.filter (p ∣ ·)).filter (d ∣ ·)) : ℝ) - X / p / d| :=
  selberg_concrete (A.filter (p ∣ ·)) Pset hP (X / p) (D / p) hy

/-- **Lower bound for `#S0`.** -/
theorem lower_S0 (A : Finset ℕ) (B : ℕ) (D : ℝ) (W Z : ℕ) (hWZ : W ≤ Z)
    (hPW : ((∏ q ∈ PB B W, q : ℕ) : ℝ) ≤ D) (hZD : ∀ p : ℕ, 1 ≤ p → p < Z → 1 ≤ D / p) :
    (#A : ℝ) * (∏ q ∈ PB B Z, (1 - 1 / (q : ℝ))) -
        (#A : ℝ) * ∑ p ∈ (Ico W Z).filter (fun p => p.Prime ∧ ¬ p ∣ B),
          (1 / (p * selS (PB B p) (D / p)) - (∏ q ∈ PB B p, (1 - 1 / (q : ℝ))) / p) -
        2 * levelSum A B D ≤
      (#(A.filter (fun n => ∀ q ∈ PB B Z, ¬ q ∣ n)) : ℝ) := by
  classical
  set X := (#A : ℝ)
  set BP := (Ico W Z).filter (fun p => p.Prime ∧ ¬ p ∣ B)
  have hBP : PB B Z \ PB B W = BP := PB_sdiff B W Z hWZ
  have hR0 := levelSum_nonneg A B D
  -- inclusion–exclusion at `W`
  have h1 := card_sift_ge A (PB B W) (PB_primes B W)
  have h1e : ∑ d ∈ (∏ q ∈ PB B W, q).divisors, |(#(A.filter (d ∣ ·)) : ℝ) - X / d| ≤ levelSum A B D := by
    unfold levelSum
    calc _ ≤ ∑ d ∈ (∏ q ∈ PB B W, q).divisors, (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors d) *
          |(countDvd A d : ℝ) - X / d| := by
          apply Finset.sum_le_sum; intro d _
          have : (1 : ℝ) ≤ 3 ^ (ArithmeticFunction.cardDistinctFactors d) := one_le_pow₀ (by norm_num)
          unfold countDvd
          nlinarith [abs_nonneg ((#(A.filter (d ∣ ·)) : ℝ) - X / d)]
      _ ≤ _ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro d hd
            rw [Nat.mem_divisors] at hd
            simp only [mem_filter, mem_Icc]
            have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd.1 (Nat.pos_of_ne_zero hd.2)
            refine ⟨⟨hd0, Nat.le_floor ?_⟩, coprime_of_dvd_prod_PB _ B
              (fun q hq => by simp only [PB, mem_filter] at hq; exact hq.2) d hd.1⟩
            exact le_trans (by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hd.2) hd.1) hPW
          · intro d _ _; positivity
  -- Buchstab
  have h2 := buchstab_le A B W Z hWZ
  rw [hBP] at h2
  have h2' : (#(A.filter (fun n => ∀ q ∈ PB B W, ¬ q ∣ n)) : ℝ) ≤
      (#(A.filter (fun n => ∀ q ∈ PB B Z, ¬ q ∣ n)) : ℝ) +
      ∑ p ∈ BP, (#((A.filter (p ∣ ·)).filter (fun n => ∀ q ∈ PB B p, ¬ q ∣ n)) : ℝ) := by
    have : ∀ p, A.filter (fun n => p ∣ n ∧ ∀ q ∈ PB B p, ¬ q ∣ n) =
        (A.filter (p ∣ ·)).filter (fun n => ∀ q ∈ PB B p, ¬ q ∣ n) := fun p => by
      rw [Finset.filter_filter]
    simp only [this] at h2
    exact_mod_cast h2
  -- Selberg for each `p`
  have h3 : ∑ p ∈ BP, (#((A.filter (p ∣ ·)).filter (fun n => ∀ q ∈ PB B p, ¬ q ∣ n)) : ℝ) ≤
      ∑ p ∈ BP, X / p / selS (PB B p) (D / p) +
      ∑ p ∈ BP, ∑ d ∈ (∏ q ∈ PB B p, q).divisors with (((d : ℕ) : ℝ) ≤ D / p),
        (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors d) *
          |(#((A.filter (p ∣ ·)).filter (d ∣ ·)) : ℝ) - X / p / d| := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro p hp
    simp only [BP, mem_filter, mem_Ico] at hp
    exact selberg_Ap A p (PB B p) (PB_primes B p) X D (hZD p hp.2.1.one_lt.le hp.1.2)
  have h3e := err_sum_le A B X D BP (fun p => PB B p)
    (fun p hp => by simp only [BP, mem_filter] at hp; exact hp.2)
    (fun p _ q hq => by simp only [PB, mem_filter, mem_range] at hq; exact ⟨hq.2.1, hq.2.2, hq.1⟩)
  -- telescoping
  have h4 := telescope_V B W Z hWZ
  have h5 : ∑ p ∈ BP, X / p / selS (PB B p) (D / p) = X * ∑ p ∈ BP, 1 / (p * selS (PB B p) (D / p)) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; field_simp
  have h6 : X * ∑ p ∈ BP, (1 / (p * selS (PB B p) (D / p)) - (∏ q ∈ PB B p, (1 - 1 / (q : ℝ))) / p) =
      X * ∑ p ∈ BP, 1 / (p * selS (PB B p) (D / p)) -
        X * ∑ p ∈ BP, (∏ q ∈ PB B p, (1 - 1 / (q : ℝ))) / p := by
    rw [Finset.sum_sub_distrib, mul_sub]
  unfold levelSum at h3e h1e ⊢
  set E1 := ∑ d ∈ (∏ q ∈ PB B W, q).divisors, |(#(A.filter (d ∣ ·)) : ℝ) - X / d|
  set E3 := ∑ p ∈ BP, ∑ d ∈ (∏ q ∈ PB B p, q).divisors with (((d : ℕ) : ℝ) ≤ D / p),
        (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors d) *
          |(#((A.filter (p ∣ ·)).filter (d ∣ ·)) : ℝ) - X / p / d|
  set R := ∑ q ∈ (Icc 1 ⌊D⌋₊).filter (fun q => Nat.Coprime q B),
    (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors q) * |(countDvd A q : ℝ) - X / q|
  set VW := ∏ q ∈ PB B W, (1 - 1 / (q : ℝ))
  set VZ := ∏ q ∈ PB B Z, (1 - 1 / (q : ℝ))
  set T1 := ∑ p ∈ BP, 1 / (p * selS (PB B p) (D / p))
  set T2 := ∑ p ∈ BP, (∏ q ∈ PB B p, (1 - 1 / (q : ℝ))) / p
  set S0 := (#(A.filter (fun n => ∀ q ∈ PB B Z, ¬ q ∣ n)) : ℝ)
  set SW := (#(A.filter (fun n => ∀ q ∈ PB B W, ¬ q ∣ n)) : ℝ)
  set SE := ∑ p ∈ BP, (#((A.filter (p ∣ ·)).filter (fun n => ∀ q ∈ PB B p, ¬ q ∣ n)) : ℝ)
  have hT : X * T1 - X * T2 = X * T1 - X * T2 := rfl
  rw [h6]
  have k1 : X * VW - E1 ≤ SW := h1
  have k2 : SW ≤ S0 + SE := h2'
  have k3 : SE ≤ X * T1 + E3 := by rw [← h5]; exact h3
  have k4 : VW - VZ = T2 := h4
  have k5 : X * VW = X * VZ + X * T2 := by rw [← k4]; ring
  linarith

/-- **Upper bound for the Richert terms.** -/
theorem upper_rich (A : Finset ℕ) (B : ℕ) (D : ℝ) (Z : ℕ) (RP : Finset ℕ) (w : ℕ → ℝ)
    (hRP : ∀ p ∈ RP, p.Prime ∧ Z ≤ p ∧ ¬ p ∣ B ∧ 1 ≤ D / p) (hw : ∀ p ∈ RP, 0 ≤ w p ∧ w p ≤ 1) :
    ∑ p ∈ RP, w p * (#((A.filter (fun n => ∀ q ∈ PB B Z, ¬ q ∣ n)).filter (p ∣ ·)) : ℝ) ≤
      (#A : ℝ) * ∑ p ∈ RP, w p / (p * selS (PB B Z) (D / p)) + levelSum A B D := by
  classical
  set X := (#A : ℝ)
  have he := err_sum_le A B X D RP (fun _ => PB B Z)
    (fun p hp => ⟨(hRP p hp).1, (hRP p hp).2.2.1⟩)
    (fun p hp q hq => by
      simp only [PB, mem_filter, mem_range] at hq
      exact ⟨hq.2.1, hq.2.2, lt_of_lt_of_le hq.1 (hRP p hp).2.1⟩)
  unfold levelSum
  refine le_trans ?_ (add_le_add le_rfl he)
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro p hp
  have hsel := selberg_Ap A p (PB B Z) (PB_primes B Z) X D (hRP p hp).2.2.2
  have hcomm : (A.filter (fun n => ∀ q ∈ PB B Z, ¬ q ∣ n)).filter (p ∣ ·) =
      (A.filter (p ∣ ·)).filter (fun n => ∀ q ∈ PB B Z, ¬ q ∣ n) := by
    rw [Finset.filter_filter, Finset.filter_filter]; apply Finset.filter_congr; intro n _; exact And.comm
  rw [hcomm]
  obtain ⟨hw0, hw1⟩ := hw p hp
  set err := ∑ d ∈ (∏ q ∈ PB B Z, q).divisors with (((d : ℕ) : ℝ) ≤ D / p),
        (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors d) *
          |(#((A.filter (p ∣ ·)).filter (d ∣ ·)) : ℝ) - X / p / d|
  have herr : 0 ≤ err := Finset.sum_nonneg (fun d _ => by positivity)
  have e1 : X / p / selS (PB B Z) (D / p) * w p = X * (w p / (p * selS (PB B Z) (D / p))) := by
    field_simp
  calc w p * (#((A.filter (p ∣ ·)).filter (fun n => ∀ q ∈ PB B Z, ¬ q ∣ n)) : ℝ)
      ≤ w p * (X / p / selS (PB B Z) (D / p) + err) := mul_le_mul_of_nonneg_left hsel hw0
    _ = X / p / selS (PB B Z) (D / p) * w p + w p * err := by ring
    _ ≤ X * (w p / (p * selS (PB B Z) (D / p))) + err := by
        rw [e1]; nlinarith

end Palprimes
