import KappaOmega2.Items.QK01_Exp

namespace KappaOmega2

open Finset Palprimes

/-! Item QK01: reduction of `A_{p²} − X/p²` to Farey-type sums of `|f|` for the κ-sequence (port of Q01 over the
index set `(u, w)`, product formula `QK01.fK_exp`). -/

open QK01

lemma qk1_ee_add (a c : ℝ) : ee (a + c) = ee a * ee c := by
  unfold ee
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma qk1_ee_zero : ee 0 = 1 := by simp [ee]

lemma qk1_ee_int (z : ℤ) : ee (z : ℝ) = 1 := by
  unfold ee
  have := Complex.exp_int_mul_two_pi_mul_I z
  rw [← this]
  congr 1
  push_cast
  ring

lemma qk1_norm_ee (t : ℝ) : ‖ee t‖ = 1 := by
  unfold ee
  have := Complex.norm_exp_ofReal_mul_I (2 * Real.pi * t)
  rw [← this]
  congr 2
  push_cast
  ring

/-- Full orthogonality. -/
lemma qk1_orth (q : ℕ) (hq : 0 < q) (m : ℤ) :
    ∑ h ∈ Finset.range q, ee ((m : ℝ) * ((h : ℝ) / q)) = if (q : ℤ) ∣ m then (q : ℂ) else 0 := by
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((m : ℂ) / (q : ℂ))) :=
    ⟨_, rfl⟩
  have key : ∀ h : ℕ, ee ((m : ℝ) * ((h : ℝ) / q)) = z ^ h := by
    intro h
    unfold ee
    rw [hz, ← Complex.exp_natCast_mul]
    congr 1
    push_cast
    ring
  simp only [key]
  by_cases hd : (q : ℤ) ∣ m
  · rw [if_pos hd]
    obtain ⟨n, hn⟩ := hd
    have hz1 : z = 1 := by
      rw [hz]
      have : (2 * (Real.pi : ℂ) * Complex.I * ((m : ℂ) / (q : ℂ))) = (n : ℂ) * (2 * Real.pi * Complex.I) := by
        have : (m : ℂ) = (q : ℂ) * n := by exact_mod_cast hn
        rw [this]; field_simp
      rw [this, Complex.exp_int_mul_two_pi_mul_I]
    simp [hz1]
  · rw [if_neg hd]
    have hz1 : z ≠ 1 := by
      intro h1
      rw [hz] at h1
      obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
      have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have h3 : ((m : ℂ) / (q : ℂ) - n) * (2 * (Real.pi : ℂ) * Complex.I) = 0 := by
        linear_combination hn
      have h4 : (m : ℂ) / (q : ℂ) - n = 0 := (mul_eq_zero.mp h3).resolve_right hpi
      have h5 : (m : ℂ) = (n : ℂ) * (q : ℂ) := by
        rw [sub_eq_zero, div_eq_iff hqC] at h4
        exact h4
      have h6 : m = n * (q : ℤ) := by exact_mod_cast h5
      exact hd ⟨n, by rw [h6]; ring⟩
    have hzq : z ^ q = 1 := by
      rw [hz, ← Complex.exp_natCast_mul]
      have h7 : (q : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * ((m : ℂ) / (q : ℂ)))
          = (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        field_simp
      rw [h7, Complex.exp_int_mul_two_pi_mul_I]
    rw [geom_sum_eq hz1, hzq, sub_self, zero_div]

lemma qk1_ee_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ee (∑ i ∈ s, f i) = ∏ i ∈ s, ee (f i) := by
  unfold ee
  push_cast
  rw [Finset.mul_sum, Complex.exp_sum]

/-! ### Fourier expansion of the coprimality indicator -/

noncomputable def qk1I (r n : ℕ) : ℂ := open Classical in if Nat.Coprime n r then 1 else 0

noncomputable def qk1c (r k : ℕ) : ℂ :=
  (1 / (r : ℂ)) * ∑ ρ ∈ range r, qk1I r ρ * ee (-((ρ : ℝ) * ((k : ℝ) / r)))

lemma qk1_I_fourier (r n : ℕ) (hr : 0 < r) :
    qk1I r n = ∑ k ∈ range r, qk1c r k * ee ((n : ℝ) * ((k : ℝ) / r)) := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have h1 : ∀ k : ℕ, qk1c r k * ee ((n : ℝ) * ((k : ℝ) / r)) =
      ∑ ρ ∈ range r, (1 / (r : ℂ)) * (qk1I r ρ * ee ((((n : ℤ) - ρ : ℤ) : ℝ) * ((k : ℝ) / r))) := by
    intro k
    unfold qk1c
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ρ _
    have : ee ((((n : ℤ) - ρ : ℤ) : ℝ) * ((k : ℝ) / r)) =
        ee (-((ρ : ℝ) * ((k : ℝ) / r))) * ee ((n : ℝ) * ((k : ℝ) / r)) := by
      rw [← qk1_ee_add]; congr 1; push_cast; ring
    rw [this]; ring
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ ρ ∈ range r, ∑ k ∈ range r, (1 / (r : ℂ)) * (qk1I r ρ * ee ((((n : ℤ) - ρ : ℤ) : ℝ) * ((k : ℝ) / r))) =
      if ρ = n % r then qk1I r ρ else 0 := by
    intro ρ hρ
    rw [← Finset.mul_sum, ← Finset.mul_sum, qk1_orth r hr]
    have hρ' : ρ < r := Finset.mem_range.mp hρ
    by_cases hc : ρ = n % r
    · have hd : (r : ℤ) ∣ (n : ℤ) - ρ := by
        rw [hc]
        have := Nat.div_add_mod n r
        exact ⟨(n / r : ℕ), by
          have h' : (n : ℤ) = r * (n / r : ℕ) + (n % r : ℕ) := by exact_mod_cast this.symm
          rw [h']; ring⟩
      rw [if_pos hd, if_pos hc]
      field_simp
    · have hd : ¬ (r : ℤ) ∣ (n : ℤ) - ρ := by
        intro hd
        apply hc
        have h3 : (n : ℤ) % r = (ρ : ℤ) % r := by
          exact Int.emod_eq_emod_iff_emod_sub_eq_zero.2 (Int.emod_eq_zero_of_dvd hd)
        have h4 : n % r = ρ % r := by exact_mod_cast h3
        rw [h4, Nat.mod_eq_of_lt hρ']
      rw [if_neg hd, if_neg hc]; simp
  rw [Finset.sum_congr rfl h2, Finset.sum_ite_eq' (range r) (n % r)]
  rw [if_pos (Finset.mem_range.mpr (Nat.mod_lt _ hr))]
  unfold qk1I
  have : Nat.Coprime (n % r) r ↔ Nat.Coprime n r := by
    unfold Nat.Coprime
    rw [← Nat.gcd_rec, Nat.gcd_comm]
  simp only [this]

lemma qk1_c_norm (r k : ℕ) (hr : 0 < r) : ‖qk1c r k‖ ≤ 1 := by
  unfold qk1c
  rw [norm_mul]
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have h1 : ‖∑ ρ ∈ range r, qk1I r ρ * ee (-((ρ : ℝ) * ((k : ℝ) / r)))‖ ≤ r := by
    calc _ ≤ ∑ ρ ∈ range r, ‖qk1I r ρ * ee (-((ρ : ℝ) * ((k : ℝ) / r)))‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ range r, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro ρ _
        rw [norm_mul, qk1_norm_ee, mul_one]
        unfold qk1I
        split_ifs <;> simp
      _ = r := by simp
  have h2 : ‖(1 / (r : ℂ))‖ = 1 / (r : ℝ) := by
    rw [norm_div, norm_one]; simp
  rw [h2]
  calc 1 / (r : ℝ) * _ ≤ 1 / (r : ℝ) * r := by gcongr
    _ = 1 := by field_simp

/-! ### The coprime-weighted sum `Φ` -/

noncomputable def qk1Phi (b : ℕ) (g : ℕ → ℝ) (N : ℕ) (x : ℝ) : ℂ :=
  ∑ d : KIdx b N, (kw b g N d : ℂ) * qk1I (bigB b) (kv b N d) * ee ((kv b N d : ℝ) * x)

lemma qk1_Phi_fourier (b : ℕ) (g : ℕ → ℝ) (N : ℕ) (hr : 0 < bigB b) (x : ℝ) :
    qk1Phi b g N x = ∑ k ∈ range (bigB b), qk1c (bigB b) k * fK b g N (x + (k : ℝ) / (bigB b : ℝ)) := by
  unfold qk1Phi
  simp_rw [fK_exp, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [qk1_I_fourier (bigB b) (kv b N d) hr, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  have : ee ((kv b N d : ℝ) * (x + (k : ℝ) / (bigB b : ℝ))) =
      ee ((kv b N d : ℝ) * ((k : ℝ) / (bigB b : ℝ))) * ee ((kv b N d : ℝ) * x) := by
    rw [← qk1_ee_add]; congr 1; ring
  rw [this]; ring

lemma qk1_Phi_norm (b : ℕ) (g : ℕ → ℝ) (N : ℕ) (hr : 0 < bigB b) (x : ℝ) :
    ‖qk1Phi b g N x‖ ≤ ∑ k ∈ range (bigB b), ‖fK b g N (x + (k : ℝ) / (bigB b : ℝ))‖ := by
  rw [qk1_Phi_fourier b g N hr x]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul]
  calc _ ≤ 1 * ‖fK b g N (x + (k : ℝ) / (bigB b : ℝ))‖ := by
        gcongr; exact qk1_c_norm _ _ hr
    _ = _ := one_mul _

lemma qk1_Phi_zero (b : ℕ) (g : ℕ → ℝ) (N : ℕ) : qk1Phi b g N 0 = (XK b g N : ℂ) := by
  classical
  unfold qk1Phi XK
  rw [AK_eq]
  push_cast
  apply Finset.sum_congr rfl
  intro d _
  simp only [mul_zero, qk1_ee_zero, mul_one, qk1I, Nat.dvd_one, one_dvd, and_true]
  split_ifs <;> simp

lemma qk1_Phi_sum (b : ℕ) (g : ℕ → ℝ) (N q : ℕ) (hq : 0 < q) :
    ∑ h ∈ range q, qk1Phi b g N ((h : ℝ) / q) = (q : ℂ) * (AK b g N q : ℂ) := by
  classical
  unfold qk1Phi
  rw [AK_eq]
  rw [Finset.sum_comm]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [← Finset.mul_sum]
  have := qk1_orth q hq (kv b N d : ℤ)
  push_cast at this
  simp only [Int.natCast_dvd_natCast] at this
  rw [this]
  unfold qk1I
  split_ifs <;> simp_all [mul_comm]

/-- The set of `h ∈ [0,p²)` divisible by `p`. -/
lemma qk1_filter_dvd (p : ℕ) (hp : 0 < p) :
    (range (p ^ 2)).filter (fun h => p ∣ h) = (range p).image (fun c => p * c) := by
  ext h
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨hlt, c, rfl⟩
    refine ⟨c, ?_, rfl⟩
    by_contra hc
    push_neg at hc
    nlinarith
  · rintro ⟨c, hc, rfl⟩
    exact ⟨by nlinarith, dvd_mul_right _ _⟩

theorem itemQK01 : ItemQK01 := by
  intro b g N p hb hp _
  have hr : 0 < bigB b := by
    unfold bigB
    have : b < b ^ 3 := by
      calc b = b ^ 1 := (pow_one b).symm
        _ < b ^ 3 := Nat.pow_lt_pow_right (by omega) (by omega)
    omega
  have hp0 : 0 < p := hp.pos
  have hq : 0 < p ^ 2 := pow_pos hp0 2
  set A := AK b g N (p ^ 2) with hA
  have key := qk1_Phi_sum b g N (p ^ 2) hq
  -- split the sum over h < p²
  rw [← Finset.sum_filter_add_sum_filter_not (range (p ^ 2)) (fun h => p ∣ h), qk1_filter_dvd p hp0,
    Finset.sum_image (fun x _ y _ hxy => Nat.eq_of_mul_eq_mul_left hp0 hxy)] at key
  have hdv : ∀ c : ℕ, qk1Phi b g N (((p * c : ℕ) : ℝ) / ((p ^ 2 : ℕ) : ℝ)) = qk1Phi b g N ((c : ℝ) / p) := by
    intro c
    congr 1
    have : (p : ℝ) ≠ 0 := by exact_mod_cast hp0.ne'
    push_cast
    field_simp
  simp_rw [hdv] at key
  have hsplit : ∑ c ∈ range p, qk1Phi b g N ((c : ℝ) / p) =
      qk1Phi b g N 0 + ∑ c ∈ Ico 1 p, qk1Phi b g N ((c : ℝ) / p) := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hp0]
    simp
  rw [hsplit, qk1_Phi_zero] at key
  have hmain : ((p ^ 2 : ℕ) : ℂ) * ((A : ℂ) - (XK b g N : ℂ) / ((p : ℂ) ^ 2)) =
      ∑ h ∈ (range (p ^ 2)).filter (fun h => ¬ p ∣ h), qk1Phi b g N ((h : ℝ) / ((p ^ 2 : ℕ) : ℝ)) +
        ∑ c ∈ Ico 1 p, qk1Phi b g N ((c : ℝ) / p) := by
    have hp2 : ((p : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hq.ne'
    push_cast at key ⊢
    have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp0.ne'
    have e1 : (p : ℂ) ^ 2 * ((XK b g N : ℂ) / (p : ℂ) ^ 2) = (XK b g N : ℂ) := by field_simp
    linear_combination -key - e1
  have hp2R : (0 : ℝ) < ((p : ℝ) ^ 2) := by positivity
  have hnorm : |A - XK b g N / (p : ℝ) ^ 2| =
      (1 / (p : ℝ) ^ 2) * ‖∑ h ∈ (range (p ^ 2)).filter (fun h => ¬ p ∣ h), qk1Phi b g N ((h : ℝ) / ((p ^ 2 : ℕ) : ℝ)) +
        ∑ c ∈ Ico 1 p, qk1Phi b g N ((c : ℝ) / p)‖ := by
    rw [← hmain, norm_mul]
    have : ‖((p ^ 2 : ℕ) : ℂ)‖ = (p : ℝ) ^ 2 := by simp
    have h2 : ‖((A : ℂ) - (XK b g N : ℂ) / ((p : ℂ) ^ 2))‖ = |A - XK b g N / (p : ℝ) ^ 2| := by
      have : ((A - XK b g N / (p : ℝ) ^ 2 : ℝ) : ℂ) = (A : ℂ) - (XK b g N : ℂ) / (p : ℂ) ^ 2 := by push_cast; ring
      rw [← this, Complex.norm_real, Real.norm_eq_abs]
    rw [this, h2]
    field_simp
  rw [hnorm]
  have htau : (1 : ℝ) ≤ ((bigB b).divisors.card : ℝ) := by
    have : 0 < (bigB b).divisors.card := Finset.card_pos.2 ⟨1, Nat.mem_divisors.2 ⟨one_dvd _, hr.ne'⟩⟩
    exact_mod_cast this
  have hS1 : ‖∑ h ∈ (range (p ^ 2)).filter (fun h => ¬ p ∣ h), qk1Phi b g N ((h : ℝ) / ((p ^ 2 : ℕ) : ℝ))‖ ≤
      ∑ k ∈ range (bigB b), ∑ h ∈ (range (p ^ 2)).filter (fun h => ¬ p ∣ h),
            ‖fK b g N ((h : ℝ) / (p ^ 2 : ℕ) + (k : ℝ) / (bigB b : ℝ))‖ := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun h _ => qk1_Phi_norm b g N hr _).trans (le_of_eq ?_)
    exact Finset.sum_comm
  have hS2 : ‖∑ c ∈ Ico 1 p, qk1Phi b g N ((c : ℝ) / p)‖ ≤
      ∑ k ∈ range (bigB b), ∑ h ∈ Ico 1 p, ‖fK b g N ((h : ℝ) / p + (k : ℝ) / (bigB b : ℝ))‖ := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun h _ => qk1_Phi_norm b g N hr _).trans (le_of_eq ?_)
    exact Finset.sum_comm
  have hb1 : ‖∑ h ∈ (range (p ^ 2)).filter (fun h => ¬ p ∣ h), qk1Phi b g N ((h : ℝ) / ((p ^ 2 : ℕ) : ℝ)) +
        ∑ c ∈ Ico 1 p, qk1Phi b g N ((c : ℝ) / p)‖ ≤
      ∑ k ∈ range (bigB b), ((∑ h ∈ (range (p ^ 2)).filter (fun h => ¬ p ∣ h),
            ‖fK b g N ((h : ℝ) / (p ^ 2 : ℕ) + (k : ℝ) / (bigB b : ℝ))‖) +
          ∑ h ∈ Ico 1 p, ‖fK b g N ((h : ℝ) / p + (k : ℝ) / (bigB b : ℝ))‖) := by
    refine (norm_add_le _ _).trans ?_
    rw [Finset.sum_add_distrib]
    exact add_le_add hS1 hS2
  have hnn : 0 ≤ ∑ k ∈ range (bigB b), ((∑ h ∈ (range (p ^ 2)).filter (fun h => ¬ p ∣ h),
            ‖fK b g N ((h : ℝ) / (p ^ 2 : ℕ) + (k : ℝ) / (bigB b : ℝ))‖) +
          ∑ h ∈ Ico 1 p, ‖fK b g N ((h : ℝ) / p + (k : ℝ) / (bigB b : ℝ))‖) := by positivity
  rw [← Finset.mul_sum]
  calc (1 / (p : ℝ) ^ 2) * _ ≤ (1 / (p : ℝ) ^ 2) * ∑ k ∈ range (bigB b), ((∑ h ∈ (range (p ^ 2)).filter (fun h => ¬ p ∣ h),
            ‖fK b g N ((h : ℝ) / (p ^ 2 : ℕ) + (k : ℝ) / (bigB b : ℝ))‖) +
          ∑ h ∈ Ico 1 p, ‖fK b g N ((h : ℝ) / p + (k : ℝ) / (bigB b : ℝ))‖) :=
        mul_le_mul_of_nonneg_left hb1 (by positivity)
    _ = ((p : ℝ) ^ 2)⁻¹ * ∑ k ∈ range (bigB b), ((∑ h ∈ (range (p ^ 2)).filter (fun h => ¬ p ∣ h),
            ‖fK b g N ((h : ℝ) / (p ^ 2 : ℕ) + (k : ℝ) / (bigB b : ℝ))‖) +
          ∑ h ∈ Ico 1 p, ‖fK b g N ((h : ℝ) / p + (k : ℝ) / (bigB b : ℝ))‖) := by rw [one_div]
    _ ≤ _ := by
        apply le_mul_of_one_le_left (by positivity) htau

end KappaOmega2
