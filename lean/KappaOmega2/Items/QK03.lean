import KappaOmega2.Items.LK09_Core

/-!
# QK03: route E′ for κ-palindromes (Parseval modulo `p²`)

`g_J(α)² = Σ_x w(x) e(b^{m−j} V(x) α)` (`LK09_Core`). For `p ∤ b` and `6 W b^{2j} ≤ p²` the frequencies are
distinct modulo `p²`: `p² ∣ b^{m−j}(V − V′)` gives `p² ∣ V − V′`, and `|V − V′| < 2 W b^{2j} ≤ p²`, so `V = V′`,
hence equal indices by Lemma E. Parseval modulo `p²` gives `p² Σ w² = p² m_w(4)^j m_M(4)`.
-/

namespace KappaOmega2

open Finset Palprimes

set_option linter.style.longLine false

lemma qk3_ee_conj (a : ℝ) : (starRingEnd ℂ) (ee a) = ee (-a) := by
  unfold ee
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat, Complex.ofReal_neg]
  ring

lemma qk3_ee_add (a c : ℝ) : ee (a + c) = ee a * ee c := by
  unfold ee
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma qk3_ee_zero : ee 0 = 1 := by simp [ee]

lemma qk3_ee_mul_conj (a b y : ℝ) :
    ee (a * y) * (starRingEnd ℂ) (ee (b * y)) = ee ((a - b) * y) := by
  rw [qk3_ee_conj, ← qk3_ee_add]
  congr 1
  ring

/-- Orthogonality for frequencies not divisible by `q`. -/
lemma qk3_orth (q : ℕ) (hq : 0 < q) (β : ℝ) (m : ℤ) (hm : ¬ (q : ℤ) ∣ m) :
    ∑ h ∈ Finset.range q, ee ((m : ℝ) * ((h : ℝ) / q + β)) = 0 := by
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((m : ℂ) / (q : ℂ))) :=
    ⟨_, rfl⟩
  have key : ∀ h : ℕ, ee ((m : ℝ) * ((h : ℝ) / q + β)) = ee ((m : ℝ) * β) * z ^ h := by
    intro h
    unfold ee
    rw [hz, ← Complex.exp_natCast_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [key]
  rw [← Finset.mul_sum]
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
    exact hm ⟨n, by rw [h6]; ring⟩
  have hzq : z ^ q = 1 := by
    rw [hz, ← Complex.exp_natCast_mul]
    have h7 : (q : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * ((m : ℂ) / (q : ℂ)))
        = (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      field_simp
    rw [h7, Complex.exp_int_mul_two_pi_mul_I]
  rw [geom_sum_eq hz1, hzq, sub_self, zero_div, mul_zero]

/-- Generic Parseval modulo `q` for a trigonometric polynomial with injective frequencies mod `q`. -/
lemma qk3_core {ι : Type*} (S : Finset ι) (A : ι → ℝ) (ω : ι → ℤ) (q : ℕ) (hq : 0 < q) (β : ℝ)
    (hinj : ∀ σ ∈ S, ∀ τ ∈ S, (q : ℤ) ∣ ω σ - ω τ → σ = τ) :
    ∑ h ∈ range q, ‖∑ σ ∈ S, (A σ : ℂ) * ee ((ω σ : ℝ) * ((h : ℝ) / q + β))‖ ^ 2 =
      (q : ℝ) * ∑ σ ∈ S, A σ ^ 2 := by
  classical
  apply Complex.ofReal_injective
  have hx : ∀ h : ℕ, ((‖∑ σ ∈ S, (A σ : ℂ) * ee ((ω σ : ℝ) * ((h : ℝ) / q + β))‖ ^ 2 : ℝ) : ℂ) =
      ∑ σ ∈ S, ∑ τ ∈ S, ((A σ : ℂ) * (A τ : ℂ)) * ee (((ω σ : ℝ) - (ω τ : ℝ)) * ((h : ℝ) / q + β)) := by
    intro h
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    apply Finset.sum_congr rfl
    intro τ _
    rw [map_mul, Complex.conj_ofReal]
    linear_combination ((A σ : ℂ) * (A τ : ℂ)) * qk3_ee_mul_conj (ω σ : ℝ) (ω τ : ℝ) ((h : ℝ) / q + β)
  rw [Complex.ofReal_sum]
  simp_rw [hx]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := range q)]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [Finset.sum_eq_single σ]
  · simp only [sub_self, zero_mul, qk3_ee_zero]
    rw [← Finset.mul_sum]
    simp [sq]
    ring
  · intro τ hτ hne
    rw [← Finset.mul_sum]
    have hd : ¬ (q : ℤ) ∣ ω σ - ω τ := fun hd => hne (hinj σ hσ τ hτ hd).symm
    have o := qk3_orth q hq β (ω σ - ω τ) hd
    push_cast at o
    rw [o, mul_zero]
  · intro h; exact absurd hσ h

open LK09 in
theorem itemQK03 : ItemQK03 := by
  intro b g N j p β hb hj hp hpb hbig
  classical
  have hW : (WK b N) = b ^ ellK N := rfl
  have hW1 : 1 ≤ WK b N := Nat.one_le_pow _ _ (by omega)
  have hq : 0 < p ^ 2 := pow_pos hp.pos 2
  set ω : Idx b (WK b N) j → ℤ := fun x => ((b ^ (mK N - j) * Vf b (ellK N) j (WK b N) x : ℕ) : ℤ) with hω
  have h1 : ∀ h ∈ range (p ^ 2), ‖gJK b g N j ((h : ℝ) / (p ^ 2 : ℕ) + β)‖ ^ 4 =
      ‖∑ x ∈ (univ : Finset (Idx b (WK b N) j)), (wt b g (WK b N) j x : ℂ) *
          ee (((ω x : ℤ) : ℝ) * ((h : ℝ) / (p ^ 2 : ℕ) + β))‖ ^ 2 := by
    intro h _
    have e4 : ∀ z : ℂ, ‖z‖ ^ 4 = ‖z ^ 2‖ ^ 2 := fun z => by rw [norm_pow]; ring
    rw [e4, gJK_sq b (by omega) g N j hj]
    refine congrArg (fun z : ℂ => ‖z‖ ^ 2) (Finset.sum_congr rfl (fun x _ => ?_))
    rw [hω]
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl h1]
  rw [qk3_core (univ : Finset (Idx b (WK b N) j)) (wt b g (WK b N) j) ω (p ^ 2) hq β ?_, sum_wt_sq b g (WK b N) j hW1]
  · push_cast; ring
  intro x _ y _ hd
  apply Vf_inj b (ellK N) j (WK b N) hb (ellK_pos N) hW x y
  have hdiff : ω x - ω y = (b : ℤ) ^ (mK N - j) * ((Vf b (ellK N) j (WK b N) x : ℤ) - (Vf b (ellK N) j (WK b N) y : ℤ)) := by
    rw [hω]; push_cast; ring
  rw [hdiff] at hd
  have hcop : IsCoprime (((p ^ 2 : ℕ) : ℤ)) ((b : ℤ) ^ (mK N - j)) := by
    have h1 : Nat.Coprime p b := (Nat.Prime.coprime_iff_not_dvd hp).2 hpb
    have h2 : Nat.Coprime (p ^ 2) (b ^ (mK N - j)) := Nat.Coprime.pow _ _ h1
    have := Nat.isCoprime_iff_coprime.2 h2
    simpa using this
  have hV1 := hcop.dvd_of_dvd_mul_left hd
  have hx := Vf_lt b (ellK N) j (WK b N) (by omega) hW x
  have hy := Vf_lt b (ellK N) j (WK b N) (by omega) hW y
  have hbig' : ((6 * (WK b N) * b ^ (2 * j) : ℕ) : ℤ) ≤ ((p ^ 2 : ℕ) : ℤ) := by exact_mod_cast hbig
  have hVb : |(Vf b (ellK N) j (WK b N) x : ℤ) - (Vf b (ellK N) j (WK b N) y : ℤ)| < ((p ^ 2 : ℕ) : ℤ) := by
    have hx' : ((Vf b (ellK N) j (WK b N) x : ℕ) : ℤ) < ((2 * (WK b N) * b ^ (2 * j) : ℕ) : ℤ) := by exact_mod_cast hx
    have hy' : ((Vf b (ellK N) j (WK b N) y : ℕ) : ℤ) < ((2 * (WK b N) * b ^ (2 * j) : ℕ) : ℤ) := by exact_mod_cast hy
    push_cast at hx' hy' hbig' ⊢
    have h0 : (0 : ℤ) ≤ ((WK b N) : ℤ) * (b : ℤ) ^ (2 * j) := by positivity
    rw [abs_lt]; constructor <;> nlinarith
  have := Int.eq_zero_of_abs_lt_dvd hV1 hVb
  omega

end KappaOmega2
