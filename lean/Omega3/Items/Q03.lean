import Omega3.Statements
import Palprimes.Digits.LemmaThree

namespace Omega3

open Finset Palprimes

/-! Item Q03: exact fourth moment mod `p²` of `g_J`.  Plan in reports/Q03.md. -/

lemma q3_ee_conj (a : ℝ) : (starRingEnd ℂ) (ee a) = ee (-a) := by
  unfold ee
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat, Complex.ofReal_neg]
  ring

lemma q3_ee_add (a c : ℝ) : ee (a + c) = ee a * ee c := by
  unfold ee
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma q3_ee_zero : ee 0 = 1 := by simp [ee]

lemma q3_ee_mul_conj (a b y : ℝ) :
    ee (a * y) * (starRingEnd ℂ) (ee (b * y)) = ee ((a - b) * y) := by
  rw [q3_ee_conj, ← q3_ee_add]
  congr 1
  ring

/-- Orthogonality for frequencies not divisible by `q`. -/
lemma q3_orth (q : ℕ) (hq : 0 < q) (β : ℝ) (m : ℤ) (hm : ¬ (q : ℤ) ∣ m) :
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
lemma q3_core {ι : Type*} (S : Finset ι) (A : ι → ℝ) (ω : ι → ℤ) (q : ℕ) (hq : 0 < q) (β : ℝ)
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
    linear_combination ((A σ : ℂ) * (A τ : ℂ)) * q3_ee_mul_conj (ω σ : ℝ) (ω τ : ℝ) ((h : ℝ) / q + β)
  rw [Complex.ofReal_sum]
  simp_rw [hx]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := range q)]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [Finset.sum_eq_single σ]
  · simp only [sub_self, zero_mul, q3_ee_zero]
    rw [← Finset.mul_sum]
    simp [sq]
    ring
  · intro τ hτ hne
    rw [← Finset.mul_sum]
    have hd : ¬ (q : ℤ) ∣ ω σ - ω τ := fun hd => hne (hinj σ hσ τ hτ hd).symm
    have o := q3_orth q hq β (ω σ - ω τ) hd
    push_cast at o
    rw [o, mul_zero]
  · intro h; exact absurd hσ h

/-! ### Squaring `G_g` -/

def q3cc (b : ℕ) (g : ℕ → ℝ) (s : ℕ) : ℝ :=
  ∑ i ∈ range (s + 1), if i < b ∧ s - i < b then g i * g (s - i) else 0

lemma q3_mw4 (b : ℕ) (g : ℕ → ℝ) : mw4 b g = ∑ s ∈ range (2 * b - 1), q3cc b g s ^ 2 := rfl

def q3ccC (M : ℕ) (γ : ℕ → ℂ) (s : ℕ) : ℂ :=
  ∑ i ∈ Finset.range M, if i ≤ s ∧ s - i < M then γ i * γ (s - i) else 0

lemma q3_sq_expand (M : ℕ) (γ : ℕ → ℂ) (y : ℝ) :
    (∑ n ∈ Finset.range M, γ n * ee ((n : ℝ) * y)) ^ 2 =
      ∑ s ∈ Finset.range (2 * M - 1), q3ccC M γ s * ee ((s : ℝ) * y) := by
  unfold q3ccC
  rw [sq, Finset.sum_mul_sum]
  simp_rw [Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < M := Finset.mem_range.mp hi
  have hsub : (Finset.range M).image (fun j => i + j) ⊆ Finset.range (2 * M - 1) := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    simp only [Finset.mem_range] at hj ⊢
    omega
  have hzero : ∀ x ∈ Finset.range (2 * M - 1), x ∉ (Finset.range M).image (fun j => i + j) →
      (if i ≤ x ∧ x - i < M then γ i * γ (x - i) else 0) * ee ((x : ℝ) * y) = 0 := by
    intro x _ hnot
    rw [if_neg, zero_mul]
    rintro ⟨h1, h2⟩
    apply hnot
    rw [Finset.mem_image]
    exact ⟨x - i, Finset.mem_range.mpr h2, by show i + (x - i) = x; omega⟩
  rw [← Finset.sum_subset hsub hzero, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro j hj
    have hj' : j < M := Finset.mem_range.mp hj
    have h1 : i ≤ i + j ∧ i + j - i < M := ⟨by omega, by omega⟩
    show γ i * ee ((i : ℝ) * y) * (γ j * ee ((j : ℝ) * y)) =
      (if i ≤ i + j ∧ i + j - i < M then γ i * γ (i + j - i) else 0) * ee (((i + j : ℕ) : ℝ) * y)
    rw [if_pos h1, Nat.add_sub_cancel_left, Nat.cast_add, add_mul, q3_ee_add]
    ring
  · intro x _ z _ hxz
    simpa using hxz

lemma q3_Gg_sq (b : ℕ) (g : ℕ → ℝ) (t : ℝ) :
    Gg b g t ^ 2 = ∑ s ∈ range (2 * b - 1), ((q3cc b g s : ℝ) : ℂ) * ee ((s : ℝ) * t) := by
  unfold Gg
  rw [q3_sq_expand b (fun a => (g a : ℂ)) t]
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  unfold q3ccC q3cc
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  have : (range b).filter (fun i => i ≤ s ∧ s - i < b) = (range (s + 1)).filter (fun i => i < b ∧ s - i < b) := by
    ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [this]
  push_cast
  rfl

/-! ### Expansion of `g_J²` -/

lemma q3_ee_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ee (∑ i ∈ s, f i) = ∏ i ∈ s, ee (f i) := by
  unfold ee
  push_cast
  rw [Finset.mul_sum, Complex.exp_sum]

lemma q3_gJ_eq (b : ℕ) (g : ℕ → ℝ) (N j : ℕ) (hj : j ≤ N) (α : ℝ) :
    gJ b g N (Ico (N - j) N) α = ∏ i : Fin j, Gg b g ((cK b N (N - j + i) : ℝ) * α) := by
  unfold gJ
  rw [Finset.prod_Ico_eq_prod_range, show N - (N - j) = j by omega, Finset.prod_range]

lemma q3_expand (b : ℕ) (g : ℕ → ℝ) (N j : ℕ) (α : ℝ) :
    (∏ i : Fin j, Gg b g ((cK b N (N - j + i) : ℝ) * α)) ^ 2 =
      ∑ σ ∈ Fintype.piFinset (fun _ : Fin j => range (2 * b - 1)),
        ((∏ i, q3cc b g (σ i) : ℝ) : ℂ) *
          ee (((∑ i, (σ i : ℤ) * (cK b N (N - j + i) : ℤ) : ℤ) : ℝ) * α) := by
  rw [← Finset.prod_pow]
  simp_rw [q3_Gg_sq]
  rw [Finset.prod_univ_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Finset.prod_mul_distrib]
  congr 1
  · push_cast; rfl
  · rw [← q3_ee_sum]
    congr 1
    push_cast
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring

lemma q3_sum_sq (b : ℕ) (g : ℕ → ℝ) (j : ℕ) :
    ∑ σ ∈ Fintype.piFinset (fun _ : Fin j => range (2 * b - 1)), (∏ i, q3cc b g (σ i)) ^ 2 =
      mw4 b g ^ j := by
  simp_rw [← Finset.prod_pow]
  rw [← Finset.prod_univ_sum (fun _ : Fin j => range (2 * b - 1)) (fun _ s => q3cc b g s ^ 2)]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, q3_mw4]

/-! ### Injectivity of the frequencies modulo `p²` -/

lemma q3_geom (b j : ℕ) (hb : 2 ≤ b) :
    ((b : ℤ) - 1) * ∑ i ∈ range j, ((b : ℤ) ^ i + (b : ℤ) ^ (2 * j - i)) <
      (b : ℤ) ^ (2 * j + 1) := by
  have h1 : ∑ i ∈ range j, (b : ℤ) ^ (2 * j - i) = (b : ℤ) ^ (j + 1) * ∑ i ∈ range j, (b : ℤ) ^ i := by
    rw [Finset.mul_sum, ← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [← pow_add]
    congr 1
    omega
  rw [Finset.sum_add_distrib, h1]
  have h2 := geom_sum_mul (b : ℤ) j
  have hb' : (2 : ℤ) ≤ b := by exact_mod_cast hb
  have hp : (b : ℤ) ^ j < (b : ℤ) ^ (j + 1) := by
    apply pow_lt_pow_right₀ (by omega) (by omega)
  have : ((b : ℤ) - 1) * ((∑ i ∈ range j, (b : ℤ) ^ i) + (b : ℤ) ^ (j + 1) * ∑ i ∈ range j, (b : ℤ) ^ i)
      = ((b : ℤ) ^ j - 1) * (1 + (b : ℤ) ^ (j + 1)) := by
    rw [← h2]; ring
  have e : (b : ℤ) ^ (2 * j + 1) = (b : ℤ) ^ j * (b : ℤ) ^ (j + 1) := by
    rw [← pow_add]; congr 1; ring
  rw [this, e]
  nlinarith [hp]

lemma q3_cK (b N j i : ℕ) (hj : j ≤ N) (hi : i < j) :
    (cK b N (N - j + i) : ℤ) = (b : ℤ) ^ (N - j) * ((b : ℤ) ^ i + (b : ℤ) ^ (2 * j - i)) := by
  unfold cK
  rw [if_pos (by omega)]
  push_cast
  rw [mul_add, ← pow_add, ← pow_add]
  congr 2 <;> omega

lemma q3_inj (b N j p : ℕ) (hb : 2 ≤ b) (hj : 1 ≤ j) (hjN : j < N) (hp : p.Prime) (hpb : ¬ p ∣ b)
    (hbig : 2 * b ^ (2 * j + 1) ≤ p ^ 2) (σ τ : Fin j → ℕ)
    (hσ : σ ∈ Fintype.piFinset (fun _ : Fin j => range (2 * b - 1)))
    (hτ : τ ∈ Fintype.piFinset (fun _ : Fin j => range (2 * b - 1)))
    (hd : ((p ^ 2 : ℕ) : ℤ) ∣ (∑ i, (σ i : ℤ) * (cK b N (N - j + i) : ℤ)) -
        ∑ i, (τ i : ℤ) * (cK b N (N - j + i) : ℤ)) : σ = τ := by
  rw [Fintype.mem_piFinset] at hσ hτ
  set F : Fin j → ℤ := fun i => (σ i : ℤ) - τ i with hF
  have hFb : ∀ i, |F i| ≤ 2 * (b : ℤ) - 2 := by
    intro i
    have h1 := Finset.mem_range.mp (hσ i)
    have h2 := Finset.mem_range.mp (hτ i)
    show |(σ i : ℤ) - τ i| ≤ _
    rw [abs_le]
    constructor <;> omega
  set V : ℤ := ∑ i : Fin j, F i * ((b : ℤ) ^ (i : ℕ) + (b : ℤ) ^ (2 * j - i)) with hV
  have hdiff : (∑ i, (σ i : ℤ) * (cK b N (N - j + i) : ℤ)) -
        ∑ i, (τ i : ℤ) * (cK b N (N - j + i) : ℤ) = (b : ℤ) ^ (N - j) * V := by
    rw [← Finset.sum_sub_distrib, hV, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← sub_mul, q3_cK b N j i (by omega) i.2, hF]
    ring
  rw [hdiff] at hd
  have hcop : IsCoprime (((p ^ 2 : ℕ) : ℤ)) ((b : ℤ) ^ (N - j)) := by
    have h1 : Nat.Coprime p b := (Nat.Prime.coprime_iff_not_dvd hp).2 hpb
    have h2 : Nat.Coprime (p ^ 2) (b ^ (N - j)) := Nat.Coprime.pow _ _ h1
    have := Nat.isCoprime_iff_coprime.2 h2
    simpa using this
  have hV1 : ((p ^ 2 : ℕ) : ℤ) ∣ V := hcop.dvd_of_dvd_mul_left hd
  have hVb : |V| < ((p ^ 2 : ℕ) : ℤ) := by
    have hb1 : |V| ≤ ∑ i : Fin j, |F i| * ((b : ℤ) ^ (i : ℕ) + (b : ℤ) ^ (2 * j - i)) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (b : ℤ) ^ (i : ℕ) + (b : ℤ) ^ (2 * j - i))]
    have hb2 : ∑ i : Fin j, |F i| * ((b : ℤ) ^ (i : ℕ) + (b : ℤ) ^ (2 * j - i)) ≤
        ∑ i : Fin j, (2 * (b : ℤ) - 2) * ((b : ℤ) ^ (i : ℕ) + (b : ℤ) ^ (2 * j - i)) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (hFb i) (by positivity)
    rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun i => (b : ℤ) ^ i + (b : ℤ) ^ (2 * j - i)) j] at hb2
    have hg := q3_geom b j hb
    have hbig' : (2 : ℤ) * (b : ℤ) ^ (2 * j + 1) ≤ ((p ^ 2 : ℕ) : ℤ) := by exact_mod_cast hbig
    calc |V| ≤ _ := hb1.trans hb2
      _ < ((p ^ 2 : ℕ) : ℤ) := by nlinarith
  have hV0 : V = 0 := Int.eq_zero_of_abs_lt_dvd hV1 hVb
  rw [hV0, mul_zero] at hdiff
  -- apply Proposition S (a)
  let s : ℕ → ℤ := fun k => if h : N - j ≤ k ∧ k < N then F ⟨k - (N - j), by omega⟩ else 0
  have hsum : ∑ k ∈ range (N + 1), s k * (cK b N k : ℤ) = 0 := by
    have hsub : Ico (N - j) N ⊆ range (N + 1) := by
      intro k hk; simp only [Finset.mem_Ico, Finset.mem_range] at hk ⊢; omega
    rw [← Finset.sum_subset hsub (by
      intro k hk hk'
      have : ¬ (N - j ≤ k ∧ k < N) := by
        simp only [Finset.mem_Ico, Finset.mem_range] at hk hk'; omega
      simp only [s, dif_neg this, zero_mul]),
      Finset.sum_Ico_eq_sum_range, show N - (N - j) = j by omega, Finset.sum_range]
    rw [← hdiff, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hc : N - j ≤ N - j + (i : ℕ) ∧ N - j + (i : ℕ) < N := ⟨by omega, by have := i.2; omega⟩
    simp only [s, dif_pos hc]
    have : (⟨N - j + (i : ℕ) - (N - j), by omega⟩ : Fin j) = i := Fin.ext (by simp)
    rw [this, hF]
    ring
  have hz := sum_cK_eq_zero b N hb s (by
    intro k hk
    by_cases h : N - j ≤ k ∧ k < N
    · simp only [s, dif_pos h]; exact hFb _
    · simp only [s, dif_neg h]; simp; omega) hsum
  funext i
  have := hz (N - j + (i : ℕ)) (by have := i.2; omega)
  have hc : N - j ≤ N - j + (i : ℕ) ∧ N - j + (i : ℕ) < N := ⟨by omega, by have := i.2; omega⟩
  simp only [s, dif_pos hc] at this
  have e : (⟨N - j + (i : ℕ) - (N - j), by omega⟩ : Fin j) = i := Fin.ext (by simp)
  rw [e] at this
  have : (σ i : ℤ) = τ i := by simpa [hF, sub_eq_zero] using this
  exact_mod_cast this

theorem itemQ03 : ItemQ03 := by
  intro b g N j p β hb hj hjN hp hpb hbig
  have hq : 0 < p ^ 2 := pow_pos hp.pos 2
  have h1 : ∀ h ∈ range (p ^ 2), ‖gJ b g N (Ico (N - j) N) ((h : ℝ) / (p ^ 2 : ℕ) + β)‖ ^ 4 =
      ‖∑ σ ∈ Fintype.piFinset (fun _ : Fin j => range (2 * b - 1)),
        (((∏ i, q3cc b g (σ i) : ℝ)) : ℂ) *
          ee (((∑ i, (σ i : ℤ) * (cK b N (N - j + i) : ℤ) : ℤ) : ℝ) *
            ((h : ℝ) / (p ^ 2 : ℕ) + β))‖ ^ 2 := by
    intro h _
    rw [← q3_expand, q3_gJ_eq b g N j (by omega), norm_pow]
    ring
  rw [Finset.sum_congr rfl h1]
  rw [q3_core (Fintype.piFinset (fun _ : Fin j => range (2 * b - 1)))
    (fun σ => ∏ i, q3cc b g (σ i))
    (fun σ => ∑ i, (σ i : ℤ) * (cK b N (N - j + i) : ℤ)) (p ^ 2) hq β
    (by
      intro σ hσ τ hτ hd
      exact q3_inj b N j p hb hj hjN hp hpb hbig σ τ hσ hτ hd), q3_sum_sq]
  push_cast
  ring

end Omega3
