import Omega3.Statements
import Palprimes.Digits.LemmaThree

namespace Omega3

open Finset Palprimes

set_option linter.style.longLine false

lemma q2_ee_add (a c : ℝ) : ee (a + c) = ee a * ee c := by
  unfold ee
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma q2_ee_zero : ee 0 = 1 := by simp [ee]

lemma q2_ee_cos (t : ℝ) : ee t + ee (-t) = ((2 * Real.cos (2 * Real.pi * t) : ℝ) : ℂ) := by
  unfold ee
  have h1 : (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) = (((2 * Real.pi * t : ℝ)) : ℂ) * Complex.I := by
    push_cast; ring
  have h2 : (2 * (Real.pi : ℂ) * Complex.I * ((-t : ℝ) : ℂ)) = (-((2 * Real.pi * t : ℝ) : ℂ)) * Complex.I := by
    push_cast; ring
  rw [h1, h2, Complex.exp_mul_I, Complex.exp_mul_I]
  rw [Complex.cos_neg, Complex.sin_neg]
  push_cast
  ring

lemma q2_trigE (H : ℕ) (τ : ℕ → ℝ) (t : ℝ) :
    (trigEval H τ t : ℂ) = ∑ u ∈ Icc (-(H : ℤ)) H, (τ u.natAbs : ℂ) * ee ((u : ℝ) * t) := by
  induction H with
  | zero =>
    have : Icc (-((0 : ℕ) : ℤ)) ((0 : ℕ) : ℤ) = {0} := by
      ext u; simp only [Finset.mem_Icc, Finset.mem_singleton]; omega
    rw [this]
    simp [trigEval, q2_ee_zero]
  | succ H ih =>
    have e : Icc (-((H + 1 : ℕ) : ℤ)) ((H + 1 : ℕ) : ℤ) =
        insert (-((H + 1 : ℕ) : ℤ)) (insert ((H + 1 : ℕ) : ℤ) (Icc (-(H : ℤ)) H)) := by
      ext u; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
    have h1 : (-((H + 1 : ℕ) : ℤ)) ∉ insert ((H + 1 : ℕ) : ℤ) (Icc (-(H : ℤ)) H) := by
      simp only [Finset.mem_insert, Finset.mem_Icc, not_or]; push_cast; omega
    have h2 : ((H + 1 : ℕ) : ℤ) ∉ Icc (-(H : ℤ)) H := by
      simp only [Finset.mem_Icc]; push_cast; omega
    rw [e, Finset.sum_insert h1, Finset.sum_insert h2, ← ih]
    have hs : trigEval (H + 1) τ t = trigEval H τ t + 2 * (τ (H + 1) * Real.cos (2 * Real.pi * (((H + 1 : ℕ) : ℝ) * t))) := by
      unfold trigEval
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hX : 2 * Real.pi * ((H + 1 : ℕ) : ℝ) * t = 2 * Real.pi * (((H + 1 : ℕ) : ℝ) * t) := by ring
      rw [hX]
      ring
    rw [hs]
    have hn1 : (-((H + 1 : ℕ) : ℤ)).natAbs = H + 1 := by omega
    have hn2 : (((H + 1 : ℕ) : ℤ)).natAbs = H + 1 := by omega
    rw [hn1, hn2]
    simp only [Int.cast_neg, Int.cast_natCast]
    have h3 : ee (-((H + 1 : ℕ) : ℝ) * t) = ee (-(((H + 1 : ℕ) : ℝ) * t)) := by congr 1; ring
    have := q2_ee_cos (((H + 1 : ℕ) : ℝ) * t)
    rw [h3]
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat] at this ⊢
    linear_combination (-(τ (H + 1) : ℂ)) * this

lemma q2_ee_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ee (∑ i ∈ s, f i) = ∏ i ∈ s, ee (f i) := by
  unfold ee
  push_cast
  rw [Finset.mul_sum, Complex.exp_sum]

/-- Expansion of the product of majorants over `K`. -/
lemma q2_prod (b H N : ℕ) (τ : ℕ → ℝ) (K : Finset ℕ) (x : ℝ) :
    ((∏ k ∈ K, trigEval H τ ((cK b N k : ℝ) * x) : ℝ) : ℂ) =
      ∑ u ∈ Fintype.piFinset (fun _ : K => Icc (-(H : ℤ)) H),
        ((∏ i : K, τ (u i).natAbs : ℝ) : ℂ) *
          ee (((∑ i : K, u i * (cK b N i : ℤ) : ℤ) : ℝ) * x) := by
  classical
  push_cast
  rw [← Finset.prod_coe_sort K]
  simp_rw [q2_trigE]
  rw [Finset.prod_univ_sum (fun _ : K => Icc (-(H : ℤ)) H) (fun (i : K) (u : ℤ) => (τ u.natAbs : ℂ) * ee ((u : ℝ) * ((cK b N i : ℝ) * x)))]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.prod_mul_distrib, ← q2_ee_sum]
  congr 1
  congr 1
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring
/-- Full orthogonality. -/

lemma q2_norm_ee (t : ℝ) : ‖ee t‖ = 1 := by
  unfold ee
  have := Complex.norm_exp_ofReal_mul_I (2 * Real.pi * t)
  rw [← this]
  congr 2
  push_cast
  ring

lemma q2_orth (q : ℕ) (hq : 0 < q) (m : ℤ) :
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

lemma q2_orth_beta (q : ℕ) (hq : 0 < q) (β : ℝ) (m : ℤ) :
    ∑ h ∈ Finset.range q, ee ((m : ℝ) * ((h : ℝ) / q + β)) =
      if (q : ℤ) ∣ m then (q : ℂ) * ee ((m : ℝ) * β) else 0 := by
  have : ∀ h : ℕ, ee ((m : ℝ) * ((h : ℝ) / q + β)) = ee ((m : ℝ) * ((h : ℝ) / q)) * ee ((m : ℝ) * β) := by
    intro h; rw [← q2_ee_add]; congr 1; ring
  simp_rw [this]
  rw [← Finset.sum_mul, q2_orth q hq m]
  split_ifs <;> simp

noncomputable def q2m (b N : ℕ) (K : Finset ℕ) (u : K → ℤ) : ℤ := ∑ i : K, u i * (cK b N i : ℤ)

lemma q2_single (b H N : ℕ) (τ : ℕ → ℝ) (K : Finset ℕ) (β : ℝ) (q : ℕ) (hq : 0 < q) :
    |∑ h ∈ range q, ∏ k ∈ K, trigEval H τ ((cK b N k : ℝ) * ((h : ℝ) / q + β)) - q * τ 0 ^ K.card| ≤
      ∑ u ∈ (Fintype.piFinset (fun _ : K => Icc (-(H : ℤ)) H)).erase (fun _ => 0),
        |∏ i : K, τ (u i).natAbs| * (if (q : ℤ) ∣ q2m b N K u then (q : ℝ) else 0) := by
  classical
  set pi := Fintype.piFinset (fun _ : K => Icc (-(H : ℤ)) H) with hpi
  have h0 : (fun _ : K => (0 : ℤ)) ∈ pi := by
    rw [hpi, Fintype.mem_piFinset]; intro i; simp
  have hc : ((∑ h ∈ range q, ∏ k ∈ K, trigEval H τ ((cK b N k : ℝ) * ((h : ℝ) / q + β)) : ℝ) : ℂ) =
      ∑ u ∈ pi, ((∏ i : K, τ (u i).natAbs : ℝ) : ℂ) *
        (if (q : ℤ) ∣ q2m b N K u then (q : ℂ) * ee ((q2m b N K u : ℝ) * β) else 0) := by
    rw [Complex.ofReal_sum]
    simp_rw [q2_prod]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    rw [← Finset.mul_sum]
    congr 1
    exact q2_orth_beta q hq β (q2m b N K u)
  have hsplit := Finset.add_sum_erase pi (fun u => ((∏ i : K, τ (u i).natAbs : ℝ) : ℂ) *
        (if (q : ℤ) ∣ q2m b N K u then (q : ℂ) * ee ((q2m b N K u : ℝ) * β) else 0)) h0
  have hu0 : ((∏ i : K, τ ((fun _ : K => (0 : ℤ)) i).natAbs : ℝ) : ℂ) *
        (if (q : ℤ) ∣ q2m b N K (fun _ => 0) then (q : ℂ) * ee ((q2m b N K (fun _ => 0) : ℝ) * β) else 0) =
      ((q * τ 0 ^ K.card : ℝ) : ℂ) := by
    have : q2m b N K (fun _ => 0) = 0 := by simp [q2m]
    rw [this]
    simp [q2_ee_zero, Finset.prod_const, Finset.card_univ]
    ring
  rw [hu0] at hsplit
  have hD : ((∑ h ∈ range q, ∏ k ∈ K, trigEval H τ ((cK b N k : ℝ) * ((h : ℝ) / q + β)) - q * τ 0 ^ K.card : ℝ) : ℂ) =
      ∑ u ∈ pi.erase (fun _ => 0), ((∏ i : K, τ (u i).natAbs : ℝ) : ℂ) *
        (if (q : ℤ) ∣ q2m b N K u then (q : ℂ) * ee ((q2m b N K u : ℝ) * β) else 0) := by
    rw [Complex.ofReal_sub, hc, ← hsplit]; ring
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hD]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun u _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  split_ifs
  · rw [norm_mul, q2_norm_ee, mul_one]; simp
  · simp
lemma q2_geom (b j : ℕ) (hb : 2 ≤ b) :
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


lemma q2_sum_cK_lt (b N : ℕ) (hb : 2 ≤ b) :
    (∑ k ∈ range N, (cK b N k : ℤ)) < (b : ℤ) ^ (2 * N + 1) := by
  have h := q2_geom b N hb
  have hb' : (1 : ℤ) ≤ (b : ℤ) - 1 := by
    have : (2 : ℤ) ≤ b := by exact_mod_cast hb
    linarith
  have hS : ∑ k ∈ range N, (cK b N k : ℤ) = ∑ i ∈ range N, ((b : ℤ) ^ i + (b : ℤ) ^ (2 * N - i)) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    simp [cK, hk]
  rw [hS]
  have hnn : 0 ≤ ∑ i ∈ range N, ((b : ℤ) ^ i + (b : ℤ) ^ (2 * N - i)) :=
    Finset.sum_nonneg (fun i _ => by positivity)
  nlinarith

lemma q2_sym (f : ℕ → ℝ) (H : ℕ) :
    ∑ v ∈ Icc (-(H : ℤ)) H, f v.natAbs = f 0 + 2 * ∑ u ∈ Icc 1 H, f u := by
  induction H with
  | zero =>
    have : Icc (-((0 : ℕ) : ℤ)) ((0 : ℕ) : ℤ) = {0} := by
      ext u; simp only [Finset.mem_Icc, Finset.mem_singleton]; omega
    rw [this]; simp
  | succ H ih =>
    have e : Icc (-((H + 1 : ℕ) : ℤ)) ((H + 1 : ℕ) : ℤ) =
        insert (-((H + 1 : ℕ) : ℤ)) (insert ((H + 1 : ℕ) : ℤ) (Icc (-(H : ℤ)) H)) := by
      ext u; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
    have h1 : (-((H + 1 : ℕ) : ℤ)) ∉ insert ((H + 1 : ℕ) : ℤ) (Icc (-(H : ℤ)) H) := by
      simp only [Finset.mem_insert, Finset.mem_Icc, not_or]; push_cast; omega
    have h2 : ((H + 1 : ℕ) : ℤ) ∉ Icc (-(H : ℤ)) H := by
      simp only [Finset.mem_Icc]; push_cast; omega
    rw [e, Finset.sum_insert h1, Finset.sum_insert h2, ih, Finset.sum_Icc_succ_top (by omega)]
    have hn1 : (-((H + 1 : ℕ) : ℤ)).natAbs = H + 1 := by omega
    have hn2 : (((H + 1 : ℕ) : ℤ)).natAbs = H + 1 := by omega
    rw [hn1, hn2]; ring

lemma q2_sum_P (H : ℕ) (τ : ℕ → ℝ) (K : Finset ℕ) :
    ∑ u ∈ Fintype.piFinset (fun _ : K => Icc (-(H : ℤ)) H), |∏ i : K, τ (u i).natAbs| =
      trigMass H τ ^ K.card := by
  classical
  have h1 : ∀ u : K → ℤ, |∏ i : K, τ (u i).natAbs| = ∏ i : K, |τ (u i).natAbs| := fun u => by
    rw [Finset.abs_prod]
  simp_rw [h1]
  rw [← Finset.prod_univ_sum (fun _ : K => Icc (-(H : ℤ)) H) (fun (_ : K) (v : ℤ) => |τ v.natAbs|)]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe]
  congr 1
  rw [q2_sym (fun n => |τ n|) H]
  unfold trigMass
  ring

lemma q2_m_facts (b H N : ℕ) (hb : 2 ≤ b) (hH : H ≤ 2 * b - 2) (K : Finset ℕ) (hK : K ⊆ Ico 1 N)
    (u : K → ℤ) (hu : u ∈ Fintype.piFinset (fun _ : K => Icc (-(H : ℤ)) H)) (hne : u ≠ fun _ => 0) :
    q2m b N K u ≠ 0 ∧ |q2m b N K u| ≤ 2 * (H : ℤ) * (b : ℤ) ^ (2 * N + 1) := by
  classical
  rw [Fintype.mem_piFinset] at hu
  have hKN : K ⊆ range N := fun k hk => by
    have := hK hk; rw [Finset.mem_Ico] at this; rw [Finset.mem_range]; omega
  refine ⟨?_, ?_⟩
  · intro h0
    apply hne
    set s : ℕ → ℤ := fun k => if h : k ∈ K then u ⟨k, h⟩ else 0 with hs
    have hbound : ∀ k ≤ N, |s k| ≤ 2 * (b : ℤ) - 2 := by
      intro k _
      by_cases hk : k ∈ K
      · simp only [hs, dif_pos hk]
        have := hu ⟨k, hk⟩
        rw [Finset.mem_Icc] at this
        have hH' : (H : ℤ) ≤ 2 * (b : ℤ) - 2 := by
          have : (H : ℤ) ≤ ((2 * b - 2 : ℕ) : ℤ) := by exact_mod_cast hH
          rw [Nat.cast_sub (by omega)] at this
          push_cast at this; linarith
        rw [abs_le]; constructor <;> linarith [this.1, this.2]
      · simp only [hs, dif_neg hk]; simp
        have : (0 : ℤ) ≤ (b : ℤ) := by positivity
        have : (2 : ℤ) ≤ b := by exact_mod_cast hb
        linarith
    have hq : q2m b N K u = ∑ k ∈ K, s k * (cK b N k : ℤ) := by
      unfold q2m
      rw [← Finset.sum_coe_sort K (fun k => s k * (cK b N k : ℤ))]
      apply Finset.sum_congr rfl
      intro i _
      simp [hs]
    have hsub : ∑ k ∈ K, s k * (cK b N k : ℤ) = ∑ k ∈ range (N + 1), s k * (cK b N k : ℤ) := by
      apply Finset.sum_subset (fun k hk => by
        have := hKN hk; rw [Finset.mem_range] at this ⊢; omega)
      intro k _ hk
      simp [hs, hk]
    have hsum : ∑ k ∈ range (N + 1), s k * (cK b N k : ℤ) = 0 := by
      rw [← hsub, ← hq, h0]
    have hz := sum_cK_eq_zero b N hb s hbound hsum
    funext i
    have := hz i (by have := hKN i.2; rw [Finset.mem_range] at this; omega)
    simpa [hs] using this
  · have hbd : ∀ i : K, |u i| ≤ H := by
      intro i
      have := hu i
      rw [Finset.mem_Icc] at this
      rw [abs_le]; constructor <;> linarith [this.1, this.2]
    calc |q2m b N K u| ≤ ∑ i : K, |u i * (cK b N i : ℤ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : K, (H : ℤ) * (cK b N i : ℤ) := by
          apply Finset.sum_le_sum; intro i _
          rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (cK b N i : ℤ))]
          exact mul_le_mul_of_nonneg_right (hbd i) (by positivity)
      _ = (H : ℤ) * ∑ k ∈ K, (cK b N k : ℤ) := by
          rw [← Finset.mul_sum, Finset.sum_coe_sort K (fun k => (cK b N k : ℤ))]
      _ ≤ (H : ℤ) * ∑ k ∈ range N, (cK b N k : ℤ) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Finset.sum_le_sum_of_subset_of_nonneg hKN
          intro k _ _; positivity
      _ ≤ 2 * (H : ℤ) * (b : ℤ) ^ (2 * N + 1) := by
          have := q2_sum_cK_lt b N hb
          have hH0 : (0 : ℤ) ≤ H := by positivity
          have h2 : (H : ℤ) * ∑ k ∈ range N, (cK b N k : ℤ) ≤ H * (b : ℤ) ^ (2 * N + 1) :=
            mul_le_mul_of_nonneg_left this.le hH0
          have h3 : 0 ≤ (H : ℤ) * (b : ℤ) ^ (2 * N + 1) := by positivity
          linarith

lemma q2_count (Q M : ℕ) (hQ : 2 ≤ Q) (m : ℤ) (hm0 : m ≠ 0) (hmM : |m| ≤ (M : ℤ)) :
    ((((Ico Q (2 * Q)).filter Nat.Prime).filter (fun p : ℕ => (p : ℤ) ∣ m)).card : ℝ) ≤
      Real.log M / Real.log Q := by
  classical
  set S := ((Ico Q (2 * Q)).filter Nat.Prime).filter (fun p : ℕ => (p : ℤ) ∣ m) with hS
  have hSp : ∀ p ∈ S, p.Prime := fun p hp => (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).2
  have hdvd : (∏ p ∈ S, p) ∣ m.natAbs := by
    apply Finset.prod_primes_dvd
    · intro p hp; exact (hSp p hp).prime
    · intro p hp
      exact Int.natCast_dvd.1 (Finset.mem_filter.1 hp).2
  have hmn : m.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hm0
  have h1 : (∏ p ∈ S, p) ≤ m.natAbs := Nat.le_of_dvd (Nat.pos_of_ne_zero hmn) hdvd
  have h2 : Q ^ S.card ≤ ∏ p ∈ S, p := Finset.pow_card_le_prod S (fun p => p) Q (fun p hp => by
    have := (Finset.mem_Ico.1 (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).1).1
    exact this)
  have h3 : m.natAbs ≤ M := by
    have : ((m.natAbs : ℕ) : ℤ) ≤ M := by rw [Int.natCast_natAbs]; exact hmM
    exact_mod_cast this
  have h4 : (Q : ℝ) ^ S.card ≤ M := by exact_mod_cast h2.trans (h1.trans h3)
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hQ1 : 0 < Real.log Q := Real.log_pos (by exact_mod_cast (by omega : 1 < Q))
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le (pow_pos hQ0 _) h4
  rw [le_div_iff₀ hQ1]
  have := Real.log_le_log (pow_pos hQ0 _) h4
  rw [Real.log_pow] at this
  exact this

lemma q2_abstract (b H N Q : ℕ) (τ : ℕ → ℝ) (K : Finset ℕ) (β : ℝ) (hb : 2 ≤ b) (hH : H ≤ 2 * b - 2)
    (hK : K ⊆ Ico 1 N) (hQ : 2 ≤ Q) (qf : ℕ → ℕ) (W : ℝ) (hW0 : 0 ≤ W)
    (hqpos : ∀ p ∈ (Ico Q (2 * Q)).filter Nat.Prime, 0 < qf p)
    (hqW : ∀ p ∈ (Ico Q (2 * Q)).filter Nat.Prime, (qf p : ℝ) ≤ W)
    (hqd : ∀ p ∈ (Ico Q (2 * Q)).filter Nat.Prime, ∀ m : ℤ, (qf p : ℤ) ∣ m → (p : ℤ) ∣ m) :
    ∑ p ∈ (Ico Q (2 * Q)).filter Nat.Prime, ∑ h ∈ range (qf p),
        ∏ k ∈ K, trigEval H τ ((cK b N k : ℝ) * ((h : ℝ) / (qf p : ℝ) + β)) ≤
      (∑ p ∈ (Ico Q (2 * Q)).filter Nat.Prime, (qf p : ℝ)) * τ 0 ^ K.card +
        W * (Real.log (2 * H * (b : ℝ) ^ (2 * N + 1)) / Real.log Q) * trigMass H τ ^ K.card := by
  classical
  set Pr := (Ico Q (2 * Q)).filter Nat.Prime with hPr
  set pi := Fintype.piFinset (fun _ : K => Icc (-(H : ℤ)) H) with hpi
  set M : ℕ := 2 * H * b ^ (2 * N + 1) with hM
  have hMcast : (2 * (H : ℝ) * (b : ℝ) ^ (2 * N + 1)) = (M : ℝ) := by rw [hM]; push_cast; ring
  rw [hMcast]
  have hℓ : 0 ≤ Real.log M / Real.log Q := by
    have hQ1 : 0 < Real.log Q := Real.log_pos (by exact_mod_cast (by omega : 1 < Q))
    apply div_nonneg _ hQ1.le
    by_cases hM0 : M = 0
    · rw [hM0]; simp
    · exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hM0)
  -- per prime
  have hper : ∀ p ∈ Pr, ∑ h ∈ range (qf p), ∏ k ∈ K, trigEval H τ ((cK b N k : ℝ) * ((h : ℝ) / (qf p : ℝ) + β)) ≤
      (qf p : ℝ) * τ 0 ^ K.card + ∑ u ∈ pi.erase (fun _ => 0), |∏ i : K, τ (u i).natAbs| *
        (if (qf p : ℤ) ∣ q2m b N K u then (qf p : ℝ) else 0) := by
    intro p hp
    have := q2_single b H N τ K β (qf p) (hqpos p hp)
    have := (abs_le.1 this).2
    linarith
  refine (Finset.sum_le_sum hper).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  apply add_le_add le_rfl
  rw [Finset.sum_comm]
  have hfin : ∀ u ∈ pi.erase (fun _ => 0), ∑ p ∈ Pr, |∏ i : K, τ (u i).natAbs| *
      (if (qf p : ℤ) ∣ q2m b N K u then (qf p : ℝ) else 0) ≤
      |∏ i : K, τ (u i).natAbs| * (W * (Real.log M / Real.log Q)) := by
    intro u hu
    have hu' := Finset.mem_erase.1 hu
    obtain ⟨hm0, hmb⟩ := q2_m_facts b H N hb hH K hK u hu'.2 hu'.1
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have h1 : ∑ p ∈ Pr, (if (qf p : ℤ) ∣ q2m b N K u then (qf p : ℝ) else 0) ≤
        ∑ p ∈ Pr, (if (p : ℤ) ∣ q2m b N K u then W else 0) := by
      apply Finset.sum_le_sum
      intro p hp
      by_cases hd : (qf p : ℤ) ∣ q2m b N K u
      · rw [if_pos hd, if_pos (hqd p hp _ hd)]; exact hqW p hp
      · rw [if_neg hd]; split_ifs <;> linarith
    refine h1.trans ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    apply mul_le_mul_of_nonneg_left _ hW0
    have := q2_count Q M hQ (q2m b N K u) hm0 (by rw [hM]; push_cast; linarith)
    exact this
  calc ∑ u ∈ pi.erase (fun _ => 0), ∑ p ∈ Pr, |∏ i : K, τ (u i).natAbs| *
        (if (qf p : ℤ) ∣ q2m b N K u then (qf p : ℝ) else 0)
      ≤ ∑ u ∈ pi.erase (fun _ => 0), |∏ i : K, τ (u i).natAbs| * (W * (Real.log M / Real.log Q)) :=
        Finset.sum_le_sum hfin
    _ ≤ ∑ u ∈ pi, |∏ i : K, τ (u i).natAbs| * (W * (Real.log M / Real.log Q)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        intro u _ _; exact mul_nonneg (abs_nonneg _) (mul_nonneg hW0 hℓ)
    _ = W * (Real.log M / Real.log Q) * trigMass H τ ^ K.card := by
        rw [← Finset.sum_mul, hpi, q2_sum_P]; ring

lemma q2_card_Pr (Q : ℕ) : (((Ico Q (2 * Q)).filter Nat.Prime).card : ℝ) ≤ Q := by
  have h1 : ((Ico Q (2 * Q)).filter Nat.Prime).card ≤ (Ico Q (2 * Q)).card := Finset.card_filter_le _ _
  have h2 : (Ico Q (2 * Q)).card = Q := by simp; omega
  have : ((Ico Q (2 * Q)).filter Nat.Prime).card ≤ Q := by omega
  exact_mod_cast this

theorem itemQ02 : ItemQ02 := by
  classical
  intro b H N Q τ K β hb hH hτ hK hQ
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hpow : 0 ≤ τ 0 ^ K.card := pow_nonneg hτ _
  have hcard := q2_card_Pr Q
  constructor
  · have := q2_abstract b H N Q τ K β hb hH hK hQ (fun p => p ^ 2) (4 * (Q : ℝ) ^ 2) (by positivity)
      (fun p hp => pow_pos (Finset.mem_filter.1 hp).2.pos 2)
      (fun p hp => by
        have hpQ := (Finset.mem_Ico.1 (Finset.mem_filter.1 hp).1).2
        have : (p : ℝ) < 2 * Q := by exact_mod_cast hpQ
        have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
        push_cast
        nlinarith)
      (fun p hp m hm => by
        have : (p : ℤ) ∣ ((p ^ 2 : ℕ) : ℤ) := by push_cast; exact dvd_pow_self _ (by norm_num)
        exact this.trans hm)
    refine this.trans ?_
    have hsum : ∑ p ∈ (Ico Q (2 * Q)).filter Nat.Prime, (((fun p => p ^ 2) p : ℕ) : ℝ) ≤ 4 * (Q : ℝ) ^ 3 := by
      calc _ ≤ ∑ p ∈ (Ico Q (2 * Q)).filter Nat.Prime, 4 * (Q : ℝ) ^ 2 := by
            apply Finset.sum_le_sum
            intro p hp
            have hpQ := (Finset.mem_Ico.1 (Finset.mem_filter.1 hp).1).2
            have : (p : ℝ) < 2 * Q := by exact_mod_cast hpQ
            have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
            push_cast
            nlinarith
        _ = (((Ico Q (2 * Q)).filter Nat.Prime).card : ℝ) * (4 * (Q : ℝ) ^ 2) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ Q * (4 * (Q : ℝ) ^ 2) := mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = 4 * (Q : ℝ) ^ 3 := by ring
    have := mul_le_mul_of_nonneg_right hsum hpow
    simp only at this ⊢
    linarith
  · have := q2_abstract b H N Q τ K β hb hH hK hQ (fun p => p) (2 * (Q : ℝ)) (by positivity)
      (fun p hp => (Finset.mem_filter.1 hp).2.pos)
      (fun p hp => by
        have hpQ := (Finset.mem_Ico.1 (Finset.mem_filter.1 hp).1).2
        have : (p : ℝ) < 2 * Q := by exact_mod_cast hpQ
        exact this.le)
      (fun p hp m hm => hm)
    refine this.trans ?_
    have hsum : ∑ p ∈ (Ico Q (2 * Q)).filter Nat.Prime, (((fun p => p) p : ℕ) : ℝ) ≤ 4 * (Q : ℝ) ^ 2 := by
      calc _ ≤ ∑ p ∈ (Ico Q (2 * Q)).filter Nat.Prime, 2 * (Q : ℝ) := by
            apply Finset.sum_le_sum
            intro p hp
            have hpQ := (Finset.mem_Ico.1 (Finset.mem_filter.1 hp).1).2
            have : (p : ℝ) < 2 * Q := by exact_mod_cast hpQ
            exact this.le
        _ = (((Ico Q (2 * Q)).filter Nat.Prime).card : ℝ) * (2 * (Q : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ Q * (2 * (Q : ℝ)) := mul_le_mul_of_nonneg_right hcard (by positivity)
        _ ≤ 4 * (Q : ℝ) ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_right hsum hpow
    simp only at this ⊢
    linarith

end Omega3
