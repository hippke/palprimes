import Omega3.Items.M02_E

/-! # M02 helpers, part D: Selberg diagonalisation `Q(λ) = Σ_k g(k)(ν − η(k))²` and the expansion of `G B₀`. -/

namespace Omega3

open Finset Palprimes
open scoped ArithmeticFunction.Moebius

set_option linter.style.longLine false

/-- `V(d) = Σ_{d | k < z} μ(k/d) y_k`. -/
noncomputable def m02V (b : ℕ) (e : StepFn) (x : ℝ) (d : ℕ) : ℝ :=
  ∑ k ∈ (ltSet (Real.sqrt x)).filter (fun k => d ∣ k), (μ (k / d) : ℝ) * ykA b e x k

lemma m02_V_zero (b : ℕ) (e : StepFn) (x : ℝ) (d : ℕ) (hd : ¬ Nat.Coprime d (bigB b)) : m02V b e x d = 0 := by
  unfold m02V
  apply Finset.sum_eq_zero
  intro k hk
  rw [Finset.mem_filter] at hk
  unfold ykA gS
  rw [if_neg]
  · ring
  · intro h; exact hd (Nat.Coprime.coprime_dvd_left hk.2 h.2)

lemma m02_term (b : ℕ) (e : StepFn) (x : ℝ) (d1 d2 : ℕ) (h1 : 1 ≤ d1) (h2 : 1 ≤ d2) :
    lamA b e x d1 * lamA b e x d2 * rhoB b (Nat.lcm d1 d2) / (Nat.lcm d1 d2 : ℝ) =
      m02V b e x d1 * m02V b e x d2 * (Nat.gcd d1 d2 : ℝ) := by
  classical
  by_cases c1 : Nat.Coprime d1 (bigB b)
  · by_cases c2 : Nat.Coprime d2 (bigB b)
    · have hl : Nat.Coprime (Nat.lcm d1 d2) (bigB b) :=
        Nat.Coprime.coprime_dvd_left (Nat.lcm_dvd (dvd_mul_right d1 d2) (dvd_mul_left d2 d1))
          (Nat.coprime_mul_iff_left.2 ⟨c1, c2⟩)
      have hl1 : lamA b e x d1 = d1 * m02V b e x d1 := by unfold lamA m02V; rw [if_pos c1]
      have hl2 : lamA b e x d2 = d2 * m02V b e x d2 := by unfold lamA m02V; rw [if_pos c2]
      have hρ : rhoB b (Nat.lcm d1 d2) = 1 := by unfold rhoB; rw [if_pos hl]
      rw [hl1, hl2, hρ]
      have hgl : (Nat.gcd d1 d2 : ℝ) * (Nat.lcm d1 d2 : ℝ) = d1 * d2 := by exact_mod_cast Nat.gcd_mul_lcm d1 d2
      have hl0 : (Nat.lcm d1 d2 : ℝ) ≠ 0 := by
        have : Nat.lcm d1 d2 ≠ 0 := Nat.lcm_ne_zero (by omega) (by omega)
        exact_mod_cast this
      field_simp
      linear_combination (-(m02V b e x d1 * m02V b e x d2)) * hgl
    · have hl2 : lamA b e x d2 = 0 := by unfold lamA; rw [if_neg c2]
      rw [hl2, m02_V_zero b e x d2 c2]; ring
  · have hl1 : lamA b e x d1 = 0 := by unfold lamA; rw [if_neg c1]
    rw [hl1, m02_V_zero b e x d1 c1]; ring

lemma m02_gcd_sum (z : ℝ) (d1 d2 : ℕ) (h1 : d1 ∈ ltSet z) (h2 : d2 ∈ ltSet z) :
    (Nat.gcd d1 d2 : ℝ) = ∑ t ∈ ltSet z, if t ∣ d1 ∧ t ∣ d2 then (t.totient : ℝ) else 0 := by
  classical
  rw [m02_mem_ltSet] at h1 h2
  rw [← Finset.sum_filter]
  have hs : (ltSet z).filter (fun t => t ∣ d1 ∧ t ∣ d2) = (Nat.gcd d1 d2).divisors := by
    ext t
    rw [Finset.mem_filter, Nat.mem_divisors, m02_mem_ltSet, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨_, h⟩; exact ⟨h, Nat.gcd_ne_zero_left (by omega)⟩
    · rintro ⟨h, _⟩
      have : t ≤ d1 := Nat.le_of_dvd (by omega) h.1
      refine ⟨⟨Nat.pos_of_dvd_of_pos h.1 (by omega), lt_of_le_of_lt (by exact_mod_cast this) h1.2⟩, h⟩
  rw [hs]
  have := Nat.sum_totient (Nat.gcd d1 d2)
  exact_mod_cast this.symm

lemma m02_mu_sum (m : ℕ) (hm : 0 < m) : ∑ j ∈ m.divisors, (μ j : ℝ) = if m = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f m) ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  have : ((∑ j ∈ m.divisors, μ j : ℤ) : ℝ) = ((if m = 1 then 1 else 0 : ℤ) : ℝ) := by rw [h]
  push_cast at this
  exact this

lemma m02_inner (k t : ℕ) (hk : 1 ≤ k) (htk : t ∣ k) :
    ∑ d ∈ k.divisors.filter (fun d => t ∣ d), (μ (k / d) : ℝ) = if k = t then 1 else 0 := by
  classical
  obtain ⟨m, rfl⟩ := htk
  have ht0 : 0 < t := Nat.pos_of_ne_zero (by rintro rfl; simp at hk)
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hk)
  have hb : ∑ d ∈ (t * m).divisors.filter (fun d => t ∣ d), (μ (t * m / d) : ℝ) = ∑ d' ∈ m.divisors, (μ (m / d') : ℝ) := by
    symm
    apply Finset.sum_nbij' (fun d' => t * d') (fun d => d / t)
    · intro d' hd'
      simp only [Finset.mem_coe, Nat.mem_divisors] at hd'
      simp only [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors]
      exact ⟨⟨Nat.mul_dvd_mul_left t hd'.1, by positivity⟩, dvd_mul_right t d'⟩
    · intro d hd
      simp only [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors] at hd
      simp only [Finset.mem_coe, Nat.mem_divisors]
      obtain ⟨⟨h1, _⟩, c, rfl⟩ := hd
      rw [Nat.mul_div_cancel_left c ht0]
      exact ⟨Nat.dvd_of_mul_dvd_mul_left ht0 h1, by omega⟩
    · intro d' _; exact Nat.mul_div_cancel_left d' ht0
    · intro d hd
      simp only [Finset.mem_coe, Finset.mem_filter] at hd
      exact Nat.mul_div_cancel' hd.2
    · intro d' _
      rw [Nat.mul_div_mul_left m d' ht0]
  rw [hb, Nat.sum_div_divisors m (fun j => (μ j : ℝ)), m02_mu_sum m hm0]
  have : t * m = t ↔ m = 1 := by
    constructor
    · intro h; have := Nat.eq_of_mul_eq_mul_left ht0 (h.trans (mul_one t).symm); exact this
    · rintro rfl; ring
  by_cases h : m = 1
  · rw [if_pos h, if_pos (this.2 h)]
  · rw [if_neg h, if_neg (fun h' => h (this.1 h'))]

lemma m02_mobius (b : ℕ) (e : StepFn) (x : ℝ) (t : ℕ) (ht : t ∈ ltSet (Real.sqrt x)) :
    ∑ d ∈ (ltSet (Real.sqrt x)).filter (fun d => t ∣ d), m02V b e x d = ykA b e x t := by
  classical
  set z := Real.sqrt x with hz
  unfold m02V
  rw [← hz]
  rw [Finset.sum_comm' (t' := (ltSet z).filter (fun k => t ∣ k)) (s' := fun k => k.divisors.filter (fun d => t ∣ d))]
  swap
  · intro d k
    simp only [Finset.mem_filter, Nat.mem_divisors, m02_mem_ltSet]
    constructor
    · rintro ⟨⟨hd, htd⟩, hk, hdk⟩
      exact ⟨⟨⟨hdk, by omega⟩, htd⟩, hk, dvd_trans htd hdk⟩
    · rintro ⟨⟨⟨hdk, hk0⟩, htd⟩, hk, _⟩
      have : d ≤ k := Nat.le_of_dvd (by omega) hdk
      exact ⟨⟨⟨Nat.pos_of_dvd_of_pos hdk (by omega), lt_of_le_of_lt (by exact_mod_cast this) hk.2⟩, htd⟩, hk, hdk⟩
  have e1 : ∀ k ∈ (ltSet z).filter (fun k => t ∣ k),
      ∑ d ∈ k.divisors.filter (fun d => t ∣ d), (μ (k / d) : ℝ) * ykA b e x k = if k = t then ykA b e x k else 0 := by
    intro k hk
    rw [Finset.mem_filter, m02_mem_ltSet] at hk
    rw [← Finset.sum_mul, m02_inner k t hk.1.1 hk.2]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl e1, Finset.sum_ite_eq']
  rw [if_pos]
  rw [Finset.mem_filter]; exact ⟨ht, dvd_refl t⟩

/-- **Diagonalisation**: `Q(λ) = Σ_k g(k)(ν − η(k))²`. -/
theorem m02_diag (b : ℕ) (e : StepFn) (x : ℝ) :
    Qform b x (lamA b e x) = ∑ k ∈ ltSet (Real.sqrt x), gS b k * (nuA b e x - etaK b e x k) ^ 2 := by
  classical
  set z := Real.sqrt x with hz
  unfold Qform
  rw [← hz]
  have e1 : ∀ d1 ∈ ltSet z, ∀ d2 ∈ ltSet z,
      lamA b e x d1 * lamA b e x d2 * rhoB b (Nat.lcm d1 d2) / (Nat.lcm d1 d2 : ℝ) =
        ∑ t ∈ ltSet z, (if t ∣ d1 then m02V b e x d1 else 0) * (if t ∣ d2 then m02V b e x d2 else 0) * (t.totient : ℝ) := by
    intro d1 h1 d2 h2
    rw [m02_term b e x d1 d2 ((m02_mem_ltSet z d1).1 h1).1 ((m02_mem_ltSet z d2).1 h2).1, m02_gcd_sum z d1 d2 h1 h2,
      Finset.mul_sum]
    apply Finset.sum_congr rfl; intro t _
    by_cases a1 : t ∣ d1 <;> by_cases a2 : t ∣ d2 <;> simp [a1, a2]
  rw [Finset.sum_congr rfl (fun d1 h1 => Finset.sum_congr rfl (fun d2 h2 => e1 d1 h1 d2 h2))]
  have e2 : ∀ d1 ∈ ltSet z, ∑ d2 ∈ ltSet z, ∑ t ∈ ltSet z,
      (if t ∣ d1 then m02V b e x d1 else 0) * (if t ∣ d2 then m02V b e x d2 else 0) * (t.totient : ℝ) =
      ∑ t ∈ ltSet z, ∑ d2 ∈ ltSet z,
      (if t ∣ d1 then m02V b e x d1 else 0) * (if t ∣ d2 then m02V b e x d2 else 0) * (t.totient : ℝ) := by
    intro d1 _; exact Finset.sum_comm
  rw [Finset.sum_congr rfl e2, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  have hsum : ∀ f : ℕ → ℝ, ∑ d ∈ ltSet z, (if t ∣ d then f d else 0) = ∑ d ∈ (ltSet z).filter (fun d => t ∣ d), f d :=
    fun f => (Finset.sum_filter _ _).symm
  have e3 : ∑ d1 ∈ ltSet z, ∑ d2 ∈ ltSet z,
      (if t ∣ d1 then m02V b e x d1 else 0) * (if t ∣ d2 then m02V b e x d2 else 0) * (t.totient : ℝ) =
      (t.totient : ℝ) * (∑ d ∈ ltSet z, (if t ∣ d then m02V b e x d else 0)) ^ 2 := by
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro d1 _
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro d2 _; ring
  rw [e3, hsum, m02_mobius b e x t ht]
  unfold ykA
  by_cases hg : Squarefree t ∧ Nat.Coprime t (bigB b)
  · have hμ : (μ t : ℝ) ^ 2 = 1 := by
      have := ArithmeticFunction.moebius_sq_eq_one_of_squarefree hg.1
      exact_mod_cast this
    have hφ : (0 : ℝ) < t.totient := by
      have := ((m02_mem_ltSet z t).1 ht).1
      exact_mod_cast Nat.totient_pos.2 (by omega)
    unfold gS; rw [if_pos hg]
    have : ((μ t : ℝ) * (1 / (t.totient : ℝ)) * (nuA b e x - etaK b e x t)) ^ 2 =
        (μ t : ℝ) ^ 2 * (1 / (t.totient : ℝ)) ^ 2 * (nuA b e x - etaK b e x t) ^ 2 := by ring
    rw [this, hμ]
    field_simp
  · unfold gS; rw [if_neg hg]; ring

/-- `Q·G = 1 − H² + G B₀`. -/
lemma m02_QG (b : ℕ) (e : StepFn) (x : ℝ) (hG : 0 < GS b (Real.sqrt x)) :
    Qform b x (lamA b e x) * GS b (Real.sqrt x) =
      1 - (∑ k ∈ ltSet (Real.sqrt x), gS b k * etaK b e x k) ^ 2 +
        GS b (Real.sqrt x) * ∑ k ∈ ltSet (Real.sqrt x), gS b k * etaK b e x k ^ 2 := by
  rw [m02_diag]
  set z := Real.sqrt x
  set G := GS b z with hGdef
  set H := ∑ k ∈ ltSet z, gS b k * etaK b e x k with hH
  set B0 := ∑ k ∈ ltSet z, gS b k * etaK b e x k ^ 2 with hB0
  have hnu : nuA b e x = (1 + H) / G := rfl
  have e1 : ∑ k ∈ ltSet z, gS b k * (nuA b e x - etaK b e x k) ^ 2 =
      nuA b e x ^ 2 * G - 2 * nuA b e x * H + B0 := by
    have hk : ∀ k ∈ ltSet z, gS b k * (nuA b e x - etaK b e x k) ^ 2 =
        nuA b e x ^ 2 * gS b k - 2 * nuA b e x * (gS b k * etaK b e x k) + gS b k * etaK b e x k ^ 2 := by
      intro k _; ring
    rw [Finset.sum_congr rfl hk, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hG' : G = ∑ k ∈ ltSet z, gS b k := rfl
    rw [hG']
  rw [e1, hnu]
  field_simp
  ring

/-- `Σ_k g(k)(Σ_{p | k} f p)² = Σ_{p, p' ∈ P(z)} f p f p' A'_{p', p}`. -/
lemma m02_B0 (b : ℕ) (z : ℝ) (f : ℕ → ℝ) :
    ∑ k ∈ ltSet z, gS b k * (∑ p ∈ k.primeFactors, f p) ^ 2 =
      ∑ p ∈ m02Pz z, ∑ p' ∈ m02Pz z, f p * f p' * m02A2 b z p' p := by
  classical
  have hpf : ∀ k ∈ ltSet z, ∀ F : ℕ → ℝ, ∑ p ∈ k.primeFactors, F p = ∑ p ∈ m02Pz z, if p ∣ k then F p else 0 := by
    intro k hk F
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext p
    rw [Finset.mem_filter, Nat.mem_primeFactors]
    unfold m02Pz
    rw [Finset.mem_filter, m02_mem_ltSet]
    rw [m02_mem_ltSet] at hk
    constructor
    · rintro ⟨hp, hpk, _⟩
      have : p ≤ k := Nat.le_of_dvd (by omega) hpk
      exact ⟨⟨⟨hp.one_lt.le, lt_of_le_of_lt (by exact_mod_cast this) hk.2⟩, hp⟩, hpk⟩
    · rintro ⟨⟨_, hp⟩, hpk⟩; exact ⟨hp, hpk, by omega⟩
  have e1 : ∀ k ∈ ltSet z, gS b k * (∑ p ∈ k.primeFactors, f p) ^ 2 =
      ∑ p ∈ m02Pz z, ∑ p' ∈ m02Pz z, f p * f p' * (if p ∣ k ∧ p' ∣ k then gS b k else 0) := by
    intro k hk
    rw [hpf k hk f, sq, Finset.sum_mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro p _
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p' _
    by_cases a1 : p ∣ k <;> by_cases a2 : p' ∣ k <;> simp [a1, a2] <;> ring
  rw [Finset.sum_congr rfl e1, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro p _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro p' _
  rw [← Finset.mul_sum]
  unfold m02A2
  rw [Finset.sum_filter]

end Omega3
