import Omega3.Items.S08_S

/-! # S08 helpers, part L: exact algebra of `λ_q` and `ν` (Step 1 of S08_PLAN). -/

namespace Omega3

open Finset Palprimes
open scoped ArithmeticFunction.Moebius

set_option linter.style.longLine false

/-- `A'_{p,q} = Σ_{k < z, q | k, p | k} g(k)`. -/
noncomputable def s08A2 (b : ℕ) (z : ℝ) (p q : ℕ) : ℝ :=
  ∑ k ∈ (ltSet z).filter (fun k => q ∣ k ∧ p ∣ k), gS b k

lemma s08_mu_term (b q k : ℕ) (hq : q.Prime) (hqk : q ∣ k) :
    (μ (k / q) : ℝ) * (μ k : ℝ) * gS b k = -gS b k := by
  by_cases hg : Squarefree k ∧ Nat.Coprime k (bigB b)
  · obtain ⟨j, rfl⟩ := hqk
    have hq0 : 0 < q := hq.pos
    rw [Nat.mul_div_cancel_left j hq0]
    have hsq := hg.1
    have hc : Nat.Coprime q j := (Nat.squarefree_mul_iff.1 hsq).1
    have hj : Squarefree j := (Nat.squarefree_mul_iff.1 hsq).2.2
    have hmul : μ (q * j) = μ q * μ j := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hc
    rw [ArithmeticFunction.moebius_apply_prime hq] at hmul
    have hsq1 : (μ j : ℤ) ^ 2 = 1 := ArithmeticFunction.moebius_sq_eq_one_of_squarefree hj
    have : (μ j : ℝ) * (μ (q * j) : ℝ) = -1 := by
      rw [hmul]; push_cast
      have : ((μ j : ℤ) : ℝ) ^ 2 = 1 := by exact_mod_cast hsq1
      nlinarith
    rw [this]; ring
  · unfold gS; rw [if_neg hg]; ring

/-- Swap `Σ_{k ∈ F} g(k) Σ_{p | k} η(p) = Σ_{p ∈ P(z)} η(p) Σ_{k ∈ F, p | k} g(k)`. -/
lemma s08_swap (b : ℕ) (z : ℝ) (F : Finset ℕ) (hF : F ⊆ ltSet z) (f : ℕ → ℝ) :
    ∑ k ∈ F, gS b k * ∑ p ∈ k.primeFactors, f p = ∑ p ∈ s08Pz z, f p * ∑ k ∈ F.filter (fun k => p ∣ k), gS b k := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm' (t' := s08Pz z) (s' := fun p => F.filter (fun k => p ∣ k))]
  · apply Finset.sum_congr rfl; intro p _; apply Finset.sum_congr rfl; intro k _; ring
  · intro k p
    simp only [Finset.mem_filter, s08Pz]
    constructor
    · rintro ⟨hk, hp⟩
      have hkl := hF hk
      rw [s08_mem_ltSet] at hkl
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hpk := Nat.dvd_of_mem_primeFactors hp
      have : p ≤ k := Nat.le_of_dvd (by omega) hpk
      refine ⟨⟨hk, hpk⟩, ?_, hpp⟩
      rw [s08_mem_ltSet]
      exact ⟨hpp.one_lt.le, lt_of_le_of_lt (by exact_mod_cast this) hkl.2⟩
    · rintro ⟨⟨hk, hpk⟩, _, hpp⟩
      have hkl := hF hk
      rw [s08_mem_ltSet] at hkl
      exact ⟨hk, Nat.mem_primeFactors.2 ⟨hpp, hpk, by omega⟩⟩

/-- `λ_q = −q (ν A_q − Σ_p η(p) A'_{p,q})` for a prime `q` coprime to `B`. -/
lemma s08_lamq (b : ℕ) (e : StepFn) (x : ℝ) (q : ℕ) (hq : q.Prime) (hqB : Nat.Coprime q (bigB b)) :
    lamA b e x q = -(q : ℝ) * (nuA b e x * s08A b (Real.sqrt x) q -
      ∑ p ∈ s08Pz (Real.sqrt x), etaQ b e x p * s08A2 b (Real.sqrt x) p q) := by
  classical
  set z := Real.sqrt x with hz
  unfold lamA
  rw [if_pos hqB, ← hz]
  have e1 : ∀ k ∈ (ltSet z).filter (fun k => q ∣ k), (μ (k / q) : ℝ) * ykA b e x k =
      -(gS b k * nuA b e x) + gS b k * ∑ p ∈ k.primeFactors, etaQ b e x p := by
    intro k hk
    rw [Finset.mem_filter] at hk
    unfold ykA etaK
    have := s08_mu_term b q k hq hk.2
    calc (μ (k / q) : ℝ) * ((μ k : ℝ) * gS b k * (nuA b e x - ∑ p ∈ k.primeFactors, etaQ b e x p))
        = ((μ (k / q) : ℝ) * (μ k : ℝ) * gS b k) * (nuA b e x - ∑ p ∈ k.primeFactors, etaQ b e x p) := by ring
      _ = _ := by rw [this]; ring
  rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.sum_mul,
    s08_swap b z _ (Finset.filter_subset _ _)]
  unfold s08A s08A2
  simp only [Finset.filter_filter]
  ring

/-- `H = Σ_k g(k) η(k) = Σ_{p ∈ P(z)} η(p) A_p`. -/
lemma s08_H (b : ℕ) (e : StepFn) (x : ℝ) :
    ∑ k ∈ ltSet (Real.sqrt x), gS b k * etaK b e x k =
      ∑ p ∈ s08Pz (Real.sqrt x), etaQ b e x p * s08A b (Real.sqrt x) p := by
  unfold etaK s08A
  exact s08_swap b _ _ (Finset.Subset.refl _) _

lemma s08_A2_self (b : ℕ) (z : ℝ) (q : ℕ) : s08A2 b z q q = s08A b z q := by
  unfold s08A2 s08A
  congr 1
  apply Finset.filter_congr
  intro k _; simp

lemma s08_A2_ne (b : ℕ) (z : ℝ) (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    s08A2 b z p q = s08A b z (p * q) := by
  unfold s08A2 s08A
  congr 1
  apply Finset.filter_congr
  intro k _
  constructor
  · rintro ⟨h1, h2⟩
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.coprime_primes hp hq).2 hpq) h2 h1
  · intro h
    exact ⟨dvd_trans (dvd_mul_left q p) h, dvd_trans (dvd_mul_right p q) h⟩

end Omega3
