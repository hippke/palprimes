import KappaOmega2.Statements
import KappaOmega2.Items.M01_Core

namespace KappaOmega2

open Finset Palprimes Palprimes.Greaves KappaOmega2.M01c
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius

set_option linter.style.longLine false

lemma m01_rho_mul (b m n : ℕ) : rhoB b (m * n) = rhoB b m * rhoB b n := by
  classical
  unfold rhoB
  by_cases h1 : Nat.Coprime m (bigB b) <;> by_cases h2 : Nat.Coprime n (bigB b)
  · rw [if_pos (Nat.Coprime.mul_left h1 h2), if_pos h1, if_pos h2]; ring
  · have : ¬ Nat.Coprime (m * n) (bigB b) := fun h => h2 (Nat.Coprime.coprime_dvd_left (dvd_mul_left n m) h)
    rw [if_neg this, if_neg h2]; ring
  · have : ¬ Nat.Coprime (m * n) (bigB b) := fun h => h1 (Nat.Coprime.coprime_dvd_left (dvd_mul_right m n) h)
    rw [if_neg this, if_neg h1]; ring
  · have : ¬ Nat.Coprime (m * n) (bigB b) := fun h => h1 (Nat.Coprime.coprime_dvd_left (dvd_mul_right m n) h)
    rw [if_neg this, if_neg h1]; ring

lemma m01_delta (b : ℕ) (B : BandData) (y : ℝ) (hy : 1 < y) (δ : ℕ) (hδ : δ ∈ Dset y (y ^ UU) mm)
    (P : ℕ) (hP : P = primorialLt (y ^ UU)) :
    ∑ d1 ∈ ltSet (Real.sqrt (y / δ)), ∑ d2 ∈ ltSet (Real.sqrt (y / δ)),
      (if Nat.lcm d1 d2 * δ ∈ P.divisors then LamD b B y δ d1 * LamD b B y δ d2 *
        (rhoB b (Nat.lcm d1 d2 * δ) / ((Nat.lcm d1 d2 * δ : ℕ) : ℝ)) else 0) =
      rhoB b δ / δ * Qform b (y / δ) (LamD b B y δ) := by
  classical
  obtain ⟨hδ0, hδ1, hsqδ, hdvd, hpz, hyle⟩ := c_Dfacts y δ hδ
  unfold Qform
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d1 hd1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d2 hd2
  by_cases hz : LamD b B y δ d1 * LamD b B y δ d2 = 0
  · rw [hz]; simp
  · have h1 : LamD b B y δ d1 ≠ 0 := fun h => hz (by rw [h, zero_mul])
    have h2 : LamD b B y δ d2 ≠ 0 := fun h => hz (by rw [h, mul_zero])
    have s1 := (c_supp b (etaOf B y δ) (y / δ) d1 h1)
    have s2 := (c_supp b (etaOf B y δ) (y / δ) d2 h2)
    obtain ⟨hsq, hc, hdP⟩ := c_lcm_dvdP y hy δ hδ d1 d2 hd1 hd2 s1.1 s2.1
    have hmem : Nat.lcm d1 d2 * δ ∈ P.divisors := by
      rw [Nat.mem_divisors, hP]
      refine ⟨hdP, ?_⟩
      unfold primorialLt
      exact Finset.prod_ne_zero_iff.2 (fun p hp => ((mem_primesBelow _ p).1 hp).1.ne_zero)
    rw [if_pos hmem, m01_rho_mul]
    have hℓ0 : (Nat.lcm d1 d2 : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.lcm_ne_zero s1.1.ne_zero s2.1.ne_zero)
    have hδ0' : (δ : ℝ) ≠ 0 := by exact_mod_cast hδ0
    push_cast
    field_simp

theorem itemM01 : ItemM01 := by
  classical
  intro b B ε y hb hy
  set z := y ^ UU with hz
  set P := primorialLt z with hP
  unfold MTs M1
  have hsplit : ∀ n ∈ P.divisors, cSieve b B ε y n * rhoB b n / n =
      ((μ n : ℝ) * chi y mm n * phiW W1 (wy y) n * rhoB b n / n) -
      (1 + ε) * ∑ δ ∈ Dset y z mm, phiW W1 (wy y) δ *
        ∑ d1 ∈ ltSet (Real.sqrt (y / δ)), ∑ d2 ∈ ltSet (Real.sqrt (y / δ)),
          (if Nat.lcm d1 d2 * δ = n then LamD b B y δ d1 * LamD b B y δ d2 * (rhoB b n / (n : ℝ)) else 0) := by
    intro n hn
    have hnP : n ∣ P := Nat.dvd_of_mem_divisors hn
    unfold cSieve
    rw [← hz, ← hP, if_pos hnP]
    have e2 : ((∑ δ ∈ Dset y z mm, phiW W1 (wy y) δ *
        ∑ d1 ∈ ltSet (Real.sqrt (y / δ)), ∑ d2 ∈ ltSet (Real.sqrt (y / δ)),
          (if Nat.lcm d1 d2 * δ = n then LamD b B y δ d1 * LamD b B y δ d2 else 0))) * (rhoB b n / (n : ℝ)) =
        ∑ δ ∈ Dset y z mm, phiW W1 (wy y) δ *
        ∑ d1 ∈ ltSet (Real.sqrt (y / δ)), ∑ d2 ∈ ltSet (Real.sqrt (y / δ)),
          (if Nat.lcm d1 d2 * δ = n then LamD b B y δ d1 * LamD b B y δ d2 * (rhoB b n / (n : ℝ)) else 0) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro δ hδ
      rw [mul_assoc]
      congr 1
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d1 _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d2 _
      split_ifs <;> simp
    rw [← e2]
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, ← Finset.mul_sum]
  congr 2
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro δ hδ
  rw [show (∑ n ∈ P.divisors, phiW W1 (wy y) δ *
        ∑ d1 ∈ ltSet (Real.sqrt (y / δ)), ∑ d2 ∈ ltSet (Real.sqrt (y / δ)),
          (if Nat.lcm d1 d2 * δ = n then LamD b B y δ d1 * LamD b B y δ d2 * (rhoB b n / (n : ℝ)) else 0)) =
      phiW W1 (wy y) δ * ∑ n ∈ P.divisors,
        ∑ d1 ∈ ltSet (Real.sqrt (y / δ)), ∑ d2 ∈ ltSet (Real.sqrt (y / δ)),
          (if Nat.lcm d1 d2 * δ = n then LamD b B y δ d1 * LamD b B y δ d2 * (rhoB b n / (n : ℝ)) else 0) from
    (Finset.mul_sum _ _ _).symm]
  have hsw : ∑ n ∈ P.divisors, ∑ d1 ∈ ltSet (Real.sqrt (y / δ)), ∑ d2 ∈ ltSet (Real.sqrt (y / δ)),
          (if Nat.lcm d1 d2 * δ = n then LamD b B y δ d1 * LamD b B y δ d2 * (rhoB b n / (n : ℝ)) else 0) =
      ∑ d1 ∈ ltSet (Real.sqrt (y / δ)), ∑ d2 ∈ ltSet (Real.sqrt (y / δ)),
        (if Nat.lcm d1 d2 * δ ∈ P.divisors then LamD b B y δ d1 * LamD b B y δ d2 *
          (rhoB b (Nat.lcm d1 d2 * δ) / ((Nat.lcm d1 d2 * δ : ℕ) : ℝ)) else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d1 _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d2 _
    rw [Finset.sum_ite_eq]
  rw [hsw, m01_delta b B y hy δ hδ P hP]
  ring

end KappaOmega2
