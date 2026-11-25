import Omega3.Statements
import Palprimes.Sieve.SelbergSum

/-!
# S07 helpers: facts on `𝒟` (copied from S13 with new names), the weight `W`, band search
-/

namespace Omega3

open Finset Palprimes Palprimes.Greaves
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius

set_option linter.style.longLine false

lemma S07_mem (y : ℝ) (δ : ℕ) (h : δ ∈ Dset y (y ^ UU) mm) :
    δ ∣ primorialLt (y ^ UU) ∧ δ ≠ 1 ∧ chibar y mm δ = 1 ∧ Odd (ω δ) ∧ (ω δ : ℝ) ≤ 1 / mm := by
  classical
  unfold Dset at h
  rw [Finset.mem_filter, Nat.mem_divisors] at h
  exact ⟨h.1.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

lemma S07_chi (y m : ℝ) (δ : ℕ) (h1 : δ ≠ 1) (h : chibar y m δ = 1) :
    chiProp y m (δ / δ.minFac) ∧ ¬ chiProp y m δ := by
  classical
  unfold chibar at h
  rw [if_neg h1] at h
  unfold chi at h
  by_cases ha : chiProp y m (δ / δ.minFac)
  · by_cases hb : chiProp y m δ
    · simp [ha, hb] at h
    · exact ⟨ha, hb⟩
  · by_cases hb : chiProp y m δ
    · simp [ha, hb] at h; norm_num at h
    · simp [ha, hb] at h

lemma S07_primorial (z : ℝ) (δ : ℕ) (h : δ ∣ primorialLt z) (hδ : δ ≠ 0) :
    Squarefree δ ∧ ∀ p ∈ δ.primeFactors, (p : ℝ) < z := by
  have hsq := SelbergPort.prod_primes_squarefree (primesBelow z) (fun p hp => ((mem_primesBelow z p).1 hp).1)
  refine ⟨hsq.squarefree_of_dvd h, fun p hp => ?_⟩
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpd : p ∣ ∏ q ∈ primesBelow z, q := (Nat.dvd_of_mem_primeFactors hp).trans h
  obtain ⟨q, hq, hpq⟩ := Prime.exists_mem_finset_dvd hpp.prime hpd
  have := (Nat.prime_dvd_prime_iff_eq hpp ((mem_primesBelow z q).1 hq).1).1 hpq
  rw [this]; exact ((mem_primesBelow z q).1 hq).2

/-- The violating divisor contains `p(δ)`, so `y ≤ δ p(δ)²`. -/
lemma S07_y_le (y : ℝ) (δ : ℕ) (hsq : Squarefree δ) (h1 : δ ≠ 1)
    (hc1 : chiProp y mm (δ / δ.minFac)) (hc0 : ¬ chiProp y mm δ) :
    y ≤ (δ : ℝ) * (δ.minFac : ℝ) ^ 2 := by
  classical
  unfold chiProp at hc0
  push Not at hc0
  obtain ⟨h, hh, hne, hcond, hge⟩ := hc0
  rw [Nat.mem_divisors] at hh
  have hδ0 : δ ≠ 0 := hsq.ne_zero
  set p := δ.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime h1
  have hpδ : p ∣ δ := Nat.minFac_dvd δ
  obtain ⟨c, hc⟩ := hpδ
  have hdivc : δ / p = c := by rw [hc]; exact Nat.mul_div_cancel_left c hp.pos
  have hnd : ¬ h ∣ c := by
    intro hd
    have := hc1 h (by rw [Nat.mem_divisors, hdivc]; exact ⟨hd, by rintro rfl; simp at hc; exact hδ0 hc⟩) hne hcond
    linarith
  have hph : p ∣ h := by
    by_contra hnp
    apply hnd
    have hcop : Nat.Coprime h p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hnp).symm
    have : h ∣ p * c := by rw [← hc]; exact hh.1
    exact hcop.dvd_of_dvd_mul_left this
  have hmf : h.minFac = p := by
    apply le_antisymm
    · exact Nat.minFac_le_of_dvd hp.two_le hph
    · exact Nat.minFac_le_of_dvd (Nat.minFac_prime hne).two_le ((Nat.minFac_dvd h).trans hh.1)
  rw [hmf] at hge
  have hle : (h : ℝ) ≤ δ := by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hδ0) hh.1
  calc y ≤ (h : ℝ) * (p : ℝ) ^ 2 := hge
    _ ≤ (δ : ℝ) * (p : ℝ) ^ 2 := by gcongr

/-- A prime factor of `δ` other than `p(δ)` has `p³ < y`. -/
lemma S07_cube (y : ℝ) (δ : ℕ) (hδ0 : δ ≠ 0) (h1 : δ ≠ 1) (hc1 : chiProp y mm (δ / δ.minFac))
    (p : ℕ) (hp : p ∈ δ.primeFactors) (hne : p ≠ δ.minFac) : (p : ℝ) ^ 3 < y := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hp0 : δ.minFac.Prime := Nat.minFac_prime h1
  have hcop : Nat.Coprime δ.minFac p := (Nat.coprime_primes hp0 hpp).2 (Ne.symm hne)
  have hmul : δ.minFac * p ∣ δ :=
    hcop.mul_dvd_of_dvd_of_dvd (Nat.minFac_dvd δ) (Nat.dvd_of_mem_primeFactors hp)
  have hpd : p ∣ δ / δ.minFac := Nat.dvd_div_of_mul_dvd hmul
  have hq0 : δ / δ.minFac ≠ 0 := by
    have := Nat.div_pos (Nat.minFac_le (Nat.pos_of_ne_zero hδ0)) hp0.pos
    omega
  have hω : ((ω p : ℕ) : ℝ) ≤ 1 / mm := by
    rw [ArithmeticFunction.cardDistinctFactors_apply_prime hpp]; unfold mm; norm_num
  have := hc1 p (Nat.mem_divisors.2 ⟨hpd, hq0⟩) hpp.ne_one (Or.inr hω)
  rw [Nat.Prime.minFac_eq hpp] at this
  nlinarith

/-! ## The weight -/

lemma S07_W_zero (t : ℝ) (h : t ≤ mm) : Wf t = 0 := by
  unfold Wf; rw [if_pos h]

lemma S07_W_lin (t : ℝ) (h : mm < t) : Wf t ≤ t - mm := by
  unfold Wf
  rw [if_neg (not_le.2 h)]
  split_ifs with h1 h2
  · exact min_le_right _ _
  · exact le_rfl
  · unfold W1 mm UU at *; push Not at h2; linarith

lemma S07_W_sq (t : ℝ) (h0 : 0 ≤ t) (h : t ≤ 1 / 3) : Wf t ≤ kSq * t ^ 2 := by
  unfold Wf
  split_ifs with h1
  · unfold kSq; positivity
  · exact min_le_left _ _

lemma S07_W_eq (x : ℝ) (h0 : 1 / 3 ≤ x) (h : x ≤ UU) : Wf x = x - mm := by
  unfold Wf
  have hm : ¬ x ≤ mm := by unfold mm; intro h'; linarith
  rw [if_neg hm]
  split_ifs with h1
  · have hx : x = 1 / 3 := le_antisymm h1 h0
    rw [hx]; unfold kSq mm; norm_num
  · rfl

lemma S07_W_prop (l : ℝ) (h0 : 0 ≤ l) (h : l ≤ 1 / 3) : Wf l ≤ (1 - 3 * mm) * l := by
  by_cases hl : l ≤ mm
  · rw [S07_W_zero l hl]; unfold mm; nlinarith
  · have := S07_W_lin l (not_le.1 hl)
    unfold mm at *; nlinarith

/-! ## Band search -/

lemma S07_find (xs : List ℚ) (v : ℝ) :
    xs ≠ [] → ((xs.headD 0 : ℚ) : ℝ) ≤ v → v < ((xs.getLastD (1 / 3) : ℚ) : ℝ) →
      ∃ i, i + 1 < xs.length ∧ ((xs.getD i 0 : ℚ) : ℝ) ≤ v ∧ v < ((xs.getD (i + 1) 0 : ℚ) : ℝ) := by
  induction xs with
  | nil => intro h; exact absurd rfl h
  | cons a rest ih =>
    intro _ ha hl
    cases rest with
    | nil => simp at ha hl; linarith
    | cons c rest' =>
      by_cases hv : v < (c : ℝ)
      · exact ⟨0, by simp, by simpa using ha, by simpa using hv⟩
      · obtain ⟨i, hi, h1, h2⟩ := ih (by simp) (by simpa using not_lt.1 hv) (by simpa using hl)
        exact ⟨i + 1, by simp at hi ⊢; omega, by simpa using h1, by simpa using h2⟩

end Omega3
