import KappaOmega2.Items.M10_Comb

/-!
# M10 helper: set form of `Tpm`, `σ⁺` after a head prime, `H_p` for `p ≥ y^{1/4}`, `N_p = ∅` for `p ≥ y^{1/4}`
-/

set_option linter.style.longLine false

open Finset Real
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius

namespace KappaOmega2.M10

open Palprimes Palprimes.Greaves
open Classical

/-- The summand `μ(n) γ(n)/n`. -/
noncomputable def fm (b n : ℕ) : ℝ := (μ n : ℝ) * rhoB b n / n

theorem primesBelow_mono {a c : ℝ} (h : a ≤ c) : primesBelow a ⊆ primesBelow c := by
  intro p hp; rw [mem_primesBelow] at hp ⊢; exact ⟨hp.1, lt_of_lt_of_le hp.2 h⟩

theorem primes_PB (w : ℝ) : ∀ p ∈ primesBelow w, p.Prime := fun p hp => ((mem_primesBelow w p).1 hp).1

theorem chiMinus_iff (Y : ℝ) {D : Finset ℕ} (hD : ∀ p ∈ D, p.Prime) :
    chiMinusProp Y (∏ p ∈ D, p) ↔ ChiS false Y D := by
  simpa using chi_iff false Y hD

theorem chiPlus_iff (Y : ℝ) {D : Finset ℕ} (hD : ∀ p ∈ D, p.Prime) :
    chiPlusProp Y (∏ p ∈ D, p) ↔ ChiS true Y D := by
  simpa using chi_iff true Y hD

/-- Set form of `T^±(Y, w)`. -/
theorem Tpm_set (b : ℕ) (plus : Bool) (Y w : ℝ) :
    Tpm b plus Y w = ∑ D ∈ (primesBelow w).powerset, fm b (∏ p ∈ D, p) * (if ChiS plus Y D then 1 else 0) := by
  classical
  unfold Tpm primorialLt
  rw [sum_divisors_primes (primesBelow w) (primes_PB w)]
  apply sum_congr rfl; intro D hD
  have hDp : ∀ p ∈ D, p.Prime := fun p hp => primes_PB w p (mem_powerset.1 hD hp)
  have h := chi_iff plus Y hDp
  unfold fm
  by_cases hc : ChiS plus Y D
  · rw [if_pos (h.2 hc), if_pos hc]
  · rw [if_neg (mt h.1 hc), if_neg hc]

theorem not_dvd_prod_of_notMem {M : ℕ} {D : Finset ℕ} (hM : M.Prime) (hD : ∀ p ∈ D, p.Prime) (hMD : M ∉ D) :
    ¬ M ∣ ∏ p ∈ D, p := by
  intro h
  obtain ⟨q, hq, hMq⟩ := (Prime.dvd_finsetProd_iff hM.prime _).1 h
  rw [(Nat.prime_dvd_prime_iff_eq hM (hD q hq)).1 hMq] at hMD
  exact hMD hq

/-- `μ γ / ·` at `M · n`. -/
theorem fm_mul_prime (b : ℕ) {M n : ℕ} (hM : M.Prime) (hn : 0 < n) (hMn : ¬ M ∣ n) :
    fm b (M * n) = -(rhoB b M / M) * fm b n := by
  unfold fm
  have hcop : Nat.Coprime M n := (Nat.Prime.coprime_iff_not_dvd hM).2 hMn
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop, ArithmeticFunction.moebius_apply_prime hM]
  have hrho : rhoB b (M * n) = rhoB b M * rhoB b n := by
    unfold rhoB
    simp only [Nat.coprime_mul_iff_left]
    split_ifs <;> simp_all
  rw [hrho]
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM.pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  push_cast
  field_simp

theorem fm_insert (b : ℕ) {M : ℕ} {D : Finset ℕ} (hM : M.Prime) (hD : ∀ p ∈ D, p.Prime) (hMD : M ∉ D) :
    fm b (∏ p ∈ insert M D, p) = -(rhoB b M / M) * fm b (∏ p ∈ D, p) := by
  rw [prod_insert hMD]
  exact fm_mul_prime b hM (prod_pos_of_primes hD) (not_dvd_prod_of_notMem hM hD hMD)

theorem lt_cbrt_of_cube_lt {q X : ℝ} (hq : 0 ≤ q) (hX : 0 ≤ X) (h : q * q ^ 2 < X) : q < X ^ ((1 : ℝ) / 3) := by
  by_contra hc
  push_neg at hc
  have h1 : (X ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = X := by
    rw [show (1 : ℝ) / 3 = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.rpow_inv_natCast_pow hX (by norm_num)
  have h2 : (X ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) ≤ q ^ (3 : ℕ) :=
    pow_le_pow_left₀ (Real.rpow_nonneg hX _) hc 3
  rw [h1] at h2
  nlinarith

/-- `T⁺(X, M) = σ⁺(X)` in set form when `X^{1/3} ≤ M`. -/
theorem sigma_set (b : ℕ) {X : ℝ} (hX : 0 < X) {M : ℝ} (h3 : X ^ ((1 : ℝ) / 3) ≤ M) :
    ∑ D ∈ (primesBelow M).powerset, fm b (∏ p ∈ D, p) * (if ChiS true X D then 1 else 0) = sigmaP b X := by
  classical
  unfold sigmaP
  rw [Tpm_set]
  apply sum_powerset_of_support (primesBelow_mono h3)
  intro E hE hne
  intro q hq
  have hc : ChiS true X E := by
    by_contra h; apply hne; rw [if_neg h, mul_zero]
  have hqp : q.Prime := primes_PB M q (hE hq)
  have h1 := hc {q} (singleton_subset_iff.2 hq) (singleton_nonempty q) (by simp [par])
  rw [prod_singleton, Nat.Prime.minFac_eq hqp] at h1
  rw [mem_primesBelow]
  exact ⟨hqp, lt_cbrt_of_cube_lt (Nat.cast_nonneg _) hX.le h1⟩

/-- `Σ_{D ⊆ P(M)} μγ/·(M·ΠD) χ⁻_Y(M·ΠD) = −γ(M)/M · σ⁺(Y/M)` when `(Y/M)^{1/3} ≤ M`. -/
theorem head_sigma (b : ℕ) {Y : ℝ} (hY : 0 < Y) {M : ℕ} (hM : M.Prime) (h3 : (Y / M) ^ ((1 : ℝ) / 3) ≤ M) :
    ∑ D ∈ (primesBelow (M : ℝ)).powerset, fm b (∏ p ∈ insert M D, p) * (if ChiS false Y (insert M D) then 1 else 0) =
      -(rhoB b M / M) * sigmaP b (Y / M) := by
  classical
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM.pos
  rw [← sigma_set b (div_pos hY hM0) h3, mul_sum]
  apply sum_congr rfl; intro D hD
  have hDp : ∀ p ∈ D, p.Prime := fun p hp => primes_PB _ p (mem_powerset.1 hD hp)
  have hlt : ∀ q ∈ D, q < M := by
    intro q hq
    have := ((mem_primesBelow _ q).1 (mem_powerset.1 hD hq)).2
    exact_mod_cast this
  have hMD : M ∉ D := fun h => lt_irrefl _ (hlt M h)
  rw [fm_insert b hM hDp hMD]
  have h := chiS_minus_insert (Y := Y) hDp hM hlt
  by_cases hc : ChiS true (Y / M) D
  · rw [if_pos (h.2 hc), if_pos hc]; ring
  · rw [if_neg (mt h.1 hc), if_neg hc]; ring

/-- For `M ∈ P(z)`: the primes of `P(z)` below `M` are `P(M)`. -/
theorem filter_lt_primesBelow {z : ℝ} {M : ℕ} (hM : M ∈ primesBelow z) :
    (primesBelow z).filter (· < M) = primesBelow (M : ℝ) := by
  have hMz := ((mem_primesBelow _ M).1 hM).2
  ext q; simp only [mem_filter, mem_primesBelow]
  constructor
  · rintro ⟨⟨hq, _⟩, hqM⟩; exact ⟨hq, by exact_mod_cast hqM⟩
  · rintro ⟨hq, hqM⟩
    have : q < M := by exact_mod_cast hqM
    exact ⟨⟨hq, lt_trans hqM hMz⟩, this⟩

/-- Buchstab over the largest prime, set form. -/
theorem Tpm_max (b : ℕ) (plus : Bool) (Y z : ℝ) :
    Tpm b plus Y z = fm b 1 * (if ChiS plus Y ∅ then 1 else 0) +
      ∑ M ∈ primesBelow z, ∑ D ∈ (primesBelow (M : ℝ)).powerset,
        fm b (∏ p ∈ insert M D, p) * (if ChiS plus Y (insert M D) then 1 else 0) := by
  rw [Tpm_set, sum_powerset_max]
  simp only [prod_empty]
  congr 1
  apply sum_congr rfl; intro M hM
  rw [filter_lt_primesBelow hM]

/-- `N_p = ∅` when `y ≤ p⁴`. -/
theorem Nset_empty {y : ℝ} {p : ℕ} (hp : p.Prime) (h4 : y ≤ (p : ℝ) ^ 4) : Nset y p = ∅ := by
  classical
  apply eq_empty_of_forall_notMem
  intro n hn
  unfold Nset at hn
  rw [mem_filter, Nat.mem_divisors] at hn
  obtain ⟨⟨hdvd, hP0⟩, hn1, hev, hpm, hlt⟩ := hn
  have hn0 : 0 < n := Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hP0)
  have hnp : ¬ n.Prime := by
    intro h
    rw [ArithmeticFunction.cardDistinctFactors_apply_prime h] at hev
    exact Nat.not_even_one hev
  have hsq := Nat.minFac_sq_le_self hn0 hnp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hm : (p : ℝ) + 1 ≤ n.minFac := by exact_mod_cast hpm
  have hsq' : ((n.minFac : ℕ) : ℝ) ^ 2 ≤ n := by exact_mod_cast hsq
  have h1 : y / p ≤ (p : ℝ) ^ 3 := by
    rw [div_le_iff₀ hp0]; nlinarith
  have hmf0 : (0 : ℝ) ≤ n.minFac := Nat.cast_nonneg _
  have h2 : ((p : ℝ) + 1) ^ 3 ≤ (n.minFac : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) hm 3
  have h3 : (n.minFac : ℝ) ^ 3 ≤ (n : ℝ) * n.minFac := by nlinarith
  nlinarith

end KappaOmega2.M10
