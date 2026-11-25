import Omega3.Items.M10_Sets

/-!
# M10, exact part (`M10_PLAN.md` §3): `M*(y^U) − E11(y) = Σ_{p < y^{1/4}} w(p) Δ_p`
-/

set_option linter.style.longLine false

open Finset Real
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius

namespace Omega3

open Palprimes Palprimes.Greaves

/-! ## The weight -/

theorem Wf_UU : Wf UU = W1 := by
  unfold Wf; norm_num [mm, UU, W1]

theorem Wf_of_le_mm {t : ℝ} (ht : t ≤ mm) : Wf t = 0 := by
  unfold Wf; rw [if_pos ht]

/-- `w(p) = 0` for `p ≤ y^m`. -/
theorem wy_eq_zero {y : ℝ} (hy : 1 < y) {p : ℕ} (hp : 0 < p) (hpy : (p : ℝ) ≤ y ^ mm) : wy y p = 0 := by
  unfold wy
  apply Wf_of_le_mm
  have hly : 0 < Real.log y := Real.log_pos hy
  rw [div_le_iff₀ hly]
  have := Real.log_le_log (by exact_mod_cast hp) hpy
  rwa [Real.log_rpow (by linarith)] at this

/-! ## Primes dividing the primorial -/

theorem primorialLt_pos (z : ℝ) : 0 < primorialLt z := by
  unfold primorialLt
  exact Finset.prod_pos (fun p hp => ((mem_primesBelow z p).1 hp).1.pos)

theorem mem_primesBelow_of_dvd {z : ℝ} {p : ℕ} (hp : p.Prime) (h : p ∣ primorialLt z) : p ∈ primesBelow z := by
  unfold primorialLt at h
  obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 h
  have hq' := (mem_primesBelow z q).1 hq
  rwa [(Nat.prime_dvd_prime_iff_eq hp hq'.1).1 hpq]

/-! ## X1a: splitting `M*` -/

/-- `M*(y^U) = W(1) T⁻(y, y^U) − Σ_{p < y^U} w(p) H_p`. -/
theorem mstar_split (b : ℕ) (y : ℝ) :
    Mstar b y (y ^ UU) = W1 * Tpm b false y (y ^ UU) - ∑ p ∈ primesBelow (y ^ UU), wy y p * Hp b y p := by
  classical
  unfold Mstar Tpm Hp
  simp only [Bool.false_eq_true, ite_false]
  have hswap : ∑ d ∈ (primorialLt (y ^ UU)).divisors, ∑ p ∈ d.primeFactors,
      (μ d : ℝ) * rhoB b d / d * (if chiMinusProp y d then 1 else 0) *
        (wy y p * (if chiStarProp y mm (d1of d p) then 1 else 0)) =
      ∑ p ∈ primesBelow (y ^ UU), ∑ d ∈ (primorialLt (y ^ UU)).divisors.filter (p ∣ ·),
      (μ d : ℝ) * rhoB b d / d * (if chiMinusProp y d then 1 else 0) *
        (wy y p * (if chiStarProp y mm (d1of d p) then 1 else 0)) := by
    apply Finset.sum_comm'
    intro d p
    simp only [Finset.mem_filter, Nat.mem_primeFactors, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd, hP⟩, hp, hpd, hd0⟩
      exact ⟨⟨⟨hd, hP⟩, hpd⟩, mem_primesBelow_of_dvd hp (hpd.trans hd)⟩
    · rintro ⟨⟨⟨hd, hP⟩, hpd⟩, hpz⟩
      refine ⟨⟨hd, hP⟩, ((mem_primesBelow _ p).1 hpz).1, hpd, ?_⟩
      exact Nat.pos_iff_ne_zero.1 (Nat.pos_of_dvd_of_pos hd (primorialLt_pos _))
  have hL : ∀ d ∈ (primorialLt (y ^ UU)).divisors,
      (μ d : ℝ) * rhoB b d / d * (if chiMinusProp y d then 1 else 0) *
        (W1 - ∑ p ∈ d.primeFactors, wy y p * (if chiStarProp y mm (d1of d p) then 1 else 0)) =
      W1 * ((μ d : ℝ) * rhoB b d / d * (if chiMinusProp y d then 1 else 0)) -
        ∑ p ∈ d.primeFactors, (μ d : ℝ) * rhoB b d / d * (if chiMinusProp y d then 1 else 0) *
          (wy y p * (if chiStarProp y mm (d1of d p) then 1 else 0)) := by
    intro d _; rw [mul_sub, Finset.mul_sum]; ring
  rw [Finset.sum_congr rfl hL, Finset.sum_sub_distrib, hswap]
  congr 1
  · rw [Finset.mul_sum]
  · apply Finset.sum_congr rfl; intro p _
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro d _; ring

/-! ## Filters of `primesBelow` -/

theorem primesBelow_filter_lt {a z : ℝ} (h : a ≤ z) :
    (primesBelow z).filter (fun p : ℕ => (p : ℝ) < a) = primesBelow a := by
  ext p; simp only [Finset.mem_filter, mem_primesBelow]
  constructor
  · rintro ⟨⟨hp, _⟩, hpa⟩; exact ⟨hp, hpa⟩
  · rintro ⟨hp, hpa⟩; exact ⟨⟨hp, lt_of_lt_of_le hpa h⟩, hpa⟩

theorem rpow_half_le_UU {y : ℝ} (hy : 1 ≤ y) : y ^ ((1 : ℝ) / 2) ≤ y ^ UU :=
  Real.rpow_le_rpow_of_exponent_le hy (by norm_num [UU])

theorem rpow_quarter_le_half {y : ℝ} (hy : 1 ≤ y) : y ^ ((1 : ℝ) / 4) ≤ y ^ ((1 : ℝ) / 2) :=
  Real.rpow_le_rpow_of_exponent_le hy (by norm_num)

/-! ## The `E11` side -/

/-- `E11` with the end point `p = y^U` removed (its coefficient `W(1) − w(y^U)` is `0`). -/
theorem E11_split (b : ℕ) {y : ℝ} (hy : 1 < y) :
    E11 b y = W1 * Tpm b false y (y ^ ((1 : ℝ) / 2)) -
      ∑ p ∈ (primesBelow (y ^ UU)).filter (fun p : ℕ => y ^ ((1 : ℝ) / 2) ≤ (p : ℝ)),
        (W1 - wy y p) * rhoB b p / p * sigmaP b (y / p) +
      ∑ p ∈ primesBelow (y ^ ((1 : ℝ) / 2)), wy y p * Ep b y p := by
  classical
  unfold E11
  congr 1
  · congr 1
    symm
    apply Finset.sum_subset
    · intro p hp
      rw [Finset.mem_filter, mem_primesBelow] at hp
      rw [Finset.mem_filter, mem_primesBelow]
      exact ⟨⟨hp.1.1, by linarith [hp.1.2]⟩, hp.2, hp.1.2.le⟩
    · intro p hp hpn
      rw [Finset.mem_filter, mem_primesBelow] at hp hpn
      have hpeq : (p : ℝ) = y ^ UU := by
        rcases lt_or_eq_of_le hp.2.2 with h | h
        · exact absurd ⟨⟨hp.1.1, h⟩, hp.2.1⟩ hpn
        · exact h
      have hw : wy y p = W1 := by
        unfold wy
        rw [hpeq, Real.log_rpow (by linarith), mul_div_assoc, div_self (Real.log_pos hy).ne', mul_one, Wf_UU]
      rw [hw, sub_self, zero_mul, zero_div, zero_mul]
  · apply Finset.sum_congr rfl; intro p _
    unfold Ep Nset; ring

/-! ## The three exact range lemmas (X1b, X1c, X1d of the plan) -/

theorem pow_rpow_third {y : ℝ} (hy : 0 ≤ y) : (y ^ ((1 : ℝ) / 3)) ^ 3 = y := by
  rw [show (1 : ℝ) / 3 = ((3 : ℕ) : ℝ)⁻¹ by norm_num]; exact Real.rpow_inv_natCast_pow hy (by norm_num)

theorem pow_rpow_half {y : ℝ} (hy : 0 ≤ y) : (y ^ ((1 : ℝ) / 2)) ^ 2 = y := by
  rw [show (1 : ℝ) / 2 = ((2 : ℕ) : ℝ)⁻¹ by norm_num]; exact Real.rpow_inv_natCast_pow hy (by norm_num)

theorem pow_rpow_quarter {y : ℝ} (hy : 0 ≤ y) : (y ^ ((1 : ℝ) / 4)) ^ 4 = y := by
  rw [show (1 : ℝ) / 4 = ((4 : ℕ) : ℝ)⁻¹ by norm_num]; exact Real.rpow_inv_natCast_pow hy (by norm_num)

/-- `(Y/M)^{1/3} ≤ M` when `Y ≤ M⁴`. -/
theorem cbrt_div_le {Y M : ℝ} (hY : 0 ≤ Y) (hM : 0 < M) (h : Y ≤ M ^ 4) : (Y / M) ^ ((1 : ℝ) / 3) ≤ M := by
  by_contra hc
  push_neg at hc
  have h1 : M ^ 3 < ((Y / M) ^ ((1 : ℝ) / 3)) ^ 3 := pow_lt_pow_left₀ hc hM.le (by norm_num)
  rw [pow_rpow_third (div_nonneg hY hM.le)] at h1
  rw [lt_div_iff₀ hM] at h1
  nlinarith

theorem pow4_ge_of_half {y M : ℝ} (hy : 1 ≤ y) (h : y ^ ((1 : ℝ) / 2) ≤ M) : y ≤ M ^ 4 := by
  have h0 : 0 ≤ y ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (by linarith) _
  have h2 : y ≤ M ^ 2 := by
    have := pow_le_pow_left₀ h0 h 2
    rwa [pow_rpow_half (by linarith)] at this
  nlinarith

theorem pow4_ge_of_quarter {y M : ℝ} (hy : 1 ≤ y) (h : y ^ ((1 : ℝ) / 4) ≤ M) : y ≤ M ^ 4 := by
  have h0 : 0 ≤ y ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (by linarith) _
  have := pow_le_pow_left₀ h0 h 4
  rwa [pow_rpow_quarter (by linarith)] at this

/-- X1b (Buchstab, top): `T⁻(y, y^U) = T⁻(y, √y) − Σ_{√y ≤ p < y^U} γ(p)/p σ⁺(y/p)`. -/
theorem tminus_top (b : ℕ) {y : ℝ} (hy : 16 ≤ y) :
    Tpm b false y (y ^ UU) = Tpm b false y (y ^ ((1 : ℝ) / 2)) -
      ∑ p ∈ (primesBelow (y ^ UU)).filter (fun p : ℕ => y ^ ((1 : ℝ) / 2) ≤ (p : ℝ)),
        rhoB b p / p * sigmaP b (y / p) := by
  classical
  have hy1 : (1 : ℝ) ≤ y := by linarith
  rw [M10.Tpm_max, M10.Tpm_max]
  set G : ℕ → ℝ := fun M => ∑ D ∈ (primesBelow (M : ℝ)).powerset,
    M10.fm b (∏ p ∈ insert M D, p) * (if M10.ChiS false y (insert M D) then 1 else 0) with hG
  have hsplit := (Finset.sum_filter_add_sum_filter_not (primesBelow (y ^ UU))
    (fun p : ℕ => (p : ℝ) < y ^ ((1 : ℝ) / 2)) G).symm
  rw [primesBelow_filter_lt (rpow_half_le_UU hy1)] at hsplit
  rw [hsplit]
  have htop : ∑ M ∈ (primesBelow (y ^ UU)).filter (fun p : ℕ => ¬ (p : ℝ) < y ^ ((1 : ℝ) / 2)), G M =
      -∑ p ∈ (primesBelow (y ^ UU)).filter (fun p : ℕ => y ^ ((1 : ℝ) / 2) ≤ (p : ℝ)),
        rhoB b p / p * sigmaP b (y / p) := by
    rw [← Finset.sum_neg_distrib]
    have hfe : (primesBelow (y ^ UU)).filter (fun p : ℕ => ¬ (p : ℝ) < y ^ ((1 : ℝ) / 2)) =
        (primesBelow (y ^ UU)).filter (fun p : ℕ => y ^ ((1 : ℝ) / 2) ≤ (p : ℝ)) := by
      congr 1; ext p; exact not_lt
    rw [hfe]
    apply Finset.sum_congr rfl; intro M hM
    rw [Finset.mem_filter, mem_primesBelow] at hM
    have hM0 : (0 : ℝ) < M := by exact_mod_cast hM.1.1.pos
    rw [hG]; dsimp only
    rw [M10.head_sigma b (by linarith) hM.1.1 (cbrt_div_le (by linarith) hM0 (pow4_ge_of_half hy1 hM.2))]
    ring
  rw [htop]; ring

/-- `H_p = −γ(p)/p σ⁺(y/p)` for every prime `p < y^U` with `y ≤ p⁴`. -/
theorem Hp_high (b : ℕ) {y : ℝ} (hy : 1 ≤ y) {p : ℕ} (hp : p.Prime) (hpz : (p : ℝ) < y ^ UU)
    (h4 : y ≤ (p : ℝ) ^ 4) : Hp b y p = -(rhoB b p / p * sigmaP b (y / p)) := by
  classical
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpPB : p ∈ primesBelow (y ^ UU) := (mem_primesBelow _ p).2 ⟨hp, hpz⟩
  unfold Hp
  rw [Finset.sum_filter]
  unfold primorialLt
  rw [sum_divisors_primes (primesBelow (y ^ UU)) (M10.primes_PB _), M10.sum_powerset_max]
  simp only [prod_empty]
  have hnd : ¬ p ∣ 1 := fun h => hp.one_lt.ne' (Nat.dvd_one.1 h)
  simp only [hnd, if_false, zero_add]
  rw [Finset.sum_eq_single p]
  · rw [M10.filter_lt_primesBelow hpPB, neg_mul_eq_neg_mul, ← M10.head_sigma b (by linarith) hp (cbrt_div_le (by linarith) hp0 h4)]
    apply Finset.sum_congr rfl; intro D hD
    have hDp : ∀ q ∈ D, q.Prime := fun q hq => M10.primes_PB _ q (mem_powerset.1 hD hq)
    have hlt : ∀ q ∈ D, q < p := by
      intro q hq
      have := ((mem_primesBelow _ q).1 (mem_powerset.1 hD hq)).2
      exact_mod_cast this
    have hpD : p ∉ D := fun h => lt_irrefl _ (hlt p h)
    have hIp : ∀ q ∈ insert p D, q.Prime := by
      intro q hq; rcases mem_insert.1 hq with rfl | hq
      · exact hp
      · exact hDp q hq
    have hdv : p ∣ ∏ q ∈ insert p D, q := Finset.dvd_prod_of_mem (fun q => q) (mem_insert_self p D)
    rw [if_pos hdv]
    have hd1 : d1of (∏ q ∈ insert p D, q) p = 1 := by
      unfold d1of
      rw [Nat.primeFactors_prod hIp]
      have : (insert p D).filter (fun q : ℕ => p < q) = ∅ := by
        apply filter_eq_empty_iff.2
        intro q hq; rcases mem_insert.1 hq with rfl | hq
        · exact lt_irrefl _
        · exact fun h => lt_asymm h (hlt q hq)
      rw [this, prod_empty]
    have hstar : chiStarProp y mm 1 := by
      intro h hh h1; simp at hh; exact absurd hh h1
    rw [hd1, if_pos hstar, mul_one]
    have hc := M10.chiMinus_iff y hIp
    unfold M10.fm
    by_cases h : M10.ChiS false y (insert p D)
    · rw [if_pos (hc.2 h), if_pos h]
    · rw [if_neg (mt hc.1 h), if_neg h]
  · intro M hM hMp
    apply Finset.sum_eq_zero; intro D hD
    have hMpr : M.Prime := M10.primes_PB _ M hM
    rw [M10.filter_lt_primesBelow hM] at hD
    have hDp : ∀ q ∈ D, q.Prime := fun q hq => M10.primes_PB _ q (mem_powerset.1 hD hq)
    have hlt : ∀ q ∈ D, q < M := by
      intro q hq
      have := ((mem_primesBelow _ q).1 (mem_powerset.1 hD hq)).2
      exact_mod_cast this
    have hIp : ∀ q ∈ insert M D, q.Prime := by
      intro q hq; rcases mem_insert.1 hq with rfl | hq
      · exact hMpr
      · exact hDp q hq
    by_cases hdiv : p ∣ ∏ q ∈ insert M D, q
    · rw [if_pos hdiv]
      obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 hdiv
      have hpq' := (Nat.prime_dvd_prime_iff_eq hp (hIp q hq)).1 hpq
      subst hpq'
      have hpD : p ∈ D := by
        rcases mem_insert.1 hq with h | h
        · exact absurd h.symm hMp
        · exact h
      have hpM : p < M := hlt p hpD
      have hnot : ¬ chiMinusProp y (∏ q ∈ insert M D, q) := by
        rw [M10.chiMinus_iff y hIp]
        intro H
        have hE : ({M, p} : Finset ℕ) ⊆ insert M D := by
          intro x hx; rw [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact mem_insert_self _ _
          · exact mem_insert_of_mem hpD
        have hMp' : M ∉ ({p} : Finset ℕ) := by rw [mem_singleton]; exact hMp
        have h1 := H {M, p} hE (insert_nonempty _ _) (by
          simp only [M10.par, Bool.false_eq_true, ite_false]
          rw [card_insert_of_notMem hMp', card_singleton]; exact even_two)
        have hEp : ∀ x ∈ ({M, p} : Finset ℕ), x.Prime := by
          intro x hx; rw [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hMpr
          · exact hp
        obtain ⟨hmf, hmin⟩ := M10.minFac_prod hEp (insert_nonempty _ _)
        have hmfp : (∏ x ∈ ({M, p} : Finset ℕ), x).minFac = p := by
          rw [mem_insert, mem_singleton] at hmf
          rcases hmf with h | h
          · exfalso
            have := hmin p (by simp)
            omega
          · exact h
        rw [hmfp, prod_insert hMp', prod_singleton] at h1
        have hpM' : (p : ℝ) < M := by exact_mod_cast hpM
        push_cast at h1
        nlinarith
      rw [if_neg hnot]; ring
    · rw [if_neg hdiv]
  · intro h; exact absurd hpPB h

/-- X1c: for `√y ≤ p < y^U`, `H_p = −γ(p)/p σ⁺(y/p)`. -/
theorem Hp_top (b : ℕ) {y : ℝ} (hy : 16 ≤ y) {p : ℕ} (hp : p.Prime) (h1 : y ^ ((1 : ℝ) / 2) ≤ p)
    (h2 : (p : ℝ) < y ^ UU) : Hp b y p = -(rhoB b p / p * sigmaP b (y / p)) :=
  Hp_high b (by linarith) hp h2 (pow4_ge_of_half (by linarith) h1)

/-- X1d: for `y^{1/4} ≤ p < √y`, `Δ_p = 0`. -/
theorem DeltaP_mid (b : ℕ) {y : ℝ} (hy : 16 ≤ y) {p : ℕ} (hp : p.Prime) (h1 : y ^ ((1 : ℝ) / 4) ≤ p)
    (h2 : (p : ℝ) < y ^ ((1 : ℝ) / 2)) : DeltaP b y p = 0 := by
  have hy1 : (1 : ℝ) ≤ y := by linarith
  have h4 := pow4_ge_of_quarter hy1 h1
  unfold DeltaP Ep
  rw [Hp_high b hy1 hp (lt_of_lt_of_le h2 (rpow_half_le_UU hy1)) h4, M10.Nset_empty hp h4, sum_empty]
  ring

/-! ## X1: the exact split -/

theorem exact_split (b : ℕ) {y : ℝ} (hy : 16 ≤ y) :
    Mstar b y (y ^ UU) - E11 b y = ∑ p ∈ primesBelow (y ^ ((1 : ℝ) / 4)), wy y p * DeltaP b y p := by
  classical
  have hy1 : (1 : ℝ) < y := by linarith
  set h2 := y ^ ((1 : ℝ) / 2) with hh2
  set zU := y ^ UU with hzU
  set Top := (primesBelow zU).filter (fun p : ℕ => h2 ≤ (p : ℝ)) with hTop
  rw [mstar_split, E11_split b hy1, tminus_top b hy]
  -- split the H-sum at √y
  have hsplit := (Finset.sum_filter_add_sum_filter_not (primesBelow zU) (fun p : ℕ => (p : ℝ) < h2)
    (fun p => wy y p * Hp b y p)).symm
  rw [primesBelow_filter_lt (rpow_half_le_UU hy1.le)] at hsplit
  have hnot : (primesBelow zU).filter (fun p : ℕ => ¬ (p : ℝ) < h2) = Top := by
    rw [hTop]; congr 1; ext p; exact not_lt
  rw [hnot] at hsplit
  rw [hsplit]
  have htop : ∑ p ∈ Top, wy y p * Hp b y p = -∑ p ∈ Top, wy y p * (rhoB b p / p * sigmaP b (y / p)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro p hp
    simp only [hTop, Finset.mem_filter, mem_primesBelow] at hp
    rw [Hp_top b hy hp.1.1 hp.2 hp.1.2]; ring
  rw [htop]
  -- the √y-sum
  have hmid : ∑ p ∈ primesBelow h2, wy y p * DeltaP b y p =
      ∑ p ∈ primesBelow (y ^ ((1 : ℝ) / 4)), wy y p * DeltaP b y p := by
    have hs := (Finset.sum_filter_add_sum_filter_not (primesBelow h2) (fun p : ℕ => (p : ℝ) < y ^ ((1 : ℝ) / 4))
      (fun p => wy y p * DeltaP b y p)).symm
    rw [primesBelow_filter_lt (rpow_quarter_le_half hy1.le)] at hs
    rw [hs]
    have h0 : ∑ p ∈ (primesBelow h2).filter (fun p : ℕ => ¬ (p : ℝ) < y ^ ((1 : ℝ) / 4)),
        wy y p * DeltaP b y p = 0 := by
      apply Finset.sum_eq_zero; intro p hp
      simp only [Finset.mem_filter, mem_primesBelow, not_lt] at hp
      rw [DeltaP_mid b hy hp.1.1 hp.2 hp.1.2, mul_zero]
    rw [h0, add_zero]
  rw [← hmid]
  unfold DeltaP
  have e1 : ∑ p ∈ primesBelow h2, wy y p * (-Hp b y p - Ep b y p) =
      -∑ p ∈ primesBelow h2, wy y p * Hp b y p - ∑ p ∈ primesBelow h2, wy y p * Ep b y p := by
    rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro p _; ring
  have e2 : ∑ p ∈ Top, (W1 - wy y p) * rhoB b p / p * sigmaP b (y / p) =
      W1 * ∑ p ∈ Top, rhoB b p / p * sigmaP b (y / p) - ∑ p ∈ Top, wy y p * (rhoB b p / p * sigmaP b (y / p)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro p _; ring
  rw [e1, e2]; ring

end Omega3
