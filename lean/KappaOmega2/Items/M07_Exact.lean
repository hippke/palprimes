import KappaOmega2.Items.M07_Chi

/-!
# M07 helper: the exact identity (Greaves (4.9) = (4.10))

`M₁ − M*(z) = Σ_{δ ∈ 𝒟} φ(δ)γ(δ)/δ · T⁺(y/δ, p(δ))` for `z = y^U` (`M07_PLAN.md` §1), proved in set form:
divisors of `P(z)` are subsets of `S = primesBelow z`, and the pairs `(δ, t)` correspond to the sets
`D ⊆ S` with `χ⁻(D)` and `¬χ*(D)` by splitting `D` at the largest violating top prefix.
-/

set_option linter.style.longLine false
set_option linter.deprecated false

open Finset Real
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius

namespace KappaOmega2.M07

open Palprimes Palprimes.Greaves Palprimes.MT
open Classical

/-- `γ(Π D)/Π D` as a product. -/
noncomputable def gD (b : ℕ) (D : Finset ℕ) : ℝ := ∏ p ∈ D, gB b p

theorem rho_div_prod (b : ℕ) {D : Finset ℕ} (hD : ∀ p ∈ D, p.Prime) :
    rhoB b (∏ p ∈ D, p) / ((∏ p ∈ D, p : ℕ) : ℝ) = gD b D := by
  unfold rhoB gD gB
  by_cases h : Nat.Coprime (∏ p ∈ D, p) (bigB b)
  · rw [if_pos h]
    have h' : ∀ p ∈ D, Nat.Coprime p (bigB b) := fun p hp =>
      Nat.Coprime.coprime_dvd_left (dvd_prod_of_mem _ hp) h
    rw [prod_congr rfl (fun p hp => if_pos ⟨hD p hp, h' p hp⟩), Nat.cast_prod, one_div, ← prod_inv_distrib]
    simp [one_div]
  · rw [if_neg h, zero_div]
    rw [Nat.coprime_prod_left_iff] at h
    push Not at h
    obtain ⟨p, hp, hpc⟩ := h
    symm
    apply prod_eq_zero hp
    rw [if_neg]
    rintro ⟨_, h2⟩
    exact hpc h2

theorem moebius_prod {D : Finset ℕ} (hD : ∀ p ∈ D, p.Prime) :
    ((μ (∏ p ∈ D, p) : ℤ) : ℝ) = (-1 : ℝ) ^ D.card := by
  have h := ArithmeticFunction.IsMultiplicative.map_prod_of_subset_primeFactors
    ArithmeticFunction.isMultiplicative_moebius (∏ p ∈ D, p) D (by rw [Nat.primeFactors_prod hD])
  rw [h, prod_congr rfl (fun p hp => ArithmeticFunction.moebius_apply_prime (hD p hp)), prod_const]
  push_cast; ring

theorem primesBelow_prime {w : ℝ} {p : ℕ} (hp : p ∈ primesBelow w) : p.Prime :=
  ((mem_primesBelow w p).1 hp).1

theorem primesBelow_filter_lt (w : ℝ) {P : ℕ} (hP : P ∈ primesBelow w) :
    (primesBelow w).filter (· < P) = primesBelow (P : ℝ) := by
  ext q
  rw [mem_filter, mem_primesBelow, mem_primesBelow]
  have hPw := ((mem_primesBelow w P).1 hP).2
  constructor
  · rintro ⟨⟨hq, _⟩, hqP⟩; exact ⟨hq, by exact_mod_cast hqP⟩
  · rintro ⟨hq, hqP⟩
    have hqP' : q < P := by exact_mod_cast hqP
    exact ⟨⟨hq, lt_trans hqP hPw⟩, hqP'⟩

theorem phiW_prod (w : ℕ → ℝ) {D : Finset ℕ} (hD : ∀ p ∈ D, p.Prime) :
    phiW W1 w (∏ p ∈ D, p) = W1 - ∑ p ∈ D, w p := by
  unfold phiW; rw [Nat.primeFactors_prod hD]

theorem d1of_prod {D : Finset ℕ} (hD : ∀ p ∈ D, p.Prime) (p : ℕ) :
    d1of (∏ q ∈ D, q) p = ∏ q ∈ D.filter (fun q => p < q), q := by
  unfold d1of; rw [Nat.primeFactors_prod hD]

/-! ## Set forms of `M₁`, `M*` and `T⁺` -/

theorem M1_set (b : ℕ) (y : ℝ) :
    M1 b y = ∑ D ∈ (primesBelow (y ^ UU)).powerset,
      (-1 : ℝ) ^ D.card * gD b D * ((if ChiG Cchi y D then 1 else 0) * (W1 - ∑ p ∈ D, wy y p)) := by
  classical
  unfold M1 primorialLt
  rw [sum_divisors_primes _ (fun p hp => primesBelow_prime hp)]
  apply sum_congr rfl
  intro D hD
  have hDp : ∀ p ∈ D, p.Prime := fun p hp => primesBelow_prime (mem_powerset.1 hD hp)
  rw [moebius_prod hDp, phiW_prod _ hDp, mul_div_assoc, rho_div_prod b hDp]
  unfold chi
  by_cases h : ChiG Cchi y D
  · rw [if_pos ((chi_iff' y hDp).2 h), if_pos h]; ring
  · rw [if_neg (fun h' => h ((chi_iff' y hDp).1 h')), if_neg h]; ring

theorem Mstar_set (b : ℕ) (y z : ℝ) :
    Mstar b y z = ∑ D ∈ (primesBelow z).powerset,
      (-1 : ℝ) ^ D.card * gD b D * ((if ChiG Even y D then 1 else 0) *
        (W1 - ∑ p ∈ D, wy y p * (if ChiG Cst y (D.filter (fun q => p < q)) then 1 else 0))) := by
  classical
  unfold Mstar primorialLt
  rw [sum_divisors_primes _ (fun p hp => primesBelow_prime hp)]
  apply sum_congr rfl
  intro D hD
  have hDp : ∀ p ∈ D, p.Prime := fun p hp => primesBelow_prime (mem_powerset.1 hD hp)
  have hsum : ∑ p ∈ (∏ q ∈ D, q).primeFactors, wy y p * (if chiStarProp y mm (d1of (∏ q ∈ D, q) p) then 1 else 0) =
      ∑ p ∈ D, wy y p * (if ChiG Cst y (D.filter (fun q => p < q)) then 1 else 0) := by
    rw [Nat.primeFactors_prod hDp]
    apply sum_congr rfl
    intro p _
    have hsub : ∀ q ∈ D.filter (fun q => p < q), q.Prime := fun q hq => hDp q (mem_filter.1 hq).1
    rw [d1of_prod hDp]
    by_cases h : ChiG Cst y (D.filter (fun q => p < q))
    · rw [if_pos ((chiStar_iff' y hsub).2 h), if_pos h]
    · rw [if_neg (fun h' => h ((chiStar_iff' y hsub).1 h')), if_neg h]
  rw [hsum, moebius_prod hDp]
  have e : ((-1 : ℝ) ^ D.card * rhoB b (∏ p ∈ D, p) / ((∏ p ∈ D, p : ℕ) : ℝ)) = (-1 : ℝ) ^ D.card * gD b D := by
    rw [mul_div_assoc, rho_div_prod b hDp]
  rw [e]
  by_cases h : ChiG Even y D
  · rw [if_pos ((chiMinus_iff' y hDp).2 h), if_pos h]; ring
  · rw [if_neg (fun h' => h ((chiMinus_iff' y hDp).1 h')), if_neg h]; ring

theorem Tplus_set (b : ℕ) (Y w : ℝ) :
    Tpm b true Y w = ∑ T ∈ (primesBelow w).powerset,
      (-1 : ℝ) ^ T.card * gD b T * (if ChiG Odd Y T then 1 else 0) := by
  classical
  unfold Tpm primorialLt
  rw [sum_divisors_primes _ (fun p hp => primesBelow_prime hp)]
  apply sum_congr rfl
  intro D hD
  have hDp : ∀ p ∈ D, p.Prime := fun p hp => primesBelow_prime (mem_powerset.1 hD hp)
  rw [moebius_prod hDp, mul_div_assoc, rho_div_prod b hDp]
  simp only [ite_true]
  by_cases h : ChiG Odd Y D
  · rw [if_pos ((chiPlus_iff' Y hDp).2 h), if_pos h]
  · rw [if_neg (fun h' => h ((chiPlus_iff' Y hDp).1 h')), if_neg h]

/-! ## The set `𝒟` in set form -/

/-- `𝒟` as sets of primes. -/
noncomputable def Dsf (y z : ℝ) : Finset (Finset ℕ) :=
  open Classical in (primesBelow z).powerset.filter (fun Δ => (∏ p ∈ Δ, p) ∈ Dset y z mm)

theorem sum_Dset (y z : ℝ) (f : ℕ → ℝ) :
    ∑ δ ∈ Dset y z mm, f δ = ∑ Δ ∈ Dsf y z, f (∏ p ∈ Δ, p) := by
  classical
  have hP : ∀ p ∈ primesBelow z, p.Prime := fun p hp => primesBelow_prime hp
  have hsq := SelbergPort.prod_primes_squarefree _ hP
  have hP0 : (∏ p ∈ primesBelow z, p) ≠ 0 := hsq.ne_zero
  symm
  apply Finset.sum_nbij' (fun t => ∏ p ∈ t, p) (fun d => d.primeFactors)
  · intro t ht
    unfold Dsf at ht
    exact (mem_filter.1 ht).2
  · intro d hd
    have hd' := hd
    unfold Dset at hd
    have hdiv := (mem_filter.1 hd).1
    rw [Nat.mem_divisors] at hdiv
    unfold Dsf
    have hsub : d.primeFactors ⊆ primesBelow z := by
      have := Nat.primeFactors_mono hdiv.1 hP0
      unfold primorialLt at this
      rwa [Nat.primeFactors_prod hP] at this
    have hd1 : ∏ p ∈ d.primeFactors, p = d := Nat.prod_primeFactors_of_squarefree (hsq.squarefree_of_dvd hdiv.1)
    rw [mem_filter, mem_powerset, hd1]
    exact ⟨hsub, hd'⟩
  · intro t ht
    unfold Dsf at ht
    have ht' := mem_powerset.1 (mem_filter.1 ht).1
    exact Nat.primeFactors_prod (fun p hp => hP p (ht' hp))
  · intro d hd
    unfold Dset at hd
    have hdiv := (mem_filter.1 hd).1
    rw [Nat.mem_divisors] at hdiv
    exact Nat.prod_primeFactors_of_squarefree (hsq.squarefree_of_dvd hdiv.1)
  · intro t _; rfl

/-- Membership in `𝒟` for a set of primes. -/
theorem mem_Dsf_iff (y z : ℝ) {Δ : Finset ℕ} (hΔ : Δ ⊆ primesBelow z) :
    Δ ∈ Dsf y z ↔ Δ.Nonempty ∧ ChiG Cchi y (Δ.erase (∏ p ∈ Δ, p).minFac) ∧ ¬ ChiG Cchi y Δ ∧
      Odd Δ.card ∧ (Δ.card : ℝ) ≤ 1 / mm := by
  classical
  have hΔp : ∀ p ∈ Δ, p.Prime := fun p hp => primesBelow_prime (hΔ hp)
  have hP : ∀ p ∈ primesBelow z, p.Prime := fun p hp => primesBelow_prime hp
  have hP0 : (∏ p ∈ primesBelow z, p) ≠ 0 := (prod_pos_of_primes hP).ne'
  unfold Dsf Dset
  rw [mem_filter, mem_powerset, mem_filter, Nat.mem_divisors, omega_prod hΔp]
  have hdvd : (∏ p ∈ Δ, p) ∣ primorialLt z := prod_dvd_prod_of_subset _ _ _ hΔ
  have hne1 : (∏ p ∈ Δ, p) ≠ 1 ↔ Δ.Nonempty := by
    constructor
    · intro h; rw [nonempty_iff_ne_empty]; rintro rfl; exact h prod_empty
    · rintro ⟨q, hq⟩ h
      have := Finset.dvd_prod_of_mem (fun p => p) hq
      rw [h] at this
      exact (hΔp q hq).ne_one (Nat.dvd_one.1 this)
  constructor
  · rintro ⟨-, ⟨-, -⟩, h1, hcb, hodd, hle⟩
    have hne := hne1.1 h1
    obtain ⟨hm, _⟩ := minFac_prod hΔp hne
    set m := (∏ p ∈ Δ, p).minFac
    have hdiv : (∏ p ∈ Δ, p) / m = ∏ p ∈ Δ.erase m, p := by
      rw [← mul_prod_erase Δ (fun p => p) hm, Nat.mul_div_cancel_left _ (hΔp m hm).pos]
    have hEp : ∀ p ∈ Δ.erase m, p.Prime := fun p hp => hΔp p (mem_of_mem_erase hp)
    unfold chibar chi at hcb
    rw [if_neg h1, hdiv] at hcb
    refine ⟨hne, ?_, ?_, hodd, hle⟩
    · by_contra hc
      rw [if_neg (fun h' => hc ((chi_iff' y hEp).1 h'))] at hcb
      split_ifs at hcb <;> norm_num at hcb
    · intro hc
      rw [if_pos ((chi_iff' y hΔp).2 hc)] at hcb
      split_ifs at hcb <;> norm_num at hcb
  · rintro ⟨hne, hc1, hc2, hodd, hle⟩
    refine ⟨hΔ, ⟨hdvd, ?_⟩, hne1.2 hne, ?_, hodd, hle⟩
    · unfold primorialLt; exact hP0
    · obtain ⟨hm, _⟩ := minFac_prod hΔp hne
      set m := (∏ p ∈ Δ, p).minFac
      have hdiv : (∏ p ∈ Δ, p) / m = ∏ p ∈ Δ.erase m, p := by
        rw [← mul_prod_erase Δ (fun p => p) hm, Nat.mul_div_cancel_left _ (hΔp m hm).pos]
      have hEp : ∀ p ∈ Δ.erase m, p.Prime := fun p hp => hΔp p (mem_of_mem_erase hp)
      unfold chibar chi
      rw [if_neg (hne1.2 hne), hdiv, if_pos ((chi_iff' y hEp).2 hc1),
        if_neg (fun h' => hc2 ((chi_iff' y hΔp).1 h'))]
      norm_num

/-- Splitting `Δ = (Δ \ {m}) ∪ {m}` at its smallest element. -/
theorem split_min {Δ : Finset ℕ} {m : ℕ} (hm : m ∈ Δ) (hmin : ∀ q ∈ Δ, m ≤ q) :
    Δ = Δ.erase m ∪ {m} ∧ (∀ t ∈ ({m} : Finset ℕ), ∀ p ∈ Δ.erase m, t < p) ∧ (Δ.erase m).card + 1 = Δ.card := by
  refine ⟨?_, ?_, card_erase_add_one hm⟩
  · rw [union_comm, ← insert_eq, insert_erase hm]
  · intro t ht p hp
    rw [mem_singleton] at ht; subst ht
    exact lt_of_le_of_ne (hmin p (mem_of_mem_erase hp)) (ne_of_mem_erase hp).symm

/-- Facts on `Δ ∈ 𝒟`: `χ⁻(Δ)`, `¬χ*(Δ)` and the violation `y ≤ Π Δ · m²` (`m` the smallest prime). -/
theorem Dsf_facts (y z : ℝ) {Δ : Finset ℕ} (hΔS : Δ ⊆ primesBelow z) (hΔ : Δ ∈ Dsf y z) :
    ChiG Even y Δ ∧ ¬ ChiG Cst y Δ ∧ ChiG Cst y (Δ.erase (∏ p ∈ Δ, p).minFac) ∧
      y / ((∏ p ∈ Δ.erase (∏ p ∈ Δ, p).minFac, p : ℕ) : ℝ) ≤ (((∏ p ∈ Δ, p).minFac : ℕ) : ℝ) ^ 3 := by
  obtain ⟨hne, hc1, hc2, hodd, hle⟩ := (mem_Dsf_iff y z hΔS).1 hΔ
  have hΔp : ∀ p ∈ Δ, p.Prime := fun p hp => primesBelow_prime (hΔS hp)
  obtain ⟨hm, hmin⟩ := minFac_prod hΔp hne
  set m := (∏ p ∈ Δ, p).minFac
  obtain ⟨hsplit, hlt, hcard⟩ := split_min hm hmin
  have hEp : ∀ p ∈ Δ.erase m, p.Prime := fun p hp => hΔp p (mem_of_mem_erase hp)
  have hmp : ∀ p ∈ ({m} : Finset ℕ), p.Prime := by simp [hΔp m hm]
  have U : ∀ C : ℕ → Prop, ChiG C y Δ ↔ ChiG C y (Δ.erase m) ∧
      (C Δ.card → (m : ℝ) ^ 3 < y / ((∏ p ∈ Δ.erase m, p : ℕ) : ℝ)) := by
    intro C
    conv_lhs => rw [hsplit]
    rw [chiG_union C y hEp hmp hlt, chiG_singleton _ _ (hΔp m hm), show 1 + (Δ.erase m).card = Δ.card by omega]
  have hc1' := (chiG_chi_iff y _).1 hc1
  have hviol : ¬ ((m : ℝ) ^ 3 < y / ((∏ p ∈ Δ.erase m, p : ℕ) : ℝ)) := by
    intro h
    exact hc2 ((U Cchi).2 ⟨hc1, fun _ => h⟩)
  refine ⟨(U Even).2 ⟨hc1'.1, fun he => absurd he (Nat.not_even_iff_odd.2 hodd)⟩, ?_, hc1'.2, not_lt.1 hviol⟩
  intro h
  exact hviol (((U Cst).1 h).2 ⟨hodd, hle⟩)

/-! ## The bijection -/

/-- The summand of `M₁ − M*` in set form. -/
noncomputable def Fs (y : ℝ) (D : Finset ℕ) : ℝ :=
  open Classical in
  (if ChiG Cchi y D then 1 else 0) * (W1 - ∑ p ∈ D, wy y p) -
    (if ChiG Even y D then 1 else 0) *
      (W1 - ∑ p ∈ D, wy y p * (if ChiG Cst y (D.filter (fun q => p < q)) then 1 else 0))

theorem Fs_zero (y : ℝ) (D : Finset ℕ) (h : ¬ (ChiG Even y D ∧ ¬ ChiG Cst y D)) : Fs y D = 0 := by
  classical
  unfold Fs
  by_cases he : ChiG Even y D
  · have hs : ChiG Cst y D := by by_contra hs; exact h ⟨he, hs⟩
    have hc : ChiG Cchi y D := (chiG_chi_iff y D).2 ⟨he, hs⟩
    rw [if_pos hc, if_pos he]
    have : ∀ p ∈ D, wy y p * (if ChiG Cst y (D.filter (fun q => p < q)) then 1 else 0) = wy y p := by
      intro p _
      rw [if_pos (chiG_mono (filter_subset _ _) hs), mul_one]
    rw [sum_congr rfl this]; ring
  · have hc : ¬ ChiG Cchi y D := fun hc => he ((chiG_chi_iff y D).1 hc).1
    rw [if_neg hc, if_neg he]; ring

/-- The largest violating split point. -/
noncomputable def qs (y : ℝ) (D : Finset ℕ) : ℕ :=
  open Classical in (D.filter (fun q => ¬ ChiG Cst y (D.filter (fun r => q ≤ r)))).sup id

theorem filter_ge_lt_union (D : Finset ℕ) (q : ℕ) :
    D.filter (fun r => q ≤ r) ∪ D.filter (fun r => r < q) = D := by
  ext x; simp only [mem_union, mem_filter]; constructor
  · rintro (h | h)
    · exact h.1
    · exact h.1
  · intro hx; by_cases h : q ≤ x
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, by omega⟩

theorem odd_class_shift {k : ℕ} (hk : Odd k) (j : ℕ) : Even (j + k) ↔ Odd j := by
  rw [Nat.even_add]; constructor
  · intro h; by_contra hj
    rw [Nat.not_odd_iff_even] at hj
    exact (Nat.not_even_iff_odd.2 hk) (h.1 hj)
  · intro hj
    exact ⟨fun he => absurd he (Nat.not_even_iff_odd.2 hj), fun he => absurd he (Nat.not_even_iff_odd.2 hk)⟩

/-- The exact identity in set form. -/
theorem exact_set (b : ℕ) (y z : ℝ) :
    ∑ D ∈ (primesBelow z).powerset, (-1 : ℝ) ^ D.card * gD b D * Fs y D =
      ∑ Δ ∈ Dsf y z, (W1 - ∑ p ∈ Δ, wy y p) * gD b Δ *
        ∑ T ∈ ((primesBelow z).filter (· < (∏ p ∈ Δ, p).minFac)).powerset,
          (-1 : ℝ) ^ T.card * gD b T * (if ChiG Odd (y / ((∏ p ∈ Δ, p : ℕ) : ℝ)) T then 1 else 0) := by
  classical
  set S := primesBelow z with hSdef
  have hSp : ∀ p ∈ S, p.Prime := fun p hp => primesBelow_prime hp
  -- left side: restrict to `χ⁻ ∧ ¬χ*`
  set tt := S.powerset.filter (fun D => ChiG Even y D ∧ ¬ ChiG Cst y D) with htt
  have hL : ∑ D ∈ S.powerset, (-1 : ℝ) ^ D.card * gD b D * Fs y D =
      ∑ D ∈ tt, (-1 : ℝ) ^ D.card * gD b D * Fs y D := by
    rw [htt, sum_filter]
    apply sum_congr rfl; intro D _
    split_ifs with h
    · rfl
    · rw [Fs_zero y D h, mul_zero]
  -- right side: a sum over pairs
  set tf : Finset ℕ → Finset (Finset ℕ) := fun Δ =>
    S.powerset.filter (fun T => (∀ t ∈ T, ∀ p ∈ Δ, t < p) ∧ ChiG Odd (y / ((∏ p ∈ Δ, p : ℕ) : ℝ)) T) with htf
  set ss := (Dsf y z ×ˢ S.powerset).filter (fun x => x.2 ∈ tf x.1) with hss
  have hDsfS : ∀ Δ ∈ Dsf y z, Δ ⊆ S := fun Δ hΔ => by unfold Dsf at hΔ; exact mem_powerset.1 (mem_filter.1 hΔ).1
  have hfib : ∀ Δ ∈ Dsf y z, ∑ T ∈ (S.filter (· < (∏ p ∈ Δ, p).minFac)).powerset,
        (-1 : ℝ) ^ T.card * gD b T * (if ChiG Odd (y / ((∏ p ∈ Δ, p : ℕ) : ℝ)) T then 1 else 0) =
      ∑ T ∈ tf Δ, (-1 : ℝ) ^ T.card * gD b T := by
    intro Δ hΔ
    have hΔS := hDsfS Δ hΔ
    have hΔp : ∀ p ∈ Δ, p.Prime := fun p hp => hSp p (hΔS hp)
    obtain ⟨hne, -⟩ := (mem_Dsf_iff y z hΔS).1 hΔ
    obtain ⟨hm, hmin⟩ := minFac_prod hΔp hne
    rw [htf, sum_filter]
    apply sum_subset_zero_on_sdiff
    · intro T hT; rw [mem_powerset] at hT ⊢; exact hT.trans (filter_subset _ _)
    · intro T hT
      rw [mem_sdiff, mem_powerset, mem_powerset] at hT
      rw [if_neg]
      rintro ⟨h1, -⟩
      apply hT.2
      intro t ht
      exact mem_filter.2 ⟨hT.1 ht, h1 t ht _ hm⟩
    · intro T hT
      rw [mem_powerset] at hT
      have hlt : ∀ t ∈ T, ∀ p ∈ Δ, t < p := fun t ht p hp =>
        lt_of_lt_of_le (mem_filter.1 (hT ht)).2 (hmin p hp)
      by_cases hc : ChiG Odd (y / ((∏ p ∈ Δ, p : ℕ) : ℝ)) T
      · rw [if_pos hc, mul_one, if_pos (And.intro hlt hc)]
      · rw [if_neg hc, mul_zero, if_neg (fun h => hc h.2)]
  have hR : ∑ Δ ∈ Dsf y z, (W1 - ∑ p ∈ Δ, wy y p) * gD b Δ *
        ∑ T ∈ (S.filter (· < (∏ p ∈ Δ, p).minFac)).powerset,
          (-1 : ℝ) ^ T.card * gD b T * (if ChiG Odd (y / ((∏ p ∈ Δ, p : ℕ) : ℝ)) T then 1 else 0) =
      ∑ x ∈ ss, (W1 - ∑ p ∈ x.1, wy y p) * gD b x.1 * ((-1 : ℝ) ^ x.2.card * gD b x.2) := by
    rw [sum_congr rfl (fun Δ hΔ => by rw [hfib Δ hΔ])]
    rw [Finset.sum_finset_product ss (Dsf y z) tf (fun x => by
      rw [hss, mem_filter, mem_product]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩
        exact ⟨⟨h1, (mem_filter.1 h3).1⟩, h3⟩)]
    apply sum_congr rfl; intro Δ _; rw [mul_sum]
  rw [hL, hR]
  symm
  -- the bijection `(Δ, T) ↦ Δ ∪ T`
  apply Finset.sum_nbij' (fun x => x.1 ∪ x.2)
    (fun D => (D.filter (fun r => qs y D ≤ r), D.filter (fun r => r < qs y D)))
  · -- hi
    intro x hx
    rw [hss, mem_filter, mem_product] at hx
    obtain ⟨⟨hΔ, hT⟩, hx2⟩ := hx
    rw [htf, mem_filter] at hx2
    obtain ⟨-, hlt, hodd⟩ := hx2
    have hΔS := hDsfS _ hΔ
    have hTS := mem_powerset.1 hT
    have hΔp : ∀ p ∈ x.1, p.Prime := fun p hp => hSp p (hΔS hp)
    have hTp : ∀ p ∈ x.2, p.Prime := fun p hp => hSp p (hTS hp)
    obtain ⟨hE, hnS, -, -⟩ := Dsf_facts y z hΔS hΔ
    obtain ⟨-, -, -, hcard, -⟩ := (mem_Dsf_iff y z hΔS).1 hΔ
    rw [htt, mem_filter, mem_powerset]
    refine ⟨union_subset hΔS hTS, ?_, ?_⟩
    · rw [chiG_union Even y hΔp hTp hlt]
      exact ⟨hE, (chiG_congr_class (odd_class_shift hcard)).2 hodd⟩
    · intro h; exact hnS (chiG_mono subset_union_left h)
  · -- hj
    intro D hD
    rw [htt, mem_filter, mem_powerset] at hD
    obtain ⟨hDS, hDE, hDS'⟩ := hD
    have hDp : ∀ p ∈ D, p.Prime := fun p hp => hSp p (hDS hp)
    set V := D.filter (fun q => ¬ ChiG Cst y (D.filter (fun r => q ≤ r))) with hV
    have hDne : D.Nonempty := by
      rw [nonempty_iff_ne_empty]; rintro rfl; exact hDS' (chiG_empty _ _)
    have hVne : V.Nonempty := by
      refine ⟨D.min' hDne, mem_filter.2 ⟨min'_mem D hDne, ?_⟩⟩
      have : D.filter (fun r => D.min' hDne ≤ r) = D := by
        ext r; simp only [mem_filter, and_iff_left_iff_imp]; exact fun hr => min'_le D r hr
      rw [this]; exact hDS'
    obtain ⟨q0, hq0V, hq0⟩ := Finset.exists_mem_eq_sup V hVne id
    have hqs : qs y D = q0 := by rw [qs, ← hV, hq0]; rfl
    have hqV : qs y D ∈ V := by rw [hqs]; exact hq0V
    have hqmax : ∀ q ∈ V, q ≤ qs y D := fun q hq => by
      rw [qs, ← hV]; exact Finset.le_sup (f := id) hq
    set q := qs y D
    have hqD : q ∈ D := (mem_filter.1 hqV).1
    have hqviol : ¬ ChiG Cst y (D.filter (fun r => q ≤ r)) := (mem_filter.1 hqV).2
    set Δ := D.filter (fun r => q ≤ r) with hΔdef
    set T := D.filter (fun r => r < q) with hTdef
    have hΔS : Δ ⊆ S := (filter_subset _ _).trans hDS
    have hTS : T ⊆ S := (filter_subset _ _).trans hDS
    have hΔp : ∀ p ∈ Δ, p.Prime := fun p hp => hSp p (hΔS hp)
    have hTp : ∀ p ∈ T, p.Prime := fun p hp => hSp p (hTS hp)
    have hqΔ : q ∈ Δ := mem_filter.2 ⟨hqD, le_rfl⟩
    have hΔmin : ∀ r ∈ Δ, q ≤ r := fun r hr => (mem_filter.1 hr).2
    have hΔne : Δ.Nonempty := ⟨q, hqΔ⟩
    have hmf : (∏ p ∈ Δ, p).minFac = q := by
      obtain ⟨h1, h2⟩ := minFac_prod hΔp hΔne
      exact le_antisymm (h2 q hqΔ) (hΔmin _ h1)
    have hlt : ∀ t ∈ T, ∀ p ∈ Δ, t < p := fun t ht p hp =>
      lt_of_lt_of_le (mem_filter.1 ht).2 (hΔmin p hp)
    have hDU : D = Δ ∪ T := (filter_ge_lt_union D q).symm
    -- the top part `Δ \ {q}` satisfies `χ*`
    have hE' : ChiG Cst y (Δ.erase q) := by
      rcases (Δ.erase q).eq_empty_or_nonempty with he | hne'
      · rw [he]; exact chiG_empty _ _
      · set q' := (Δ.erase q).min' hne'
        have hq'mem : q' ∈ Δ.erase q := min'_mem _ hne'
        have hq'gt : q < q' := lt_of_le_of_ne (hΔmin q' (mem_of_mem_erase hq'mem)) (ne_of_mem_erase hq'mem).symm
        have hq'D : q' ∈ D := (mem_filter.1 (mem_of_mem_erase hq'mem)).1
        have hnotV : q' ∉ V := fun h => absurd (hqmax q' h) (not_le.2 hq'gt)
        have hok : ChiG Cst y (D.filter (fun r => q' ≤ r)) := by
          by_contra hc; exact hnotV (mem_filter.2 ⟨hq'D, hc⟩)
        have heq : D.filter (fun r => q' ≤ r) = Δ.erase q := by
          ext r; simp only [mem_filter, mem_erase, Δ]; constructor
          · rintro ⟨hr, hr'⟩; exact ⟨by omega, hr, by omega⟩
          · rintro ⟨hrq, hr, hqr⟩
            exact ⟨hr, min'_le _ r (mem_erase.2 ⟨hrq, mem_filter.2 ⟨hr, hqr⟩⟩)⟩
        rw [← heq]; exact hok
    have hEE : ChiG Even y (Δ.erase q) := chiG_mono ((erase_subset _ _).trans (filter_subset _ _)) hDE
    have hcE : ChiG Cchi y (Δ.erase q) := (chiG_chi_iff y _).2 ⟨hEE, hE'⟩
    obtain ⟨hsplit, hlt1, hcard⟩ := split_min hqΔ hΔmin
    have hEp : ∀ p ∈ Δ.erase q, p.Prime := fun p hp => hΔp p (mem_of_mem_erase hp)
    have hqp : ∀ p ∈ ({q} : Finset ℕ), p.Prime := by simp [hΔp q hqΔ]
    have U : ∀ C : ℕ → Prop, ChiG C y Δ ↔ ChiG C y (Δ.erase q) ∧
        (C Δ.card → (q : ℝ) ^ 3 < y / ((∏ p ∈ Δ.erase q, p : ℕ) : ℝ)) := by
      intro C
      conv_lhs => rw [hsplit]
      rw [chiG_union C y hEp hqp hlt1, chiG_singleton _ _ (hΔp q hqΔ), show 1 + (Δ.erase q).card = Δ.card by omega]
    have hCst : Cst Δ.card := by
      by_contra hc
      exact hqviol ((U Cst).2 ⟨hE', fun h => absurd h hc⟩)
    have hΔD : Δ ∈ Dsf y z := by
      rw [mem_Dsf_iff y z hΔS, hmf]
      exact ⟨hΔne, hcE, fun h => hqviol (chiG_mono_class (fun j hj => Or.inr hj.2) h), hCst.1, hCst.2⟩
    rw [hss, mem_filter, mem_product, htf, mem_filter]
    refine ⟨⟨hΔD, mem_powerset.2 hTS⟩, mem_powerset.2 hTS, hlt, ?_⟩
    have := ((chiG_union Even y hΔp hTp hlt).1 (hDU ▸ hDE)).2
    exact (chiG_congr_class (odd_class_shift hCst.1)).1 this
  · -- left_inv
    intro x hx
    rw [hss, mem_filter, mem_product] at hx
    obtain ⟨⟨hΔ, hT⟩, hx2⟩ := hx
    rw [htf, mem_filter] at hx2
    obtain ⟨-, hlt, -⟩ := hx2
    have hΔS := hDsfS _ hΔ
    have hΔp : ∀ p ∈ x.1, p.Prime := fun p hp => hSp p (hΔS hp)
    obtain ⟨hne, -⟩ := (mem_Dsf_iff y z hΔS).1 hΔ
    obtain ⟨hm, hmin⟩ := minFac_prod hΔp hne
    obtain ⟨-, hnS, hE', -⟩ := Dsf_facts y z hΔS hΔ
    set m := (∏ p ∈ x.1, p).minFac
    have hTm : ∀ t ∈ x.2, t < m := fun t ht => hlt t ht m hm
    have hge : (x.1 ∪ x.2).filter (fun r => m ≤ r) = x.1 := by
      ext r; simp only [mem_filter, mem_union]; constructor
      · rintro ⟨h | h, hr⟩
        · exact h
        · exact absurd hr (not_le.2 (hTm r h))
      · intro h; exact ⟨Or.inl h, hmin r h⟩
    have hlt' : (x.1 ∪ x.2).filter (fun r => r < m) = x.2 := by
      ext r; simp only [mem_filter, mem_union]; constructor
      · rintro ⟨h | h, hr⟩
        · exact absurd (hmin r h) (not_le.2 hr)
        · exact h
      · intro h; exact ⟨Or.inr h, hTm r h⟩
    have hq : qs y (x.1 ∪ x.2) = m := by
      apply le_antisymm
      · apply Finset.sup_le
        intro q hq
        rw [mem_filter] at hq
        obtain ⟨hqU, hqv⟩ := hq
        by_contra hgt
        push Not at hgt
        apply hqv
        apply chiG_mono _ hE'
        intro r hr
        rw [mem_filter, mem_union] at hr
        obtain ⟨hr1 | hr1, hr2⟩ := hr
        · exact mem_erase.2 ⟨by simp only [id] at hgt; omega, hr1⟩
        · exact absurd (lt_of_lt_of_le hgt hr2) (not_lt.2 (le_of_lt (hTm r hr1)))
      · have hmV : m ∈ (x.1 ∪ x.2).filter (fun q => ¬ ChiG Cst y ((x.1 ∪ x.2).filter (fun r => q ≤ r))) :=
          mem_filter.2 ⟨mem_union_left _ hm, by beta_reduce; rw [hge]; exact hnS⟩
        exact Finset.le_sup (f := id) hmV
    rw [hq, hge, hlt']
  · -- right_inv
    intro D _
    exact filter_ge_lt_union D (qs y D)
  · -- values
    intro x hx
    rw [hss, mem_filter, mem_product] at hx
    obtain ⟨⟨hΔ, hT⟩, hx2⟩ := hx
    rw [htf, mem_filter] at hx2
    obtain ⟨-, hlt, hodd⟩ := hx2
    have hΔS := hDsfS _ hΔ
    have hTS := mem_powerset.1 hT
    have hΔp : ∀ p ∈ x.1, p.Prime := fun p hp => hSp p (hΔS hp)
    have hTp : ∀ p ∈ x.2, p.Prime := fun p hp => hSp p (hTS hp)
    obtain ⟨hne, -, -, hcard, -⟩ := (mem_Dsf_iff y z hΔS).1 hΔ
    obtain ⟨hm, hmin⟩ := minFac_prod hΔp hne
    obtain ⟨hE, hnS, hE', -⟩ := Dsf_facts y z hΔS hΔ
    set m := (∏ p ∈ x.1, p).minFac
    have hdisj : Disjoint x.1 x.2 := by
      rw [disjoint_left]; intro a ha hb; exact lt_irrefl a (hlt a hb a ha)
    have hEU : ChiG Even y (x.1 ∪ x.2) := by
      rw [chiG_union Even y hΔp hTp hlt]
      exact ⟨hE, (chiG_congr_class (odd_class_shift hcard)).2 hodd⟩
    have hCU : ¬ ChiG Cchi y (x.1 ∪ x.2) := fun h =>
      hnS (chiG_mono subset_union_left ((chiG_chi_iff y _).1 h).2)
    have hw : ∑ p ∈ x.1 ∪ x.2, wy y p * (if ChiG Cst y ((x.1 ∪ x.2).filter (fun q => p < q)) then 1 else 0) =
        ∑ p ∈ x.1, wy y p := by
      rw [sum_union hdisj]
      have h1 : ∀ p ∈ x.1, wy y p * (if ChiG Cst y ((x.1 ∪ x.2).filter (fun q => p < q)) then 1 else 0) = wy y p := by
        intro p hp
        rw [if_pos, mul_one]
        apply chiG_mono _ hE'
        intro r hr
        rw [mem_filter, mem_union] at hr
        obtain ⟨hr1 | hr1, hr2⟩ := hr
        · exact mem_erase.2 ⟨by have := hmin p hp; omega, hr1⟩
        · exact absurd (lt_trans (hlt r hr1 p hp) hr2) (lt_irrefl r)
      have h2 : ∀ p ∈ x.2, wy y p * (if ChiG Cst y ((x.1 ∪ x.2).filter (fun q => p < q)) then 1 else 0) = 0 := by
        intro p hp
        rw [if_neg, mul_zero]
        intro h
        apply hnS
        apply chiG_mono _ h
        intro r hr
        exact mem_filter.2 ⟨mem_union_left _ hr, hlt p hp r hr⟩
      rw [sum_congr rfl h1, sum_congr rfl h2, sum_const_zero, add_zero]
    unfold Fs
    rw [if_neg hCU, if_pos hEU, hw, card_union_of_disjoint hdisj, pow_add, gD, gD, gD, prod_union hdisj,
      Odd.neg_one_pow hcard]
    ring

/-- **Exact identity** (Greaves (4.9) = (4.10)). -/
theorem exact_identity (b : ℕ) (y : ℝ) :
    M1 b y - Mstar b y (y ^ UU) = ∑ δ ∈ Dset y (y ^ UU) mm,
      phiW W1 (wy y) δ * rhoB b δ / δ * Tpm b true (y / δ) (δ.minFac) := by
  have hL : M1 b y - Mstar b y (y ^ UU) =
      ∑ D ∈ (primesBelow (y ^ UU)).powerset, (-1 : ℝ) ^ D.card * gD b D * Fs y D := by
    rw [M1_set, Mstar_set, ← sum_sub_distrib]
    apply sum_congr rfl; intro D _; unfold Fs; ring
  rw [hL, exact_set, sum_Dset]
  apply sum_congr rfl
  intro Δ hΔ
  have hΔS : Δ ⊆ primesBelow (y ^ UU) := by unfold Dsf at hΔ; exact mem_powerset.1 (mem_filter.1 hΔ).1
  have hΔp : ∀ p ∈ Δ, p.Prime := fun p hp => primesBelow_prime (hΔS hp)
  obtain ⟨hne, -⟩ := (mem_Dsf_iff y _ hΔS).1 hΔ
  obtain ⟨hm, -⟩ := minFac_prod hΔp hne
  rw [phiW_prod _ hΔp, mul_assoc, mul_div_assoc, rho_div_prod b hΔp, Tplus_set,
    ← primesBelow_filter_lt _ (hΔS hm)]
  ring

end KappaOmega2.M07
