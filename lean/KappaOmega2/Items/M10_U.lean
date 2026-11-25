import KappaOmega2.Items.M10_Buch
import KappaOmega2.Items.M10_L

/-!
# M10 helper: the uniform Lemma 9 from the pointwise one (`M10_PLAN.md` §4.3, §4.4)

Input `RosserBoundStmt` (Rosser–Iwaniec upper bounds `|T^±(η, ζ)| ≤ C V(ζ)`, `s ≥ 1` resp. `s ≥ 2`); Mertens from
Palprimes; grid in `s` plus Buchstab equicontinuity.
-/

set_option linter.style.longLine false

open Finset Real
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius

namespace KappaOmega2

open Palprimes Palprimes.Greaves

/-- Rosser–Iwaniec upper bounds for the Rosser sums (classical; from Palprimes `E1.rosserAsymp_of_two_le` for
`s ≤ 9` and the monotonicity of the Rosser remainders in `ζ` for `s > 9`). -/
def RosserBoundStmt (b : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ ζ η : ℝ, 2 ≤ ζ →
    (ζ < η → |Tpm b true η ζ| ≤ C * MT.VB b ζ) ∧ (ζ ^ 2 < η → |Tpm b false η ζ| ≤ C * MT.VB b ζ)

namespace M10

open Classical

/-- `Π_{ζ < q < η} (1 + γ(q)/q) ≤ V(ζ)/V(η)`. -/
theorem prod_one_add_gt_le (b : ℕ) {ζ η : ℝ} (h : ζ ≤ η) :
    ∏ q ∈ (primesBelow η).filter (fun q : ℕ => ζ < (q : ℝ)), (1 + rhoB b q / q) ≤ MT.VB b ζ / MT.VB b η := by
  set S' := (primesBelow η).filter (fun q : ℕ => ζ < (q : ℝ)) with hS'
  set S'' := (primesBelow η).filter (fun q : ℕ => ¬ ζ < (q : ℝ)) with hS''
  have hgB : ∀ q ∈ primesBelow η, rhoB b q / (q : ℝ) = MT.gB b q := fun q hq => rhoB_div_eq_gB b (primes_PB η q hq)
  have hP1 : (∏ q ∈ S', (1 + rhoB b q / q)) * (∏ q ∈ S', (1 - MT.gB b q)) ≤ 1 := by
    rw [← prod_mul_distrib]
    apply prod_le_one₀
    · intro q hq
      rw [hgB q (mem_filter.1 hq).1]
      have := MT.gB_nonneg b q; have := E1.gB_le_half' b q; nlinarith
    · intro q hq
      rw [hgB q (mem_filter.1 hq).1]
      have := MT.gB_nonneg b q; nlinarith
  have hsplit : MT.VB b η = (∏ q ∈ S', (1 - MT.gB b q)) * ∏ q ∈ S'', (1 - MT.gB b q) := by
    unfold MT.VB; rw [hS', hS'', prod_filter_mul_prod_filter_not]
  have hS''le : ∏ q ∈ S'', (1 - MT.gB b q) ≤ MT.VB b ζ := by
    unfold MT.VB
    apply prod_le_prod_of_subset_of_le_one₀
    · intro q hq
      rw [mem_primesBelow] at hq
      rw [hS'', mem_filter, mem_primesBelow]
      exact ⟨⟨hq.1, lt_of_lt_of_le hq.2 h⟩, not_lt.2 hq.2.le⟩
    · intro q _; have := E1.gB_le_half' b q; linarith
    · intro q _ _; have := MT.gB_nonneg b q; linarith
  have hpos' : 0 < ∏ q ∈ S', (1 - MT.gB b q) := prod_pos fun q _ => by have := E1.gB_le_half' b q; linarith
  have hpos'' : 0 < ∏ q ∈ S'', (1 - MT.gB b q) := prod_pos fun q _ => by have := E1.gB_le_half' b q; linarith
  have hVη : 0 < MT.VB b η := E1.VB_pos' b η
  calc ∏ q ∈ S', (1 + rhoB b q / q) ≤ 1 / ∏ q ∈ S', (1 - MT.gB b q) := by rw [le_div_iff₀ hpos']; exact hP1
    _ = (∏ q ∈ S'', (1 - MT.gB b q)) / MT.VB b η := by
        rw [hsplit, div_mul_eq_div_div_swap, div_self hpos''.ne']
    _ ≤ MT.VB b ζ / MT.VB b η := div_le_div_of_nonneg_right hS''le hVη.le

/-- `Σ_{ζ ≤ q < ζ'} g(q) ≤ log(V(ζ)/V(ζ'))`. -/
theorem sum_gB_le_log (b : ℕ) {ζ ζ' : ℝ} (h : ζ ≤ ζ') :
    ∑ q ∈ (primesBelow ζ').filter (fun q : ℕ => ζ ≤ (q : ℝ)), MT.gB b q ≤ Real.log (MT.VB b ζ / MT.VB b ζ') := by
  have hsplit := E1.VB_split' b ζ ζ' h
  have hIco : E1.primesIco ζ ζ' = (primesBelow ζ').filter (fun q : ℕ => ζ ≤ (q : ℝ)) := by
    unfold E1.primesIco; congr 1; ext q; exact not_lt
  rw [hIco] at hsplit
  have hVζ := E1.VB_pos' b ζ
  have hpos : ∀ q ∈ (primesBelow ζ').filter (fun q : ℕ => ζ ≤ (q : ℝ)), 0 < 1 - MT.gB b q :=
    fun q _ => by have := E1.gB_le_half' b q; linarith
  rw [hsplit, div_mul_eq_div_div, div_self hVζ.ne', Real.log_div one_ne_zero (prod_pos hpos).ne', Real.log_one,
    zero_sub, Real.log_prod (fun q hq => (hpos q hq).ne'), ← sum_neg_distrib]
  apply sum_le_sum; intro q hq
  have := Real.log_le_sub_one_of_pos (hpos q hq)
  linarith

/-- Mertens increments: for every `θ > 0` there are `δ ∈ (0, 1/2]` and `ζ₁` with
`Σ_{ζ ≤ q < ζ'} g(q) ≤ θ` whenever `ζ₁ ≤ ζ ≤ ζ' ≤ ζ^{1+2δ}`. -/
theorem mertens_increment (b : ℕ) (hb : 2 ≤ b) {θ : ℝ} (hθ : 0 < θ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ ∃ ζ₁ : ℝ, 1 < ζ₁ ∧ ∀ ζ ζ' : ℝ, ζ₁ ≤ ζ → ζ ≤ ζ' → ζ' ≤ ζ ^ (1 + 2 * δ) →
      ∑ q ∈ (primesBelow ζ').filter (fun q : ℕ => ζ ≤ (q : ℝ)), MT.gB b q ≤ θ := by
  set δ := min (θ / 4) (1 / 2) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ1 : δ ≤ 1 / 2 := min_le_right _ _
  have hδθ : δ ≤ θ / 4 := min_le_left _ _
  have ha0 : 0 < 1 / (1 + 2 * δ) := by positivity
  have ha1 : 1 / (1 + 2 * δ) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  obtain ⟨y₀, hy₀, hr⟩ := E1.VB_ratio' b hb (1 / (1 + 2 * δ)) ha0 ha1 (θ / 2) (by linarith)
  refine ⟨δ, hδ0, hδ1, max y₀ 2, lt_of_lt_of_le one_lt_two (le_max_right _ _), fun ζ ζ' hζ hζζ' hζ' => ?_⟩
  have hζ1 : 1 < ζ := lt_of_lt_of_le hy₀ (le_trans (le_max_left _ _) hζ)
  have hζ'y : y₀ ≤ ζ' := le_trans (le_trans (le_max_left _ _) hζ) hζζ'
  have hwa : ζ' ^ (1 / (1 + 2 * δ)) ≤ ζ := by
    calc ζ' ^ (1 / (1 + 2 * δ)) ≤ (ζ ^ (1 + 2 * δ)) ^ (1 / (1 + 2 * δ)) :=
          Real.rpow_le_rpow (by linarith) hζ' (by positivity)
      _ = ζ := by rw [← Real.rpow_mul (by linarith), mul_one_div_cancel (by positivity), Real.rpow_one]
  have h := hr ζ' hζ'y ζ hwa hζζ'
  have hlog : Real.log ζ' / Real.log ζ ≤ 1 + 2 * δ := by
    rw [div_le_iff₀ (Real.log_pos hζ1)]
    have := Real.log_le_log (by linarith) hζ'
    rwa [Real.log_rpow (by linarith)] at this
  have hratio : MT.VB b ζ / MT.VB b ζ' ≤ 1 + 2 * δ + θ / 2 := by
    have := (abs_le.1 h).2; linarith
  refine le_trans (sum_gB_le_log b hζζ') ?_
  have hpos : 0 < MT.VB b ζ / MT.VB b ζ' := div_pos (E1.VB_pos' b ζ) (E1.VB_pos' b ζ')
  calc Real.log (MT.VB b ζ / MT.VB b ζ') ≤ MT.VB b ζ / MT.VB b ζ' - 1 := Real.log_le_sub_one_of_pos hpos
    _ ≤ θ := by linarith

/-- Mertens ratio: `V(ζ)/V(η) ≤ S + 1` for `ζ ≤ η ≤ ζ^S`, `ζ` large. -/
theorem mertens_ratio (b : ℕ) (hb : 2 ≤ b) {S : ℝ} (hS : 1 ≤ S) :
    ∃ ζ₂ : ℝ, 1 < ζ₂ ∧ ∀ ζ η : ℝ, ζ₂ ≤ ζ → ζ ≤ η → η ≤ ζ ^ S → MT.VB b ζ / MT.VB b η ≤ S + 1 := by
  have ha0 : 0 < 1 / S := by positivity
  have ha1 : 1 / S ≤ 1 := by rw [div_le_one (by linarith)]; exact hS
  obtain ⟨y₀, hy₀, hr⟩ := E1.VB_ratio' b hb (1 / S) ha0 ha1 1 one_pos
  refine ⟨y₀, hy₀, fun ζ η hζ hζη hηS => ?_⟩
  have hζ1 : 1 < ζ := lt_of_lt_of_le hy₀ hζ
  have hwa : η ^ (1 / S) ≤ ζ := by
    calc η ^ (1 / S) ≤ (ζ ^ S) ^ (1 / S) := Real.rpow_le_rpow (by linarith) hηS (by positivity)
      _ = ζ := by rw [← Real.rpow_mul (by linarith), mul_one_div_cancel (by linarith), Real.rpow_one]
  have h := hr η (le_trans hζ hζη) ζ hwa hζη
  have hlog : Real.log η / Real.log ζ ≤ S := by
    rw [div_le_iff₀ (Real.log_pos hζ1)]
    have := Real.log_le_log (by linarith) hηS
    rwa [Real.log_rpow (by linarith)] at this
  have := (abs_le.1 h).2; linarith

/-- `σ⁺(u) ≤ 4C V(u)` for large `u`. -/
theorem sigma_bound (b : ℕ) (hb : 2 ≤ b) (hRB : RosserBoundStmt b) :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∃ u₀ : ℝ, 8 ≤ u₀ ∧ ∀ u ≥ u₀, |sigmaP b u| ≤ C₂ * MT.VB b u := by
  obtain ⟨C, hC0, hC⟩ := hRB
  obtain ⟨y₀, hy₀, hr⟩ := E1.VB_ratio' b hb (1 / 3) (by norm_num) (by norm_num) 1 one_pos
  refine ⟨4 * C, by positivity, max y₀ 8, le_max_right _ _, fun u hu => ?_⟩
  have hu8 : 8 ≤ u := le_trans (le_max_right _ _) hu
  have hu0 : 0 < u := by linarith
  have h2 : 2 ≤ u ^ ((1 : ℝ) / 3) := by
    have : (8 : ℝ) ^ ((1 : ℝ) / 3) = 2 := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [← this]; exact Real.rpow_le_rpow (by norm_num) hu8 (by norm_num)
  have hle : u ^ ((1 : ℝ) / 3) ≤ u := Real.rpow_le_self_of_one_le (by linarith) (by norm_num)
  have hlt : u ^ ((1 : ℝ) / 3) < u := Real.rpow_lt_self_of_one_lt (by linarith) (by norm_num)
  have h1 := (hC _ u h2).1 hlt
  unfold sigmaP
  refine le_trans h1 ?_
  have h := hr u (le_trans (le_max_left _ _) hu) (u ^ ((1 : ℝ) / 3)) le_rfl hle
  have hl : Real.log u / Real.log (u ^ ((1 : ℝ) / 3)) = 3 := by
    rw [Real.log_rpow hu0]; field_simp [(Real.log_pos (by linarith : (1 : ℝ) < u)).ne']
  rw [hl] at h
  have hVu := E1.VB_pos' b u
  have h3 : MT.VB b (u ^ ((1 : ℝ) / 3)) ≤ 4 * MT.VB b u := by
    have h' : MT.VB b (u ^ ((1 : ℝ) / 3)) / MT.VB b u ≤ 4 := by have := (abs_le.1 h).2; linarith
    rw [div_le_iff₀ hVu] at h'; linarith
  nlinarith

/-- The exact case: `T⁺(η, ζ) = R⁺(η, ζ)` for `0 < η ≤ ζ³`. -/
theorem exact_plus (b : ℕ) {η ζ : ℝ} (hη : 0 < η) (hζ : 0 < ζ) (h3 : η ≤ ζ ^ 3) :
    Tpm b true η ζ = Rpm b η ζ true := by
  have hcbrt : η ^ ((1 : ℝ) / 3) ≤ ζ := by
    calc η ^ ((1 : ℝ) / 3) ≤ (ζ ^ 3) ^ ((1 : ℝ) / 3) := Real.rpow_le_rpow hη.le h3 (by norm_num)
      _ = ζ := by
        rw [show (ζ ^ 3) = ζ ^ (3 : ℝ) by norm_cast, ← Real.rpow_mul hζ.le]; norm_num
  rw [Tpm_set, sigma_set b hη hcbrt]
  unfold Rpm
  have hS9 : S9 η ζ true = {1} := by
    ext t
    unfold S9
    simp only [mem_filter, mem_singleton, if_true]
    constructor
    · rintro ⟨ht, hgt, hlt, hev⟩
      by_contra ht1
      have ht0 : 0 < t := Nat.pos_of_mem_divisors ht
      have htp : ¬ t.Prime := by
        intro h; rw [ArithmeticFunction.cardDistinctFactors_apply_prime h] at hev; exact Nat.not_even_one hev
      have hsq := Nat.minFac_sq_le_self ht0 htp
      have hmf : t.minFac ∈ t.primeFactors := Nat.mem_primeFactors.2 ⟨Nat.minFac_prime ht1, Nat.minFac_dvd t, ht0.ne'⟩
      have h1 := hgt _ hmf
      have h2 := hlt _ hmf
      have ht0' : (0 : ℝ) < t := by exact_mod_cast ht0
      rw [lt_div_iff₀ ht0'] at h2
      have hsq' : ((t.minFac : ℕ) : ℝ) ^ 2 ≤ t := by exact_mod_cast hsq
      have : ζ ^ 3 < (t.minFac : ℝ) ^ 3 := pow_lt_pow_left₀ h1 hζ.le (by norm_num)
      nlinarith
    · rintro rfl
      refine ⟨Nat.mem_divisors.2 ⟨one_dvd _, (primorialLt_pos' η).ne'⟩, by simp, by simp, by simp⟩
  rw [hS9, sum_singleton]
  simp [rhoB]

/-- Buchstab equicontinuity: `|T^σ(η, ζ'') − T^σ(η, ζ)| ≤ C V(ζ) Σ_{ζ ≤ M < ζ''} g(M)`. -/
theorem Tpm_diff_bound (b : ℕ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ ζ η : ℝ, 2 ≤ ζ → (ζ < η → |Tpm b true η ζ| ≤ C * MT.VB b ζ) ∧ (ζ ^ 2 < η → |Tpm b false η ζ| ≤ C * MT.VB b ζ))
    (σ : Bool) {η ζ ζ'' : ℝ} (hη : 0 < η) (hζ : 2 ≤ ζ) (hζζ : ζ ≤ ζ'') (hσ : σ = false → ζ'' ^ 2 ≤ η) :
    |Tpm b σ η ζ'' - Tpm b σ η ζ| ≤ C * MT.VB b ζ * ∑ M ∈ (primesBelow ζ'').filter (fun M : ℕ => ζ ≤ (M : ℝ)), MT.gB b M := by
  rw [Tpm_diff b σ η hζζ, mul_sum]
  refine le_trans (abs_sum_le_sum_abs _ _) (sum_le_sum fun M hM => ?_)
  rw [mem_filter, mem_primesBelow] at hM
  obtain ⟨⟨hMp, hMζ''⟩, hζM⟩ := hM
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hMp.pos
  have hM2 : (2 : ℝ) ≤ M := le_trans hζ hζM
  have hg : rhoB b M / (M : ℝ) = MT.gB b M := rhoB_div_eq_gB b hMp
  have hgn := MT.gB_nonneg b M
  have hVM : MT.VB b M ≤ MT.VB b ζ := E1.VB_anti b hζM
  rw [hg, abs_mul, abs_mul, abs_neg, abs_of_nonneg hgn]
  have hT : |(if σ = true → (M : ℝ) ^ 3 < η then (1 : ℝ) else 0)| * |Tpm b (!σ) (η / M) M| ≤ C * MT.VB b ζ := by
    cases σ with
    | true =>
      simp only [Bool.not_true, forall_const]
      by_cases h3 : (M : ℝ) ^ 3 < η
      · rw [if_pos h3, abs_one, one_mul]
        have : (M : ℝ) ^ 2 < η / M := by rw [lt_div_iff₀ hM0]; nlinarith
        exact le_trans ((hC M (η / M) hM2).2 this) (mul_le_mul_of_nonneg_left hVM hC0)
      · rw [if_neg h3, abs_zero, zero_mul]; exact mul_nonneg hC0 (E1.VB_pos' b ζ).le
    | false =>
      simp only [Bool.not_false, Bool.false_eq_true, false_implies, if_true, abs_one, one_mul]
      have h2 := hσ rfl
      have : (M : ℝ) < η / M := by
        rw [lt_div_iff₀ hM0]
        have : (M : ℝ) ^ 2 < ζ'' ^ 2 := pow_lt_pow_left₀ hMζ'' hM0.le (by norm_num)
        nlinarith
      exact le_trans ((hC M (η / M) hM2).1 this) (mul_le_mul_of_nonneg_left hVM hC0)
  calc MT.gB b M * |(if σ = true → (M : ℝ) ^ 3 < η then (1 : ℝ) else 0)| * |Tpm b (!σ) (η / M) M|
      = MT.gB b M * (|(if σ = true → (M : ℝ) ^ 3 < η then (1 : ℝ) else 0)| * |Tpm b (!σ) (η / M) M|) := by ring
    _ ≤ MT.gB b M * (C * MT.VB b ζ) := mul_le_mul_of_nonneg_left hT hgn
    _ = C * MT.VB b ζ * MT.gB b M := by ring

/-- `Σ_{t | P(η), primes > ζ, r | t} γ(t)/t ≤ γ(r)/r Π_{ζ < q < η}(1 + γ(q)/q)`. -/
theorem sum_dvd_G_gt_le (b : ℕ) (η ζ : ℝ) {r : ℕ} (hr : r ∈ (primesBelow η).filter (fun q : ℕ => ζ < (q : ℝ))) :
    ∑ t ∈ (primorialLt η).divisors, (if (∀ q ∈ t.primeFactors, ζ < (q : ℝ)) ∧ r ∣ t then rhoB b t / (t : ℝ) else 0) ≤
      rhoB b r / r * ∏ q ∈ (primesBelow η).filter (fun q : ℕ => ζ < (q : ℝ)), (1 + rhoB b q / q) := by
  set S := (primesBelow η).filter (fun q : ℕ => ζ < (q : ℝ)) with hS
  have hrp : r.Prime := primes_PB η r (mem_filter.1 hr).1
  unfold primorialLt
  rw [sum_divisors_primes (primesBelow η) (primes_PB η)]
  have e : ∀ D ∈ (primesBelow η).powerset,
      (if (∀ q ∈ (∏ p ∈ D, p).primeFactors, ζ < (q : ℝ)) ∧ r ∣ ∏ p ∈ D, p then
        rhoB b (∏ p ∈ D, p) / ((∏ p ∈ D, p : ℕ) : ℝ) else 0) =
      (if (∀ q ∈ D, ζ < (q : ℝ)) ∧ r ∈ D then ∏ q ∈ D, rhoB b q / q else 0) := by
    intro D hD
    have hDp : ∀ p ∈ D, p.Prime := fun p hp => primes_PB η p (mem_powerset.1 hD hp)
    have hiff : r ∣ ∏ p ∈ D, p ↔ r ∈ D := by
      constructor
      · intro h
        obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hrp.prime _).1 h
        rwa [(Nat.prime_dvd_prime_iff_eq hrp (hDp q hq)).1 hpq]
      · intro h; exact Finset.dvd_prod_of_mem (fun q => q) h
    rw [Nat.primeFactors_prod hDp, G_prod b hDp]
    by_cases hA : (∀ q ∈ D, ζ < (q : ℝ)) ∧ r ∈ D
    · rw [if_pos ⟨hA.1, hiff.2 hA.2⟩, if_pos hA]
    · rw [if_neg (fun h => hA ⟨h.1, hiff.1 h.2⟩), if_neg hA]
  rw [sum_congr rfl e]
  rw [sum_powerset_of_support (filter_subset (fun q : ℕ => ζ < (q : ℝ)) (primesBelow η))]
  · have e2 : ∀ D ∈ S.powerset, (if (∀ q ∈ D, ζ < (q : ℝ)) ∧ r ∈ D then ∏ q ∈ D, rhoB b q / q else 0) =
        (if r ∈ D then ∏ q ∈ D, rhoB b q / q else 0) := by
      intro D hD
      have hall : ∀ q ∈ D, ζ < (q : ℝ) := fun q hq => (mem_filter.1 (mem_powerset.1 hD hq)).2
      by_cases hrD : r ∈ D
      · rw [if_pos ⟨hall, hrD⟩, if_pos hrD]
      · rw [if_neg (fun h => hrD h.2), if_neg hrD]
    rw [sum_congr rfl e2, sum_powerset_mem S hr]
    apply mul_le_mul_of_nonneg_left _ (G_nonneg b r)
    apply prod_le_prod_of_subset_of_one_le₀ (erase_subset r S)
    · intro q _; linarith [G_nonneg b q]
    · intro q _ _; linarith [G_nonneg b q]
  · intro E hE hne q hq
    rw [mem_filter]
    refine ⟨hE hq, ?_⟩
    by_contra h
    apply hne
    rw [if_neg]
    rintro ⟨h', _⟩; exact h (h' q hq)

/-- `|R(η, ζ) − R(η, ζ'')| ≤ B · V(ζ)/V(η) · Σ_{ζ ≤ r < ζ_top} g(r)` when `|σ⁺(u)| ≤ B` for `u > ζ`. -/
theorem Rpm_diff_bound (b : ℕ) (σ : Bool) {η ζ ζ'' ζtop B : ℝ} (hζ : 0 < ζ) (hζζ : ζ ≤ ζ'') (htop : ζ'' < ζtop)
    (hζη : ζ ≤ η) (hB : ∀ u : ℝ, ζ < u → |sigmaP b u| ≤ B) :
    |Rpm b η ζ σ - Rpm b η ζ'' σ| ≤ B * (MT.VB b ζ / MT.VB b η) *
      ∑ r ∈ (primesBelow ζtop).filter (fun q : ℕ => ζ ≤ (q : ℝ)), MT.gB b r := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB (ζ + 1) (by linarith))
  have hsub : S9 η ζ'' σ ⊆ S9 η ζ σ := by
    intro t ht
    unfold S9 at ht ⊢
    rw [mem_filter] at ht ⊢
    exact ⟨ht.1, fun q hq => lt_of_le_of_lt hζζ (ht.2.1 q hq), ht.2.2⟩
  unfold Rpm
  rw [← sum_sdiff hsub, add_sub_cancel_right]
  set S := (primesBelow η).filter (fun q : ℕ => ζ < (q : ℝ)) with hS
  set R' := S.filter (fun q : ℕ => (q : ℝ) ≤ ζ'') with hR'
  set G : ℕ → ℝ := fun n => rhoB b n / (n : ℝ) with hG
  have hG0 : ∀ n, 0 ≤ G n := fun n => G_nonneg b n
  -- pointwise bound and the r-cover
  have h1 : ∀ t ∈ S9 η ζ σ \ S9 η ζ'' σ, |rhoB b t / t * sigmaP b (η / t)| ≤
      B * ∑ r ∈ R', (if (∀ q ∈ t.primeFactors, ζ < (q : ℝ)) ∧ r ∣ t then G t else 0) := by
    intro t ht
    rw [mem_sdiff] at ht
    have ht1 := ht.1
    unfold S9 at ht1
    rw [mem_filter] at ht1
    have ht0 : 0 < t := Nat.pos_of_mem_divisors ht1.1
    -- a prime of t at most ζ''
    have hex : ∃ r ∈ t.primeFactors, (r : ℝ) ≤ ζ'' := by
      by_contra hcon
      push_neg at hcon
      apply ht.2
      unfold S9; rw [mem_filter]
      exact ⟨ht1.1, hcon, ht1.2.2⟩
    obtain ⟨r, hrt, hrζ⟩ := hex
    have hrp := Nat.prime_of_mem_primeFactors hrt
    have hζr : ζ < (r : ℝ) := ht1.2.1 r hrt
    have hrη : (r : ℝ) < η / t := ht1.2.2.1 r hrt
    have hr1 : (1 : ℝ) ≤ t := by exact_mod_cast ht0
    have hrR : r ∈ R' := by
      rw [hR', hS, mem_filter, mem_filter, mem_primesBelow]
      refine ⟨⟨⟨hrp, ?_⟩, hζr⟩, hrζ⟩
      exact lt_of_lt_of_le hrη (div_le_self (by linarith) hr1)
    have hsig := hB (η / t) (lt_trans hζr hrη)
    rw [abs_mul, abs_of_nonneg (hG0 t)]
    have hsingle := single_le_sum (f := fun r => (if (∀ q ∈ t.primeFactors, ζ < (q : ℝ)) ∧ r ∣ t then G t else 0))
      (fun r _ => by split_ifs <;> simp [hG0]) hrR
    rw [if_pos (show (∀ q ∈ t.primeFactors, ζ < (q : ℝ)) ∧ r ∣ t from
      ⟨ht1.2.1, Nat.dvd_of_mem_primeFactors hrt⟩)] at hsingle
    calc G t * |sigmaP b (η / t)| ≤ G t * B := mul_le_mul_of_nonneg_left hsig (hG0 t)
      _ ≤ B * ∑ r ∈ R', (if (∀ q ∈ t.primeFactors, ζ < (q : ℝ)) ∧ r ∣ t then G t else 0) := by
          rw [mul_comm]; exact mul_le_mul_of_nonneg_left hsingle hB0
  have hdiv : S9 η ζ σ \ S9 η ζ'' σ ⊆ (primorialLt η).divisors := fun t ht =>
    (mem_filter.1 (mem_sdiff.1 ht).1).1
  calc |∑ t ∈ S9 η ζ σ \ S9 η ζ'' σ, rhoB b t / t * sigmaP b (η / t)|
      ≤ ∑ t ∈ S9 η ζ σ \ S9 η ζ'' σ, B * ∑ r ∈ R', (if (∀ q ∈ t.primeFactors, ζ < (q : ℝ)) ∧ r ∣ t then G t else 0) :=
        le_trans (abs_sum_le_sum_abs _ _) (sum_le_sum h1)
    _ ≤ ∑ t ∈ (primorialLt η).divisors, B * ∑ r ∈ R', (if (∀ q ∈ t.primeFactors, ζ < (q : ℝ)) ∧ r ∣ t then G t else 0) :=
        sum_le_sum_of_subset_of_nonneg hdiv (fun t _ _ => mul_nonneg hB0 (sum_nonneg fun r _ => by split_ifs <;> simp [hG0]))
    _ = B * ∑ r ∈ R', ∑ t ∈ (primorialLt η).divisors, (if (∀ q ∈ t.primeFactors, ζ < (q : ℝ)) ∧ r ∣ t then G t else 0) := by
        rw [← mul_sum, sum_comm]
    _ ≤ B * ∑ r ∈ R', MT.gB b r * (MT.VB b ζ / MT.VB b η) := by
        apply mul_le_mul_of_nonneg_left _ hB0
        apply sum_le_sum; intro r hr
        have hrS : r ∈ S := (mem_filter.1 hr).1
        rw [← rhoB_div_eq_gB b (primes_PB η r (mem_filter.1 hrS).1)]
        refine le_trans (sum_dvd_G_gt_le b η ζ hrS) ?_
        exact mul_le_mul_of_nonneg_left (prod_one_add_gt_le b hζη) (G_nonneg b r)
    _ = B * (MT.VB b ζ / MT.VB b η) * ∑ r ∈ R', MT.gB b r := by rw [← sum_mul]; ring
    _ ≤ B * (MT.VB b ζ / MT.VB b η) * ∑ r ∈ (primesBelow ζtop).filter (fun q : ℕ => ζ ≤ (q : ℝ)), MT.gB b r := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hB0 (div_nonneg (E1.VB_pos' b ζ).le (E1.VB_pos' b η).le))
        apply sum_le_sum_of_subset_of_nonneg _ (fun r _ _ => MT.gB_nonneg b r)
        intro r hr
        rw [hR', hS, mem_filter, mem_filter, mem_primesBelow] at hr
        rw [mem_filter, mem_primesBelow]
        exact ⟨⟨hr.1.1.1, lt_of_le_of_lt hr.2 htop⟩, hr.1.2.le⟩

/-- §4.4: the uniform Lemma 9 from the pointwise one and the Rosser bounds. -/
theorem lemma9U_of_RB (b : ℕ) (hb : 2 ≤ b) (h9 : Lemma9Stmt b) (hRB : RosserBoundStmt b) : Lemma9UStmt b := by
  intro S ε hε
  obtain ⟨C₂, hC₂0, u₀, hu₀8, hσ⟩ := sigma_bound b hb hRB
  obtain ⟨C, hC0, hC⟩ := hRB
  set S' := max S 3 with hS'
  have hS'3 : (3 : ℝ) ≤ S' := le_max_right _ _
  obtain ⟨ζ₂, hζ₂1, hMR⟩ := mertens_ratio b hb (S := S') (by linarith)
  set K := C + C₂ * (S' + 1) + 1 with hK
  have hK0 : 0 < K := by positivity
  set θ := ε / (3 * K) with hθ
  have hθ0 : 0 < θ := by positivity
  obtain ⟨δ, hδ0, hδ1, ζ₁, hζ₁1, hMI⟩ := mertens_increment b hb hθ0
  set sg : Bool → ℕ → ℝ := fun pl j => (if pl then (3 : ℝ) else 2) + j * δ with hsg
  have hsg2 : ∀ pl j, 2 ≤ sg pl j := by
    intro pl j; simp only [hsg]
    have : (0 : ℝ) ≤ j * δ := by positivity
    cases pl <;> simp <;> linarith
  have hgrid : ∀ (j : ℕ) (pl : Bool), ∃ y₀ : ℝ, ∀ y ≥ y₀,
      |Tpm b pl y (y ^ (1 / sg pl j)) - T9sum b y (sg pl j) pl| ≤ ε / 3 * MT.VB b (y ^ (1 / sg pl j)) :=
    fun j pl => h9 (sg pl j) (by linarith [hsg2 pl j]) pl (fun _ => hsg2 pl j) (ε / 3) (by positivity)
  choose Y hY using hgrid
  set J := ⌈S' / δ⌉₊ with hJ
  set Ysum := ∑ j ∈ range (J + 1), (|Y j true| + |Y j false|) with hYsum
  refine ⟨max (max (max ζ₁ ζ₂) u₀) (max 2 Ysum), fun ζ hζ η hη pl hpl hηS => ?_⟩
  have hζζ₁ : ζ₁ ≤ ζ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_trans (le_max_left _ _) hζ)
  have hζζ₂ : ζ₂ ≤ ζ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_trans (le_max_left _ _) hζ)
  have hζu₀ : u₀ ≤ ζ := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hζ)
  have hζ2 : (2 : ℝ) ≤ ζ := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hζ)
  have hζY : Ysum ≤ ζ := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hζ)
  have hζ1 : (1 : ℝ) < ζ := by linarith
  have hζ0 : (0 : ℝ) < ζ := by linarith
  have hVζ := E1.VB_pos' b ζ
  by_cases hex : pl = true ∧ η ≤ ζ ^ 3
  · obtain ⟨rfl, h3⟩ := hex
    rw [exact_plus b hη hζ0 h3, sub_self, abs_zero]; positivity
  -- the generic case: s_lo < s ≤ S'
  set slo : ℝ := if pl then 3 else 2 with hslo
  have hslo2 : (2 : ℝ) ≤ slo := by simp only [hslo]; split_ifs <;> norm_num
  set L := Real.log ζ with hL
  have hL0 : 0 < L := Real.log_pos hζ1
  set s := Real.log η / L with hs
  have hηs : η = ζ ^ s := by
    rw [hs, Real.rpow_def_of_pos hζ0, ← hL, mul_div_cancel₀ _ hL0.ne', Real.exp_log hη]
  have hlo : slo < s := by
    have hpow : ζ ^ slo < η := by
      cases pl with
      | true =>
        simp only [hslo, if_true]
        have : ¬ η ≤ ζ ^ 3 := fun h => hex ⟨rfl, h⟩
        push_neg at this
        rw [show (ζ ^ (3 : ℝ)) = ζ ^ 3 by norm_cast]; exact this
      | false =>
        simp only [hslo, Bool.false_eq_true, if_false]
        rw [show (ζ ^ (2 : ℝ)) = ζ ^ 2 by norm_cast]; exact hpl rfl
    rw [hηs] at hpow
    exact (Real.rpow_lt_rpow_left_iff hζ1).1 hpow
  have hhi : s ≤ S' := by
    have : ζ ^ s ≤ ζ ^ S := by rw [← hηs]; exact hηS
    exact le_trans ((Real.rpow_le_rpow_left_iff hζ1).1 this) (le_max_left _ _)
  have hs2 : 2 < s := lt_of_le_of_lt hslo2 hlo
  -- grid index
  set j := ⌊(s - slo) / δ⌋₊ with hj
  have hjle : (j : ℝ) * δ ≤ s - slo := by
    have := Nat.floor_le (div_nonneg (by linarith) hδ0.le : 0 ≤ (s - slo) / δ)
    rw [le_div_iff₀ hδ0] at this; linarith
  have hjlt : s - slo < ((j : ℝ) + 1) * δ := by
    have := Nat.lt_floor_add_one ((s - slo) / δ)
    rw [div_lt_iff₀ hδ0] at this; linarith
  have hjJ : j ≤ J := by
    apply Nat.floor_le_of_le
    calc (s - slo) / δ ≤ S' / δ := div_le_div_of_nonneg_right (by linarith) hδ0.le
      _ ≤ ⌈S' / δ⌉₊ := Nat.le_ceil _
  set sj := sg pl j with hsj
  have hsj_eq : sj = slo + j * δ := by simp only [hsj, hsg, hslo]
  have hsj2 : 2 ≤ sj := hsg2 pl j
  have hsjs : sj ≤ s := by rw [hsj_eq]; linarith
  have hssj : s < sj + δ := by rw [hsj_eq]; linarith
  set ζj := η ^ (1 / sj) with hζj
  have hζj_eq : ζj = ζ ^ (s / sj) := by
    rw [hζj, hηs, ← Real.rpow_mul hζ0.le]; ring_nf
  have hζζj : ζ ≤ ζj := by
    rw [hζj_eq]
    calc ζ = ζ ^ (1 : ℝ) := (Real.rpow_one ζ).symm
      _ ≤ ζ ^ (s / sj) := Real.rpow_le_rpow_of_exponent_le hζ1.le (by rw [le_div_iff₀ (by linarith)]; linarith)
  have hζjδ : ζj ≤ ζ ^ (1 + δ) := by
    rw [hζj_eq]
    apply Real.rpow_le_rpow_of_exponent_le hζ1.le
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hζjtop : ζj < ζ ^ (1 + 2 * δ) :=
    lt_of_le_of_lt hζjδ (Real.rpow_lt_rpow_of_exponent_lt hζ1 (by linarith))
  have hζη : ζ ≤ η := by
    rw [hηs]; calc ζ = ζ ^ (1 : ℝ) := (Real.rpow_one ζ).symm
      _ ≤ ζ ^ s := Real.rpow_le_rpow_of_exponent_le hζ1.le (by linarith)
  -- term 1: Lemma 9 at the grid point
  have hYj : Y j pl ≤ η := by
    have h1 : Y j pl ≤ |Y j true| + |Y j false| := by
      cases pl
      · exact le_trans (le_abs_self _) (le_add_of_nonneg_left (abs_nonneg _))
      · exact le_trans (le_abs_self _) (le_add_of_nonneg_right (abs_nonneg _))
    have h2 : |Y j true| + |Y j false| ≤ Ysum :=
      single_le_sum (f := fun j => |Y j true| + |Y j false|) (fun _ _ => by positivity) (mem_range.2 (by omega))
    linarith
  have hT1 := hY j pl η hYj
  rw [T9sum_eq_Rpm] at hT1
  have hVζj : MT.VB b ζj ≤ MT.VB b ζ := E1.VB_anti b hζζj
  -- term 2: Buchstab
  have hT2 := Tpm_diff_bound b hC0 hC pl hη hζ2 hζζj (fun _ => by
    rw [hζj, ← Real.rpow_natCast, ← Real.rpow_mul hη.le]
    have h1η : 1 ≤ η := by linarith
    calc η ^ (1 / sj * ((2 : ℕ) : ℝ)) ≤ η ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1η (by
          rw [Nat.cast_ofNat, div_mul_eq_mul_div, one_mul, div_le_one (by linarith)]; exact hsj2)
      _ = η := Real.rpow_one η)
  have hMI1 := hMI ζ ζj hζζ₁ hζζj (le_trans hζjδ (Real.rpow_le_rpow_of_exponent_le hζ1.le (by linarith)))
  -- term 3: the t-sums
  have hB : ∀ u : ℝ, ζ < u → |sigmaP b u| ≤ C₂ * MT.VB b ζ := by
    intro u hu
    exact le_trans (hσ u (by linarith)) (mul_le_mul_of_nonneg_left (E1.VB_anti b hu.le) hC₂0)
  have hT3 := Rpm_diff_bound b pl hζ0 hζζj hζjtop hζη hB
  have hMI2 := hMI ζ (ζ ^ (1 + 2 * δ)) hζζ₁ (le_trans hζζj hζjtop.le) le_rfl
  have hMR1 := hMR ζ η hζζ₂ hζη (le_trans hηS (Real.rpow_le_rpow_of_exponent_le hζ1.le (le_max_left _ _)))
  -- combine
  have hsum1 : 0 ≤ ∑ M ∈ (primesBelow ζj).filter (fun M : ℕ => ζ ≤ (M : ℝ)), MT.gB b M :=
    sum_nonneg fun M _ => MT.gB_nonneg b M
  have hsum2 : 0 ≤ ∑ r ∈ (primesBelow (ζ ^ (1 + 2 * δ))).filter (fun q : ℕ => ζ ≤ (q : ℝ)), MT.gB b r :=
    sum_nonneg fun M _ => MT.gB_nonneg b M
  have hR0 : 0 ≤ MT.VB b ζ / MT.VB b η := div_nonneg hVζ.le (E1.VB_pos' b η).le
  calc |Tpm b pl η ζ - Rpm b η ζ pl|
      = |(Tpm b pl η ζj - Rpm b η ζj pl) - (Tpm b pl η ζj - Tpm b pl η ζ) - (Rpm b η ζ pl - Rpm b η ζj pl)| := by
        congr 1; ring
    _ ≤ |Tpm b pl η ζj - Rpm b η ζj pl| + |Tpm b pl η ζj - Tpm b pl η ζ| + |Rpm b η ζ pl - Rpm b η ζj pl| := by
        have a := abs_sub (Tpm b pl η ζj - Rpm b η ζj pl - (Tpm b pl η ζj - Tpm b pl η ζ)) (Rpm b η ζ pl - Rpm b η ζj pl)
        have c := abs_sub (Tpm b pl η ζj - Rpm b η ζj pl) (Tpm b pl η ζj - Tpm b pl η ζ)
        linarith
    _ ≤ ε / 3 * MT.VB b ζ + C * MT.VB b ζ * θ + C₂ * MT.VB b ζ * (S' + 1) * θ := by
        have e1 : |Tpm b pl η ζj - Rpm b η ζj pl| ≤ ε / 3 * MT.VB b ζ :=
          le_trans hT1 (mul_le_mul_of_nonneg_left hVζj (by positivity))
        have e2 : |Tpm b pl η ζj - Tpm b pl η ζ| ≤ C * MT.VB b ζ * θ :=
          le_trans hT2 (mul_le_mul_of_nonneg_left hMI1 (by positivity))
        have e3 : |Rpm b η ζ pl - Rpm b η ζj pl| ≤ C₂ * MT.VB b ζ * (S' + 1) * θ := by
          refine le_trans hT3 ?_
          exact mul_le_mul (mul_le_mul_of_nonneg_left hMR1 (by positivity)) hMI2 hsum2 (by positivity)
        linarith
    _ = (ε / 3 + (C + C₂ * (S' + 1)) * θ) * MT.VB b ζ := by ring
    _ ≤ ε * MT.VB b ζ := by
        apply mul_le_mul_of_nonneg_right _ hVζ.le
        have : (C + C₂ * (S' + 1)) * θ ≤ ε / 3 := by
          rw [hθ]
          have hK' : C + C₂ * (S' + 1) ≤ K := by rw [hK]; linarith
          calc (C + C₂ * (S' + 1)) * (ε / (3 * K)) ≤ K * (ε / (3 * K)) :=
                mul_le_mul_of_nonneg_right hK' (by positivity)
            _ = ε / 3 := by field_simp
        linarith

end M10

end KappaOmega2
