import KappaOmega2.Items.M10_Buch
import KappaOmega2.Items.M10_X
import KappaOmega2.Items.M10_U
import KappaOmega2.Items.M10_Bridge

/-!
# M10 helper: Rosser bounds (`M10_PLAN.md` §4.3)

R-a: `T⁺(η, ζ) ≥ V(ζ) ≥ T⁻(η, ζ)` (Buchstab induction); R-b: `T⁺ − V` and `V − T⁻` are non-decreasing in `ζ`;
hence `|T^±(η, ζ)| ≤ C V(ζ)` from two one-parameter bounds: `σ⁺(u) ≤ C₁ V(u)` and `T⁻(u, √u) ≥ −C V(√u)`
(the latter is Lemma 9 at `s = 2`, where the `t`-sum is empty).
-/

set_option linter.style.longLine false

open Finset Real
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius

namespace KappaOmega2.M10

open Palprimes Palprimes.Greaves
open Classical

theorem fm_one (b : ℕ) : fm b 1 = 1 := by simp [fm, rhoB]

theorem chiS_empty (σ : Bool) (Y : ℝ) : ChiS σ Y ∅ := by
  intro E hE hne; exact absurd (subset_empty.1 hE) (nonempty_iff_ne_empty.1 hne)

/-- Buchstab over all primes: `T^σ(Y, z) = 1 − Σ_{M < z} γ(M)/M [σ → M³ < Y] T^{¬σ}(Y/M, M)`. -/
theorem Tpm_rec (b : ℕ) (σ : Bool) (Y z : ℝ) :
    Tpm b σ Y z = 1 + ∑ M ∈ primesBelow z,
      -(rhoB b M / M) * (if σ = true → (M : ℝ) ^ 3 < Y then 1 else 0) * Tpm b (!σ) (Y / M) M := by
  rw [Tpm_max, fm_one, if_pos (chiS_empty σ Y), mul_one]
  congr 1
  apply sum_congr rfl; intro M hM
  exact head_sum b σ Y (primes_PB z M hM)

/-- R-a: `V(ζ) ≤ T⁺(η, ζ)` and `T⁻(η, ζ) ≤ V(ζ)`. -/
theorem rosser_pos (b : ℕ) : ∀ n : ℕ, ∀ ζ : ℝ, ζ ≤ n → ∀ η : ℝ,
    MT.VB b ζ ≤ Tpm b true η ζ ∧ Tpm b false η ζ ≤ MT.VB b ζ := by
  intro n
  induction n with
  | zero =>
    intro ζ hζ η
    have hPB : primesBelow ζ = ∅ := by
      apply eq_empty_of_forall_notMem; intro p hp
      rw [mem_primesBelow] at hp
      have : (0 : ℝ) ≤ p := Nat.cast_nonneg p
      push_cast at hζ; linarith [hp.2]
    have hV : MT.VB b ζ = 1 := by unfold MT.VB; rw [hPB, prod_empty]
    rw [Tpm_rec, Tpm_rec, hPB, sum_empty, sum_empty, hV]; simp
  | succ n ih =>
    intro ζ hζ η
    have htel := E1.telescope_primesBelow b ζ
    have hM : ∀ M ∈ primesBelow ζ, (M : ℝ) ≤ n := by
      intro M hM
      have h1 := ((mem_primesBelow ζ M).1 hM).2
      have : M < n + 1 := by
        have : (M : ℝ) < n + 1 := by push_cast at hζ; linarith
        exact_mod_cast this
      exact_mod_cast Nat.lt_succ_iff.1 this
    have hg : ∀ M ∈ primesBelow ζ, rhoB b M / (M : ℝ) = MT.gB b M := fun M hM => rhoB_div_eq_gB b (primes_PB ζ M hM)
    constructor
    · rw [Tpm_rec]
      have : MT.VB b ζ = 1 - ∑ M ∈ primesBelow ζ, MT.gB b M * MT.VB b M := by linarith
      rw [this]
      have key : ∀ M ∈ primesBelow ζ, -(MT.gB b M * MT.VB b M) ≤
          -(rhoB b M / M) * (if true = true → (M : ℝ) ^ 3 < η then 1 else 0) * Tpm b (!true) (η / M) M := by
        intro M hMm
        rw [hg M hMm]
        have hgn := MT.gB_nonneg b M
        have hV := E1.VB_pos' b M
        simp only [forall_const, Bool.not_true]
        by_cases h3 : (M : ℝ) ^ 3 < η
        · rw [if_pos h3, mul_one]
          have := (ih M (hM M hMm) (η / M)).2
          nlinarith
        · rw [if_neg h3, mul_zero, zero_mul]; nlinarith
      have := sum_le_sum key
      rw [sum_neg_distrib] at this
      linarith
    · rw [Tpm_rec]
      have : MT.VB b ζ = 1 - ∑ M ∈ primesBelow ζ, MT.gB b M * MT.VB b M := by linarith
      rw [this]
      have key : ∀ M ∈ primesBelow ζ,
          -(rhoB b M / M) * (if false = true → (M : ℝ) ^ 3 < η then 1 else 0) * Tpm b (!false) (η / M) M ≤
          -(MT.gB b M * MT.VB b M) := by
        intro M hMm
        rw [hg M hMm]
        have hgn := MT.gB_nonneg b M
        simp only [Bool.false_eq_true, false_implies, if_true, mul_one, Bool.not_false]
        have := (ih M (hM M hMm) (η / M)).1
        nlinarith
      have := sum_le_sum key
      rw [sum_neg_distrib] at this
      linarith

theorem rosser_pos' (b : ℕ) (ζ η : ℝ) : MT.VB b ζ ≤ Tpm b true η ζ ∧ Tpm b false η ζ ≤ MT.VB b ζ :=
  rosser_pos b ⌈ζ⌉₊ ζ (Nat.le_ceil ζ) η

/-- R-b: `T⁺ − V` and `V − T⁻` are non-decreasing in `ζ`. -/
theorem rosser_mono (b : ℕ) {ζ ζ' : ℝ} (h : ζ ≤ ζ') (η : ℝ) :
    Tpm b true η ζ - MT.VB b ζ ≤ Tpm b true η ζ' - MT.VB b ζ' ∧
      MT.VB b ζ - Tpm b false η ζ ≤ MT.VB b ζ' - Tpm b false η ζ' := by
  have htel := E1.telescope b h
  have hIco : E1.primesIco ζ ζ' = (primesBelow ζ').filter (fun q : ℕ => ζ ≤ (q : ℝ)) := by
    unfold E1.primesIco; congr 1; ext q; exact not_lt
  rw [hIco] at htel
  have hg : ∀ M ∈ (primesBelow ζ').filter (fun q : ℕ => ζ ≤ (q : ℝ)), rhoB b M / (M : ℝ) = MT.gB b M :=
    fun M hM => rhoB_div_eq_gB b (primes_PB ζ' M (mem_filter.1 hM).1)
  constructor
  · have hd := Tpm_diff b true η h
    have key : ∀ M ∈ (primesBelow ζ').filter (fun q : ℕ => ζ ≤ (q : ℝ)), 0 ≤ MT.gB b M * MT.VB b M +
        -(rhoB b M / M) * (if true = true → (M : ℝ) ^ 3 < η then 1 else 0) * Tpm b (!true) (η / M) M := by
      intro M hM
      rw [hg M hM]
      have hgn := MT.gB_nonneg b M
      have hV := E1.VB_pos' b M
      simp only [forall_const, Bool.not_true]
      by_cases h3 : (M : ℝ) ^ 3 < η
      · rw [if_pos h3, mul_one]
        have := (rosser_pos' b M (η / M)).2
        nlinarith
      · rw [if_neg h3, mul_zero, zero_mul, add_zero]; positivity
    have := sum_nonneg key
    rw [sum_add_distrib] at this
    linarith
  · have hd := Tpm_diff b false η h
    have key : ∀ M ∈ (primesBelow ζ').filter (fun q : ℕ => ζ ≤ (q : ℝ)), 0 ≤ -(MT.gB b M * MT.VB b M) -
        -(rhoB b M / M) * (if false = true → (M : ℝ) ^ 3 < η then 1 else 0) * Tpm b (!false) (η / M) M := by
      intro M hM
      rw [hg M hM]
      have hgn := MT.gB_nonneg b M
      simp only [Bool.false_eq_true, false_implies, if_true, mul_one, Bool.not_false]
      have := (rosser_pos' b M (η / M)).1
      nlinarith
    have := sum_nonneg key
    rw [sum_sub_distrib, sum_neg_distrib] at this
    linarith

/-- The `t`-sum of Lemma 9 at `s = 2`, sign `−`, is empty. -/
theorem T9sum_two_false (b : ℕ) {η : ℝ} (hη : 0 < η) : T9sum b η 2 false = 0 := by
  unfold T9sum
  apply sum_eq_zero
  intro t ht
  exfalso
  unfold T9set at ht
  rw [mem_filter] at ht
  obtain ⟨htd, hgt, hlt, hodd⟩ := ht
  simp only [Bool.false_eq_true, if_false] at hodd
  have ht0 : 0 < t := Nat.pos_of_mem_divisors htd
  have ht1 : t ≠ 1 := by rintro rfl; simp at hodd
  have hq : t.minFac ∈ t.primeFactors := Nat.mem_primeFactors.2 ⟨Nat.minFac_prime ht1, Nat.minFac_dvd t, ht0.ne'⟩
  have h1 := hgt _ hq
  have h2 := hlt _ hq
  have hqt : (t.minFac : ℝ) ≤ t := by exact_mod_cast Nat.minFac_le ht0
  have ht0' : (0 : ℝ) < t := by exact_mod_cast ht0
  rw [lt_div_iff₀ ht0'] at h2
  have hh : (η ^ (1 / (2 : ℝ))) ^ 2 = η := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hη.le]; norm_num
  have hq0 : (0 : ℝ) ≤ η ^ (1 / (2 : ℝ)) := Real.rpow_nonneg hη.le _
  have : η < (t.minFac : ℝ) ^ 2 := by
    rw [← hh]; exact pow_lt_pow_left₀ h1 hq0 (by norm_num)
  nlinarith

/-- Rosser bounds from `σ⁺(u) ≤ C₁ V(u)` (large `u`) and Lemma 9 at `s = 2`. -/
theorem rosserBound_of (b : ℕ) (h9 : Lemma9Stmt b)
    (hσ1 : ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∃ u₁ : ℝ, ∀ u ≥ u₁, sigmaP b u ≤ C₁ * MT.VB b u) : RosserBoundStmt b := by
  obtain ⟨C₁, hC₁, u₁, hσ⟩ := hσ1
  obtain ⟨y₀, hy₀⟩ := h9 2 (by norm_num) false (fun _ => le_rfl) 1 one_pos
  set U := max (max u₁ y₀) 4 with hU
  have hU4 : (4 : ℝ) ≤ U := le_max_right _ _
  have hVU := E1.VB_pos' b U
  set K₀ := Kp b U / MT.VB b U with hK₀
  have hK₀0 : 0 ≤ K₀ := div_nonneg (Kp_pos b U).le hVU.le
  -- a bound in the bounded region
  have hsmall : ∀ (σ' : Bool) (Y w : ℝ), w ≤ U → |Tpm b σ' Y w| ≤ K₀ * MT.VB b w := by
    intro σ' Y w hw
    have h1 := le_trans (abs_Tpm_le b σ' Y w) (prodPB_le_Kp b hw)
    have h2 : MT.VB b U ≤ MT.VB b w := E1.VB_anti b hw
    calc |Tpm b σ' Y w| ≤ Kp b U := h1
      _ = K₀ * MT.VB b U := by rw [hK₀]; field_simp
      _ ≤ K₀ * MT.VB b w := mul_le_mul_of_nonneg_left h2 hK₀0
  -- σ⁺ everywhere
  have hσall : ∀ u : ℝ, 0 < u → sigmaP b u ≤ (C₁ + K₀) * MT.VB b u := by
    intro u hu
    have hVu := E1.VB_pos' b u
    by_cases hu1 : u₁ ≤ u
    · have := hσ u hu1; nlinarith
    · push_neg at hu1
      have huU : u ≤ U := le_trans hu1.le (le_trans (le_max_left _ _) (le_max_left _ _))
      have hw : u ^ ((1 : ℝ) / 3) ≤ U := by
        rcases le_or_gt u 1 with h | h
        · exact le_trans (Real.rpow_le_one hu.le h (by norm_num)) (by linarith)
        · exact le_trans (Real.rpow_le_self_of_one_le h.le (by norm_num)) huU
      have h1 := hsmall true u _ hw
      have h2 : MT.VB b U ≤ MT.VB b u := E1.VB_anti b huU
      unfold sigmaP
      have h3 : K₀ * MT.VB b (u ^ ((1 : ℝ) / 3)) ≤ K₀ * MT.VB b U * (MT.VB b (u ^ ((1:ℝ)/3)) / MT.VB b U) := by
        field_simp; rfl
      -- simpler: |T| ≤ Kp U ≤ K₀ V(u)
      have h4 : |Tpm b true u (u ^ ((1 : ℝ) / 3))| ≤ K₀ * MT.VB b u := by
        have := le_trans (abs_Tpm_le b true u _) (prodPB_le_Kp b hw)
        calc |Tpm b true u (u ^ ((1 : ℝ) / 3))| ≤ Kp b U := this
          _ = K₀ * MT.VB b U := by rw [hK₀]; field_simp
          _ ≤ K₀ * MT.VB b u := mul_le_mul_of_nonneg_left h2 hK₀0
      have := le_abs_self (Tpm b true u (u ^ ((1 : ℝ) / 3)))
      nlinarith
  -- T⁻(η, √η) from below
  have hTm : ∀ η : ℝ, 0 < η → -((1 + K₀) * MT.VB b (η ^ (1 / (2 : ℝ)))) ≤ Tpm b false η (η ^ (1 / (2 : ℝ))) := by
    intro η hη
    have hV := E1.VB_pos' b (η ^ (1 / (2 : ℝ)))
    by_cases hηy : y₀ ≤ η
    · have h := hy₀ η hηy
      rw [T9sum_two_false b hη, sub_zero, one_mul] at h
      have := (abs_le.1 h).1
      nlinarith
    · push_neg at hηy
      have hw : η ^ (1 / (2 : ℝ)) ≤ U := by
        have hηU : η ≤ U := le_trans hηy.le (le_trans (le_max_right _ _) (le_max_left _ _))
        rcases le_or_gt η 1 with h | h
        · exact le_trans (Real.rpow_le_one hη.le h (by norm_num)) (by linarith)
        · exact le_trans (Real.rpow_le_self_of_one_le h.le (by norm_num)) hηU
      have := (abs_le.1 (hsmall false η _ hw)).1
      nlinarith
  refine ⟨2 + C₁ + K₀, by positivity, fun ζ η hζ2 => ⟨fun hζη => ?_, fun hζη => ?_⟩⟩
  · have hη : 0 < η := by linarith
    have hVζ := E1.VB_pos' b ζ
    have hVη : MT.VB b η ≤ MT.VB b ζ := E1.VB_anti b hζη.le
    have hpos := (rosser_pos' b ζ η).1
    rw [abs_of_nonneg (le_trans hVζ.le hpos)]
    by_cases hc : ζ ≤ η ^ ((1 : ℝ) / 3)
    · have hm := (rosser_mono b hc η).1
      have hs : Tpm b true η (η ^ ((1 : ℝ) / 3)) = sigmaP b η := rfl
      rw [hs] at hm
      have h1 := hσall η hη
      have hV3 := E1.VB_pos' b (η ^ ((1 : ℝ) / 3))
      nlinarith
    · push_neg at hc
      have heq : Tpm b true η ζ = sigmaP b η := by rw [Tpm_set, sigma_set b hη hc.le]
      rw [heq]
      have h1 := hσall η hη
      nlinarith
  · have hη : 0 < η := by nlinarith
    have hVζ := E1.VB_pos' b ζ
    have hζh : ζ ≤ η ^ (1 / (2 : ℝ)) := by
      have hh : (η ^ (1 / (2 : ℝ))) ^ 2 = η := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hη.le]; norm_num
      by_contra hc; push_neg at hc
      have := pow_lt_pow_left₀ hc (Real.rpow_nonneg hη.le _) (by norm_num : (2 : ℕ) ≠ 0)
      rw [hh] at this; linarith
    have hm := (rosser_mono b hζh η).2
    have hVh : MT.VB b (η ^ (1 / (2 : ℝ))) ≤ MT.VB b ζ := E1.VB_anti b hζh
    have h1 := hTm η hη
    have hup := (rosser_pos' b ζ η).2
    rw [abs_le]
    constructor <;> nlinarith [E1.VB_pos' b (η ^ (1 / (2 : ℝ)))]

theorem rosserBound (b : ℕ) (hb : 2 ≤ b) (h9 : Lemma9Stmt b) : RosserBoundStmt b :=
  rosserBound_of b h9 (sigma_upper b hb)

end KappaOmega2.M10

namespace KappaOmega2

/-- §4.3–§4.4: the uniform Lemma 9 from the pointwise one. -/
theorem lemma9U_of (b : ℕ) (hb : 2 ≤ b) (h9 : Lemma9Stmt b) : Lemma9UStmt b :=
  M10.lemma9U_of_RB b hb h9 (M10.rosserBound b hb h9)

end KappaOmega2
