import Palprimes.Greaves.Remainder
import Palprimes.Defs

/-! # Ω ≤ 4 from the level, the squares and the main term (dossier Proposition 1′)

`omega4_skeleton`: if the `3^ω`-weighted level holds up to `x^θ` (HL), the prime-square divisors
in `(x^{θT₀}, x^{1/4−ε₀})` are rare (HS), and Greaves' main term is `≥ c / log x` (HM), then a
proportion `≫ 1/log x` of `Π*_b(2N)` has `Ω ≤ 4` and all prime factors `> x^{θT₀}`. -/

set_option linter.style.longLine false

open Finset Real
open scoped ArithmeticFunction.Omega

namespace Palprimes.Greaves

/-- `Ω n = Σ_p v_p(n)`. -/
theorem cardFactors_eq_sum (n : ℕ) : Ω n = ∑ p ∈ n.primeFactors, n.factorization p := by
  rw [ArithmeticFunction.cardFactors_apply]
  have h := Multiset.toFinset_sum_count_eq (n.primeFactorsList : Multiset ℕ)
  simp only [Multiset.coe_card, Multiset.coe_count, Multiset.coe_toFinset] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro p _
  exact Nat.primeFactorsList_count_eq

/-- `Ω = ν` when all prime factors exceed `Y₀` and none in `(Y₀, Y)` divides squared. -/
theorem omega_eq_nu (a : ℕ) (ha : a ≠ 0) (Y0 Y : ℝ)
    (hbig : ∀ p ∈ a.primeFactors, Y0 < p)
    (hsq : ∀ p : ℕ, p.Prime → Y0 < p → (p : ℝ) < Y → ¬ p ^ 2 ∣ a) :
    Ω a = nu a Y := by
  classical
  rw [cardFactors_eq_sum, nu, ← Finset.sum_filter_add_sum_filter_not a.primeFactors
    (fun p : ℕ => (p : ℝ) < Y)]
  congr 1
  · rw [Finset.card_eq_sum_ones]
    apply Finset.sum_congr rfl
    intro p hp
    rw [mem_filter] at hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp.1
    have h1 : 1 ≤ a.factorization p :=
      hpp.factorization_pos_of_dvd ha (Nat.dvd_of_mem_primeFactors hp.1)
    have h2 : a.factorization p < 2 := by
      by_contra h
      push Not at h
      exact hsq p hpp (hbig p hp.1) hp.2 ((hpp.pow_dvd_iff_le_factorization ha).2 h)
    omega
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext p; simp [not_lt]

theorem countDvd_eq_zero_of_not_coprime (b N d : ℕ) (hd : ¬ Nat.Coprime d (bigB b)) :
    countDvd (piStar b N) d = 0 := by
  unfold countDvd
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro a ha hda
  simp only [piStar, mem_filter] at ha
  exact hd (Nat.Coprime.coprime_dvd_left hda ha.2.2)

/-- Greaves' main term `S_ℬ(y, w)` for `Π*_b`: density `1/d` on `d` coprime to `b³ − b`. -/
noncomputable def MT (P : WPar) (b : ℕ) (y : ℝ) : ℝ :=
  ∑ T ∈ (primesBelow y).powerset, term (P.wn y) false y (P.wn y 1) T *
    (if Nat.Coprime (∏ p ∈ T, p) (bigB b) then 1 / ((∏ p ∈ T, p : ℕ) : ℝ) else 0)

/-- **Main term plus remainder.** -/
theorem sieve_lower (P : WPar) (b N : ℕ) (hb : 2 ≤ b) (y g : ℝ) (hy : 1 < y) (hg : g ≤ P.V + 4 * P.U)
    (hgx : ∀ a ∈ piStar b N, (a : ℝ) < y ^ g) :
    (#(piStar b N) : ℝ) * MT P b y -
        P.wn y 1 * ∑ q ∈ (Icc 1 ⌊y⌋₊).filter (fun q => Nat.Coprime q (bigB b)),
          (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors q) *
            |(countDvd (piStar b N) q : ℝ) - (#(piStar b N) : ℝ) / q| ≤
      ∑ a ∈ piStar b N, (if nu a (y ^ P.U) ≤ 4 then P.wn y a.minFac else 0) := by
  classical
  set X : ℝ := (#(piStar b N) : ℝ) with hX
  set E : ℕ → ℝ := fun q => (countDvd (piStar b N) q : ℝ) - X / q with hE
  have hw0 : ∀ p, 0 ≤ P.wn y p := by
    intro p; unfold WPar.wn; split_ifs
    · exact P.UV_pos.le
    · exact P.W_nonneg _
  have hwle : ∀ p, P.wn y p ≤ P.wn y 1 := by
    intro p; rw [P.wn_one]; unfold WPar.wn; split_ifs
    · exact le_rfl
    · exact P.W_le _
  have hsieve := sieve_ineq P y g 4 hy (by push_cast; linarith) (piStar b N)
    (fun a ha => ⟨by
      simp only [piStar, mem_filter, mem_Ico] at ha
      have : 1 ≤ b ^ (2 * N) := Nat.one_le_pow _ _ (by omega)
      omega, hgx a ha⟩)
  refine le_trans ?_ hsieve
  -- `count = X γ/d + err`
  have hsplit : ∀ T ∈ (primesBelow y).powerset,
      term (P.wn y) false y (P.wn y 1) T * (#((piStar b N).filter (fun a => (∏ p ∈ T, p) ∣ a)) : ℝ) =
      X * (term (P.wn y) false y (P.wn y 1) T *
        (if Nat.Coprime (∏ p ∈ T, p) (bigB b) then 1 / ((∏ p ∈ T, p : ℕ) : ℝ) else 0)) +
      term (P.wn y) false y (P.wn y 1) T *
        (if Nat.Coprime (∏ p ∈ T, p) (bigB b) then E (∏ p ∈ T, p) else 0) := by
    intro T _
    have hc : (#((piStar b N).filter (fun a => (∏ p ∈ T, p) ∣ a)) : ℝ) = countDvd (piStar b N) (∏ p ∈ T, p) := rfl
    rw [hc]
    split_ifs with hcop
    · simp only [hE]; ring
    · rw [countDvd_eq_zero_of_not_coprime b N _ hcop]; simp
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hMT : ∑ T ∈ (primesBelow y).powerset, term (P.wn y) false y (P.wn y 1) T *
      (if Nat.Coprime (∏ p ∈ T, p) (bigB b) then 1 / ((∏ p ∈ T, p : ℕ) : ℝ) else 0) = MT P b y := rfl
  rw [hMT]
  -- the remainder
  have hrem : |∑ T ∈ (primesBelow y).powerset, term (P.wn y) false y (P.wn y 1) T *
        (if Nat.Coprime (∏ p ∈ T, p) (bigB b) then E (∏ p ∈ T, p) else 0)| ≤
      P.wn y 1 * ∑ q ∈ (Icc 1 ⌊y⌋₊).filter (fun q => Nat.Coprime q (bigB b)),
        (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors q) * |E q| := by
    set S' := ((primesBelow y).powerset).filter (fun T =>
      RosOK false y (toDec T) ∧ Nat.Coprime (∏ p ∈ T, p) (bigB b)) with hS'
    have hprimes : ∀ p ∈ primesBelow y, p.Prime := fun p hp => ((mem_primesBelow y p).1 hp).1
    calc _ ≤ ∑ T ∈ (primesBelow y).powerset, |term (P.wn y) false y (P.wn y 1) T *
            (if Nat.Coprime (∏ p ∈ T, p) (bigB b) then E (∏ p ∈ T, p) else 0)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ T ∈ S', P.wn y 1 * ((3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors (∏ p ∈ T, p)) *
            |E (∏ p ∈ T, p)|) := by
          rw [hS', Finset.sum_filter]
          apply Finset.sum_le_sum
          intro T hT
          have hTp : ∀ p ∈ T, p.Prime := fun p hp => hprimes p (Finset.mem_powerset.1 hT hp)
          have homega : ArithmeticFunction.cardDistinctFactors (∏ p ∈ T, p) = T.card := by
            rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset,
              ← Nat.primeFactors.eq_def, Nat.primeFactors_prod hTp]
          by_cases hc : Nat.Coprime (∏ p ∈ T, p) (bigB b)
          · by_cases hR : RosOK false y (toDec T)
            · rw [if_pos hc, if_pos ⟨hR, hc⟩, abs_mul, homega]
              have := abs_term_le (P.wn y) hw0 hwle false y T
              have h0 : 0 ≤ |E (∏ p ∈ T, p)| := abs_nonneg _
              nlinarith
            · have : term (P.wn y) false y (P.wn y 1) T = 0 := by
                unfold term; rw [if_neg hR]
              rw [if_pos hc, this, if_neg (fun h => hR h.1)]; simp
          · rw [if_neg hc, if_neg (fun h => hc h.2)]; simp
      _ = P.wn y 1 * ∑ q ∈ S'.image (fun T => ∏ p ∈ T, p),
            (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors q) * |E q| := by
          rw [← Finset.mul_sum, Finset.sum_image]
          intro T1 h1 T2 h2 h
          exact prod_injOn (primesBelow y) hprimes (by
            simp only [coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, coe_subset]
            exact Finset.mem_powerset.1 (Finset.mem_of_mem_filter _ h1)) (by
            simp only [coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, coe_subset]
            exact Finset.mem_powerset.1 (Finset.mem_of_mem_filter _ h2)) h
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (le_trans (hw0 1) (hwle 1))
          apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => by positivity)
          intro q hq
          rw [Finset.mem_image] at hq
          obtain ⟨T, hT, rfl⟩ := hq
          rw [hS', mem_filter] at hT
          obtain ⟨hTP, hR, hcop⟩ := hT
          rw [mem_filter, mem_Icc]
          refine ⟨⟨Finset.prod_pos (fun p hp => (hprimes p (Finset.mem_powerset.1 hTP hp)).pos), ?_⟩, hcop⟩
          rcases prod_le_of_mem y T (Finset.mem_powerset.1 hTP) hR with h | h
          · exact Nat.le_floor h
          · rw [h, Finset.prod_empty]; exact Nat.le_floor (by norm_num; linarith)
  have := neg_abs_le (∑ T ∈ (primesBelow y).powerset, term (P.wn y) false y (P.wn y 1) T *
        (if Nat.Coprime (∏ p ∈ T, p) (bigB b) then E (∏ p ∈ T, p) else 0))
  linarith

/-- `w(q) > 0` forces `q > y^{T₀}`. -/
theorem lt_of_wn_pos (P : WPar) (y : ℝ) (hy : 1 < y) (q : ℕ) (hq : q.Prime) (h : 0 < P.wn y q) :
    y ^ P.T0 < q := by
  rw [P.wn_prime y q hq] at h
  have hL : 0 < Real.log y := Real.log_pos hy
  have ht : P.T0 < Real.log q / Real.log y := by
    by_contra hle
    push Not at hle
    have h1 : ¬ P.U < Real.log q / Real.log y := by have := P.hU; have := P.hT1; linarith
    have h2 : ¬ 1 / 4 < Real.log q / Real.log y := by have := P.hT1; linarith
    have h3 : ¬ P.T0 < Real.log q / Real.log y := not_lt.2 hle
    unfold WPar.W at h; rw [if_neg h1, if_neg h2, if_neg h3] at h; exact lt_irrefl 0 h
  rw [lt_div_iff₀ hL] at ht
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  rw [← Real.exp_log hq0, Real.rpow_def_of_pos (by linarith)]
  exact Real.exp_lt_exp.2 (by linarith)

/-- **Proposition 1′ (skeleton)**: level + squares + main term ⇒ `Ω ≤ 4` with large prime factors. -/
theorem omega4_skeleton (b : ℕ) (hb : 2 ≤ b) (P : WPar) (θ ε₀ : ℝ) (hθ : 0 < θ)
    (hU : P.U = (1 / 4 - ε₀) / θ) (hV : P.V = 4 * ε₀ / θ)
    (HL : ∃ N₁ : ℕ, ∀ N ≥ N₁,
      ∑ q ∈ (Icc 1 ⌊((b : ℝ) ^ (2 * N + 1)) ^ θ⌋₊).filter (fun q => Nat.Coprime q (bigB b)),
          (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors q) *
            |(countDvd (piStar b N) q : ℝ) - (#(piStar b N) : ℝ) / q|
        ≤ (#(piStar b N) : ℝ) / (Real.log ((b : ℝ) ^ (2 * N + 1))) ^ 3)
    (HS : ∃ N₂ : ℕ, ∀ N ≥ N₂,
      ∑ p ∈ (Icc ⌈((b : ℝ) ^ (2 * N + 1)) ^ (θ * P.T0)⌉₊ ⌊((b : ℝ) ^ (2 * N + 1)) ^ (1 / 4 - ε₀)⌋₊).filter Nat.Prime,
          (countDvd (piStar b N) (p ^ 2) : ℝ)
        ≤ (#(piStar b N) : ℝ) / (Real.log ((b : ℝ) ^ (2 * N + 1))) ^ 3)
    (HM : ∃ c : ℝ, 0 < c ∧ ∃ N₃ : ℕ, ∀ N ≥ N₃,
      c / Real.log ((b : ℝ) ^ (2 * N + 1)) ≤ MT P b (((b : ℝ) ^ (2 * N + 1)) ^ θ)) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      c * ((#(piStar b N) : ℝ) / Real.log ((b : ℝ) ^ (2 * N + 1))) ≤
        (#((piStar b N).filter (fun n => Ω n ≤ 4 ∧
          ∀ p ∈ n.primeFactors, ((b : ℝ) ^ (2 * N + 1)) ^ (θ * P.T0) < (p : ℝ))) : ℝ) := by
  classical
  obtain ⟨N₁, hN₁⟩ := HL
  obtain ⟨N₂, hN₂⟩ := HS
  obtain ⟨c, hc, N₃, hN₃⟩ := HM
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have hlogb : 0 < Real.log b := Real.log_pos hb1
  -- `L² ≥ 8/c` eventually
  obtain ⟨N₄, hN₄⟩ : ∃ N₄ : ℕ, ∀ N ≥ N₄, 8 / c ≤ (Real.log ((b : ℝ) ^ (2 * N + 1))) ^ 2 := by
    obtain ⟨M, hM⟩ := exists_nat_gt (Real.sqrt (8 / c) / Real.log b)
    refine ⟨M, fun N hN => ?_⟩
    rw [Real.log_pow]
    have h1 : Real.sqrt (8 / c) ≤ ((2 * N + 1 : ℕ) : ℝ) * Real.log b := by
      rw [div_lt_iff₀ hlogb] at hM
      have : (M : ℝ) ≤ ((2 * N + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : M ≤ 2 * N + 1)
      nlinarith
    calc 8 / c = Real.sqrt (8 / c) ^ 2 := (Real.sq_sqrt (by positivity)).symm
      _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  refine ⟨c / 2, by positivity, max (max N₁ N₂) (max (max N₃ N₄) 1), fun N hN => ?_⟩
  have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN3 : N₃ ≤ N := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hN
  have hN4 : N₄ ≤ N := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hN
  have hN0 : 1 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  set x : ℝ := (b : ℝ) ^ (2 * N + 1) with hx
  set X : ℝ := (#(piStar b N) : ℝ) with hX
  set L : ℝ := Real.log x with hL
  have hx1 : 1 < x := one_lt_pow₀ hb1 (by omega)
  have hL0 : 0 < L := Real.log_pos hx1
  set y : ℝ := x ^ θ with hy
  have hy1 : 1 < y := Real.one_lt_rpow hx1 hθ
  have hX0 : 0 ≤ X := by positivity
  -- parameters
  have hgx : ∀ a ∈ piStar b N, (a : ℝ) < y ^ (1 / θ) := by
    intro a ha
    rw [hy, ← Real.rpow_mul (by linarith), mul_one_div_cancel hθ.ne', Real.rpow_one]
    simp only [piStar, mem_filter, mem_Ico] at ha
    rw [hx]; exact_mod_cast ha.1.2
  have hg : 1 / θ ≤ P.V + 4 * P.U := by
    rw [hU, hV]; field_simp; ring_nf; rfl
  have hYU : y ^ P.U = x ^ (1 / 4 - ε₀) := by
    rw [hy, ← Real.rpow_mul (by linarith), hU]; congr 1; field_simp
  have hY0 : y ^ P.T0 = x ^ (θ * P.T0) := by rw [hy, ← Real.rpow_mul (by linarith)]
  -- the sieve lower bound
  have hlow := sieve_lower P b N hb y (1 / θ) hy1 hg hgx
  have hLev := hN₁ N hN1
  have hw1 : P.wn y 1 = P.U - P.V := P.wn_one y
  have hw1pos : 0 < P.wn y 1 := by rw [hw1]; exact P.UV_pos
  have hw1le : P.wn y 1 ≤ 1 := by rw [hw1]; have := P.hU1; have := P.hV; linarith
  have hw0 : ∀ p, 0 ≤ P.wn y p := by
    intro p; unfold WPar.wn; split_ifs
    · exact P.UV_pos.le
    · exact P.W_nonneg _
  have hwle : ∀ p, P.wn y p ≤ P.wn y 1 := by
    intro p; rw [P.wn_one]; unfold WPar.wn; split_ifs
    · exact le_rfl
    · exact P.W_le _
  have hMT := hN₃ N hN3
  -- the sets
  set S1 := (piStar b N).filter (fun a => nu a (y ^ P.U) ≤ 4 ∧ 0 < P.wn y a.minFac) with hS1
  have hsumS1 : ∑ a ∈ piStar b N, (if nu a (y ^ P.U) ≤ 4 then P.wn y a.minFac else 0) ≤
      P.wn y 1 * #S1 := by
    rw [hS1, Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
    apply Finset.sum_le_sum; intro a _
    by_cases h1 : nu a (y ^ P.U) ≤ 4
    · by_cases h2 : 0 < P.wn y a.minFac
      · rw [if_pos h1, if_pos ⟨h1, h2⟩]; simp [hwle]
      · rw [if_pos h1, if_neg (fun h => h2 h.2)]
        have := hw0 a.minFac; simp; linarith
    · rw [if_neg h1, if_neg (fun h => h1 h.1)]; simp
  set Qs := (Icc ⌈x ^ (θ * P.T0)⌉₊ ⌊x ^ (1 / 4 - ε₀)⌋₊).filter Nat.Prime with hQs
  set Bad := S1.filter (fun a => ∃ p ∈ Qs, p ^ 2 ∣ a) with hBad
  have hBadle : (#Bad : ℝ) ≤ X / L ^ 3 := by
    have h1 : #Bad ≤ ∑ p ∈ Qs, countDvd (piStar b N) (p ^ 2) := by
      calc #Bad ≤ #(Qs.biUnion (fun p => (piStar b N).filter (fun a => p ^ 2 ∣ a))) := by
            apply Finset.card_le_card
            intro a ha
            rw [hBad, mem_filter] at ha
            obtain ⟨hS, p, hp, hpa⟩ := ha
            rw [Finset.mem_biUnion]
            exact ⟨p, hp, mem_filter.2 ⟨Finset.mem_of_mem_filter a hS, hpa⟩⟩
        _ ≤ _ := Finset.card_biUnion_le
    calc (#Bad : ℝ) ≤ ∑ p ∈ Qs, (countDvd (piStar b N) (p ^ 2) : ℝ) := by exact_mod_cast h1
      _ ≤ X / L ^ 3 := hN₂ N hN2
  -- the good elements are in the target set
  have hgood : S1 \ Bad ⊆ (piStar b N).filter (fun n => Ω n ≤ 4 ∧
      ∀ p ∈ n.primeFactors, x ^ (θ * P.T0) < (p : ℝ)) := by
    intro a ha
    rw [mem_sdiff, hS1, mem_filter] at ha
    obtain ⟨⟨haP, hnu, hwa⟩, hnb⟩ := ha
    have ha1 : 1 < a := by
      simp only [piStar, mem_filter, mem_Ico] at haP
      have : b ≤ b ^ (2 * N) := by
        calc b = b ^ 1 := (pow_one b).symm
          _ ≤ b ^ (2 * N) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have ha0 : a ≠ 0 := by omega
    have hq := Nat.minFac_prime (by omega : a ≠ 1)
    have hqY := lt_of_wn_pos P y hy1 a.minFac hq hwa
    rw [hY0] at hqY
    have hbig : ∀ p ∈ a.primeFactors, x ^ (θ * P.T0) < (p : ℝ) := by
      intro p hp
      have : a.minFac ≤ p := Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactors hp).two_le
        (Nat.dvd_of_mem_primeFactors hp)
      have : (a.minFac : ℝ) ≤ p := by exact_mod_cast this
      linarith
    have hsq : ∀ p : ℕ, p.Prime → x ^ (θ * P.T0) < p → (p : ℝ) < y ^ P.U → ¬ p ^ 2 ∣ a := by
      intro p hp h1 h2 hpa
      apply hnb
      rw [hBad, mem_filter]
      refine ⟨mem_filter.2 ⟨haP, hnu, hwa⟩, p, ?_, hpa⟩
      rw [hQs, mem_filter, mem_Icc]
      refine ⟨⟨Nat.ceil_le.2 h1.le, Nat.le_floor (by rw [← hYU]; exact h2.le)⟩, hp⟩
    rw [mem_filter]
    refine ⟨haP, ?_, hbig⟩
    rw [omega_eq_nu a ha0 (x ^ (θ * P.T0)) (y ^ P.U) hbig hsq]
    exact hnu
  -- counting
  have hcount : (#S1 : ℝ) - #Bad ≤ #((piStar b N).filter (fun n => Ω n ≤ 4 ∧
      ∀ p ∈ n.primeFactors, x ^ (θ * P.T0) < (p : ℝ))) := by
    have h1 : #S1 - #Bad ≤ #(S1 \ Bad) := by
      have := Finset.card_sdiff_add_card_inter S1 Bad
      have : #(S1 ∩ Bad) ≤ #Bad := Finset.card_le_card Finset.inter_subset_right
      omega
    have h2 := Finset.card_le_card hgood
    have h3 : (#S1 : ℝ) - #Bad ≤ #(S1 \ Bad) := by
      have : (#S1 : ℝ) ≤ #(S1 \ Bad) + #Bad := by exact_mod_cast (by omega : #S1 ≤ #(S1 \ Bad) + #Bad)
      linarith
    exact le_trans h3 (by exact_mod_cast h2)
  -- the final inequality
  have hS1low : X * (c / L) - X / L ^ 3 ≤ P.wn y 1 * #S1 := by
    have h1 : X * (c / L) ≤ X * MT P b y := mul_le_mul_of_nonneg_left hMT hX0
    have h2 : P.wn y 1 * ∑ q ∈ (Icc 1 ⌊y⌋₊).filter (fun q => Nat.Coprime q (bigB b)),
          (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors q) *
            |(countDvd (piStar b N) q : ℝ) - X / q| ≤ X / L ^ 3 := by
      calc _ ≤ 1 * (X / L ^ 3) := mul_le_mul hw1le hLev (by positivity) (by norm_num)
        _ = _ := one_mul _
    linarith
  have hL4 := hN₄ N hN4
  have hS1' : X * (c / L) - X / L ^ 3 ≤ #S1 := by
    have h0 : 0 ≤ (#S1 : ℝ) := by positivity
    have : P.wn y 1 * #S1 ≤ #S1 := by nlinarith
    linarith
  have hfin : c / 2 * (X / L) ≤ X * (c / L) - 2 * (X / L ^ 3) := by
    have hL3 : 0 < L ^ 3 := by positivity
    have : X / L ^ 3 ≤ c / 8 * (X / L) := by
      rw [div_le_iff₀ hL3]
      have : X / L * L ^ 3 = X * L ^ 2 := by field_simp
      rw [mul_assoc, this]
      have h8 : 1 ≤ c / 8 * L ^ 2 := by
        have := mul_le_mul_of_nonneg_left hL4 (by positivity : (0 : ℝ) ≤ c / 8)
        rw [show c / 8 * (8 / c) = 1 by field_simp] at this; linarith
      nlinarith
    have e : X * (c / L) = c * (X / L) := by ring
    nlinarith
  calc c / 2 * (X / L) ≤ X * (c / L) - 2 * (X / L ^ 3) := hfin
    _ ≤ (#S1 : ℝ) - #Bad := by linarith
    _ ≤ _ := hcount

end Palprimes.Greaves
