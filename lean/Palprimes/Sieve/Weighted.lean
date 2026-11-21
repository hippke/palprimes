import Palprimes.Defs
import Palprimes.Sieve.Vendor.Mertens
import Palprimes.Sieve.SelbergSum
import Palprimes.Sieve.Assembly
import Palprimes.Sieve.Certificate

/-! # M13. The weighted sieve and the Ω ≤ 5 conclusion

Route (`notes/SIEVE_ROUTE.md`): exact inclusion–exclusion at `w = ⌊log x/8⌋`, one Buchstab step,
Selberg's Λ² bound (`Sieve/Vendor/Selberg.lean`) with lower bounds for the Selberg sum from Rankin's
trick and a one-prime smooth-number bound, Richert's weights on `[x^{1/20}, x^{23/100})` with
`λ = 8/5`. The numeric inequality is the generated certificate `Sieve/Certificate.lean`.

Main results: `richert_omega_le_five` (Ω bookkeeping), `sieve_core` (the weighted sieve for one
`x`), `sieve_omega_le_five` (the abstract sieve consumed by the main theorem). -/

open Finset Real

open scoped ArithmeticFunction.Omega

namespace Palprimes

/-! ## M12. Mertens inputs: `Palprimes/Mertens.lean` (port of PNT+, `mertens1_upper`,
`mertens2_interval`, `mertens3`, `eulerMascheroni_lt`).

## M13. Sieve components: Selberg's bound `selberg_concrete` (`Palprimes/Selberg.lean`), lower bounds
for the Selberg sum (`Palprimes/SieveG.lean`). -/

/-- Elements of `A` without prime factors below `z`. -/
noncomputable def sifted (A : Finset ℕ) (z : ℝ) : Finset ℕ :=
  A.filter (fun n => ∀ p ∈ n.primeFactors, z ≤ (p : ℝ))

/-- Richert's penalty `Σ_{p ∣ n, p < y} (1 − log p / log y)` (distinct primes). -/
noncomputable def richertPenalty (y : ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ n.primeFactors.filter (fun p : ℕ => (p : ℝ) < y), (1 - Real.log p / Real.log y)

/-- **Ω bookkeeping.** Positive Richert weight forces `Ω ≤ 5`: with `y = x^{23/100}`, squarefree below `y`
and penalty `< 8/5`, `Ω(n) < 8/5 + log x / log y = 8/5 + 100/23 < 6`. No lower sifting limit is needed. -/
theorem richert_omega_le_five (x : ℝ) (hx : 1 < x) (n : ℕ) (hn : 1 ≤ n) (hnx : (n : ℝ) ≤ x)
    (hsq : ∀ p : ℕ, p.Prime → (p : ℝ) < x ^ (23 / 100 : ℝ) → ¬ p ^ 2 ∣ n)
    (hw : richertPenalty (x ^ (23 / 100 : ℝ)) n < 8 / 5) :
    Ω n ≤ 5 := by
  classical
  set y : ℝ := x ^ (23 / 100 : ℝ) with hy
  have hL : 0 < Real.log x := Real.log_pos hx
  have hly : Real.log y = 23 / 100 * Real.log x := by rw [hy, Real.log_rpow (by linarith)]
  have hly0 : 0 < Real.log y := by rw [hly]; positivity
  set F := n.primeFactors
  set Sm := F.filter (fun p : ℕ => (p : ℝ) < y)
  set Lg := F.filter (fun p : ℕ => ¬ (p : ℝ) < y)
  have hn0 : n ≠ 0 := by omega
  -- Ω and log n as sums over prime factors
  have hΩ : (Ω n : ℝ) = ∑ p ∈ F, (n.factorization p : ℝ) := by
    rw [ArithmeticFunction.cardFactors_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]
    push_cast; rfl
  have hlog : Real.log n = ∑ p ∈ F, (n.factorization p : ℝ) * Real.log p := by
    rw [Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]
  -- small primes appear once
  have hsm1 : ∀ p ∈ Sm, n.factorization p = 1 := by
    intro p hp
    simp only [Sm, F, mem_filter, Nat.mem_primeFactors] at hp
    obtain ⟨⟨hpp, hpd, -⟩, hpy⟩ := hp
    have h1 : 1 ≤ n.factorization p := (hpp.dvd_iff_one_le_factorization hn0).1 hpd
    by_contra hne
    have h2 : 2 ≤ n.factorization p := by omega
    exact hsq p hpp hpy ((hpp.pow_dvd_iff_le_factorization hn0).2 h2)
  have hsplit : ∀ f : ℕ → ℝ, ∑ p ∈ F, f p = ∑ p ∈ Sm, f p + ∑ p ∈ Lg, f p := fun f =>
    (Finset.sum_filter_add_sum_filter_not F _ f).symm
  have hΩ' : (Ω n : ℝ) = (#Sm : ℝ) + ∑ p ∈ Lg, (n.factorization p : ℝ) := by
    rw [hΩ, hsplit, Finset.card_eq_sum_ones, Nat.cast_sum]
    congr 1
    apply Finset.sum_congr rfl; intro p hp; rw [hsm1 p hp]
  have hlog' : Real.log n = ∑ p ∈ Sm, Real.log p + ∑ p ∈ Lg, (n.factorization p : ℝ) * Real.log p := by
    rw [hlog, hsplit]
    congr 1
    apply Finset.sum_congr rfl; intro p hp; rw [hsm1 p hp]; simp
  have hlarge : Real.log y * ∑ p ∈ Lg, (n.factorization p : ℝ) ≤
      ∑ p ∈ Lg, (n.factorization p : ℝ) * Real.log p := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro p hp
    simp only [Lg, F, mem_filter, Nat.mem_primeFactors] at hp
    have hpy : y ≤ p := not_lt.1 hp.2
    have hy0 : 0 < y := by rw [hy]; exact Real.rpow_pos_of_pos (by linarith) _
    have : Real.log y ≤ Real.log p := Real.log_le_log hy0 hpy
    have h0 : (0 : ℝ) ≤ n.factorization p := Nat.cast_nonneg _
    nlinarith
  have hpen : richertPenalty y n = (#Sm : ℝ) - (∑ p ∈ Sm, Real.log p) / Real.log y := by
    unfold richertPenalty
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.sum_div]
  have hlogn : Real.log n ≤ Real.log x := Real.log_le_log (by exact_mod_cast hn) hnx
  -- Ω < 8/5 + 100/23 < 6
  have hkey : (Ω n : ℝ) < 6 := by
    have hLgsum : ∑ p ∈ Lg, (n.factorization p : ℝ) ≤
        (Real.log x - ∑ p ∈ Sm, Real.log p) / Real.log y := by
      rw [le_div_iff₀ hly0]; linarith
    have hfrac : Real.log x / Real.log y = 100 / 23 := by
      rw [hly]; field_simp
    have : (∑ p ∈ Sm, Real.log p) / Real.log y + (Real.log x - ∑ p ∈ Sm, Real.log p) / Real.log y
        = 100 / 23 := by rw [← add_div]; ring_nf; rw [← hfrac]; ring_nf
    rw [hpen] at hw
    linarith
  have : (Ω n : ℝ) < ((6 : ℕ) : ℝ) := by exact_mod_cast hkey
  have := Nat.cast_lt.1 this
  omega

/-- For `n` free of `PB B Z` and coprime to `B`, the prime factors below `y` are the primes of
`[Z, ⌈y⌉)` dividing `n`. -/
theorem primeFactors_eq_RP (B Z : ℕ) (y : ℝ) (n : ℕ) (hn : n ≠ 0) (hcop : Nat.Coprime n B)
    (hfree : ∀ q ∈ PB B Z, ¬ q ∣ n) :
    n.primeFactors.filter (fun p : ℕ => (p : ℝ) < y) =
      ((Ico Z ⌈y⌉₊).filter Nat.Prime).filter (· ∣ n) := by
  ext p
  simp only [mem_filter, Nat.mem_primeFactors, mem_Ico]
  constructor
  · rintro ⟨⟨hp, hpn, -⟩, hpy⟩
    refine ⟨⟨⟨?_, Nat.lt_ceil.2 hpy⟩, hp⟩, hpn⟩
    by_contra hlt; push_neg at hlt
    have hpB : ¬ p ∣ B := fun h => by
      have := Nat.Coprime.coprime_dvd_left hpn hcop
      exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd this h)
    exact hfree p (by simp only [PB, mem_filter, mem_range]; exact ⟨hlt, hp, hpB⟩) hpn
  · rintro ⟨⟨⟨_, hpy⟩, hp⟩, hpn⟩
    exact ⟨⟨hp, hpn, hn⟩, Nat.lt_ceil.1 hpy⟩

/-- **Core of the weighted sieve**, for one `x`. -/
theorem sieve_core (A : Finset ℕ) (B : ℕ) (x : ℝ) (hx : 1 < x) (hB1 : 1 ≤ B)
    (hA : ∀ n ∈ A, 1 ≤ n ∧ (n : ℝ) ≤ x ∧ Nat.Coprime n B) (hne : A.Nonempty)
    (W Z : ℕ) (hWZ : W ≤ Z) (hBZ : B < Z) (hxZ : x ^ ((1 : ℝ) / 20) ≤ (Z : ℝ))
    (hPW : ((∏ q ∈ PB B W, q : ℕ) : ℝ) ≤ x ^ ((6 : ℝ) / 25))
    (hZD : ∀ p : ℕ, 1 ≤ p → p < Z → 1 ≤ x ^ ((6 : ℝ) / 25) / p)
    (hyD : ∀ p : ℕ, 1 ≤ p → (p : ℝ) < x ^ ((23 : ℝ) / 100) → 1 ≤ x ^ ((6 : ℝ) / 25) / p)
    (eB eR : ℝ)
    (hB : ∑ p ∈ (Ico W Z).filter (fun p => p.Prime ∧ ¬ p ∣ B),
        (1 / (p * selS (PB B p) (x ^ ((6 : ℝ) / 25) / p)) - (∏ q ∈ PB B p, (1 - 1 / (q : ℝ))) / p) ≤
        eB * ∏ q ∈ PB B Z, (1 - 1 / (q : ℝ)))
    (hR : ∑ p ∈ (Ico Z ⌈x ^ ((23 : ℝ) / 100)⌉₊).filter Nat.Prime,
        (1 - Real.log p / Real.log (x ^ ((23 : ℝ) / 100))) /
          (p * selS (PB B Z) (x ^ ((6 : ℝ) / 25) / p)) ≤
        eR * ∏ q ∈ PB B Z, (1 - 1 / (q : ℝ)))
    (hlev : levelSum A B (x ^ ((6 : ℝ) / 25)) ≤ (#A : ℝ) / Real.log x ^ 3)
    (hsq : ∑ p ∈ (Icc ⌈x ^ (1 / 20 : ℝ)⌉₊ ⌊x ^ (23 / 100 : ℝ)⌋₊).filter Nat.Prime,
        (countDvd A (p ^ 2) : ℝ) ≤ (#A : ℝ) / Real.log x ^ 3)
    (hmargin : 6 / Real.log x ^ 3 <
        (8 / 5 * (1 - eB) - eR) * ∏ q ∈ PB B Z, (1 - 1 / (q : ℝ))) :
    ∃ n ∈ A, Nat.IsAtMostAlmostPrime 5 n := by
  classical
  set y := x ^ ((23 : ℝ) / 100) with hy
  set D := x ^ ((6 : ℝ) / 25) with hD
  set X := (#A : ℝ)
  set VZ := ∏ q ∈ PB B Z, (1 - 1 / (q : ℝ))
  set S0 := A.filter (fun n => ∀ q ∈ PB B Z, ¬ q ∣ n)
  set RP := (Ico Z ⌈y⌉₊).filter Nat.Prime
  set w : ℕ → ℝ := fun p => 1 - Real.log p / Real.log y
  set R := levelSum A B D
  have hL : 0 < Real.log x := Real.log_pos hx
  have hly : Real.log y = 23 / 100 * Real.log x := by rw [hy, Real.log_rpow (by linarith)]
  have hly0 : 0 < Real.log y := by rw [hly]; positivity
  have hX : 0 < X := by simp only [X]; exact_mod_cast hne.card_pos
  have hR0 : 0 ≤ R := levelSum_nonneg A B D
  have hVZ := V_PB_pos B Z
  -- weights
  have hw : ∀ p ∈ RP, 0 ≤ w p ∧ w p ≤ 1 := by
    intro p hp
    simp only [RP, mem_filter, mem_Ico] at hp
    have hp0 : (1 : ℝ) ≤ p := by exact_mod_cast hp.2.one_lt.le
    have hpy : (p : ℝ) < y := Nat.lt_ceil.1 hp.1.2
    have h1 : 0 ≤ Real.log p := Real.log_nonneg hp0
    have h2 : Real.log p < Real.log y := Real.log_lt_log (by linarith) hpy
    simp only [w]
    constructor
    · rw [sub_nonneg, div_le_one hly0]; linarith
    · have : 0 ≤ Real.log p / Real.log y := div_nonneg h1 hly0.le
      linarith
  have hRP : ∀ p ∈ RP, p.Prime ∧ Z ≤ p ∧ ¬ p ∣ B ∧ 1 ≤ D / p := by
    intro p hp
    simp only [RP, mem_filter, mem_Ico] at hp
    refine ⟨hp.2, hp.1.1, fun h => ?_, hyD p hp.2.one_lt.le (Nat.lt_ceil.1 hp.1.2)⟩
    have := Nat.le_of_dvd (by omega) h; have := hp.1.1; omega
  -- the two main estimates
  have hlow := lower_S0 A B D W Z hWZ hPW hZD
  have hup := upper_rich A B D Z RP w hRP hw
  -- the penalty sum
  set pen : ℕ → ℝ := fun n => richertPenalty y n
  have hpen0 : ∀ n ∈ S0, 0 ≤ pen n := by
    intro n hn
    simp only [pen, richertPenalty]
    apply Finset.sum_nonneg; intro p hp
    simp only [mem_filter, Nat.mem_primeFactors] at hp
    have hp0 : (1 : ℝ) ≤ p := by exact_mod_cast hp.1.1.one_lt.le
    have h2 : Real.log p < Real.log y := Real.log_lt_log (by linarith) hp.2
    rw [sub_nonneg, div_le_one hly0]; linarith
  have hpensum : ∑ n ∈ S0, pen n = ∑ p ∈ RP, w p * (#(S0.filter (p ∣ ·)) : ℝ) := by
    have h1 : ∀ n ∈ S0, pen n = ∑ p ∈ RP.filter (· ∣ n), w p := by
      intro n hn
      simp only [S0, mem_filter] at hn
      obtain ⟨h1, h2, h3⟩ := hA n hn.1
      simp only [pen, richertPenalty]
      rw [primeFactors_eq_RP B Z y n (by omega) h3 hn.2]
    rw [Finset.sum_congr rfl h1]
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro p _
    rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro n _
    split_ifs <;> simp
  -- the bad count
  set bad : ℕ → Prop := fun n => ∃ p ∈ (Icc ⌈x ^ (1 / 20 : ℝ)⌉₊ ⌊x ^ (23 / 100 : ℝ)⌋₊).filter Nat.Prime, p ^ 2 ∣ n
  have hbad : (#(S0.filter bad) : ℝ) ≤ X / Real.log x ^ 3 := by
    refine le_trans ?_ hsq
    have hsub : S0.filter bad ⊆ ((Icc ⌈x ^ (1 / 20 : ℝ)⌉₊ ⌊x ^ (23 / 100 : ℝ)⌋₊).filter Nat.Prime).biUnion
        (fun p => A.filter ((p ^ 2) ∣ ·)) := by
      intro n hn
      simp only [S0, bad, mem_filter] at hn
      obtain ⟨⟨hnA, -⟩, p, hp, hpn⟩ := hn
      rw [mem_biUnion]; exact ⟨p, mem_filter.2 hp, mem_filter.2 ⟨hnA, hpn⟩⟩
    have := le_trans (card_le_card hsub) card_biUnion_le
    simp only [countDvd]; exact_mod_cast this
  -- the weighted sum beats the bad count
  have hW : 8 / 5 * (#(S0.filter bad) : ℝ) < ∑ n ∈ S0, (8 / 5 - pen n) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hpensum]
    have hRP' : ∑ p ∈ RP, w p / (p * selS (PB B Z) (D / p)) ≤ eR * VZ := hR
    have hS0 : X * VZ - X * (eB * VZ) - 2 * R ≤ (#S0 : ℝ) := by
      have := mul_le_mul_of_nonneg_left hB hX.le
      linarith [hlow]
    have hup' : ∑ p ∈ RP, w p * (#(S0.filter (p ∣ ·)) : ℝ) ≤ X * (eR * VZ) + R := by
      have := mul_le_mul_of_nonneg_left hRP' hX.le
      linarith [hup]
    have hm : X * (6 / Real.log x ^ 3) < X * ((8 / 5 * (1 - eB) - eR) * VZ) :=
      mul_lt_mul_of_pos_left hmargin hX
    have hRl : R ≤ X / Real.log x ^ 3 := hlev
    have e1 : X * (6 / Real.log x ^ 3) = 6 * (X / Real.log x ^ 3) := by ring
    nlinarith
  obtain ⟨n, hnS, hnbad, hnpen⟩ := exists_good_of_weighted S0 bad pen (8 / 5) hpen0 hW
  have hnS' := hnS
  simp only [S0, mem_filter] at hnS'
  obtain ⟨hn1, hnx, hncop⟩ := hA n hnS'.1
  refine ⟨n, hnS'.1, ⟨by omega, ?_⟩⟩
  apply richert_omega_le_five x hx n hn1 hnx _ hnpen
  intro p hp hpy hp2
  by_cases hpZ : p < Z
  · by_cases hpB : p ∣ B
    · have hpn : p ∣ n := dvd_trans (dvd_pow_self p two_ne_zero) hp2
      have := Nat.Coprime.coprime_dvd_left hpn hncop
      exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd this hpB)
    · exact hnS'.2 p (by simp only [PB, mem_filter, mem_range]; exact ⟨hpZ, hp, hpB⟩)
        (dvd_trans (dvd_pow_self p two_ne_zero) hp2)
  · apply hnbad
    refine ⟨p, ?_, hp2⟩
    simp only [mem_filter, mem_Icc]
    refine ⟨⟨?_, Nat.le_floor hpy.le⟩, hp⟩
    apply Nat.ceil_le.2
    push_neg at hpZ
    have : (Z : ℝ) ≤ p := by exact_mod_cast hpZ
    linarith


/-! ## The sieve interface consumed by the main theorem -/

theorem eventually_W_le_Z : ∀ᶠ x : ℝ in Filter.atTop, Wc x ≤ Zc x := by
  filter_upwards [eventually_le_rpow 5 (1 / 40) (by norm_num), Filter.eventually_gt_atTop (1 : ℝ)] with x h5 hx
  have hL := Real.log_le_rpow_div (x := x) (ε := 1 / 40) (by linarith) (by norm_num)
  have hs : x ^ ((1 : ℝ) / 20) = (x ^ ((1 : ℝ) / 40)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  have hL0 : 0 ≤ Real.log x := Real.log_nonneg hx.le
  have h1 : (Wc x : ℝ) ≤ Real.log x / 8 := Nat.floor_le (by positivity)
  have h2 : Real.log x / 8 ≤ x ^ ((1 : ℝ) / 20) := by
    rw [hs]; have : x ^ ((1 : ℝ) / 40) / (1 / 40) = 40 * x ^ ((1 : ℝ) / 40) := by ring
    rw [this] at hL; nlinarith
  have h3 : x ^ ((1 : ℝ) / 20) ≤ (Zc x : ℝ) := Nat.le_ceil _
  exact_mod_cast (le_trans h1 (le_trans h2 h3))

theorem eventually_PW (B : ℕ) : ∀ᶠ x : ℝ in Filter.atTop,
    ((∏ q ∈ PB B (Wc x), q : ℕ) : ℝ) ≤ x ^ ((6 : ℝ) / 25) := by
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
  have hL0 : 0 ≤ Real.log x := Real.log_nonneg hx.le
  have h1 : ((∏ q ∈ PB B (Wc x), q : ℕ) : ℝ) ≤ (4 : ℝ) ^ (Wc x) := by exact_mod_cast prod_PB_le B (Wc x)
  refine le_trans h1 ?_
  have hW : (Wc x : ℝ) ≤ Real.log x / 8 := Nat.floor_le (by positivity)
  have hl4 : Real.log 4 ≤ 48 / 25 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; have := Real.log_two_lt_d9; push_cast; linarith
  rw [← Real.exp_log (by positivity : (0 : ℝ) < 4 ^ (Wc x)), Real.log_pow,
    Real.rpow_def_of_pos (by linarith)]
  apply Real.exp_le_exp.2
  have : (Wc x : ℝ) * Real.log 4 ≤ Real.log x / 8 * (48 / 25) :=
    mul_le_mul hW hl4 (Real.log_nonneg (by norm_num)) (by positivity)
  linarith

theorem betaB_le_one (B : ℕ) : betaB B ≤ 1 := by
  unfold betaB
  apply Finset.prod_le_one₀
  · intro q hq
    have : (1 : ℝ) < q := by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).one_lt
    have : 1 / (q : ℝ) < 1 := by rw [div_lt_one (by linarith)]; exact this
    linarith
  · intro q hq
    have : (0 : ℝ) ≤ 1 / q := by positivity
    linarith

theorem eventually_margin (C₃ : ℝ)
    (hC₃ : ∀ t : ℝ, 2 ≤ t →
      |(∏ p ∈ (Finset.Icc 1 ⌊t⌋₊).filter Nat.Prime, (1 - 1 / (p : ℝ))) * Real.log t -
        Real.exp (-Real.eulerMascheroniConstant)| ≤ C₃ / Real.log t)
    (B : ℕ) (hB : 1 ≤ B) (c : ℝ) (hc : 1 / 50 ≤ c) :
    ∀ᶠ x : ℝ in Filter.atTop, 6 / Real.log x ^ 3 < c * ∏ q ∈ PB B (Zc x), (1 - 1 / (q : ℝ)) := by
  have H := tendsto_Zc.eventually (mertens_two_sided C₃ hC₃ B hB (1 / 2) (by norm_num) (by norm_num))
  have HL := Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (10 : ℝ))
  have H3 := tendsto_Zc.eventually (Filter.eventually_ge_atTop 3)
  filter_upwards [H, HL, H3, Filter.eventually_gt_atTop (1 : ℝ)] with x h1 h2 h3 hx
  set VZ := ∏ q ∈ PB B (Zc x), (1 - 1 / (q : ℝ))
  have hVZ := V_PB_pos B (Zc x)
  have hβ := betaB_pos B
  have hβ1 := betaB_le_one B
  have he := exp_neg_gamma_ge
  have hZ : Real.log ((Zc x : ℝ) - 1) ≤ Real.log x / 20 := by
    have h3' : (3 : ℝ) ≤ Zc x := by exact_mod_cast h3
    have := Real.log_le_log (by linarith) (Zc_sub_one_le x hx.le)
    rw [Real.log_rpow (by linarith)] at this; linarith
  have hlow : 1 / 2 * (10000 / 17813) ≤ VZ * betaB B * (Real.log x / 20) := by
    have := h1.1
    have h3 : VZ * betaB B * Real.log ((Zc x : ℝ) - 1) ≤ VZ * betaB B * (Real.log x / 20) :=
      mul_le_mul_of_nonneg_left hZ (by positivity)
    nlinarith
  have hVL : 1 / 2 * (10000 / 17813) * 20 ≤ VZ * Real.log x := by
    have : VZ * betaB B * (Real.log x / 20) ≤ VZ * (Real.log x / 20) :=
      mul_le_mul_of_nonneg_right (by nlinarith) (by linarith)
    linarith
  have hL : 0 < Real.log x := by linarith
  rw [div_lt_iff₀ (by positivity)]
  have : 6 < c * (VZ * Real.log x) * Real.log x ^ 2 := by
    have h4 : (100 : ℝ) ≤ Real.log x ^ 2 := by nlinarith
    have h5 : (1 / 50) * (1 / 2 * (10000 / 17813) * 20) ≤ c * (VZ * Real.log x) :=
      mul_le_mul hc hVL (by norm_num) (by linarith)
    nlinarith
  nlinarith

/-- **Abstract weighted sieve.** A finite set of integers `≤ x`, coprime to `B`, with level of
distribution `6/25` (weights `3^ω`) and controlled prime squares, contains an element with at
most five prime factors. -/
theorem sieve_omega_le_five (B : ℕ) (hB : 1 ≤ B) :
    ∃ x₀ : ℝ, ∀ (A : Finset ℕ) (x : ℝ), x₀ ≤ x →
      (∀ n ∈ A, 1 ≤ n ∧ (n : ℝ) ≤ x ∧ Nat.Coprime n B) →
      ∑ q ∈ (Icc 1 ⌊x ^ (6 / 25 : ℝ)⌋₊).filter (fun q => Nat.Coprime q B),
          (3 : ℝ) ^ (ArithmeticFunction.cardDistinctFactors q) *
            |(countDvd A q : ℝ) - (#A : ℝ) / q| ≤ (#A : ℝ) / (Real.log x) ^ 3 →
      ∑ p ∈ (Icc ⌈x ^ (1 / 20 : ℝ)⌉₊ ⌊x ^ (23 / 100 : ℝ)⌋₊).filter Nat.Prime,
          (countDvd A (p ^ 2) : ℝ) ≤ (#A : ℝ) / (Real.log x) ^ 3 →
      A.Nonempty →
      ∃ n ∈ A, Nat.IsAtMostAlmostPrime 5 n := by
  obtain ⟨c₁, hc₁⟩ := mertens1_upper
  obtain ⟨C₂, hC₂⟩ := mertens2_interval
  obtain ⟨C₃, hC₃⟩ := mertens3
  set δ : ℝ := 1 / 1000
  set eB : ℝ := 1 / 2000 + δ + (73899 / 500000 + δ)
  set eR : ℝ := 1200877 / 1000000 + δ
  have hc0 : (1 : ℝ) / 50 ≤ 8 / 5 * (1 - eB) - eR := by norm_num [eB, eR, δ]
  have hRt := R_total C₂ C₃ c₁ hC₂ hC₃ hc₁ B hB δ (by norm_num)
  have hBt := B_total C₂ C₃ c₁ hC₂ hC₃ hc₁ B hB δ (by norm_num)
  have hTt := tail_total c₁ hc₁ C₃ hC₃ B hB δ (by norm_num)
  have hm := eventually_margin C₃ hC₃ B hB _ hc0
  have hBZ := tendsto_Zc.eventually (Filter.eventually_gt_atTop B)
  have hall : ∀ᶠ x : ℝ in Filter.atTop,
      (∑ p ∈ (Ioc ⌊x ^ (aR 0)⌋₊ ⌊x ^ (aR 48)⌋₊).filter Nat.Prime, fR B x p ≤
        (1200877 / 1000000 + δ) * ∏ q ∈ PB B (Zc x), (1 - 1 / (q : ℝ))) ∧
      (∑ p ∈ (Ioc ⌊x ^ (aB 0)⌋₊ ⌊x ^ (aB 20)⌋₊).filter Nat.Prime, fB B x p ≤
        (73899 / 500000 + δ) * ∏ q ∈ PB B (Zc x), (1 - 1 / (q : ℝ))) ∧
      (∑ p ∈ ((Icc 1 ⌊x ^ ((1 : ℝ) / 200)⌋₊).filter Nat.Prime).filter (fun p => Wc x ≤ p), fB B x p ≤
        (1 / 2000 + δ) * ∏ q ∈ PB B (Zc x), (1 - 1 / (q : ℝ))) ∧
      (6 / Real.log x ^ 3 < (8 / 5 * (1 - eB) - eR) * ∏ q ∈ PB B (Zc x), (1 - 1 / (q : ℝ))) ∧
      B < Zc x ∧ Wc x ≤ Zc x ∧ ((∏ q ∈ PB B (Wc x), q : ℕ) : ℝ) ≤ x ^ ((6 : ℝ) / 25) ∧ 1 < x := by
    filter_upwards [hRt, hBt, hTt, hm, hBZ, eventually_W_le_Z, eventually_PW B,
      Filter.eventually_gt_atTop (1 : ℝ)] with x h1 h2 h3 h4 h5 h6 h7 h8
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1 hall
  refine ⟨x₀, fun A x hx hA hlev hsq hne => ?_⟩
  obtain ⟨hR1, hB1, hT1, hmar, hBZx, hWZ, hPW, hx1⟩ := hx₀ x hx
  have ha0 : aR 0 = 49 / 1000 := by norm_num [aR]
  have ha48 : aR 48 = 23 / 100 := by norm_num [aR]
  have hb0 : aB 0 = 1 / 200 := by norm_num [aB]
  have hb20 : aB 20 = 1 / 20 := by norm_num [aB]
  rw [ha0, ha48] at hR1
  rw [hb0, hb20] at hB1
  have h20 : x ^ ((1 : ℝ) / 20) ≤ x ^ ((6 : ℝ) / 25) := Real.rpow_le_rpow_of_exponent_le hx1.le (by norm_num)
  have h23 : x ^ ((23 : ℝ) / 100) ≤ x ^ ((6 : ℝ) / 25) := Real.rpow_le_rpow_of_exponent_le hx1.le (by norm_num)
  apply sieve_core A B x hx1 hB hA hne (Wc x) (Zc x) hWZ hBZx (Nat.le_ceil _) hPW
    (fun p hp1 hpZ => by
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp1
      rw [le_div_iff₀ hp0, one_mul]
      have : (p : ℝ) < x ^ ((1 : ℝ) / 20) := Nat.lt_ceil.1 hpZ
      linarith)
    (fun p hp1 hpy => by
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp1
      rw [le_div_iff₀ hp0, one_mul]; linarith)
    eB eR
    (by
      refine le_trans (B_glue B x hx1) ?_
      have : eB * ∏ q ∈ PB B (Zc x), (1 - 1 / (q : ℝ)) =
          (1 / 2000 + δ) * ∏ q ∈ PB B (Zc x), (1 - 1 / (q : ℝ)) +
          (73899 / 500000 + δ) * ∏ q ∈ PB B (Zc x), (1 - 1 / (q : ℝ)) := by simp only [eB]; ring
      rw [this]; exact add_le_add hT1 hB1)
    (le_trans (R_glue B x hx1) hR1)
    hlev hsq hmar

end Palprimes
