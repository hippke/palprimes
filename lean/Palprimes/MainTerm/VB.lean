import Palprimes.MainTerm.PrimeRiemann

/-! # Mertens' third theorem for the density `gB`

`V(w) log w → κ_B = e^{−γ} / Π_{p ∣ b³−b} (1 − 1/p)` with error `O(1/log w)`. -/

set_option linter.style.longLine false

open Finset Real Filter Topology

namespace Palprimes.MT

open Palprimes.Greaves

/-- `c_B = Π_{p ∣ b³ − b} (1 − 1/p)`. -/
noncomputable def cB (b : ℕ) : ℝ := ∏ p ∈ (Palprimes.bigB b).primeFactors, (1 - 1 / (p : ℝ))

theorem cB_pos (b : ℕ) : 0 < cB b := by
  unfold cB
  apply Finset.prod_pos
  intro p hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  have : 1 / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; exact hp1
  linarith

/-- For `w > b³ − b`, `V(w) = (Π_{p<w} (1 − 1/p)) / c_B`. -/
theorem VB_eq (b : ℕ) (hb : 2 ≤ b) (w : ℝ) (hw : (Palprimes.bigB b : ℝ) < w) :
    VB b w = (∏ p ∈ primesBelow w, (1 - 1 / (p : ℝ))) / cB b := by
  classical
  have hB0 : Palprimes.bigB b ≠ 0 := bigB_ne_zero' b hb
  rw [eq_div_iff (cB_pos b).ne']
  have hsplit : ∏ p ∈ primesBelow w, (1 - 1 / (p : ℝ)) =
      (∏ p ∈ (primesBelow w).filter (fun p => Nat.Coprime p (Palprimes.bigB b)), (1 - 1 / (p : ℝ))) *
      ∏ p ∈ (primesBelow w).filter (fun p => ¬ Nat.Coprime p (Palprimes.bigB b)), (1 - 1 / (p : ℝ)) :=
    (Finset.prod_filter_mul_prod_filter_not _ _ _).symm
  have hB : (primesBelow w).filter (fun p => ¬ Nat.Coprime p (Palprimes.bigB b)) =
      (Palprimes.bigB b).primeFactors := by
    ext p
    simp only [mem_filter, mem_primesBelow, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨hp, _⟩, hnc⟩
      exact ⟨hp, (Nat.Prime.dvd_iff_not_coprime hp).2 hnc, hB0⟩
    · rintro ⟨hp, hdvd, _⟩
      refine ⟨⟨hp, ?_⟩, (Nat.Prime.dvd_iff_not_coprime hp).1 hdvd⟩
      have : p ≤ Palprimes.bigB b := Nat.le_of_dvd (Nat.pos_of_ne_zero hB0) hdvd
      have : (p : ℝ) ≤ Palprimes.bigB b := by exact_mod_cast this
      linarith
  rw [hsplit, hB]
  unfold VB cB
  congr 1
  rw [← Finset.prod_filter_mul_prod_filter_not (primesBelow w) (fun p => Nat.Coprime p (Palprimes.bigB b))]
  have h1 : ∏ p ∈ (primesBelow w).filter (fun p => ¬ Nat.Coprime p (Palprimes.bigB b)), (1 - gB b p) = 1 := by
    apply Finset.prod_eq_one
    intro p hp
    rw [mem_filter] at hp
    unfold gB; rw [if_neg (fun h => hp.2 h.2)]; ring
  rw [h1, mul_one]
  apply Finset.prod_congr rfl
  intro p hp
  rw [mem_filter, mem_primesBelow] at hp
  unfold gB; rw [if_pos ⟨hp.1.1, hp.2⟩]

/-- Primes below `w` are the primes up to `⌈w⌉ − 1`. -/
theorem primesBelow_eq (w : ℝ) (hw : 1 ≤ w) :
    primesBelow w = (Icc 1 ⌊((⌈w⌉₊ - 1 : ℕ) : ℝ)⌋₊).filter Nat.Prime := by
  ext p
  rw [mem_primesBelow, mem_filter, mem_Icc, Nat.floor_natCast]
  constructor
  · rintro ⟨hp, hpw⟩
    refine ⟨⟨hp.one_lt.le, ?_⟩, hp⟩
    have : p < ⌈w⌉₊ := Nat.lt_ceil.2 hpw
    omega
  · rintro ⟨⟨_, hp2⟩, hp⟩
    refine ⟨hp, ?_⟩
    have h1 : p + 1 ≤ ⌈w⌉₊ := by
      have : 1 ≤ ⌈w⌉₊ := Nat.one_le_iff_ne_zero.2 (by
        intro h; rw [Nat.ceil_eq_zero] at h; linarith)
      omega
    have h2 : p < ⌈w⌉₊ := by omega
    exact Nat.lt_ceil.1 h2

/-- `κ_B = e^{−γ} / c_B`. -/
noncomputable def kappaB (b : ℕ) : ℝ := Real.exp (-Real.eulerMascheroniConstant) / cB b

theorem kappaB_pos (b : ℕ) : 0 < kappaB b := div_pos (Real.exp_pos _) (cB_pos b)

/-- **Mertens 3 for `gB`**: `|V(w) log w − κ_B| ≤ C / log w`. -/
theorem VB_log (b : ℕ) (hb : 2 ≤ b) : ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℝ, (Palprimes.bigB b : ℝ) + 4 ≤ w →
    |VB b w * Real.log w - kappaB b| ≤ C / Real.log w := by
  obtain ⟨C3, hC3⟩ := Palprimes.mertens3
  refine ⟨(2 * |C3| + 1) / cB b, by have := cB_pos b; positivity, fun w hw => ?_⟩
  have hB0 : (0 : ℝ) ≤ Palprimes.bigB b := Nat.cast_nonneg _
  have hw4 : 4 ≤ w := by linarith
  have hw1 : 1 ≤ w := by linarith
  set t : ℝ := ((⌈w⌉₊ - 1 : ℕ) : ℝ) with ht
  have hceil1 : (w : ℝ) ≤ ⌈w⌉₊ := Nat.le_ceil w
  have hceil2 : (⌈w⌉₊ : ℝ) < w + 1 := Nat.ceil_lt_add_one (by linarith)
  have hc1 : 1 ≤ ⌈w⌉₊ := by
    have : (1 : ℝ) ≤ ⌈w⌉₊ := by linarith
    exact_mod_cast this
  have htw : t = (⌈w⌉₊ : ℝ) - 1 := by rw [ht, Nat.cast_sub hc1]; simp
  have ht1 : w - 1 ≤ t := by rw [htw]; linarith
  have ht2 : t < w := by rw [htw]; linarith
  have ht2' : 2 ≤ t := by linarith
  have hlw : 0 < Real.log w := Real.log_pos (by linarith)
  have hlt : 0 < Real.log t := Real.log_pos (by linarith)
  set P := ∏ p ∈ (Icc 1 ⌊t⌋₊).filter Nat.Prime, (1 - 1 / (p : ℝ)) with hP
  have hVB : VB b w = P / cB b := by
    rw [VB_eq b hb w (by linarith), primesBelow_eq w hw1]
  have hP0 : 0 ≤ P := Finset.prod_nonneg (fun p hp => by
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors (by
      simp only [mem_filter] at hp; exact Nat.mem_primeFactors.2 ⟨hp.2, dvd_refl p, hp.2.ne_zero⟩)).one_lt.le
    have : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hp1
    linarith)
  have hP1 : P ≤ 1 := Finset.prod_le_one₀ (fun p hp => by
      have hp1 : (1 : ℝ) ≤ p := by
        simp only [mem_filter] at hp; exact_mod_cast hp.2.one_lt.le
      have : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hp1
      linarith) (fun p hp => by
      have : 0 ≤ 1 / (p : ℝ) := by positivity
      linarith)
  have hM := hC3 t ht2'
  -- `log w − log t ≤ 1/t ≤ 1/log w`
  have hdiff : Real.log w - Real.log t ≤ 1 / Real.log w := by
    have h1 : Real.log w - Real.log t ≤ w / t - 1 := by
      rw [← Real.log_div (by linarith) (by linarith)]
      exact Real.log_le_sub_one_of_pos (by positivity)
    have h2 : w / t - 1 ≤ 1 / t := by
      rw [div_sub_one (by linarith), div_le_div_iff_of_pos_right (by linarith)]; linarith
    have h3 : Real.log w ≤ t := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < w / 2)
      rw [Real.log_div (by linarith) (by norm_num)] at this
      have := Real.log_two_lt_d9
      linarith
    have h4 : 1 / t ≤ 1 / Real.log w := one_div_le_one_div_of_le hlw h3
    linarith
  have hdiff0 : 0 ≤ Real.log w - Real.log t := by
    have := Real.log_le_log (by linarith) ht2.le; linarith
  -- `log t ≥ log w / 2`
  have hlt2 : Real.log w / 2 ≤ Real.log t := by
    have h1 : Real.log (w / 2) ≤ Real.log t := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_div (by linarith) (by norm_num)] at h1
    have h2 : Real.log 2 ≤ Real.log w / 2 := by
      have := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hw4
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at this; push_cast at this; linarith
    linarith
  have hCt : |C3| / Real.log t ≤ 2 * |C3| / Real.log w := by
    rw [div_le_div_iff₀ hlt hlw]
    nlinarith [abs_nonneg C3]
  rw [hVB, kappaB]
  have hcB := cB_pos b
  have e : P / cB b * Real.log w - Real.exp (-Real.eulerMascheroniConstant) / cB b =
      ((P * Real.log t - Real.exp (-Real.eulerMascheroniConstant)) + P * (Real.log w - Real.log t)) / cB b := by
    field_simp; ring
  rw [e, abs_div, abs_of_pos hcB, div_le_div_iff₀ hcB hlw, div_mul_eq_mul_div,
    le_div_iff₀ hcB]
  have hA : |P * Real.log t - Real.exp (-Real.eulerMascheroniConstant) + P * (Real.log w - Real.log t)| ≤
      |C3| / Real.log t + 1 / Real.log w := by
    calc _ ≤ |P * Real.log t - Real.exp (-Real.eulerMascheroniConstant)| + |P * (Real.log w - Real.log t)| :=
          abs_add_le _ _
      _ ≤ C3 / Real.log t + 1 * (1 / Real.log w) := by
          apply add_le_add hM
          rw [abs_mul, abs_of_nonneg hP0, abs_of_nonneg hdiff0]
          exact mul_le_mul hP1 hdiff hdiff0 (by norm_num)
      _ ≤ |C3| / Real.log t + 1 / Real.log w := by
          have : C3 / Real.log t ≤ |C3| / Real.log t := div_le_div_of_nonneg_right (le_abs_self _) hlt.le
          linarith
  have hfin : (|C3| / Real.log t + 1 / Real.log w) * Real.log w ≤ 2 * |C3| + 1 := by
    have h1 : 1 / Real.log w * Real.log w = 1 := by field_simp
    have h2 : |C3| / Real.log t * Real.log w ≤ 2 * |C3| := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hlt]; nlinarith [abs_nonneg C3]
    nlinarith
  calc |P * Real.log t - Real.exp (-Real.eulerMascheroniConstant) + P * (Real.log w - Real.log t)| * Real.log w * cB b
      ≤ (|C3| / Real.log t + 1 / Real.log w) * Real.log w * cB b := by gcongr
    _ ≤ (2 * |C3| + 1) * cB b := by gcongr
    _ = _ := by ring

end Palprimes.MT
