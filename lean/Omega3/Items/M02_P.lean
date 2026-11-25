import Omega3.Items.M02_A
import Palprimes.Sieve.Vendor.Mertens

/-! # M02 helpers (copied from S08, renamed), part P: Mertens on half-open intervals and prime sums of step functions. -/

namespace Omega3

open Finset Palprimes

set_option linter.style.longLine false

/-- Sandwich: a set `S` of exactly the primes in `[A, T)` lies between `(A, T/2]` and `(A/2, T]`. -/
lemma m02_sandwich (S : Finset ℕ) (A T : ℝ) (hA : 0 < A)
    (hS1 : ∀ p ∈ S, p.Prime ∧ A ≤ p ∧ (p : ℝ) < T) (hS2 : ∀ p : ℕ, p.Prime → A ≤ p → (p : ℝ) < T → p ∈ S)
    (f : ℕ → ℝ) (hf : ∀ p, 0 ≤ f p) :
    ∑ p ∈ (Ioc ⌊A⌋₊ ⌊T / 2⌋₊).filter Nat.Prime, f p ≤ ∑ p ∈ S, f p ∧
      ∑ p ∈ S, f p ≤ ∑ p ∈ (Ioc ⌊A / 2⌋₊ ⌊T⌋₊).filter Nat.Prime, f p := by
  constructor
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      rw [Finset.mem_filter, Finset.mem_Ioc] at hp
      have h1 : A < p := by
        have := Nat.lt_floor_add_one A
        have : ⌊A⌋₊ + 1 ≤ p := hp.1.1
        have : ((⌊A⌋₊ + 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast this
        push_cast at this; linarith
      have h2 : (p : ℝ) ≤ T / 2 := by
        have := hp.1.2
        have hT : 0 ≤ T / 2 := by
          by_contra hneg; push_neg at hneg
          rw [Nat.floor_of_nonpos hneg.le] at this; omega
        exact le_trans (by exact_mod_cast this) (Nat.floor_le hT)
      have hp0 : (0 : ℝ) < p := by linarith
      exact hS2 p hp.2 h1.le (by linarith)
    · intro p _ _; exact hf p
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hpp, h1, h2⟩ := hS1 p hp
      rw [Finset.mem_filter, Finset.mem_Ioc]
      refine ⟨⟨?_, ?_⟩, hpp⟩
      · have : (⌊A / 2⌋₊ : ℝ) < p := lt_of_le_of_lt (Nat.floor_le (by linarith)) (by linarith)
        exact_mod_cast this
      · exact Nat.le_floor h2.le
    · intro p _ _; exact hf p

lemma m02_log_sub_le (y c : ℝ) (hc : 0 ≤ c) (hyc : c < y) : Real.log y - Real.log (y - c) ≤ c / (y - c) := by
  have h1 : 0 < y - c := by linarith
  rw [← Real.log_div (by linarith) h1.ne']
  have := Real.log_le_sub_one_of_pos (show 0 < y / (y - c) from div_pos (by linarith) h1)
  have e : y / (y - c) - 1 = c / (y - c) := by rw [div_sub_one h1.ne']; congr 1; ring
  linarith

/-- Mertens 2 on `[A, T)`. -/
theorem m02_mertens2 : ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : Finset ℕ) (A T : ℝ), 4 ≤ A → A ≤ T →
    (∀ p ∈ S, p.Prime ∧ A ≤ p ∧ (p : ℝ) < T) → (∀ p : ℕ, p.Prime → A ≤ p → (p : ℝ) < T → p ∈ S) →
    |∑ p ∈ S, (1 : ℝ) / p - (Real.log (Real.log T) - Real.log (Real.log A))| ≤ C / Real.log A := by
  obtain ⟨C, hC⟩ := mertens2_interval
  refine ⟨2 * Real.log 2 + 2 * |C|, by positivity, ?_⟩
  intro S A T hA hAT hS1 hS2
  have hsand := m02_sandwich S A T (by linarith) hS1 hS2 (fun p => (1 : ℝ) / p) (fun p => div_nonneg zero_le_one (Nat.cast_nonneg p))
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlA : 2 * Real.log 2 ≤ Real.log A := by
    rw [← Real.log_rpow (by norm_num)]; apply Real.log_le_log (by positivity); norm_num; linarith
  have hlA0 : 0 < Real.log A := by linarith
  have hlT : Real.log A ≤ Real.log T := Real.log_le_log (by linarith) hAT
  have hCa : ∀ a : ℝ, 0 < a → C / a ≤ |C| / a := fun a ha => div_le_div_of_nonneg_right (le_abs_self C) ha.le
  rw [abs_le]
  constructor
  · -- lower
    rcases le_or_gt A (T / 2) with h | h
    · have hm := hC A (T / 2) (by linarith) h
      rw [abs_le] at hm
      have hlT2 : Real.log (T / 2) = Real.log T - Real.log 2 := Real.log_div (by linarith) (by norm_num)
      have hlT2' : Real.log A ≤ Real.log (T / 2) := Real.log_le_log (by linarith) h
      have hd := m02_log_sub_le (Real.log T) (Real.log 2) hl2.le (by linarith)
      rw [← hlT2] at hd
      have hd2 : Real.log 2 / Real.log (T / 2) ≤ Real.log 2 / Real.log A :=
        div_le_div_of_nonneg_left hl2.le hlA0 hlT2'
      have h3 := hCa (Real.log A) hlA0
      have e : (2 * Real.log 2 + 2 * |C|) / Real.log A = 2 * (Real.log 2 / Real.log A) + 2 * (|C| / Real.log A) := by ring
      have : 0 ≤ Real.log 2 / Real.log A := by positivity
      have : 0 ≤ |C| / Real.log A := by positivity
      linarith [hsand.1]
    · have hS0 : 0 ≤ ∑ p ∈ S, (1 : ℝ) / p := Finset.sum_nonneg (fun p _ => by positivity)
      have hT2 : Real.log T ≤ Real.log A + Real.log 2 := by
        rw [← Real.log_mul (by linarith) (by norm_num)]; exact Real.log_le_log (by linarith) (by linarith)
      have hd := m02_log_sub_le (Real.log A + Real.log 2) (Real.log 2) hl2.le (by linarith)
      simp only [add_sub_cancel_right] at hd
      have h4 : Real.log (Real.log T) ≤ Real.log (Real.log A + Real.log 2) := Real.log_le_log (by linarith) hT2
      have : Real.log 2 / Real.log A ≤ (2 * Real.log 2 + 2 * |C|) / Real.log A := by
        apply div_le_div_of_nonneg_right _ hlA0.le; have := abs_nonneg C; linarith
      linarith
  · -- upper
    have hm := hC (A / 2) T (by linarith) (by linarith)
    rw [abs_le] at hm
    have hlA2 : Real.log (A / 2) = Real.log A - Real.log 2 := Real.log_div (by linarith) (by norm_num)
    have hd := m02_log_sub_le (Real.log A) (Real.log 2) hl2.le (by linarith)
    rw [← hlA2] at hd
    have hla2 : Real.log A / 2 ≤ Real.log (A / 2) := by rw [hlA2]; linarith
    have hla20 : 0 < Real.log (A / 2) := by linarith
    have hd2 : Real.log 2 / Real.log (A / 2) ≤ 2 * Real.log 2 / Real.log A := by
      rw [div_le_div_iff₀ hla20 hlA0]; nlinarith
    have h3 : C / Real.log (A / 2) ≤ 2 * |C| / Real.log A := by
      refine le_trans (hCa _ hla20) ?_
      rw [div_le_div_iff₀ hla20 hlA0]; have := abs_nonneg C; nlinarith
    have : 2 * Real.log 2 / Real.log A + 2 * |C| / Real.log A = (2 * Real.log 2 + 2 * |C|) / Real.log A := by ring
    linarith [hsand.2]

/-- Mertens 1 on `[A, T)`. -/
theorem m02_mertens1 : ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : Finset ℕ) (A T : ℝ), 2 ≤ A → A ≤ T →
    (∀ p ∈ S, p.Prime ∧ A ≤ p ∧ (p : ℝ) < T) → (∀ p : ℕ, p.Prime → A ≤ p → (p : ℝ) < T → p ∈ S) →
    |∑ p ∈ S, Real.log p / p - (Real.log T - Real.log A)| ≤ C := by
  obtain ⟨c, hc0, hc⟩ := Mertens.E₁p.bounded
  have hint : ∀ a t : ℝ, 1 ≤ a → a ≤ t →
      |∑ p ∈ (Ioc ⌊a⌋₊ ⌊t⌋₊).filter Nat.Prime, Real.log p / p - (Real.log t - Real.log a)| ≤ 2 * c := by
    intro a t ha hat
    have hfl : ⌊a⌋₊ ≤ ⌊t⌋₊ := Nat.floor_le_floor hat
    have hsplit : ∑ p ∈ (Ioc ⌊a⌋₊ ⌊t⌋₊).filter Nat.Prime, Real.log p / p =
        ∑ p ∈ Ioc 0 ⌊t⌋₊ with p.Prime, Real.log p / p - ∑ p ∈ Ioc 0 ⌊a⌋₊ with p.Prime, Real.log p / p := by
      simp only [Finset.sum_filter]
      rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le ⌊a⌋₊) hfl]
      ring
    rw [hsplit, Mertens.sum_log_prime_div_eq, Mertens.sum_log_prime_div_eq]
    have h1 := hc t (by linarith)
    have h2 := hc a ha
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith
  refine ⟨Real.log 2 + 2 * c, by have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity, ?_⟩
  intro S A T hA hAT hS1 hS2
  have hsand := m02_sandwich S A T (by linarith) hS1 hS2 (fun p => Real.log p / p)
    (fun p => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [abs_le]
  constructor
  · rcases le_or_gt A (T / 2) with h | h
    · have hm := hint A (T / 2) (by linarith) h
      rw [abs_le] at hm
      have : Real.log (T / 2) = Real.log T - Real.log 2 := Real.log_div (by linarith) (by norm_num)
      linarith [hsand.1]
    · have hS0 : 0 ≤ ∑ p ∈ S, Real.log p / p :=
        Finset.sum_nonneg (fun p _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))
      have hT2 : Real.log T ≤ Real.log A + Real.log 2 := by
        rw [← Real.log_mul (by linarith) (by norm_num)]; exact Real.log_le_log (by linarith) (by linarith)
      linarith
  · have hm := hint (A / 2) T (by linarith) (by linarith)
    rw [abs_le] at hm
    have : Real.log (A / 2) = Real.log A - Real.log 2 := Real.log_div (by linarith) (by norm_num)
    linarith [hsand.2]

/-! ### Prime sums over `P(z)` in the coordinate `u = log p/log z` -/

/-- The primes `< z`. -/
noncomputable def m02Pz (z : ℝ) : Finset ℕ := (ltSet z).filter Nat.Prime

/-- `u_p = log p/log z`. -/
noncomputable def m02u (z : ℝ) (p : ℕ) : ℝ := Real.log p / Real.log z

/-- The integral of one piece: `∫₀^s 1[a ≤ v < m](s − v)/v dv`. -/
noncomputable def m02Ip (a m s : ℝ) : ℝ :=
  if a < min m s then s * (Real.log (min m s) - Real.log a) - (min m s - a) else 0

lemma m02_mem_set (z : ℝ) (hz : 1 < z) (a b' : ℝ) (hb1 : b' ≤ 1) (p : ℕ) :
    (p ∈ (m02Pz z).filter (fun p => a ≤ m02u z p ∧ m02u z p < b')) ↔
      (p.Prime ∧ z ^ a ≤ (p : ℝ) ∧ (p : ℝ) < z ^ b') := by
  have hL : 0 < Real.log z := Real.log_pos hz
  have hz0 : 0 < z := by linarith
  unfold m02Pz m02u
  rw [Finset.mem_filter, Finset.mem_filter, m02_mem_ltSet]
  constructor
  · rintro ⟨⟨⟨h1, _⟩, hp⟩, ha, hb⟩
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    refine ⟨hp, ?_, ?_⟩
    · rw [le_div_iff₀ hL] at ha
      rw [Real.rpow_def_of_pos hz0, ← Real.exp_log hp0]
      exact Real.exp_le_exp.2 (by linarith)
    · rw [div_lt_iff₀ hL] at hb
      rw [Real.rpow_def_of_pos hz0, ← Real.exp_log hp0]
      exact Real.exp_lt_exp.2 (by linarith)
  · rintro ⟨hp, ha, hb⟩
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hzb : z ^ b' ≤ z := by
      calc z ^ b' ≤ z ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hz.le hb1
        _ = z := Real.rpow_one z
    refine ⟨⟨⟨hp.one_lt.le, by linarith⟩, hp⟩, ?_, ?_⟩
    · rw [le_div_iff₀ hL]
      rw [Real.rpow_def_of_pos hz0] at ha
      have := Real.log_le_log (Real.exp_pos _) ha
      rw [Real.log_exp] at this; linarith
    · rw [div_lt_iff₀ hL]
      rw [Real.rpow_def_of_pos hz0] at hb
      have := Real.log_lt_log hp0 hb
      rw [Real.log_exp] at this; linarith

/-- One piece of a step function against Mertens. -/
lemma m02_piece (a m : ℝ) (ha : 0 < a) : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, 1 < z → Real.log 4 ≤ a * Real.log z →
    ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      |∑ p ∈ m02Pz z, (1 / (p : ℝ)) * (if a ≤ m02u z p ∧ m02u z p < m then 1 else 0) * max (s - m02u z p) 0 -
        m02Ip a m s| ≤ C / Real.log z := by
  classical
  obtain ⟨C2, hC2, hM2⟩ := m02_mertens2
  obtain ⟨C1, hC1, hM1⟩ := m02_mertens1
  refine ⟨C2 / a + C1, by positivity, ?_⟩
  intro z hz h4 s hs0 hs1
  have hL : 0 < Real.log z := Real.log_pos hz
  have hz0 : 0 < z := by linarith
  set m' := min m s with hm'
  have key : ∀ u w : ℝ, w * (if a ≤ u ∧ u < m then 1 else 0) * max (s - u) 0 =
      if a ≤ u ∧ u < m' then w * (s - u) else 0 := by
    intro u w
    split_ifs with h1 h2 h2
    · rw [max_eq_left (by have := min_le_right m s; linarith)]; ring
    · have : s ≤ u := by
        by_contra hc; push_neg at hc; exact h2 ⟨h1.1, lt_min h1.2 hc⟩
      rw [max_eq_right (by linarith)]; ring
    · exact absurd ⟨h2.1, lt_of_lt_of_le h2.2 (min_le_left _ _)⟩ h1
    · ring
  rw [Finset.sum_congr rfl (fun p _ => key (m02u z p) (1 / (p : ℝ))), ← Finset.sum_filter]
  unfold m02Ip
  rw [← hm']
  split_ifs with ham
  swap
  · rw [Finset.sum_eq_zero]
    · simp only [sub_zero, abs_zero]; positivity
    · intro p hp
      rw [Finset.mem_filter] at hp
      exact absurd (lt_of_le_of_lt hp.2.1 hp.2.2) (not_lt.2 (not_lt.1 ham))
  have hm's : m' ≤ s := min_le_right _ _
  have hm'1 : m' ≤ 1 := le_trans hm's hs1
  have hm'0 : 0 < m' := lt_trans ha ham
  set S := (m02Pz z).filter (fun p => a ≤ m02u z p ∧ m02u z p < m') with hS
  have hmem := m02_mem_set z hz a m' hm'1
  have hS1 : ∀ p ∈ S, p.Prime ∧ z ^ a ≤ (p : ℝ) ∧ (p : ℝ) < z ^ m' := fun p hp => (hmem p).1 hp
  have hS2 : ∀ p : ℕ, p.Prime → z ^ a ≤ (p : ℝ) → (p : ℝ) < z ^ m' → p ∈ S :=
    fun p h1 h2 h3 => (hmem p).2 ⟨h1, h2, h3⟩
  have hlA : Real.log (z ^ a) = a * Real.log z := Real.log_rpow hz0 a
  have hlT : Real.log (z ^ m') = m' * Real.log z := Real.log_rpow hz0 m'
  have hA4 : 4 ≤ z ^ a := by
    rw [Real.rpow_def_of_pos hz0, ← Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    exact Real.exp_le_exp.2 (by linarith)
  have hAT : z ^ a ≤ z ^ m' := Real.rpow_le_rpow_of_exponent_le hz.le ham.le
  have m2 := hM2 S (z ^ a) (z ^ m') hA4 hAT hS1 hS2
  have m1 := hM1 S (z ^ a) (z ^ m') (by linarith) hAT hS1 hS2
  rw [hlA, hlT] at m2 m1
  have hll : Real.log (m' * Real.log z) - Real.log (a * Real.log z) = Real.log m' - Real.log a := by
    rw [Real.log_mul hm'0.ne' hL.ne', Real.log_mul ha.ne' hL.ne']; ring
  rw [hll] at m2
  have hsplit : ∑ p ∈ S, 1 / (p : ℝ) * (s - m02u z p) =
      s * ∑ p ∈ S, (1 : ℝ) / p - (1 / Real.log z) * ∑ p ∈ S, Real.log p / p := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro p _; unfold m02u; ring
  rw [hsplit]
  set X := ∑ p ∈ S, (1 : ℝ) / p
  set Y := ∑ p ∈ S, Real.log p / p
  have e : s * X - 1 / Real.log z * Y - (s * (Real.log m' - Real.log a) - (m' - a)) =
      s * (X - (Real.log m' - Real.log a)) - (Y - (m' * Real.log z - a * Real.log z)) / Real.log z := by
    field_simp; ring
  rw [e]
  have haL : 0 < a * Real.log z := by positivity
  calc _ ≤ |s * (X - (Real.log m' - Real.log a))| + |(Y - (m' * Real.log z - a * Real.log z)) / Real.log z| :=
        abs_sub _ _
    _ ≤ 1 * (C2 / (a * Real.log z)) + C1 / Real.log z := by
        rw [abs_mul, abs_div, abs_of_pos hL, abs_of_nonneg hs0]
        gcongr
    _ = (C2 / a + C1) / Real.log z := by field_simp

end Omega3
