import KappaOmega2.Statements
import Palprimes.E1.Mertens
import Palprimes.Sieve.SelbergSum

namespace KappaOmega2

open Finset Palprimes

/-! Item M03: `G(z) ≥ H_s(K)` (grouping by the radical) and Mertens. -/

lemma m03_gS_nonneg (b n : ℕ) : 0 ≤ gS b n := by
  unfold gS
  split_ifs
  · positivity
  · exact le_rfl

lemma m03_HB_le (b : ℕ) (hb : 2 ≤ b) (K : ℕ) (z : ℝ) (hKz : (K : ℝ) < z) (hz : 0 < z) :
    HB (bigB b).primeFactors K ≤ GS b z := by
  classical
  have hB0 : bigB b ≠ 0 := by
    unfold bigB
    have : b < b ^ 3 := by
      calc b = b ^ 1 := (pow_one b).symm
        _ < b ^ 3 := Nat.pow_lt_pow_right (by omega) (by omega)
    omega
  set Pset : Finset ℕ := (range (K + 1)).filter (fun p => p.Prime ∧ ¬ p ∣ bigB b) with hPset
  have hP : ∀ p ∈ Pset, p.Prime := fun p hp => (Finset.mem_filter.1 hp).2.1
  -- Step 1: HB ≤ Σ over factored numbers
  have h1 : HB (bigB b).primeFactors K ≤
      ∑ n ∈ (Icc 1 K).filter (fun n => n ∈ Nat.factoredNumbers Pset), (1 : ℝ) / n := by
    unfold HB
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro m hm
      rw [Finset.mem_filter, Finset.mem_Icc] at hm ⊢
      refine ⟨hm.1, ?_⟩
      rw [Nat.mem_factoredNumbers]
      refine ⟨by omega, fun p hp' => ?_⟩
      have hp := Nat.prime_of_mem_primeFactorsList hp'
      have hpm := Nat.dvd_of_mem_primeFactorsList hp'
      rw [hPset, Finset.mem_filter, Finset.mem_range]
      refine ⟨by have := Nat.le_of_dvd (by omega) hpm; omega, hp, fun hpB => ?_⟩
      exact hm.2 p (Nat.mem_primeFactors.2 ⟨hp, hpB, hB0⟩) hpm
    · intro m _ _; positivity
  have h2 := factored_le_selbergS Pset hP K ((K : ℝ) ^ 2) le_rfl
  -- Step 2: Selberg side ≤ GS
  have hPsq : Squarefree (∏ p ∈ Pset, p) := SelbergPort.prod_primes_squarefree Pset hP
  have hPcop : Nat.Coprime (∏ p ∈ Pset, p) (bigB b) := by
    apply Nat.Coprime.prod_left
    intro p hp
    have := (Finset.mem_filter.1 hp).2
    exact (Nat.Prime.coprime_iff_not_dvd this.1).2 this.2
  have h3 : ∑ l ∈ (∏ p ∈ Pset, p).divisors with (((l : ℕ) : ℝ) ^ 2 ≤ (K : ℝ) ^ 2), (1 : ℝ) / (Nat.totient l) ≤
      GS b z := by
    have hterm : ∀ l ∈ (∏ p ∈ Pset, p).divisors.filter (fun l : ℕ => (((l : ℕ) : ℝ) ^ 2 ≤ (K : ℝ) ^ 2)),
        (1 : ℝ) / (Nat.totient l) = gS b l := by
      intro l hl
      rw [Finset.mem_filter, Nat.mem_divisors] at hl
      unfold gS
      rw [if_pos ⟨hPsq.squarefree_of_dvd hl.1.1, Nat.Coprime.coprime_dvd_left hl.1.1 hPcop⟩]
    rw [Finset.sum_congr rfl hterm]
    unfold GS
    calc ∑ l ∈ (∏ p ∈ Pset, p).divisors.filter (fun l : ℕ => (((l : ℕ) : ℝ) ^ 2 ≤ (K : ℝ) ^ 2)), gS b l
        ≤ ∑ n ∈ Icc 1 K, gS b n := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro l hl
            rw [Finset.mem_filter, Nat.mem_divisors] at hl
            rw [Finset.mem_Icc]
            refine ⟨Nat.pos_of_dvd_of_pos hl.1.1 (Nat.pos_of_ne_zero hl.1.2), ?_⟩
            have : (l : ℝ) ≤ K := by
              have h0 : (0 : ℝ) ≤ l := Nat.cast_nonneg _
              have h0' : (0 : ℝ) ≤ K := Nat.cast_nonneg _
              nlinarith [hl.2]
            exact_mod_cast this
          · intro n _ _; exact m03_gS_nonneg b n
      _ ≤ ∑ n ∈ ltSet z, gS b n := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro n hn
            rw [Finset.mem_Icc] at hn
            unfold ltSet
            rw [Finset.mem_filter, Finset.mem_range]
            have hnz : (n : ℝ) < z := lt_of_le_of_lt (by exact_mod_cast hn.2) hKz
            exact ⟨Nat.lt_ceil.2 hnz, hn.1, hnz⟩
          · intro n _ _; exact m03_gS_nonneg b n
  linarith

theorem itemM03 : ItemM03 := by
  intro b hb ε hε
  set s := (bigB b).primeFactors with hs
  have hsP : ∀ q ∈ s, q.Prime := fun q hq => Nat.prime_of_mem_primeFactors hq
  set β : ℝ := ∏ q ∈ s, (1 - 1 / (q : ℝ)) with hβ
  have hβpos : 0 < β := MT.cB_pos b
  set η : ℝ := ε / (2 * (1 + ε)) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨x1, hx1, hV⟩ := E1.VB_log_bounds b hb hη0
  set C1 : ℝ := 2 ^ (#s) * (2 + 2 * Real.log (∏ q ∈ s, q : ℕ)) with hC1
  set C2 : ℝ := β + C1 with hC2
  set Lz : ℝ := max (2 * C2 * (1 + ε / 2) / (β * ε)) 0 with hLz
  set M : ℝ := max x1 (max 3 (Real.exp Lz)) with hM
  have hM3 : 3 ≤ M := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_refl M))
  refine ⟨M ^ 2, fun x hx => ?_⟩
  have hz : M ≤ Real.sqrt x := by
    rw [show M = Real.sqrt (M ^ 2) by rw [Real.sqrt_sq (by linarith)]]
    exact Real.sqrt_le_sqrt hx
  set z := Real.sqrt x with hzdef
  have hz3 : 3 ≤ z := le_trans hM3 hz
  have hz1 : x1 ≤ z := le_trans (le_max_left _ _) hz
  have hzL : Real.exp Lz ≤ z :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hz
  have hlogz : Lz ≤ Real.log z := by
    rw [← Real.log_exp Lz]; exact Real.log_le_log (Real.exp_pos _) hzL
  have hlogpos : 0 < Real.log z := Real.log_pos (by linarith)
  -- K
  set K : ℕ := ⌈z⌉₊ - 1 with hK
  have hKz : (K : ℝ) < z := by
    have h1 : (⌈z⌉₊ : ℝ) < z + 1 := Nat.ceil_lt_add_one (by linarith)
    have h2 : 1 ≤ ⌈z⌉₊ := Nat.one_le_iff_ne_zero.2 (by
      have := Nat.ceil_pos.2 (show 0 < z by linarith); omega)
    rw [hK, Nat.cast_sub h2]; push_cast; linarith
  have hKz' : z - 1 ≤ K := by
    have h1 : z ≤ (⌈z⌉₊ : ℝ) := Nat.le_ceil z
    have h2 : 1 ≤ ⌈z⌉₊ := Nat.one_le_iff_ne_zero.2 (by
      have := Nat.ceil_pos.2 (show 0 < z by linarith); omega)
    rw [hK, Nat.cast_sub h2]; push_cast; linarith
  have hK1 : 1 ≤ K := by
    have : (1 : ℝ) < K := by linarith
    exact_mod_cast this.le
  -- G ≥ β log z - C2
  have hG1 := m03_HB_le b hb K z hKz (by linarith)
  have hHB := HB_approx s hsP K hK1
  have hlogK : Real.log z - 1 ≤ Real.log K := by
    have hKpos : (0 : ℝ) < K := by exact_mod_cast hK1
    have h2 : z / 2 ≤ K := by linarith
    have : Real.log (z / 2) ≤ Real.log K := Real.log_le_log (by linarith) h2
    rw [Real.log_div (by linarith) (by norm_num)] at this
    have := Real.log_two_lt_d9
    linarith
  have hG : β * Real.log z - C2 ≤ GS b z := by
    have h1 := (abs_le.1 hHB).1
    have h2 : β * (Real.log z - 1) ≤ β * Real.log K := mul_le_mul_of_nonneg_left hlogK hβpos.le
    nlinarith
  -- numerics
  have hε2 : 0 < ε / 2 := by positivity
  have hkey : β * Real.log z / (1 + ε / 2) ≤ β * Real.log z - C2 := by
    have hq : 2 * C2 * (1 + ε / 2) / (β * ε) ≤ Real.log z := le_trans (le_max_left _ _) hlogz
    rw [div_le_iff₀ (by positivity)] at hq
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_pos hβpos hε2]
  have hGpos : 0 < GS b z := by
    have : 0 < β * Real.log z / (1 + ε / 2) := by positivity
    linarith
  have hVz := (hV z hz1).1
  have hκ : Real.exp Real.eulerMascheroniConstant * MT.kappaB b = 1 / β := by
    unfold MT.kappaB
    rw [show MT.cB b = β from rfl, ← mul_div_assoc, ← Real.exp_add]
    simp
  have hVlow : (1 + ε / 2) / (β * Real.log z) ≤ (1 + ε) * Real.exp Real.eulerMascheroniConstant * MT.VB b z := by
    have h1 : (1 - η) * MT.kappaB b / Real.log z ≤ MT.VB b z := by
      rw [div_le_iff₀ hlogpos]; exact hVz
    have h2 : (1 + ε) * (1 - η) = 1 + ε / 2 := by
      rw [hη]; field_simp; ring
    calc (1 + ε / 2) / (β * Real.log z) = (1 + ε) * (1 - η) * (1 / β) / Real.log z := by
          rw [h2]; field_simp
      _ = (1 + ε) * (1 - η) * (Real.exp Real.eulerMascheroniConstant * MT.kappaB b) / Real.log z := by
          rw [hκ]
      _ = (1 + ε) * Real.exp Real.eulerMascheroniConstant * ((1 - η) * MT.kappaB b / Real.log z) := by ring
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left h1
          positivity
  calc 1 / GS b z ≤ 1 / (β * Real.log z / (1 + ε / 2)) := by
        apply one_div_le_one_div_of_le (by positivity)
        linarith
    _ = (1 + ε / 2) / (β * Real.log z) := by field_simp
    _ ≤ _ := hVlow

end KappaOmega2
