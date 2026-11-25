import KappaOmega2.Statements
import KappaOmega2.Items.M04_Band

/-!
# M04: band cost (Lemma 5′)

Only band primes contribute (`cOf = 1` elsewhere); for a band prime `δ`, `φ(δ) = U − x_δ ≥ 0` and `ρ(δ)/δ = gB(δ)`,
so the sum is at most `Σ_i (c_i − 1) e^γ Σ_{band i} (U − x_p) gB(p) V(√(y/p))`, and `m04_band` bounds each band.
-/

set_option linter.style.longLine false

open Finset Real Filter Topology

namespace KappaOmega2

open Palprimes Palprimes.MT Palprimes.Greaves

/-- Copy of S14 (band primes), renamed. -/
theorem m04_s14 : ItemS14 := by
  classical
  unfold ItemS14
  intro B hB y hy i δ hin
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hB
  obtain ⟨hδp, hi, hlo, hhi⟩ := hin
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hy0 : 0 < y := by linarith
  have hδpos : (0 : ℝ) < δ := Nat.cast_pos.mpr hδp.pos
  have hmono : ∀ j k : ℕ, j < k → k < B.xs.length → B.xs.getD j 0 < B.xs.getD k 0 := by
    intro j k hjk hk
    have hj : j < B.xs.length := by omega
    rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hk]
    exact List.pairwise_iff_getElem.mp h4 j k hj hk hjk
  have hin_i : inBand B y i δ := ⟨hδp, hi, hlo, hhi⟩
  have huniq : ∀ j k : ℕ, inBand B y j δ → inBand B y k δ → j = k := by
    intro j k hj hk
    obtain ⟨_, hjl, hj1, hj2⟩ := hj
    obtain ⟨_, hkl, hk1, hk2⟩ := hk
    have hjx : j + 1 < B.xs.length := by omega
    have hkx : k < B.xs.length := by omega
    have hjx' : j < B.xs.length := by omega
    rcases lt_trichotomy j k with h | h | h
    · exfalso
      have hle : B.xs.getD (j + 1) 0 ≤ B.xs.getD k 0 := by
        rcases (show j + 1 = k ∨ j + 1 < k by omega) with e | e
        · rw [e]
        · exact le_of_lt (hmono _ _ e hkx)
      have hcast : ((B.xs.getD (j + 1) 0 : ℚ) : ℝ) ≤ ((B.xs.getD k 0 : ℚ) : ℝ) :=
        Rat.cast_le.mpr hle
      have hpow : y ^ ((B.xs.getD (j + 1) 0 : ℚ) : ℝ) ≤ y ^ ((B.xs.getD k 0 : ℚ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) hcast
      linarith
    · exact h
    · exfalso
      have hle : B.xs.getD (k + 1) 0 ≤ B.xs.getD j 0 := by
        rcases (show k + 1 = j ∨ k + 1 < j by omega) with e | e
        · rw [e]
        · exact le_of_lt (hmono _ _ e hjx')
      have hcast : ((B.xs.getD (k + 1) 0 : ℚ) : ℝ) ≤ ((B.xs.getD j 0 : ℚ) : ℝ) :=
        Rat.cast_le.mpr hle
      have hpow : y ^ ((B.xs.getD (k + 1) 0 : ℚ) : ℝ) ≤ y ^ ((B.xs.getD j 0 : ℚ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) hcast
      linarith
  have hfind : ∃ j, inBand B y j δ := ⟨i, hin_i⟩
  have hfeq : Nat.find hfind = i := huniq _ _ (Nat.find_spec hfind) hin_i
  have hcs_i : i < B.cs.length := by omega
  have hc1 : (1 : ℚ) ≤ B.cs.getD i 1 := by
    rw [List.getD_eq_getElem _ _ hcs_i]
    exact h6 _ (List.getElem_mem _)
  have hxi : (1 : ℚ) / 3 ≤ B.xs.getD i 0 := by
    rcases Nat.eq_zero_or_pos i with e | e
    · subst e
      have h0 : B.xs.getD 0 0 = 1 / 3 := by
        rw [List.getD_eq_getElem?_getD, ← List.head?_eq_getElem?, h3]
        simp
      rw [h0]
    · have hlt := hmono 0 i e (by omega)
      have h0 : B.xs.getD 0 0 = 1 / 3 := by
        rw [List.getD_eq_getElem?_getD, ← List.head?_eq_getElem?, h3]
        simp
      rw [h0] at hlt
      exact le_of_lt hlt
  have hxi1 : B.xs.getD (i + 1) 0 ≤ B.xn := by
    have hlast : B.xn = B.xs.getD (B.xs.length - 1) 0 := by
      unfold BandData.xn
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega)]
      simp
    rw [hlast]
    rcases (show i + 1 = B.xs.length - 1 ∨ i + 1 < B.xs.length - 1 by omega) with e | e
    · rw [e]
    · exact le_of_lt (hmono _ _ e (by omega))
  have t5 : ((B.xs.getD i 0 : ℚ) : ℝ) ≤ Real.log δ / Real.log y := by
    have hl := Real.log_le_log (Real.rpow_pos_of_pos hy0 _) hlo
    rw [Real.log_rpow hy0] at hl
    rw [le_div_iff₀ hlogy]
    linarith
  have t6 : Real.log δ / Real.log y ≤ ((B.xs.getD (i + 1) 0 : ℚ) : ℝ) := by
    have hl := Real.log_lt_log hδpos hhi
    rw [Real.log_rpow hy0] at hl
    rw [div_le_iff₀ hlogy]
    linarith
  have ht_lo : (1 / 3 : ℝ) ≤ Real.log δ / Real.log y := by
    have hx' : ((1 / 3 : ℚ) : ℝ) ≤ ((B.xs.getD i 0 : ℚ) : ℝ) := Rat.cast_le.mpr hxi
    push_cast at hx'
    linarith
  have ht_hi : Real.log δ / Real.log y ≤ UU := by
    have h9 : ((B.xs.getD (i + 1) 0 : ℚ) : ℝ) ≤ ((B.xn : ℚ) : ℝ) := Rat.cast_le.mpr hxi1
    have hU : UU = 99 / 103 := rfl
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold etaOf
    rw [dif_pos hfind, hfeq]
  · unfold cOf
    rw [dif_pos hfind, hfeq]
  · rw [List.getD_eq_getElem _ _ (by omega : i < B.etas.length)]
    exact List.getElem_mem _
  · unfold cOf
    rw [dif_pos hfind, hfeq]
    exact_mod_cast hc1
  · exact t5
  · exact t6
  · unfold phiW wy Wf
    rw [Nat.Prime.primeFactors hδp, Finset.sum_singleton]
    have hmm : mm = 2 / 103 := rfl
    have hUU : UU = 99 / 103 := rfl
    have hW1 : W1 = 97 / 103 := rfl
    have hk : kSq = 582 / 103 := rfl
    set t := Real.log δ / Real.log y with ht
    rw [hmm] at *
    split_ifs with h1 h2 h3
    · exfalso
      norm_num at h1
      linarith
    · have ht3 : t = 1 / 3 := le_antisymm h2 ht_lo
      have hle : t - 2 / 103 ≤ kSq * t ^ 2 := by
        rw [hk, ht3]
        norm_num
      rw [min_eq_right hle, hW1, hUU, ht3]
      norm_num
    · rw [hW1, hmm, hUU]
      ring

/-- Band edges: `1/3 ≤ x_i < x_{i+1} ≤ 2U − 1`. -/
theorem m04_edges (B : BandData) (hB : BandOK B) (i : ℕ) (hi : i < B.etas.length) :
    (1 / 3 : ℝ) ≤ ((B.xs.getD i 0 : ℚ) : ℝ) ∧ ((B.xs.getD i 0 : ℚ) : ℝ) < ((B.xs.getD (i + 1) 0 : ℚ) : ℝ) ∧
      ((B.xs.getD (i + 1) 0 : ℚ) : ℝ) ≤ 2 * UU - 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hB
  have hmono : ∀ j k : ℕ, j < k → k < B.xs.length → B.xs.getD j 0 < B.xs.getD k 0 := by
    intro j k hjk hk
    have hj : j < B.xs.length := by omega
    rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hk]
    exact List.pairwise_iff_getElem.mp h4 j k hj hk hjk
  have h0 : B.xs.getD 0 0 = 1 / 3 := by
    rw [List.getD_eq_getElem?_getD, ← List.head?_eq_getElem?, h3]
    simp
  have hxi : (1 : ℚ) / 3 ≤ B.xs.getD i 0 := by
    rcases Nat.eq_zero_or_pos i with e | e
    · subst e; rw [h0]
    · have hlt := hmono 0 i e (by omega)
      rw [h0] at hlt
      exact le_of_lt hlt
  have hxi1 : B.xs.getD (i + 1) 0 ≤ B.xn := by
    have hlast : B.xn = B.xs.getD (B.xs.length - 1) 0 := by
      unfold BandData.xn
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega)]
      simp
    rw [hlast]
    rcases (show i + 1 = B.xs.length - 1 ∨ i + 1 < B.xs.length - 1 by omega) with e | e
    · rw [e]
    · exact le_of_lt (hmono _ _ e (by omega))
  refine ⟨?_, ?_, ?_⟩
  · have := (Rat.cast_le (K := ℝ)).mpr hxi
    push_cast at this; exact this
  · exact Rat.cast_lt.mpr (hmono i (i + 1) (by omega) (by omega))
  · have := (Rat.cast_le (K := ℝ)).mpr hxi1
    linarith

theorem m04_cge (B : BandData) (hB : BandOK B) (i : ℕ) : (1 : ℝ) ≤ ((B.cs.getD i 1 : ℚ) : ℝ) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hB
  have : (1 : ℚ) ≤ B.cs.getD i 1 := by
    rcases lt_or_ge i B.cs.length with h | h
    · rw [List.getD_eq_getElem _ _ h]; exact h6 _ (List.getElem_mem _)
    · rw [List.getD_eq_default _ _ h]
  exact_mod_cast this

theorem itemM04 : ItemM04 := by
  classical
  intro b hb B hB ε hε
  obtain ⟨n, hn⟩ : ∃ n, n = B.etas.length := ⟨_, rfl⟩
  obtain ⟨Csum, hCsum⟩ : ∃ Csum : ℝ, Csum = ∑ i ∈ range n, (((B.cs.getD i 1 : ℚ) : ℝ) - 1) := ⟨_, rfl⟩
  have hCs0 : 0 ≤ Csum := by
    rw [hCsum]; exact sum_nonneg (fun i _ => by linarith [m04_cge B hB i])
  obtain ⟨ε', hε'⟩ : ∃ ε' : ℝ, ε' = ε / (1 + Csum) := ⟨_, rfl⟩
  have hε'0 : 0 < ε' := by rw [hε']; positivity
  have hband : ∀ i ∈ range n, ∀ᶠ y in atTop, ∀ S : Finset ℕ,
      (∀ p ∈ S, p.Prime ∧ y ^ ((B.xs.getD i 0 : ℚ) : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) < y ^ ((B.xs.getD (i + 1) 0 : ℚ) : ℝ)) →
      ∑ p ∈ S, (UU - Real.log p / Real.log y) * gB b p * VB b (Real.sqrt (y / p)) ≤
        2 * VB b y * (bandI ((B.xs.getD i 0 : ℚ) : ℝ) ((B.xs.getD (i + 1) 0 : ℚ) : ℝ) + ε') := by
    intro i hi
    have hi' : i < B.etas.length := by rw [← hn]; simpa using hi
    obtain ⟨e1, e2, e3⟩ := m04_edges B hB i hi'
    exact m04_band b hb _ _ e1 e2 e3 ε' hε'0
  have hall := (eventually_all_finset (range n)).2 hband
  obtain ⟨y0, hy0⟩ := eventually_atTop.1 (hall.and (eventually_gt_atTop 1))
  refine ⟨y0, fun y hy => ?_⟩
  obtain ⟨hyb, hy1⟩ := hy0 y hy
  obtain ⟨gt, hgt⟩ : ∃ gt : ℕ → ℝ, gt = fun δ : ℕ => (UU - Real.log δ / Real.log y) * gB b δ * VB b (Real.sqrt (y / δ)) :=
    ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Real.exp Real.eulerMascheroniConstant := ⟨_, rfl⟩
  rw [← hE]
  have hE0 : 0 < E := by rw [hE]; exact Real.exp_pos _
  have hVy0 : 0 ≤ VB b y := m04_VB_nonneg b y
  -- band primes have nonnegative `gt`
  have hgt0 : ∀ i δ, inBand B y i δ → 0 ≤ gt δ := by
    intro i δ hin
    obtain ⟨-, -, -, -, -, hx6, -⟩ := m04_s14 B hB y hy1 i δ hin
    obtain ⟨-, -, e3⟩ := m04_edges B hB i hin.2.1
    have hU : UU = 99 / 103 := rfl
    rw [hgt]
    apply mul_nonneg (mul_nonneg _ (gB_nonneg b δ)) (m04_VB_nonneg b _)
    rw [hU] at e3 ⊢; linarith
  -- pointwise
  have hpt : ∀ δ ∈ Dset y (y ^ UU) mm,
      phiW W1 (wy y) δ * rhoB b δ / δ * E * VB b (Real.sqrt (y / δ)) * (cOf B y δ - 1) ≤
        ∑ i ∈ range n, (if inBand B y i δ then (((B.cs.getD i 1 : ℚ) : ℝ) - 1) * (E * gt δ) else 0) := by
    intro δ _
    by_cases h : ∃ i, inBand B y i δ
    · have hin := Nat.find_spec h
      obtain ⟨-, hcOf, -, -, -, -, hphi⟩ := m04_s14 B hB y hy1 _ δ hin
      have hrho : gB b δ = rhoB b δ / δ := by
        unfold gB rhoB
        by_cases hc : Nat.Coprime δ (bigB b)
        · rw [if_pos ⟨hin.1, hc⟩, if_pos hc]
        · rw [if_neg (fun h' => hc h'.2), if_neg hc]; simp
      have heq : phiW W1 (wy y) δ * rhoB b δ / δ * E * VB b (Real.sqrt (y / δ)) * (cOf B y δ - 1) =
          (((B.cs.getD (Nat.find h) 1 : ℚ) : ℝ) - 1) * (E * gt δ) := by
        rw [hcOf, hphi, hgt]; beta_reduce; rw [hrho]; ring
      rw [heq]
      have hmem : Nat.find h ∈ range n := by rw [mem_range, hn]; exact hin.2.1
      have hsl := Finset.single_le_sum (f := fun i => if inBand B y i δ then (((B.cs.getD i 1 : ℚ) : ℝ) - 1) * (E * gt δ) else 0)
        (fun i _ => by
          split_ifs with hi
          · exact mul_nonneg (by linarith [m04_cge B hB i]) (mul_nonneg hE0.le (hgt0 i δ hi))
          · exact le_refl _) hmem
      simp only [if_pos hin] at hsl
      exact hsl
    · have hc : cOf B y δ = 1 := by unfold cOf; rw [dif_neg h]
      rw [hc, sub_self, mul_zero]
      push_neg at h
      rw [Finset.sum_eq_zero (fun i _ => if_neg (h i))]
  calc ∑ δ ∈ Dset y (y ^ UU) mm, phiW W1 (wy y) δ * rhoB b δ / δ * E * VB b (Real.sqrt (y / δ)) * (cOf B y δ - 1)
      ≤ ∑ δ ∈ Dset y (y ^ UU) mm, ∑ i ∈ range n, (if inBand B y i δ then (((B.cs.getD i 1 : ℚ) : ℝ) - 1) * (E * gt δ) else 0) :=
        sum_le_sum hpt
    _ = ∑ i ∈ range n, (((B.cs.getD i 1 : ℚ) : ℝ) - 1) * (E * ∑ δ ∈ (Dset y (y ^ UU) mm).filter (inBand B y i), gt δ) := by
        rw [sum_comm]; apply sum_congr rfl; intro i _
        rw [sum_filter, mul_sum, mul_sum]
        apply sum_congr rfl; intro δ _
        split_ifs <;> simp
    _ ≤ ∑ i ∈ range n, (((B.cs.getD i 1 : ℚ) : ℝ) - 1) *
          (E * (2 * VB b y * (bandI ((B.xs.getD i 0 : ℚ) : ℝ) ((B.xs.getD (i + 1) 0 : ℚ) : ℝ) + ε'))) := by
        apply sum_le_sum; intro i hi
        apply mul_le_mul_of_nonneg_left _ (by linarith [m04_cge B hB i])
        apply mul_le_mul_of_nonneg_left _ hE0.le
        have := hyb i hi ((Dset y (y ^ UU) mm).filter (inBand B y i)) (by
          intro p hp
          obtain ⟨-, hin⟩ := mem_filter.1 hp
          exact ⟨hin.1, hin.2.2.1, hin.2.2.2⟩)
        rw [hgt]; exact this
    _ = 2 * E * VB b y * (bandCost B + Csum * ε') := by
        unfold bandCost
        rw [← hn, hCsum, sum_mul, ← sum_add_distrib, mul_sum]
        apply sum_congr rfl; intro i _; ring
    _ ≤ 2 * E * VB b y * (bandCost B + ε) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have : Csum * ε' ≤ ε := by
          rw [hε', mul_div_assoc', div_le_iff₀ (by linarith)]; nlinarith
        linarith

end KappaOmega2
