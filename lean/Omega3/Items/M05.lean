import Omega3.Statements
import Omega3.Items.M05_Core
import Palprimes.E1.Mertens

namespace Omega3

open Finset Palprimes Palprimes.Greaves Palprimes.MT Omega3.M05c
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius

set_option linter.style.longLine false

lemma m05_Wf_nonneg (t : ℝ) : 0 ≤ Wf t := by
  unfold Wf
  split_ifs with h1 h2 h3
  · exact le_rfl
  · apply le_min
    · have : 0 ≤ t ^ 2 := sq_nonneg t
      unfold kSq; linarith
    · unfold mm at *; linarith
  · unfold mm at *; unfold UU at *; linarith
  · unfold W1; norm_num

lemma m05_phi_le (y : ℝ) (δ : ℕ) : phiW W1 (wy y) δ ≤ W1 := by
  unfold phiW
  have : 0 ≤ ∑ p ∈ δ.primeFactors, wy y p := Finset.sum_nonneg (fun p _ => m05_Wf_nonneg _)
  linarith

lemma m05_rho_div (b : ℕ) (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) :
    rhoB b (∏ p ∈ D, p) / ((∏ p ∈ D, p : ℕ) : ℝ) = ∏ p ∈ D, gB b p := by
  classical
  unfold rhoB gB
  by_cases h : Nat.Coprime (∏ p ∈ D, p) (bigB b)
  · rw [if_pos h]
    have h' : ∀ p ∈ D, Nat.Coprime p (bigB b) := fun p hp =>
      Nat.Coprime.coprime_dvd_left (dvd_prod_of_mem _ hp) h
    rw [prod_congr rfl (fun p hp => if_pos ⟨hD p hp, h' p hp⟩), Nat.cast_prod, one_div, ← prod_inv_distrib]
    simp [one_div]
  · rw [if_neg h, zero_div]
    rw [Nat.coprime_prod_left_iff] at h
    push_neg at h
    obtain ⟨p, hp, hpc⟩ := h
    symm
    apply prod_eq_zero hp
    rw [if_neg]
    rintro ⟨_, h2⟩
    exact hpc h2

set_option maxRecDepth 20000 in
theorem itemM05 : ItemM05 := by
  classical
  intro b hb
  obtain ⟨x0, hx0, hV⟩ := E1.VB_log_bounds b hb (η := 1 / 2) (by norm_num)
  have hκ := kappaB_pos b
  obtain ⟨c0, hc0⟩ : ∃ c0 : ℝ, c0 = (1 / 2 : ℝ) * (2 / 3 : ℝ) ^ 84 := ⟨_, rfl⟩
  have hc0pos : 0 < c0 := by rw [hc0]; positivity
  have hc0le : c0 ≤ 1 := by
    rw [hc0]
    have : (2 / 3 : ℝ) ^ 84 ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = c0 / 2 := ⟨_, rfl⟩
  have hapos : 0 < a := by rw [ha]; positivity
  have ha1 : a ≤ 1 := by rw [ha]; linarith
  have haU : a ≤ UU := by unfold UU; rw [ha]; linarith [hc0le]
  set X : ℝ := max x0 2 with hX
  refine ⟨W1 * Real.exp Real.eulerMascheroniConstant * (3 / a) * (3 * UU / a), X ^ (1 / a), fun y hy => ?_⟩
  have hy1 : 1 < y := lt_of_lt_of_le (Real.one_lt_rpow (by linarith [le_max_right x0 2]) (by positivity)) hy
  have hya : X ≤ y ^ a := by
    calc X = (X ^ (1 / a)) ^ a := by
          rw [← Real.rpow_mul (by linarith [le_max_right x0 2])]; field_simp; simp
      _ ≤ y ^ a := Real.rpow_le_rpow (Real.rpow_nonneg (by linarith [le_max_right x0 2]) _) hy hapos.le
  have hLy : 0 < Real.log y := Real.log_pos hy1
  have hx0a : x0 ≤ y ^ a := le_trans (le_max_left _ _) hya
  have hyle : y ^ a ≤ y := by
    calc y ^ a ≤ y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hy1.le ha1
      _ = y := Real.rpow_one y
  have hVy := (hV y (le_trans hx0a hyle)).1
  have hlogya : Real.log (y ^ a) = a * Real.log y := Real.log_rpow (by linarith) _
  have hlogyU : Real.log (y ^ UU) = UU * Real.log y := Real.log_rpow (by linarith) _
  have hya_U : y ^ a ≤ y ^ UU := Real.rpow_le_rpow_of_exponent_le hy1.le haU
  have hx0U : x0 ≤ y ^ UU := le_trans hx0a hya_U
  -- Step 1
  have hstep1 : ∀ δ ∈ Dset y (y ^ UU) mm, MT.VB b (Real.sqrt (y / δ)) ≤ (3 / a) * MT.VB b y := by
    intro δ hδ
    have hyd : y ^ c0 ≤ y / δ := by rw [hc0]; exact c_ydelta y hy1 δ hδ
    have hw : y ^ a ≤ Real.sqrt (y / δ) := by
      rw [ha]
      have : y ^ (c0 / 2) = Real.sqrt (y ^ c0) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by linarith)]; ring_nf
      rw [this]
      exact Real.sqrt_le_sqrt hyd
    have hw0 : x0 ≤ Real.sqrt (y / δ) := le_trans hx0a hw
    have hVw := (hV _ hw0).2
    have hlogw : a * Real.log y ≤ Real.log (Real.sqrt (y / δ)) := by
      rw [← hlogya]; exact Real.log_le_log (Real.rpow_pos_of_pos (by linarith) _) hw
    have hlogwpos : 0 < Real.log (Real.sqrt (y / δ)) := by nlinarith
    have hVw' : MT.VB b (Real.sqrt (y / δ)) ≤ (3 / 2) * kappaB b / (a * Real.log y) := by
      have : MT.VB b (Real.sqrt (y / δ)) * (a * Real.log y) ≤ (3 / 2) * kappaB b := by
        have h1 : 0 ≤ MT.VB b (Real.sqrt (y / δ)) := (E1.VB_pos' b _).le
        calc _ ≤ MT.VB b (Real.sqrt (y / δ)) * Real.log (Real.sqrt (y / δ)) := mul_le_mul_of_nonneg_left hlogw h1
          _ ≤ (1 + 1 / 2) * kappaB b := hVw
          _ = _ := by ring
      rw [le_div_iff₀ (by positivity)]; exact this
    have hVy' : kappaB b / 2 / Real.log y ≤ MT.VB b y := by
      rw [div_le_iff₀ hLy]; linarith
    calc MT.VB b (Real.sqrt (y / δ)) ≤ (3 / 2) * kappaB b / (a * Real.log y) := hVw'
      _ = (3 / a) * (kappaB b / 2 / Real.log y) := by field_simp
      _ ≤ (3 / a) * MT.VB b y := mul_le_mul_of_nonneg_left hVy' (by positivity)
  -- Step 2
  have hrho0 : ∀ δ : ℕ, 0 ≤ rhoB b δ / δ := fun δ => by
    unfold rhoB; split_ifs <;> positivity
  have hstep2 : ∑ δ ∈ Dset y (y ^ UU) mm, rhoB b δ / δ ≤ 3 * UU / a := by
    set Q := E1.primesIco (y ^ a) (y ^ UU) with hQ
    have hsub : ∀ δ ∈ Dset y (y ^ UU) mm, δ.primeFactors ⊆ Q := by
      intro δ hδ p hp
      obtain ⟨hδ0, hδ1, hsq, hdvd, hpz, hyle'⟩ := c_Dfacts y δ hδ
      have hyd : y ^ c0 ≤ y / δ := by rw [hc0]; exact c_ydelta y hy1 δ hδ
      have hpp := Nat.prime_of_mem_primeFactors hp
      rw [E1.mem_primesIco]
      refine ⟨hpp, ?_, hpz p hp⟩
      have hmp : δ.minFac ≤ p := Nat.minFac_le_of_dvd hpp.two_le (Nat.dvd_of_mem_primeFactors hp)
      have hmp' : (δ.minFac : ℝ) ≤ p := by exact_mod_cast hmp
      have hδpos : (0 : ℝ) < δ := by exact_mod_cast Nat.pos_of_ne_zero hδ0
      have h1 : y ^ c0 ≤ (δ.minFac : ℝ) ^ 2 := by
        have : y / δ ≤ (δ.minFac : ℝ) ^ 2 := by rw [div_le_iff₀ hδpos]; linarith
        linarith
      have h2 : (y ^ a) ^ 2 = y ^ c0 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith), ha]; norm_num
      have h3 : y ^ a ≤ (δ.minFac : ℝ) := by
        by_contra hlt; push_neg at hlt
        have : 0 ≤ (δ.minFac : ℝ) := Nat.cast_nonneg _
        nlinarith
      linarith
    have hinj : ∀ δ ∈ Dset y (y ^ UU) mm, ∀ δ' ∈ Dset y (y ^ UU) mm, δ.primeFactors = δ'.primeFactors → δ = δ' := by
      intro δ hδ δ' hδ' he
      obtain ⟨_, _, hsq, _⟩ := c_Dfacts y δ hδ
      obtain ⟨_, _, hsq', _⟩ := c_Dfacts y δ' hδ'
      rw [← Nat.prod_primeFactors_of_squarefree hsq, ← Nat.prod_primeFactors_of_squarefree hsq', he]
    have hr : ∀ δ ∈ Dset y (y ^ UU) mm, rhoB b δ / δ = ∏ p ∈ δ.primeFactors, gB b p := by
      intro δ hδ
      obtain ⟨_, _, hsq, _⟩ := c_Dfacts y δ hδ
      have := m05_rho_div b δ.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
      rwa [Nat.prod_primeFactors_of_squarefree hsq] at this
    have hQprod : ∑ δ ∈ Dset y (y ^ UU) mm, rhoB b δ / δ ≤ ∏ p ∈ Q, (1 + gB b p) := by
      rw [Finset.sum_congr rfl hr, Finset.prod_one_add]
      calc ∑ δ ∈ Dset y (y ^ UU) mm, ∏ p ∈ δ.primeFactors, gB b p
          = ∑ S ∈ (Dset y (y ^ UU) mm).image (fun δ => δ.primeFactors), ∏ p ∈ S, gB b p :=
            (Finset.sum_image (f := fun S => ∏ p ∈ S, gB b p) (g := fun δ : ℕ => δ.primeFactors) hinj).symm
        _ ≤ ∑ S ∈ Q.powerset, ∏ p ∈ S, gB b p := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro S hS
              obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hS
              exact Finset.mem_powerset.2 (hsub δ hδ)
            · intro S _ _; exact Finset.prod_nonneg (fun p _ => gB_nonneg b p)
    have hsplit := E1.VB_split' b (y ^ a) (y ^ UU) hya_U
    have hVa := E1.VB_pos' b (y ^ a)
    have hVU := E1.VB_pos' b (y ^ UU)
    have hprodpos : 0 < ∏ p ∈ Q, (1 - gB b p) :=
      Finset.prod_pos (fun p _ => by linarith [E1.gB_le_half' b p])
    have hle1 : (∏ p ∈ Q, (1 + gB b p)) * ∏ p ∈ Q, (1 - gB b p) ≤ 1 := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_le_one₀
      · intro p _
        have := gB_nonneg b p; have := E1.gB_le_half' b p
        nlinarith
      · intro p _
        have := gB_nonneg b p
        nlinarith
    have hratio : ∏ p ∈ Q, (1 + gB b p) ≤ MT.VB b (y ^ a) / MT.VB b (y ^ UU) := by
      rw [le_div_iff₀ hVU, hsplit]
      nlinarith [hVa]
    have hVa' : MT.VB b (y ^ a) * (a * Real.log y) ≤ (3 / 2) * kappaB b := by
      have := (hV _ hx0a).2
      rw [hlogya] at this; linarith
    have hVU' : kappaB b / 2 ≤ MT.VB b (y ^ UU) * (UU * Real.log y) := by
      have := (hV _ hx0U).1
      rw [hlogyU] at this; linarith
    have hUpos : (0 : ℝ) < UU := by unfold UU; norm_num
    refine hQprod.trans (hratio.trans ?_)
    rw [div_le_iff₀ hVU]
    have hLy2 : 0 < UU * Real.log y := by positivity
    have hLy3 : 0 < a * Real.log y := by positivity
    -- V(y^a) ≤ 3/2 κ /(a L), V(y^U) ≥ κ/2/(U L)
    have e1 : MT.VB b (y ^ a) ≤ (3 / 2) * kappaB b / (a * Real.log y) := by
      rw [le_div_iff₀ hLy3]; exact hVa'
    have e2 : kappaB b / 2 / (UU * Real.log y) ≤ MT.VB b (y ^ UU) := by
      rw [div_le_iff₀ hLy2]; exact hVU'
    calc MT.VB b (y ^ a) ≤ (3 / 2) * kappaB b / (a * Real.log y) := e1
      _ = (3 * UU / a) * (kappaB b / 2 / (UU * Real.log y)) := by field_simp
      _ ≤ (3 * UU / a) * MT.VB b (y ^ UU) := mul_le_mul_of_nonneg_left e2 (by positivity)
  -- Step 3
  have hVy0 : 0 ≤ MT.VB b y := (E1.VB_pos' b y).le
  have hγ : 0 < Real.exp Real.eulerMascheroniConstant := Real.exp_pos _
  have hW1 : 0 ≤ W1 := by unfold W1; norm_num
  unfold M23
  calc ∑ δ ∈ Dset y (y ^ UU) mm, phiW W1 (wy y) δ * rhoB b δ / δ * Real.exp Real.eulerMascheroniConstant *
        MT.VB b (Real.sqrt (y / δ))
      ≤ ∑ δ ∈ Dset y (y ^ UU) mm, W1 * (rhoB b δ / δ) * Real.exp Real.eulerMascheroniConstant *
        ((3 / a) * MT.VB b y) := by
        apply Finset.sum_le_sum
        intro δ hδ
        have h0 := hrho0 δ
        have e : phiW W1 (wy y) δ * rhoB b δ / δ = phiW W1 (wy y) δ * (rhoB b δ / δ) := by ring
        rw [e]
        have hV0 : 0 ≤ MT.VB b (Real.sqrt (y / δ)) := (E1.VB_pos' b _).le
        apply mul_le_mul _ (hstep1 δ hδ) hV0 (by positivity)
        apply mul_le_mul_of_nonneg_right _ hγ.le
        exact mul_le_mul_of_nonneg_right (m05_phi_le y δ) h0
    _ = W1 * Real.exp Real.eulerMascheroniConstant * ((3 / a) * MT.VB b y) *
          ∑ δ ∈ Dset y (y ^ UU) mm, rhoB b δ / δ := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro δ _; ring
    _ ≤ W1 * Real.exp Real.eulerMascheroniConstant * ((3 / a) * MT.VB b y) * (3 * UU / a) :=
        mul_le_mul_of_nonneg_left hstep2 (by positivity)
    _ = _ := by ring

end Omega3
