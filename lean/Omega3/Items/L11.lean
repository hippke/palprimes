import Omega3.Statements

/-!
# L11: Lemma SS (self-similarity of TL¹), r238 §2.4. Sub-blueprint: `L11_PLAN.md`.
-/

namespace Omega3

open Finset Real Palprimes

lemma L11_ee_add (s t : ℝ) : ee (s + t) = ee s * ee t := by
  unfold ee; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma L11_ee_nat (n : ℕ) : ee (n : ℝ) = 1 := by
  unfold ee
  have : (2 * π * Complex.I * ((n : ℝ) : ℂ)) = (n : ℂ) * (2 * π * Complex.I) := by push_cast; ring
  rw [this, Complex.exp_nat_mul_two_pi_mul_I]

lemma L11_norm_ee (t : ℝ) : ‖ee t‖ = 1 := by
  unfold ee
  have : (2 * π * Complex.I * (t : ℂ)) = ((2 * π * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

lemma L11_Gg_norm_le (b : ℕ) (g : ℕ → ℝ) (hg : IsDigitWeight b g) (t : ℝ) : ‖Gg b g t‖ ≤ 1 := by
  unfold Gg
  calc ‖∑ a ∈ range b, (g a : ℂ) * ee (a * t)‖ ≤ ∑ a ∈ range b, ‖(g a : ℂ) * ee (a * t)‖ :=
        norm_sum_le _ _
    _ = ∑ a ∈ range b, g a := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [norm_mul, L11_norm_ee, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hg.1 a)]
    _ = 1 := hg.2

lemma L11_Gg_add_nat (b : ℕ) (g : ℕ → ℝ) (t : ℝ) (n : ℕ) : Gg b g (t + n) = Gg b g t := by
  unfold Gg
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have : (a : ℝ) * (t + n) = a * t + ((a * n : ℕ) : ℝ) := by push_cast; ring
  rw [this, L11_ee_add, L11_ee_nat, mul_one]

lemma L11_fg_add_nat (b : ℕ) (g : ℕ → ℝ) (N : ℕ) (t : ℝ) (n : ℕ) : fg b g N (t + n) = fg b g N t := by
  unfold fg
  refine Finset.prod_congr rfl (fun k _ => ?_)
  have : (cK b N k : ℝ) * (t + n) = cK b N k * t + ((cK b N k * n : ℕ) : ℝ) := by push_cast; ring
  rw [this, L11_Gg_add_nat]

lemma L11_cK_shift (b N' m j : ℕ) (hj : j ≤ N') : cK b (N' + m) (m + j) = b ^ m * cK b N' j := by
  unfold cK
  by_cases h : j < N'
  · rw [if_pos (show m + j < N' + m by omega), if_pos h]
    have he : 2 * (N' + m) - (m + j) = m + (2 * N' - j) := by omega
    rw [he, pow_add, pow_add, mul_add]
  · rw [if_neg (by omega), if_neg h, ← pow_add, add_comm]

lemma L11_fg_shift (b : ℕ) (g : ℕ → ℝ) (hg : IsDigitWeight b g) (N' m : ℕ) (α : ℝ) :
    ‖fg b g (N' + m) α‖ ≤ ‖fg b g N' ((b : ℝ) ^ m * α)‖ := by
  unfold fg
  have hr : N' + m + 1 = m + (N' + 1) := by omega
  rw [hr, Finset.prod_range_add, norm_mul]
  have h1 : ‖∏ x ∈ range m, Gg b g ((cK b (N' + m) x : ℝ) * α)‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => L11_Gg_norm_le b g hg _)
  have h2 : ∏ x ∈ range (N' + 1), Gg b g ((cK b (N' + m) (m + x) : ℝ) * α) =
      ∏ k ∈ range (N' + 1), Gg b g ((cK b N' k : ℝ) * ((b : ℝ) ^ m * α)) := by
    refine Finset.prod_congr rfl (fun x hx => ?_)
    rw [L11_cK_shift b N' m x (by simp at hx; omega)]
    push_cast; ring_nf
  rw [h2]
  calc _ ≤ 1 * ‖∏ k ∈ range (N' + 1), Gg b g ((cK b N' k : ℝ) * ((b : ℝ) ^ m * α))‖ :=
        mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = _ := one_mul _

/-- Multiplication by a unit permutes the reduced residues. -/
lemma L11_redRes_perm (d u : ℕ) (hd : 0 < d) (hu : Nat.Coprime u d) (F : ℕ → ℝ) :
    ∑ h ∈ redRes d, F (u * h % d) = ∑ h ∈ redRes d, F h := by
  have hinj : Set.InjOn (fun h => u * h % d) (redRes d) := by
    intro h1 hh1 h2 hh2 he
    simp only [redRes, Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hh1 hh2
    have hm : u * h1 ≡ u * h2 [MOD d] := he
    have := Nat.ModEq.cancel_left_of_coprime (by rw [Nat.gcd_comm]; exact hu) hm
    unfold Nat.ModEq at this
    rwa [Nat.mod_eq_of_lt hh1.1, Nat.mod_eq_of_lt hh2.1] at this
  have hsub : (redRes d).image (fun h => u * h % d) ⊆ redRes d := by
    intro y hy
    simp only [Finset.mem_image, redRes, Finset.mem_filter, Finset.mem_range] at hy ⊢
    obtain ⟨h, ⟨_, hh⟩, rfl⟩ := hy
    refine ⟨Nat.mod_lt _ hd, ?_⟩
    unfold Nat.Coprime
    rw [← Nat.gcd_rec, Nat.gcd_comm]
    exact Nat.coprime_mul_iff_left.mpr ⟨hu, hh⟩
  have heq : (redRes d).image (fun h => u * h % d) = redRes d :=
    Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_image_of_injOn hinj])
  conv_rhs => rw [← heq]
  rw [Finset.sum_image hinj]

lemma L11_L1farey_shift (b : ℕ) (g : ℕ → ℝ) (hg : IsDigitWeight b g) (N' m d : ℕ) (hd : 0 < d)
    (hdb : Nat.Coprime d b) (β : ℝ) :
    L1farey b g (N' + m) d β ≤ L1farey b g N' d ((b : ℝ) ^ m * β) := by
  unfold L1farey
  calc ∑ h ∈ redRes d, ‖fg b g (N' + m) ((h : ℝ) / d + β)‖
      ≤ ∑ h ∈ redRes d, ‖fg b g N' ((b : ℝ) ^ m * ((h : ℝ) / d + β))‖ :=
        Finset.sum_le_sum (fun h _ => L11_fg_shift b g hg N' m _)
    _ = ∑ h ∈ redRes d, ‖fg b g N' (((b ^ m * h % d : ℕ) : ℝ) / d + (b : ℝ) ^ m * β)‖ := by
        refine Finset.sum_congr rfl (fun h _ => ?_)
        have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
        have hsplit : (b : ℝ) ^ m * ((h : ℝ) / d + β) =
            (((b ^ m * h % d : ℕ) : ℝ) / d + (b : ℝ) ^ m * β) + ((b ^ m * h / d : ℕ) : ℝ) := by
          have hdm := Nat.mod_add_div (b ^ m * h) d
          have hdmR : ((b ^ m * h % d : ℕ) : ℝ) + d * ((b ^ m * h / d : ℕ) : ℝ) = (b : ℝ) ^ m * h := by
            exact_mod_cast hdm
          field_simp
          linear_combination -hdmR
        rw [hsplit, L11_fg_add_nat]
    _ = ∑ h ∈ redRes d, ‖fg b g N' ((h : ℝ) / d + (b : ℝ) ^ m * β)‖ :=
        L11_redRes_perm d (b ^ m) hd (Nat.Coprime.pow_left m hdb.symm)
          (fun h => ‖fg b g N' ((h : ℝ) / d + (b : ℝ) ^ m * β)‖)

lemma L11_block_shift (b : ℕ) (g : ℕ → ℝ) (hg : IsDigitWeight b g) (N' m D : ℕ) (_hD : 1 ≤ D) (β : ℝ) :
    blockL1 b g (N' + m) D β ≤ blockL1 b g N' D ((b : ℝ) ^ m * β) := by
  unfold blockL1
  refine Finset.sum_le_sum (fun d hd => ?_)
  simp only [Finset.mem_filter, Finset.mem_Ico] at hd
  exact L11_L1farey_shift b g hg N' m d (by omega) hd.2 β

lemma L11_xx_rpow (b n : ℕ) (s : ℝ) : xx b n ^ s = (b : ℝ) ^ (((2 * n + 1 : ℕ) : ℝ) * s) := by
  unfold xx
  rw [Real.rpow_mul (by positivity), Real.rpow_natCast]

lemma L11_xx_mono (b : ℕ) (hb : 2 ≤ b) (s : ℝ) (hs : 0 ≤ s) {n n' : ℕ} (h : n ≤ n') :
    xx b n ^ s ≤ xx b n' ^ s := by
  apply Real.rpow_le_rpow (by unfold xx; positivity) _ hs
  unfold xx
  exact pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ b)) (by omega)

theorem itemL11 : ItemL11 := by
  intro b g θ κ θ₀ hb hg hθ₀ hθθ₀ hκ hTL ε hε
  have hθ : 0 < θ := lt_trans hθ₀ hθθ₀
  set ε' : ℝ := min (κ / 2) (θ * ε) with hε'
  have hε'pos : 0 < ε' := lt_min (by linarith) (by positivity)
  obtain ⟨N₀, hN₀⟩ := hTL ε' hε'pos
  set c : ℝ := (θ + θ₀) / (2 * (θ - θ₀)) with hc
  set N₁ : ℕ := max N₀ ⌈c⌉₊ with hN₁
  refine ⟨xx b N₁ ^ θ + 1, ?_⟩
  intro N D hdy hD₀ hDx β
  have hD1 : 1 ≤ D := by obtain ⟨j, rfl⟩ := hdy; exact Nat.one_le_two_pow
  have hD1R : (1 : ℝ) ≤ D := by exact_mod_cast hD1
  let P : ℕ → Prop := fun n => N₁ ≤ n ∧ (D : ℝ) ≤ xx b n ^ θ
  have hPN : P N := by
    refine ⟨?_, hDx⟩
    by_contra hlt
    push Not at hlt
    have := L11_xx_mono b hb θ hθ.le hlt.le
    linarith
  have hex : ∃ n, P n := ⟨N, hPN⟩
  classical
  set N' := Nat.find hex with hN'
  have hN'P : P N' := Nat.find_spec hex
  have hN'N : N' ≤ N := Nat.find_min' hex hPN
  have hN'gt : N₁ < N' := by
    rcases lt_or_eq_of_le hN'P.1 with h | h
    · exact h
    · exfalso; have := hN'P.2; rw [← h] at this; linarith
  have hnotP : ¬ P (N' - 1) := Nat.find_min hex (by omega)
  have hlow : xx b (N' - 1) ^ θ < (D : ℝ) := by
    by_contra h; push Not at h; exact hnotP ⟨by omega, h⟩
  -- window condition
  have hcN : c ≤ (N' : ℝ) := by
    have h1 : c ≤ (⌈c⌉₊ : ℝ) := Nat.le_ceil c
    have h2 : (⌈c⌉₊ : ℝ) ≤ N₁ := by exact_mod_cast le_max_right _ _
    have h3 : (N₁ : ℝ) ≤ N' := by exact_mod_cast hN'gt.le
    linarith
  have hexp : ((2 * N' + 1 : ℕ) : ℝ) * θ₀ ≤ ((2 * (N' - 1) + 1 : ℕ) : ℝ) * θ := by
    have hN'1 : 1 ≤ N' := by omega
    have e1 : ((2 * (N' - 1) + 1 : ℕ) : ℝ) = 2 * (N' : ℝ) - 1 := by
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hN'1]; push_cast; ring
    rw [e1]; push_cast
    have hpos : 0 < 2 * (θ - θ₀) := by linarith
    have : (θ + θ₀) ≤ (N' : ℝ) * (2 * (θ - θ₀)) := by
      rw [hc, div_le_iff₀ hpos] at hcN; linarith
    nlinarith
  have hwin : xx b N' ^ θ₀ < (D : ℝ) := by
    calc xx b N' ^ θ₀ ≤ xx b (N' - 1) ^ θ := by
          rw [L11_xx_rpow, L11_xx_rpow]
          exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ b)) hexp
      _ < D := hlow
  have hN'0 : N₀ ≤ N' := le_trans (le_max_left _ _) hN'P.1
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hN'N
  have hTLb := hN₀ N' hN'0 D hdy hwin hN'P.2 ((b : ℝ) ^ m * β)
  have hshift := L11_block_shift b g hg N' m D hD1 β
  rw [← hm] at hshift
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hxpos : 0 < xx b N' := by unfold xx; positivity
  have hfin : xx b N' ^ (-κ + ε') ≤ (D : ℝ) ^ (-κ / θ + ε) := by
    have hneg : (-κ + ε') / θ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith [min_le_left (κ / 2) (θ * ε)]) hθ.le
    calc xx b N' ^ (-κ + ε') = (xx b N' ^ θ) ^ ((-κ + ε') / θ) := by
          rw [← Real.rpow_mul hxpos.le]; congr 1; field_simp
      _ ≤ (D : ℝ) ^ ((-κ + ε') / θ) := Real.rpow_le_rpow_of_nonpos (by linarith) hN'P.2 hneg
      _ ≤ (D : ℝ) ^ (-κ / θ + ε) := by
          apply Real.rpow_le_rpow_of_exponent_le hD1R
          have : ε' ≤ θ * ε := min_le_right _ _
          rw [div_add' _ _ _ hθ.ne', div_le_div_iff_of_pos_right hθ]
          linarith
  calc blockL1 b g N D β ≤ blockL1 b g N' D ((b : ℝ) ^ m * β) := hshift
    _ ≤ (D : ℝ) * xx b N' ^ (-κ + ε') := hTLb
    _ ≤ (D : ℝ) * (D : ℝ) ^ (-κ / θ + ε) :=
        mul_le_mul_of_nonneg_left hfin (by linarith)

end Omega3
