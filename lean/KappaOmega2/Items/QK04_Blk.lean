import KappaOmega2.Items.QK04_Cut

/-!
# QK04_Blk: one dyadic block of primes `p ∈ [Q, 2Q)` in Proposition CQ_κ

Modulus `p`: `TL¹_κ` if `Q > x^{θ₀}`, else the middle block. Modulus `p²`: the middle block if `Q² ≤ x^{θ₀}`, `TL¹_κ` at
`D = Q², 2Q²` if `x^{θ₀} < Q²` and `2Q² ≤ x^θ`, the cut (`QK04_cut`) if `2Q² > x^θ`.
-/

namespace KappaOmega2

open Finset Real Palprimes

/-- The hypothesis on the block. -/
def QK04_blockHyp (b N i : ℕ) (c₁ : ℝ) (B : Finset ℕ) : Prop :=
  ∀ q ∈ B, q.Prime ∧ ¬ q ∣ bigB b ∧ 2 ^ i ≤ q ∧ q < 2 * 2 ^ i ∧ (q : ℝ) ≤ xx b N ^ c₁

lemma QK04_x1 (b N : ℕ) (hb : 1 ≤ b) : 1 ≤ xx b N := by
  unfold xx; exact one_le_pow₀ (by exact_mod_cast hb)

/-- Modulus `p`. -/
lemma QK04_E1 (b : ℕ) (g : ℕ → ℝ) (hb : 3 ≤ b) (hg : IsDigitWeight b g) (N : ℕ) (θ θ₀ c₁ η η₁ : ℝ)
    (hη : 0 < η) (hη₁a : η₁ ≤ η / 2) (hη₁b : η₁ ≤ 3 / 40) (hθ₀3 : θ₀ < 3 / 20) (hc₁θ : c₁ ≤ θ)
    (hTLN : ∀ D : ℕ, (∃ j : ℕ, D = 2 ^ j) → xx b N ^ θ₀ < (D : ℝ) → (D : ℝ) ≤ xx b N ^ θ → ∀ β : ℝ,
      blockL1K b g N D β ≤ (D : ℝ) * xx b N ^ (-η + η / 2))
    (k i : ℕ) (B : Finset ℕ) (hB : QK04_blockHyp b N i c₁ B) :
    ∑ q ∈ B, ((q : ℝ) ^ 2)⁻¹ * ∑ h ∈ Ico 1 q, ‖fK b g N ((h : ℝ) / q + (k : ℝ) / (bigB b : ℝ))‖ ≤
      (1 + (bigB b : ℝ)) * Real.exp (-(η₁ * ((2 * (N : ℝ) + 1) * Real.log b))) := by
  classical
  have hb1 : 1 ≤ b := by omega
  set L := (2 * (N : ℝ) + 1) * Real.log b with hL
  have hL0 : 0 ≤ L := by rw [hL]; have := Real.log_nonneg (by exact_mod_cast hb1 : (1 : ℝ) ≤ b); positivity
  have hxr : ∀ e : ℝ, xx b N ^ e = Real.exp (L * e) := fun e => LK10_xx_rpow b N hb1 e
  have hx1 := QK04_x1 b N hb1
  set r := bigB b with hr
  have hr1 : 1 ≤ r := QK04_bigB_pos b (by omega)
  set β : ℝ := (k : ℝ) / (r : ℝ) with hβ
  have hE0 : 0 ≤ (1 + (r : ℝ)) * Real.exp (-(η₁ * L)) := by positivity
  rcases B.eq_empty_or_nonempty with hBe | hBne
  · rw [hBe, Finset.sum_empty]; exact hE0
  set Q : ℕ := 2 ^ i with hQ
  have hQ1 : 1 ≤ Q := Nat.one_le_two_pow
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ1
  have hcardB : (#B : ℝ) ≤ Q := by
    have hsub : B ⊆ Ico Q (2 * Q) := by
      intro q hq; obtain ⟨_, _, hq1, hq2, _⟩ := hB q hq; exact mem_Ico.2 ⟨hq1, hq2⟩
    have := Finset.card_le_card hsub
    rw [Nat.card_Ico] at this
    exact_mod_cast (show #B ≤ Q by omega)
  by_cases hQX : xx b N ^ θ₀ < (Q : ℝ)
  · have hQθ : (Q : ℝ) ≤ xx b N ^ θ := by
      obtain ⟨q, hq⟩ := hBne
      obtain ⟨_, _, hq1, _, hqx⟩ := hB q hq
      calc (Q : ℝ) ≤ q := by exact_mod_cast hq1
        _ ≤ xx b N ^ c₁ := hqx
        _ ≤ xx b N ^ θ := Real.rpow_le_rpow_of_exponent_le hx1 hc₁θ
    have hblk := hTLN Q ⟨i, rfl⟩ hQX hQθ β
    have hin := QK04_into_block b g N Q β B id (fun x _ y _ h => h) (by
      intro q hq
      obtain ⟨hqp, hqB, hq1, hq2, _⟩ := hB q hq
      simp only [id, mem_filter, mem_Ico]
      exact ⟨⟨hq1, hq2⟩, QK04_coprime_b b q (QK04_coprime_p b q hqp hqB)⟩)
    simp only [id] at hin
    calc _ ≤ ∑ q ∈ B, ((Q : ℝ) ^ 2)⁻¹ * L1fareyK b g N q β := by
          apply Finset.sum_le_sum; intro q hq
          obtain ⟨hqp, _, hq1, _⟩ := hB q hq
          have hQq : ((q : ℝ) ^ 2)⁻¹ ≤ ((Q : ℝ) ^ 2)⁻¹ :=
            inv_anti₀ (by positivity) (pow_le_pow_left₀ hQpos.le (by exact_mod_cast hq1) 2)
          apply mul_le_mul hQq _ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (by positivity)
          exact Finset.sum_le_sum_of_subset_of_nonneg (QK04_Ico_sub q hqp) (fun _ _ _ => norm_nonneg _)
      _ = ((Q : ℝ) ^ 2)⁻¹ * ∑ q ∈ B, L1fareyK b g N q β := by rw [Finset.mul_sum]
      _ ≤ ((Q : ℝ) ^ 2)⁻¹ * ((Q : ℝ) * xx b N ^ (-η + η / 2)) :=
          mul_le_mul_of_nonneg_left (hin.trans hblk) (by positivity)
      _ ≤ xx b N ^ (-η + η / 2) := by
          rw [← mul_assoc]
          have : ((Q : ℝ) ^ 2)⁻¹ * Q ≤ 1 := by
            rw [sq, mul_inv, mul_assoc, inv_mul_cancel₀ hQpos.ne', mul_one]
            exact inv_le_one_of_one_le₀ (by exact_mod_cast hQ1)
          have h0 : 0 ≤ xx b N ^ (-η + η / 2) := Real.rpow_nonneg (by linarith) _
          nlinarith
      _ ≤ _ := by
          rw [hxr]
          have h1 : Real.exp (L * (-η + η / 2)) ≤ Real.exp (-(η₁ * L)) := by
            apply Real.exp_le_exp.2
            have := mul_le_mul_of_nonneg_left hη₁a hL0
            nlinarith
          have h2 : Real.exp (-(η₁ * L)) ≤ (1 + (r : ℝ)) * Real.exp (-(η₁ * L)) := by
            have hr0 : (0 : ℝ) ≤ r := by positivity
            have : (1 : ℝ) ≤ 1 + r := by linarith
            nlinarith [Real.exp_pos (-(η₁ * L))]
          linarith
  · push Not at hQX
    obtain ⟨hWge, _⟩ := QK04_W_bounds b N hb1
    rw [← hL] at hWge
    have hW0 : (0 : ℝ) < WK b N := lt_of_lt_of_le (Real.exp_pos _) hWge
    have hpt : ∀ q ∈ B, ((q : ℝ) ^ 2)⁻¹ * ∑ h ∈ Ico 1 q, ‖fK b g N ((h : ℝ) / q + β)‖ ≤
        (r : ℝ) / (2 * (WK b N : ℝ)) := by
      intro q hq
      obtain ⟨hqp, hqB, _⟩ := hB q hq
      have hqpos : (0 : ℝ) < q := by exact_mod_cast hqp.pos
      have hs := QK04_sum_le (Ico 1 q) q (fun h hh => by simp only [mem_Ico] at hh; exact mem_range.2 hh.2)
        (fun h => ‖fK b g N ((h : ℝ) / q + β)‖) ((q : ℝ) * r / (2 * (WK b N : ℝ))) (by positivity) (by
          intro h hh
          have hh' := QK04_Ico_sub q hqp hh
          simp only [redRes, mem_filter, mem_range] at hh'
          exact LK10_mid b g hg hb1 N q h k r hqp.two_le
            (QK04_coprime_b b q (QK04_coprime_p b q hqp hqB)) (QK04_coprime_p b q hqp hqB) hr1 hh'.2)
      calc ((q : ℝ) ^ 2)⁻¹ * ∑ h ∈ Ico 1 q, ‖fK b g N ((h : ℝ) / q + β)‖
          ≤ ((q : ℝ) ^ 2)⁻¹ * (q * ((q : ℝ) * r / (2 * (WK b N : ℝ)))) :=
            mul_le_mul_of_nonneg_left hs (by positivity)
        _ = (r : ℝ) / (2 * (WK b N : ℝ)) := by field_simp
    calc _ ≤ ∑ _q ∈ B, (r : ℝ) / (2 * (WK b N : ℝ)) := Finset.sum_le_sum hpt
      _ = #B * ((r : ℝ) / (2 * (WK b N : ℝ))) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ xx b N ^ θ₀ * ((r : ℝ) / (2 * Real.exp (3 / 10 * L))) := by
          apply mul_le_mul (hcardB.trans hQX) _ (by positivity) (by positivity)
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left hWge (by norm_num)
      _ ≤ (1 + (r : ℝ)) * Real.exp (-(η₁ * L)) := by
          rw [hxr]
          have e : Real.exp (L * θ₀) * ((r : ℝ) / (2 * Real.exp (3 / 10 * L))) =
              (r : ℝ) / 2 * Real.exp (L * θ₀ - 3 / 10 * L) := by
            rw [Real.exp_sub]; field_simp
          rw [e]
          have h1 : Real.exp (L * θ₀ - 3 / 10 * L) ≤ Real.exp (-(η₁ * L)) := by
            apply Real.exp_le_exp.2
            have := mul_le_mul_of_nonneg_left (by linarith : θ₀ + η₁ ≤ 3 / 10) hL0
            nlinarith
          have h2 : (0 : ℝ) ≤ r := by positivity
          nlinarith [Real.exp_pos (-(η₁ * L)), Real.exp_pos (L * θ₀ - 3 / 10 * L)]

/-- Modulus `p²`, small `Q` (`Q² ≤ x^{θ₀}`): the middle block. -/
lemma QK04_E2mid (b : ℕ) (g : ℕ → ℝ) (hb : 3 ≤ b) (hg : IsDigitWeight b g) (N : ℕ) (θ₀ c₁ η₁ : ℝ)
    (hη₁b : η₁ ≤ 3 / 40) (hθ₀3 : θ₀ < 3 / 20)
    (k i : ℕ) (B : Finset ℕ) (hB : QK04_blockHyp b N i c₁ B) (hQX : ((2 ^ i : ℕ) : ℝ) ^ 2 ≤ xx b N ^ θ₀) :
    ∑ q ∈ B, ((q : ℝ) ^ 2)⁻¹ * ∑ h ∈ (range (q ^ 2)).filter (fun h => ¬ q ∣ h),
        ‖fK b g N ((h : ℝ) / (q ^ 2 : ℕ) + (k : ℝ) / (bigB b : ℝ))‖ ≤
      2 * (bigB b : ℝ) * Real.exp (-(η₁ * ((2 * (N : ℝ) + 1) * Real.log b))) := by
  classical
  have hb1 : 1 ≤ b := by omega
  set L := (2 * (N : ℝ) + 1) * Real.log b with hL
  have hL0 : 0 ≤ L := by rw [hL]; have := Real.log_nonneg (by exact_mod_cast hb1 : (1 : ℝ) ≤ b); positivity
  have hxr : ∀ e : ℝ, xx b N ^ e = Real.exp (L * e) := fun e => LK10_xx_rpow b N hb1 e
  set r := bigB b with hr
  have hr1 : 1 ≤ r := QK04_bigB_pos b (by omega)
  set β : ℝ := (k : ℝ) / (r : ℝ) with hβ
  set Q : ℕ := 2 ^ i with hQ
  have hQ1 : 1 ≤ Q := Nat.one_le_two_pow
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ1
  have hcardB : (#B : ℝ) ≤ Q := by
    have hsub : B ⊆ Ico Q (2 * Q) := by
      intro q hq; obtain ⟨_, _, hq1, hq2, _⟩ := hB q hq; exact mem_Ico.2 ⟨hq1, hq2⟩
    have := Finset.card_le_card hsub
    rw [Nat.card_Ico] at this
    exact_mod_cast (show #B ≤ Q by omega)
  obtain ⟨hWge, _⟩ := QK04_W_bounds b N hb1
  rw [← hL] at hWge
  have hW0 : (0 : ℝ) < WK b N := lt_of_lt_of_le (Real.exp_pos _) hWge
  have hpt : ∀ q ∈ B, ((q : ℝ) ^ 2)⁻¹ * ∑ h ∈ (range (q ^ 2)).filter (fun h => ¬ q ∣ h),
      ‖fK b g N ((h : ℝ) / (q ^ 2 : ℕ) + β)‖ ≤ 4 * (Q : ℝ) ^ 2 * r / (2 * (WK b N : ℝ)) := by
    intro q hq
    obtain ⟨hqp, hqB, _, hq2, _⟩ := hB q hq
    have hqpos : (0 : ℝ) < q := by exact_mod_cast hqp.pos
    have hq22 : 2 ≤ q ^ 2 := le_trans hqp.two_le (Nat.le_self_pow (by norm_num) q)
    have hs := QK04_sum_le ((range (q ^ 2)).filter (fun h => ¬ q ∣ h)) (q ^ 2) (Finset.filter_subset _ _)
      (fun h => ‖fK b g N ((h : ℝ) / (q ^ 2 : ℕ) + β)‖) (((q ^ 2 : ℕ) : ℝ) * r / (2 * (WK b N : ℝ)))
      (by positivity) (by
        intro h hh
        have hh' := QK04_sq_sub q hqp hh
        simp only [redRes, mem_filter, mem_range] at hh'
        have hc := QK04_coprime_sq b q hqp hqB
        exact LK10_mid b g hg hb1 N (q ^ 2) h k r hq22 (QK04_coprime_b b _ hc) hc hr1 hh'.2)
    have hqQ : (q : ℝ) ≤ 2 * Q := by exact_mod_cast hq2.le
    calc ((q : ℝ) ^ 2)⁻¹ * ∑ h ∈ (range (q ^ 2)).filter (fun h => ¬ q ∣ h),
          ‖fK b g N ((h : ℝ) / (q ^ 2 : ℕ) + β)‖
        ≤ ((q : ℝ) ^ 2)⁻¹ * (((q ^ 2 : ℕ) : ℝ) * (((q ^ 2 : ℕ) : ℝ) * r / (2 * (WK b N : ℝ)))) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ = (q : ℝ) ^ 2 * r / (2 * (WK b N : ℝ)) := by push_cast; field_simp
      _ ≤ 4 * (Q : ℝ) ^ 2 * r / (2 * (WK b N : ℝ)) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          nlinarith
  set δ := Real.log Q with hδ
  have hQe : (Q : ℝ) = Real.exp δ := (Real.exp_log hQpos).symm
  have hδ2 : 2 * δ ≤ L * θ₀ := by
    have h := hQX
    rw [hxr, hQe, ← Real.exp_natCast_mul] at h
    have := Real.exp_le_exp.1 h; push_cast at this; linarith
  calc _ ≤ ∑ _q ∈ B, 4 * (Q : ℝ) ^ 2 * r / (2 * (WK b N : ℝ)) := Finset.sum_le_sum hpt
    _ = #B * (4 * (Q : ℝ) ^ 2 * r / (2 * (WK b N : ℝ))) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Q * (4 * (Q : ℝ) ^ 2 * r / (2 * Real.exp (3 / 10 * L))) := by
        apply mul_le_mul hcardB _ (by positivity) (by positivity)
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left hWge (by norm_num)
    _ = 2 * (r : ℝ) * Real.exp (δ + δ + δ - 3 / 10 * L) := by
        rw [hQe]; simp only [Real.exp_add, Real.exp_sub]; field_simp; ring
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.exp_le_exp.2
        have := mul_le_mul_of_nonneg_left (by linarith : 3 / 2 * θ₀ + η₁ ≤ 3 / 10) hL0
        nlinarith

/-- Modulus `p²`, middle `Q` (`x^{θ₀} < Q²`, `2Q² ≤ x^θ`): `TL¹_κ` at `D = Q²` and `D = 2Q²`. -/
lemma QK04_E2tl (b : ℕ) (g : ℕ → ℝ) (hb : 3 ≤ b) (N : ℕ) (θ θ₀ c₁ η η₁ : ℝ)
    (hη : 0 < η) (hη₁a : η₁ ≤ η / 2)
    (hTLN : ∀ D : ℕ, (∃ j : ℕ, D = 2 ^ j) → xx b N ^ θ₀ < (D : ℝ) → (D : ℝ) ≤ xx b N ^ θ → ∀ β : ℝ,
      blockL1K b g N D β ≤ (D : ℝ) * xx b N ^ (-η + η / 2))
    (k i : ℕ) (B : Finset ℕ) (hB : QK04_blockHyp b N i c₁ B)
    (hQX : xx b N ^ θ₀ < ((2 ^ i : ℕ) : ℝ) ^ 2) (hQθ : 2 * ((2 ^ i : ℕ) : ℝ) ^ 2 ≤ xx b N ^ θ) :
    ∑ q ∈ B, ((q : ℝ) ^ 2)⁻¹ * ∑ h ∈ (range (q ^ 2)).filter (fun h => ¬ q ∣ h),
        ‖fK b g N ((h : ℝ) / (q ^ 2 : ℕ) + (k : ℝ) / (bigB b : ℝ))‖ ≤
      3 * Real.exp (-(η₁ * ((2 * (N : ℝ) + 1) * Real.log b))) := by
  classical
  have hb1 : 1 ≤ b := by omega
  set L := (2 * (N : ℝ) + 1) * Real.log b with hL
  have hL0 : 0 ≤ L := by rw [hL]; have := Real.log_nonneg (by exact_mod_cast hb1 : (1 : ℝ) ≤ b); positivity
  have hxr : ∀ e : ℝ, xx b N ^ e = Real.exp (L * e) := fun e => LK10_xx_rpow b N hb1 e
  set β : ℝ := (k : ℝ) / (bigB b : ℝ) with hβ
  set Q : ℕ := 2 ^ i with hQ
  have hQ1 : 1 ≤ Q := Nat.one_le_two_pow
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ1
  set D₁ : ℕ := 2 ^ (2 * i) with hD₁
  set D₂ : ℕ := 2 ^ (2 * i + 1) with hD₂
  have hD₁Q : D₁ = Q ^ 2 := by rw [hD₁, hQ, ← pow_mul, mul_comm]
  have hD₂Q : D₂ = 2 * Q ^ 2 := by rw [hD₂, pow_succ, ← hD₁, hD₁Q, mul_comm]
  have hD₁R : (D₁ : ℝ) = (Q : ℝ) ^ 2 := by rw [hD₁Q]; push_cast; ring
  have hD₂R : (D₂ : ℝ) = 2 * (Q : ℝ) ^ 2 := by rw [hD₂Q]; push_cast; ring
  have hx0 : 0 ≤ xx b N ^ θ₀ := Real.rpow_nonneg (by unfold xx; positivity) _
  have hb₁ := hTLN D₁ ⟨2 * i, rfl⟩ (by rw [hD₁R]; exact hQX) (by rw [hD₁R]; nlinarith) β
  have hb₂ := hTLN D₂ ⟨2 * i + 1, rfl⟩ (by rw [hD₂R]; nlinarith) (by rw [hD₂R]; exact hQθ) β
  set F : ℕ → ℝ := fun q => L1fareyK b g N (q ^ 2) β with hF
  have hinj : ∀ x ∈ B, ∀ y ∈ B, x ^ 2 = y ^ 2 → x = y := fun x _ y _ hxy =>
    Nat.pow_left_injective (by norm_num : 2 ≠ 0) hxy
  have hin₁ := QK04_into_block b g N D₁ β (B.filter (fun q => q ^ 2 < 2 * Q ^ 2)) (fun q => q ^ 2)
    (fun x hx y hy h => hinj x (Finset.mem_filter.1 hx).1 y (Finset.mem_filter.1 hy).1 h) (by
      intro q hq
      obtain ⟨hq, hqlt⟩ := Finset.mem_filter.1 hq
      obtain ⟨hqp, hqB, hq1, _⟩ := hB q hq
      simp only [mem_filter, mem_Ico]
      refine ⟨⟨?_, ?_⟩, QK04_coprime_b b _ (QK04_coprime_sq b q hqp hqB)⟩
      · rw [hD₁Q]; exact Nat.pow_le_pow_left hq1 2
      · rw [hD₁Q]; exact hqlt)
  have hin₂ := QK04_into_block b g N D₂ β (B.filter (fun q => ¬ q ^ 2 < 2 * Q ^ 2)) (fun q => q ^ 2)
    (fun x hx y hy h => hinj x (Finset.mem_filter.1 hx).1 y (Finset.mem_filter.1 hy).1 h) (by
      intro q hq
      obtain ⟨hq, hqlt⟩ := Finset.mem_filter.1 hq
      obtain ⟨hqp, hqB, _, hq2, _⟩ := hB q hq
      simp only [mem_filter, mem_Ico]
      refine ⟨⟨?_, ?_⟩, QK04_coprime_b b _ (QK04_coprime_sq b q hqp hqB)⟩
      · rw [hD₂Q]; omega
      · rw [hD₂Q]
        calc q ^ 2 < (2 * Q) ^ 2 := Nat.pow_lt_pow_left hq2 (by norm_num)
          _ = 2 * (2 * Q ^ 2) := by ring)
  have hsumF : ∑ q ∈ B, F q ≤ 3 * (Q : ℝ) ^ 2 * xx b N ^ (-η + η / 2) := by
    rw [← Finset.sum_filter_add_sum_filter_not B (fun q => q ^ 2 < 2 * Q ^ 2)]
    calc _ ≤ blockL1K b g N D₁ β + blockL1K b g N D₂ β := add_le_add hin₁ hin₂
      _ ≤ (D₁ : ℝ) * xx b N ^ (-η + η / 2) + (D₂ : ℝ) * xx b N ^ (-η + η / 2) := add_le_add hb₁ hb₂
      _ = _ := by rw [hD₁R, hD₂R]; ring
  calc _ ≤ ∑ q ∈ B, ((Q : ℝ) ^ 2)⁻¹ * F q := by
        apply Finset.sum_le_sum; intro q hq
        obtain ⟨hqp, _, hq1, _⟩ := hB q hq
        have hQq : ((q : ℝ) ^ 2)⁻¹ ≤ ((Q : ℝ) ^ 2)⁻¹ :=
          inv_anti₀ (by positivity) (pow_le_pow_left₀ hQpos.le (by exact_mod_cast hq1) 2)
        apply mul_le_mul hQq _ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (by positivity)
        exact Finset.sum_le_sum_of_subset_of_nonneg (QK04_sq_sub q hqp) (fun _ _ _ => norm_nonneg _)
    _ = ((Q : ℝ) ^ 2)⁻¹ * ∑ q ∈ B, F q := by rw [Finset.mul_sum]
    _ ≤ ((Q : ℝ) ^ 2)⁻¹ * (3 * (Q : ℝ) ^ 2 * xx b N ^ (-η + η / 2)) :=
        mul_le_mul_of_nonneg_left hsumF (by positivity)
    _ = 3 * xx b N ^ (-η + η / 2) := by field_simp
    _ ≤ _ := by
        rw [hxr]
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Real.exp_le_exp.2
        have := mul_le_mul_of_nonneg_left hη₁a hL0
        nlinarith

end KappaOmega2
