import KappaOmega2.Items.LK10_Aux

/-!
# QK04_Aux: small facts for Proposition CQ_κ
-/

namespace KappaOmega2

open Finset Real Palprimes

/-- Telescoping: `Σ_{a < n ≤ M} n⁻² ≤ 1/a`. -/
lemma QK04_inv_sq (a : ℕ) (ha : 1 ≤ a) (M : ℕ) : ∑ n ∈ Ioc a M, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / a := by
  have key : ∀ M, a ≤ M → ∑ n ∈ Ioc a M, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / a - 1 / M := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base => simp
    | succ M hM ih =>
        rw [Finset.sum_Ioc_succ_top hM]
        have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast le_trans ha hM
        have h2 : (1 : ℝ) / ((M + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / M - 1 / ((M + 1 : ℕ) : ℝ) := by
          push_cast
          rw [div_sub_div _ _ (by linarith) (by linarith), div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        linarith
  rcases le_or_gt a M with h | h
  · have := key M h
    have : (0 : ℝ) ≤ 1 / M := by positivity
    linarith
  · rw [Finset.Ioc_eq_empty (by omega)]; simp

lemma QK04_XK_nonneg (b : ℕ) (g : ℕ → ℝ) (hg : ∀ a, 0 ≤ g a) (N : ℕ) : 0 ≤ XK b g N := by
  unfold XK AK
  apply Finset.sum_nonneg; intro u _
  apply Finset.sum_nonneg; intro w _
  split_ifs
  · unfold wK; exact div_nonneg (Finset.prod_nonneg (fun k _ => hg _)) (by positivity)
  · exact le_refl 0

/-- The inner block length for a square modulus: `6Wb^{2j} ≤ P < 6Wb^{2j+2}`. -/
lemma QK04_jchoice (b W P : ℕ) (hb : 2 ≤ b) (hW : 1 ≤ W) (hP : 6 * W ≤ P) :
    ∃ j : ℕ, 6 * W * b ^ (2 * j) ≤ P ∧ P < 6 * W * b ^ (2 * j + 2) := by
  set t := Nat.log b (P / (6 * W)) with ht
  have hPW : 1 ≤ P / (6 * W) := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  refine ⟨t / 2, ?_, ?_⟩
  · have h1 : b ^ t ≤ P / (6 * W) := Nat.pow_log_le_self b (by omega)
    have h2 : b ^ (2 * (t / 2)) ≤ b ^ t := Nat.pow_le_pow_right (by omega) (by omega)
    calc 6 * W * b ^ (2 * (t / 2)) ≤ 6 * W * (P / (6 * W)) := Nat.mul_le_mul_left _ (h2.trans h1)
      _ ≤ P := Nat.mul_div_le P (6 * W)
  · have h1 : P / (6 * W) < b ^ (t + 1) := Nat.lt_pow_succ_log_self (by omega) _
    have h2 : P < b ^ (t + 1) * (6 * W) := (Nat.div_lt_iff_lt_mul (by omega)).1 h1
    have h3 : b ^ (t + 1) ≤ b ^ (2 * (t / 2) + 2) := Nat.pow_le_pow_right (by omega) (by omega)
    calc P < b ^ (t + 1) * (6 * W) := h2
      _ ≤ b ^ (2 * (t / 2) + 2) * (6 * W) := Nat.mul_le_mul_right _ h3
      _ = 6 * W * b ^ (2 * (t / 2) + 2) := by ring

/-- A set of moduli injected into a dyadic block: the Farey sums are bounded by the block. -/
lemma QK04_into_block (b : ℕ) (g : ℕ → ℝ) (N D : ℕ) (β : ℝ) (T : Finset ℕ) (f : ℕ → ℕ)
    (hinj : ∀ x ∈ T, ∀ y ∈ T, f x = f y → x = y)
    (hmap : ∀ x ∈ T, f x ∈ (Ico D (2 * D)).filter (fun d => Nat.Coprime d b)) :
    ∑ x ∈ T, L1fareyK b g N (f x) β ≤ blockL1K b g N D β := by
  classical
  have e := Finset.sum_image (f := fun q => L1fareyK b g N q β) hinj
  rw [← e]
  unfold blockL1K
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro q hq
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hq
    exact hmap x hx
  · intro _ _ _; exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)

/-- `[1, p) ⊆` reduced residues for a prime `p`. -/
lemma QK04_Ico_sub (p : ℕ) (hp : p.Prime) : Ico 1 p ⊆ redRes p := by
  intro h hh
  simp only [mem_Ico] at hh
  simp only [redRes, mem_filter, mem_range]
  refine ⟨hh.2, ?_⟩
  exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 (fun hd => by
    have := Nat.le_of_dvd (by omega) hd; omega))

/-- `{h < p² : p ∤ h} ⊆` reduced residues mod `p²`. -/
lemma QK04_sq_sub (p : ℕ) (hp : p.Prime) : (range (p ^ 2)).filter (fun h => ¬ p ∣ h) ⊆ redRes (p ^ 2) := by
  intro h hh
  simp only [mem_filter, mem_range] at hh
  simp only [redRes, mem_filter, mem_range]
  refine ⟨hh.1, ?_⟩
  exact Nat.Coprime.pow_right 2 (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 hh.2))

lemma QK04_coprime_sq (b p : ℕ) (hp : p.Prime) (hpB : ¬ p ∣ bigB b) : Nat.Coprime (p ^ 2) (bigB b) :=
  Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpB)

lemma QK04_coprime_p (b p : ℕ) (hp : p.Prime) (hpB : ¬ p ∣ bigB b) : Nat.Coprime p (bigB b) :=
  (Nat.Prime.coprime_iff_not_dvd hp).2 hpB

/-- A sum of norms bounded termwise over a subset of `[0, q)`. -/
lemma QK04_sum_le (s : Finset ℕ) (q : ℕ) (hs : s ⊆ range q) (F : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hF : ∀ h ∈ s, F h ≤ M) : ∑ h ∈ s, F h ≤ q * M := by
  calc ∑ h ∈ s, F h ≤ ∑ _h ∈ s, M := Finset.sum_le_sum hF
    _ = #s * M := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ q * M := by
        apply mul_le_mul_of_nonneg_right _ hM
        have := Finset.card_le_card hs
        rw [card_range] at this
        exact_mod_cast this

/-- The pointwise cut for one modulus, the small part summed over all residues. -/
lemma QK04_cut_mod (b : ℕ) (g : ℕ → ℝ) (hg : IsDigitWeight b g) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (H : ℕ) (τ : ℕ → ℝ) (hT : ∀ t : ℝ, ‖Gg b g t‖ ^ p ≤ trigEval H τ t) (S : ℕ) (κ : ℕ → ℝ) (N : ℕ)
    (hK : ∀ β : ℝ, ‖Mmid (WK b N) β‖ ^ p ≤ trigEval S κ β) (hm : 1 ≤ mK N) (j : ℕ) (hj : j ≤ mK N)
    (q : ℕ) (s : Finset ℕ) (hs : s ⊆ range q) (β t : ℝ) (ht : 0 < t) :
    ∑ h ∈ s, ‖fK b g N ((h : ℝ) / q + β)‖ ≤
      t ^ (1 - p) * (∑ h ∈ range q,
        (∏ k ∈ Ico 1 (mK N), trigEval H τ ((cK b N k : ℝ) * ((h : ℝ) / q + β))) *
          trigEval S κ ((b : ℝ) ^ mK N * ((h : ℝ) / q + β))) +
      t⁻¹ ^ 3 * (∑ h ∈ range q, ‖gJK b g N j ((h : ℝ) / q + β)‖ ^ 4) := by
  have hpt : ∀ α : ℝ, ‖fK b g N α‖ ≤ t ^ (1 - p) * ((∏ k ∈ Ico 1 (mK N), trigEval H τ ((cK b N k : ℝ) * α)) *
      trigEval S κ ((b : ℝ) ^ mK N * α)) + t⁻¹ ^ 3 * ‖gJK b g N j α‖ ^ 4 := fun α =>
    cut_pointwise _ _ _ _ _ (norm_nonneg _) (LK10_fK_le_gJK b g hg N j hj α) ht hp0 hp1
      (LK10_fKp_le b g hg p hp0 H τ hT S κ N hK hm α)
  have hT0 : ∀ α : ℝ, 0 ≤ (∏ k ∈ Ico 1 (mK N), trigEval H τ ((cK b N k : ℝ) * α)) *
      trigEval S κ ((b : ℝ) ^ mK N * α) := fun α =>
    (Real.rpow_nonneg (norm_nonneg _) p).trans (LK10_fKp_le b g hg p hp0 H τ hT S κ N hK hm α)
  calc _ ≤ ∑ h ∈ s, (t ^ (1 - p) * ((∏ k ∈ Ico 1 (mK N),
          trigEval H τ ((cK b N k : ℝ) * ((h : ℝ) / q + β))) *
            trigEval S κ ((b : ℝ) ^ mK N * ((h : ℝ) / q + β))) +
          t⁻¹ ^ 3 * ‖gJK b g N j ((h : ℝ) / q + β)‖ ^ 4) := Finset.sum_le_sum (fun h _ => hpt _)
    _ = t ^ (1 - p) * (∑ h ∈ s,
          (∏ k ∈ Ico 1 (mK N), trigEval H τ ((cK b N k : ℝ) * ((h : ℝ) / q + β))) *
            trigEval S κ ((b : ℝ) ^ mK N * ((h : ℝ) / q + β))) +
        t⁻¹ ^ 3 * (∑ h ∈ s, ‖gJK b g N j ((h : ℝ) / q + β)‖ ^ 4) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := by
        have htp : 0 ≤ t ^ (1 - p) := Real.rpow_nonneg ht.le _
        have hti : 0 ≤ t⁻¹ ^ 3 := by positivity
        exact add_le_add
          (mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => hT0 _)) htp)
          (mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hs
            (fun _ _ _ => by positivity)) hti)

end KappaOmega2

namespace KappaOmega2

open Finset Real Palprimes

/-- The divisor-count hypothesis of Lemma 2.8_κ from the divisor bound `τ(n) ≤ C n^e`. -/
lemma QK04_Td (b H N : ℕ) (hb : 1 ≤ b) (hH : H ≤ b * (b - 1)) (Qs : Finset ℕ) (hQpos : ∀ q ∈ Qs, 1 ≤ q)
    (e Ce : ℝ) (he : 0 ≤ e) (hCe0 : 0 ≤ Ce) (hCe : ∀ n : ℕ, 1 ≤ n → (#n.divisors : ℝ) ≤ Ce * (n : ℝ) ^ e) :
    ∀ v : ℤ, v ≠ 0 → |v| ≤ (2 * (H : ℤ) + 1) * (b : ℤ) ^ (2 * N + 1) →
      ((Qs.filter (fun q : ℕ => (q : ℤ) ∣ v)).card : ℝ) ≤ Ce * (2 * (b : ℝ) ^ 2 * xx b N) ^ e := by
  intro v hv hvle
  have hHb : 2 * (H : ℝ) + 1 ≤ 2 * (b : ℝ) ^ 2 := by
    have e : b * (b - 1) + b = b * b := by
      rw [← Nat.mul_succ]; congr 1; omega
    have h : 2 * H + 1 ≤ 2 * (b * b) := by omega
    have h' : ((2 * H + 1 : ℕ) : ℝ) ≤ ((2 * (b * b) : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'; nlinarith
  have h1 := card_filter_dvd_le_divisors Qs (fun q hq => hQpos q hq) v hv
  have h2 := hCe v.natAbs (Int.natAbs_pos.2 hv)
  have h3 : (v.natAbs : ℝ) ≤ 2 * (b : ℝ) ^ 2 * xx b N := by
    have h3' : ((v.natAbs : ℤ) : ℝ) ≤ (((2 * (H : ℤ) + 1) * (b : ℤ) ^ (2 * N + 1) : ℤ) : ℝ) := by
      rw [Int.natCast_natAbs]; exact_mod_cast hvle
    rw [Int.cast_natCast] at h3'
    push_cast at h3'
    unfold xx
    have hpow : (0 : ℝ) ≤ (b : ℝ) ^ (2 * N + 1) := by positivity
    calc (v.natAbs : ℝ) ≤ (2 * (H : ℝ) + 1) * (b : ℝ) ^ (2 * N + 1) := h3'
      _ ≤ 2 * (b : ℝ) ^ 2 * (b : ℝ) ^ (2 * N + 1) := mul_le_mul_of_nonneg_right hHb hpow
  calc ((Qs.filter (fun q : ℕ => (q : ℤ) ∣ v)).card : ℝ) ≤ (#(v.natAbs.divisors) : ℝ) := by
        exact_mod_cast h1
    _ ≤ Ce * (v.natAbs : ℝ) ^ e := h2
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) h3 he) hCe0

/-- `W ≥ x^{3/10}` and `W ≤ b² x^{3/10}` in exponential form. -/
lemma QK04_W_bounds (b N : ℕ) (hb : 1 ≤ b) :
    Real.exp (3 / 10 * ((2 * (N : ℝ) + 1) * Real.log b)) ≤ (WK b N : ℝ) ∧
      (WK b N : ℝ) ≤ (b : ℝ) ^ 2 * Real.exp (3 / 10 * ((2 * (N : ℝ) + 1) * Real.log b)) := by
  obtain ⟨hs1, hs2, hs3⟩ := LK10_shape N
  have hW : (WK b N : ℝ) = Real.exp ((ellK N : ℝ) * Real.log b) := by
    unfold WK; rw [Nat.cast_pow, LK10_pow_exp b hb]
  have hb2 : (b : ℝ) ^ 2 = Real.exp (2 * Real.log b) := by
    rw [LK10_pow_exp b hb]; norm_num
  have hlb : 0 ≤ Real.log b := Real.log_nonneg (by exact_mod_cast hb)
  have h : 3 * (2 * N + 1) ≤ 10 * ellK N := by omega
  have h' : 3 * (2 * (N : ℝ) + 1) ≤ 10 * (ellK N : ℝ) := by exact_mod_cast h
  have k : 10 * ellK N ≤ 3 * (2 * N + 1) + 20 := by omega
  have k' : 10 * (ellK N : ℝ) ≤ 3 * (2 * (N : ℝ) + 1) + 20 := by exact_mod_cast k
  rw [hW, hb2, ← Real.exp_add]
  constructor <;> apply Real.exp_le_exp.2 <;> nlinarith

end KappaOmega2

namespace KappaOmega2

open Finset Real Palprimes

lemma QK04_bigB_pos (b : ℕ) (hb : 2 ≤ b) : 1 ≤ bigB b := by
  unfold bigB
  have : b < b ^ 3 := by
    calc b = b ^ 1 := (pow_one b).symm
      _ < b ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  omega

lemma QK04_coprime_b (b q : ℕ) (hq : Nat.Coprime q (bigB b)) : Nat.Coprime q b :=
  Nat.Coprime.coprime_dvd_right (by unfold bigB; exact Nat.dvd_sub (dvd_pow_self b (by norm_num)) dvd_rfl) hq

/-- `Nat.log 2 Y < b(2N+1)` for `Y ≤ x`. -/
lemma QK04_log_le (b N Y : ℕ) (hb : 2 ≤ b) (hY : (Y : ℝ) ≤ xx b N) : Nat.log 2 Y + 1 ≤ b * (2 * N + 1) := by
  have hYx : Y ≤ b ^ (2 * N + 1) := by
    have : (Y : ℝ) ≤ ((b ^ (2 * N + 1) : ℕ) : ℝ) := by rw [Nat.cast_pow]; exact hY
    exact_mod_cast this
  have h2 : b ^ (2 * N + 1) < 2 ^ (b * (2 * N + 1)) := by
    rw [pow_mul]; exact Nat.pow_lt_pow_left Nat.lt_two_pow_self (by omega)
  rcases Nat.eq_zero_or_pos Y with h | h
  · subst h; simp only [Nat.log_zero_right, zero_add]; exact Nat.mul_pos (by omega) (by omega)
  · have := Nat.log_lt_of_lt_pow (by omega) (lt_of_le_of_lt hYx h2)
    omega

end KappaOmega2
