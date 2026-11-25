import KappaOmega2.StatementsK
import KappaOmega2.Items.LK17_Dig

/-!
# LK13: `X ≥ c > 0`

Keep the outer vectors with `u_0 = 1` (weight `g(1)`, and `n ≡ 1 mod b`). For fixed `u`, `n(u, w) = A(u) + w b^m` and
`b^m` is a unit mod `q = b² − 1` (`b² ≡ 1`), so the `w < W` with `n ≡ 1 mod q` form a residue class mod `q`, at least
`⌊W/q⌋` of them. These `n` are coprime to `b q = b³ − b`. With `W ≥ 2q` this gives `X ≥ g(1)/(2q)`.
-/

namespace KappaOmega2

open Finset Palprimes

lemma LK13_bigB (b : ℕ) : bigB b = b * (b ^ 2 - 1) := by
  unfold bigB
  rw [Nat.mul_sub, mul_one, ← pow_succ']

/-- At least `⌊W/q⌋` middle blocks put `n(u, w)` in the class `1 mod q`. -/
lemma LK13_count (b N : ℕ) (hb : 2 ≤ b) (u : KVec b N) :
    WK b N / (b ^ 2 - 1) ≤
      ((range (WK b N)).filter (fun w => kpalVal b N u w % (b ^ 2 - 1) = 1)).card := by
  set q := b ^ 2 - 1 with hq
  have hq2 : 2 ≤ q := by
    have : 4 ≤ b ^ 2 := by nlinarith
    omega
  haveI : NeZero q := ⟨by omega⟩
  set A : ℕ := ∑ k : Fin (mK N), (u k : ℕ) * cK b N k with hA
  have hval : ∀ w, kpalVal b N u w = A + w * b ^ mK N := fun w => rfl
  set x : ZMod q := (1 - (A : ZMod q)) * (b : ZMod q) ^ mK N with hx
  have hb2 : (b : ZMod q) ^ 2 = 1 := by
    have h1 : b ^ 2 = q + 1 := by omega
    have : ((b ^ 2 : ℕ) : ZMod q) = ((q + 1 : ℕ) : ZMod q) := by rw [h1]
    push_cast at this
    rw [this, ZMod.natCast_self, zero_add]
  have hgood : ∀ j : ℕ, kpalVal b N u (x.val + q * j) % q = 1 := by
    intro j
    have hcast : ((kpalVal b N u (x.val + q * j) : ℕ) : ZMod q) = ((1 : ℕ) : ZMod q) := by
      rw [hval]
      push_cast
      rw [ZMod.natCast_self, zero_mul, add_zero, ZMod.natCast_zmod_val, hx, mul_assoc, ← pow_add,
        ← two_mul, pow_mul, hb2, one_pow]
      ring
    rw [ZMod.natCast_eq_natCast_iff'] at hcast
    rw [hcast]
    exact Nat.mod_eq_of_lt (by omega)
  have hxlt : x.val < q := ZMod.val_lt x
  have hsub : (range (WK b N / q)).image (fun j => x.val + q * j) ⊆
      (range (WK b N)).filter (fun w => kpalVal b N u w % q = 1) := by
    intro w hw
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hw
    have hj' := Finset.mem_range.1 hj
    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 ?_, hgood j⟩
    have h1 : q * (j + 1) ≤ q * (WK b N / q) := Nat.mul_le_mul_left q hj'
    have h2 : q * (WK b N / q) ≤ WK b N := Nat.mul_div_le (WK b N) q
    have h3 : x.val + q * j < q * (j + 1) := by rw [mul_add, mul_one]; omega
    omega
  have hinj : Set.InjOn (fun j => x.val + q * j) (range (WK b N / q) : Set ℕ) := by
    intro i _ j _ h
    simp only at h
    have : q * i = q * j := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega) this
  calc WK b N / q = ((range (WK b N / q)).image (fun j => x.val + q * j)).card := by
        rw [Finset.card_image_of_injOn hinj, Finset.card_range]
    _ ≤ _ := Finset.card_le_card hsub

/-- `Σ_{u : u_0 = 1} Π_k g(u_k) = g(1)`. -/
lemma LK13_sum_u0 (b : ℕ) (g : ℕ → ℝ) (hW : IsDigitWeight b g) (hb : 2 ≤ b) (N : ℕ) (hm : 0 < mK N) :
    ∑ u : KVec b N, (if (u ⟨0, hm⟩ : ℕ) = 1 then wK b g N u else 0) = g 1 := by
  set k0 : Fin (mK N) := ⟨0, hm⟩
  let f : Fin (mK N) → Fin b → ℝ := fun k a => if k = k0 then (if (a : ℕ) = 1 then g a else 0) else g a
  have h := Finset.prod_univ_sum (fun _ : Fin (mK N) => (univ : Finset (Fin b))) f
  simp only [Fintype.piFinset_univ] at h
  have hs1 : ∑ a : Fin b, g (a : ℕ) = 1 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => g i) b]; exact hW.2
  have hs2 : ∑ a : Fin b, (if (a : ℕ) = 1 then g a else 0) = g 1 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => if i = 1 then g i else 0) b, Finset.sum_ite_eq']
    rw [if_pos (Finset.mem_range.2 (by omega))]
  have hL : ∏ k : Fin (mK N), ∑ a : Fin b, f k a = g 1 := by
    have : ∀ k : Fin (mK N), ∑ a : Fin b, f k a = if k = k0 then g 1 else 1 := by
      intro k
      by_cases hk : k = k0
      · simp only [f, hk, if_true]; exact hs2
      · simp only [f, hk, if_false]; exact hs1
    rw [Finset.prod_congr rfl (fun k _ => this k), Finset.prod_ite_eq' univ k0]
    simp
  rw [← hL, h]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : (u k0 : ℕ) = 1
  · rw [if_pos hu]
    unfold wK
    apply Finset.prod_congr rfl
    intro k _
    by_cases hk : k = k0
    · subst hk; simp [f, hu]
    · simp [f, hk]
  · rw [if_neg hu]
    exact (Finset.prod_eq_zero (Finset.mem_univ k0) (by simp [f, hu])).symm

theorem itemLK13 : ItemLK13 := by
  unfold ItemLK13
  intro b g hb hW hg1
  set q := b ^ 2 - 1 with hq
  have hq8 : 8 ≤ q := by
    have : 9 ≤ b ^ 2 := by nlinarith
    omega
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  refine ⟨g 1 / (2 * q), by positivity, 4, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hm := LK17_m_pos N hN1
  have hell : 3 ≤ ellK N := by unfold ellK mK; omega
  have hWq : 2 * q ≤ WK b N := by
    have h1 : b ^ 3 ≤ WK b N := by unfold WK; exact Nat.pow_le_pow_right (by omega) hell
    have h2 : 2 * b ^ 2 ≤ b ^ 3 := by
      have := Nat.mul_le_mul_right (b ^ 2) (show 2 ≤ b by omega)
      calc 2 * b ^ 2 ≤ b * b ^ 2 := this
        _ = b ^ 3 := by ring
    omega
  have hWpos : (0 : ℝ) < (WK b N : ℝ) := by exact_mod_cast (show 0 < WK b N by omega)
  set k := WK b N / q with hk
  have hkW : (WK b N : ℝ) ≤ 2 * q * k := by
    have hdm := Nat.div_add_mod (WK b N) q
    have hmod := Nat.mod_lt (WK b N) (show 0 < q by omega)
    have : WK b N ≤ 2 * (q * k) := by
      rw [hk]; omega
    exact_mod_cast (show WK b N ≤ 2 * q * k by rw [mul_assoc]; exact this)
  -- pointwise lower bound
  have hpt : ∀ u : KVec b N,
      (if (u ⟨0, hm⟩ : ℕ) = 1 then wK b g N u * ((k : ℝ) / (WK b N : ℝ)) else 0) ≤
        ∑ w ∈ range (WK b N),
          (if Nat.Coprime (kpalVal b N u w) (bigB b) ∧ 1 ∣ kpalVal b N u w then wK b g N u / (WK b N : ℝ)
            else 0) := by
    intro u
    have hw0 : 0 ≤ wK b g N u := Finset.prod_nonneg (fun _ _ => hW.1 _)
    have hnn : ∀ w ∈ range (WK b N), 0 ≤
        (if Nat.Coprime (kpalVal b N u w) (bigB b) ∧ 1 ∣ kpalVal b N u w then wK b g N u / (WK b N : ℝ)
          else 0) := by
      intro w _; split_ifs
      · exact div_nonneg hw0 hWpos.le
      · exact le_rfl
    by_cases hu : (u ⟨0, hm⟩ : ℕ) = 1
    · rw [if_pos hu]
      set S := (range (WK b N)).filter (fun w => kpalVal b N u w % q = 1)
      have hS : ∀ w ∈ S, (if Nat.Coprime (kpalVal b N u w) (bigB b) ∧ 1 ∣ kpalVal b N u w then
          wK b g N u / (WK b N : ℝ) else 0) = wK b g N u / (WK b N : ℝ) := by
        intro w hwS
        obtain ⟨hwr, hwq⟩ := Finset.mem_filter.1 hwS
        have hwr' := Finset.mem_range.1 hwr
        have hmb : kpalVal b N u w % b = 1 := by rw [LK17_mod_b b N hN1 u w hwr', hu]
        have hcb : Nat.Coprime b (kpalVal b N u w) := by
          unfold Nat.Coprime; rw [Nat.gcd_rec, hmb, Nat.gcd_one_left]
        have hcq : Nat.Coprime q (kpalVal b N u w) := by
          unfold Nat.Coprime; rw [Nat.gcd_rec, hwq, Nat.gcd_one_left]
        have hcop : Nat.Coprime (kpalVal b N u w) (bigB b) := by
          rw [LK13_bigB]
          exact Nat.Coprime.mul_right hcb.symm hcq.symm
        rw [if_pos ⟨hcop, one_dvd _⟩]
      have hsubS : S ⊆ range (WK b N) := Finset.filter_subset _ _
      calc wK b g N u * ((k : ℝ) / (WK b N : ℝ)) ≤ (S.card : ℝ) * (wK b g N u / (WK b N : ℝ)) := by
            have hc : (k : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast LK13_count b N (by omega) u
            have : wK b g N u * ((k : ℝ) / (WK b N : ℝ)) = (k : ℝ) * (wK b g N u / (WK b N : ℝ)) := by
              ring
            rw [this]
            exact mul_le_mul_of_nonneg_right hc (div_nonneg hw0 hWpos.le)
        _ = ∑ w ∈ S, (if Nat.Coprime (kpalVal b N u w) (bigB b) ∧ 1 ∣ kpalVal b N u w then
              wK b g N u / (WK b N : ℝ) else 0) := by
            rw [Finset.sum_congr rfl hS, Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsubS (fun w hw _ => hnn w hw)
    · rw [if_neg hu]
      exact Finset.sum_nonneg hnn
  have hX : g 1 * ((k : ℝ) / (WK b N : ℝ)) ≤ XK b g N := by
    unfold XK AK
    calc g 1 * ((k : ℝ) / (WK b N : ℝ)) =
          ∑ u : KVec b N, (if (u ⟨0, hm⟩ : ℕ) = 1 then wK b g N u * ((k : ℝ) / (WK b N : ℝ)) else 0) := by
          rw [← LK13_sum_u0 b g hW (by omega) N hm, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro u _
          split_ifs <;> ring
      _ ≤ _ := Finset.sum_le_sum (fun u _ => hpt u)
  refine le_trans ?_ hX
  rw [div_le_iff₀ (by positivity)]
  have hg0 : 0 ≤ g 1 := hW.1 1
  have : g 1 * ((k : ℝ) / (WK b N : ℝ)) * (2 * q) = g 1 * (2 * q * k) / (WK b N : ℝ) := by
    field_simp
  rw [this, le_div_iff₀ hWpos]
  exact mul_le_mul_of_nonneg_left hkW hg0

end KappaOmega2
