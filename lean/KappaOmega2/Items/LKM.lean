import KappaOmega2.StatementsK
import KappaOmega2.Items.LK01
import KappaOmega2.Items.LK06
import Palprimes.Major.Fejer
import Palprimes.ExpSum.LargeSieve

/-!
# LKM: the middle majorant `K̃ ≥ |M_W|^p`

`L = ⌊log₂ W⌋`, `M_k = 2^{L−1−k}` (`k < L`), `K̃ = (5/2) Σ_{k<L} 2^{−kp} F_{M_k}` (degree `2^{L−1} − 1 < W/2`).
For `‖β‖ ≤ 1/(2M)`, `F_M(β) ≥ 4/π² ≥ 2/5` (Jordan and `sin x ≤ x`), and `|M_W(β)| ≤ min(1, 1/(2W‖β‖))`
(`Palprimes.norm_dirK_le`). With `k` the least index with `‖β‖ ≤ 2^{k−L}` the `k`-th term alone dominates
`|M_W|^p ≤ 2^{−kp}`. Then `κ₀ = (5/2) Σ 2^{−kp}/M_k ≤ 10 L W^{−p} ≤ 15 log W · W^{−p}` and the mass is
`(5/2) Σ 2^{−kp} ≤ 10`.
-/

namespace KappaOmega2

open Finset Real Palprimes

lemma LKM_Mmid_eq (W : ℕ) (β : ℝ) : ‖Mmid W β‖ = ‖dirK W β‖ / W := by
  unfold Mmid dirK
  rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
  ring

lemma LKM_Mmid_le_one (W : ℕ) (hW : 1 ≤ W) (β : ℝ) : ‖Mmid W β‖ ≤ 1 := by
  rw [LKM_Mmid_eq, div_le_one (by exact_mod_cast (show 0 < W by omega))]
  exact norm_dirK_le_M W β

lemma LKM_Mmid_le (W : ℕ) (hW : 1 ≤ W) (β : ℝ) (h : 0 < distZ β) :
    ‖Mmid W β‖ ≤ 1 / (2 * W * distZ β) := by
  rw [LKM_Mmid_eq]
  have h1 := norm_dirK_le W β h
  have hW0 : (0 : ℝ) < W := by exact_mod_cast (show 0 < W by omega)
  calc ‖dirK W β‖ / W ≤ (1 / (2 * distZ β)) / W := div_le_div_of_nonneg_right h1 hW0.le
    _ = 1 / (2 * W * distZ β) := by field_simp

/-- `F_M(β) ≥ 2/5` for `‖β‖ ≤ 1/(2M)`. -/
lemma LKM_fejer_lower (M : ℕ) (hM : 1 ≤ M) (β : ℝ) (h : distZ β * (2 * M) ≤ 1) :
    2 / 5 ≤ fejerK M β := by
  have hF : fejerK M β = psiB M β := by rw [LK01_fejerK_eq M hM β]; rfl
  rw [hF, psiB_red]
  have hdu : distZ β = |β - round β| := rfl
  rw [hdu] at h
  set u := |β - round β| with hu
  have hu0 : 0 ≤ u := abs_nonneg _
  rcases eq_or_lt_of_le hu0 with h0 | hpos
  · rw [← h0, psiB_zero M hM]; norm_num
  · have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have hMu : (M : ℝ) * u ≤ 1 / 2 := by linarith
    have hu2 : u ≤ 1 / 2 := by nlinarith
    have hpi := Real.pi_pos
    have hsinpos : 0 < Real.sin (π * u) :=
      Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith)
    rw [psiB_sin M hM u hsinpos.ne']
    have h1 : 2 * (M : ℝ) * u ≤ Real.sin (π * M * u) := by
      have := Real.mul_le_sin (x := π * M * u) (by positivity) (by nlinarith)
      have e : 2 / π * (π * M * u) = 2 * M * u := by field_simp
      linarith
    have h2 : Real.sin (π * u) ≤ π * u := Real.sin_le (by positivity)
    have hden : 0 < (M : ℝ) * Real.sin (π * u) := by positivity
    have hr : 2 / π ≤ Real.sin (π * M * u) / (M * Real.sin (π * u)) := by
      rw [le_div_iff₀ hden]
      have h3 : 2 / π * (M * Real.sin (π * u)) ≤ 2 / π * (M * (π * u)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
      have e : 2 / π * (M * (π * u)) = 2 * M * u := by field_simp
      linarith
    have hpi2 : π ^ 2 ≤ 10 := by nlinarith [Real.pi_lt_d2]
    have h2pi : 2 / 5 ≤ (2 / π) ^ 2 := by
      rw [div_pow, le_div_iff₀ (by positivity)]; nlinarith
    calc 2 / 5 ≤ (2 / π) ^ 2 := h2pi
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hr 2

lemma LKM_trig_finsum (H : ℕ) (K : Finset ℕ) (f : ℕ → ℕ → ℝ) (t : ℝ) :
    trigEval H (fun s => ∑ k ∈ K, f k s) t = ∑ k ∈ K, trigEval H (f k) t := by
  unfold trigEval
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 2
  simp only [Finset.sum_mul]
  exact Finset.sum_comm

lemma LKM_trig_smul (H : ℕ) (a : ℝ) (f : ℕ → ℝ) (t : ℝ) :
    trigEval H (fun s => a * f s) t = a * trigEval H f t := by
  unfold trigEval
  rw [show ∑ u ∈ Icc 1 H, a * f u * Real.cos (2 * π * u * t) =
      a * ∑ u ∈ Icc 1 H, f u * Real.cos (2 * π * u * t) by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)]
  ring

lemma LKM_fejTau_nonneg (m u : ℕ) : 0 ≤ fejTau m u := by
  unfold fejTau
  split_ifs with h0 h1
  · positivity
  · apply div_nonneg _ (by positivity)
    have : (u : ℝ) < m := by exact_mod_cast h1
    linarith
  · exact le_rfl

lemma LKM_mass_eq (H : ℕ) (τ : ℕ → ℝ) (hτ : ∀ u, 0 ≤ τ u) : trigMass H τ = trigEval H τ 0 := by
  unfold trigMass trigEval
  rw [abs_of_nonneg (hτ 0)]
  congr 2
  apply Finset.sum_congr rfl
  intro u _
  rw [abs_of_nonneg (hτ u)]
  simp

/-- `((1/2)^k)^p = 2^{−pk}`. -/
lemma LKM_pow_rpow (k : ℕ) (p : ℝ) : (1 / (2 : ℝ) ^ k) ^ p = (2 : ℝ) ^ (-(p * k)) := by
  rw [one_div, ← Real.rpow_natCast, ← Real.rpow_neg (by norm_num), ← Real.rpow_mul (by norm_num)]
  congr 1; ring

theorem itemLKM : ItemLKM := by
  unfold ItemLKM KmidStmt
  intro W p hW hp1 hp2
  set L := Nat.log 2 W with hLdef
  have hL : 2 ^ L ≤ W := Nat.pow_log_le_self 2 (by omega)
  have hL' : W < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) W
  have hL4 : 4 ≤ L := Nat.le_log_of_pow_le (by norm_num) (by omega)
  have hW1 : 1 ≤ W := by omega
  have hWR : (0 : ℝ) < W := by exact_mod_cast (show 0 < W by omega)
  have hLR : ((2 : ℝ) ^ L) ≤ W := by exact_mod_cast hL
  set c : ℕ → ℝ := fun k => (2 : ℝ) ^ (-(p * k)) with hcdef
  have hc0 : ∀ k, 0 ≤ c k := fun k => Real.rpow_nonneg (by norm_num) _
  set Mk : ℕ → ℕ := fun k => 2 ^ (L - 1 - k) with hMk
  have hMk1 : ∀ k, 1 ≤ Mk k := fun k => Nat.one_le_two_pow
  set S := 2 ^ (L - 1) - 1 with hS
  have h2L : 2 ^ L = 2 * 2 ^ (L - 1) := by
    rw [← pow_succ']; congr 1; omega
  set κ : ℕ → ℝ := fun s => ∑ k ∈ range L, (5 / 2 * c k) * fejTau (Mk k) s with hκ
  have hκnn : ∀ s, 0 ≤ κ s := fun s =>
    Finset.sum_nonneg (fun k _ => mul_nonneg (by have := hc0 k; positivity) (LKM_fejTau_nonneg _ _))
  have hval : ∀ β, trigEval S κ β = ∑ k ∈ range L, (5 / 2 * c k) * fejerK (Mk k) β := by
    intro β
    rw [hκ, LKM_trig_finsum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.1 hk
    rw [LKM_trig_smul, LK06_fejer_trig (Mk k) S (hMk1 k) ?_ β]
    have : Mk k ≤ 2 ^ (L - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 1 ≤ 2 ^ (L - 1) := Nat.one_le_two_pow
    omega
  refine ⟨S, κ, ?_, hκnn, ?_, ?_, ?_⟩
  · -- degree
    have : 1 ≤ 2 ^ (L - 1) := Nat.one_le_two_pow
    omega
  · -- majorant
    intro β
    rw [hval]
    set d := distZ β with hd
    have hd0 : 0 ≤ d := distZ_nonneg β
    have hd2 : d ≤ 1 / 2 := distZ_le_half β
    have h2pos : ∀ n : ℕ, (0 : ℝ) < (2 : ℝ) ^ n := fun n => by positivity
    have hP : d ≤ (2 : ℝ) ^ (L - 1) / (2 : ℝ) ^ L := by
      have : (2 : ℝ) ^ L = 2 * (2 : ℝ) ^ (L - 1) := by exact_mod_cast h2L
      have h12 : (2 : ℝ) ^ (L - 1) / (2 : ℝ) ^ L = 1 / 2 := by
        rw [this]; field_simp
      rw [h12]; exact hd2
    classical
    have hex : ∃ k, d ≤ (2 : ℝ) ^ k / (2 : ℝ) ^ L := ⟨L - 1, hP⟩
    set k0 := Nat.find hex with hk0def
    have hk0 : d ≤ (2 : ℝ) ^ k0 / (2 : ℝ) ^ L := Nat.find_spec hex
    have hk0le : k0 ≤ L - 1 := Nat.find_min' hex hP
    -- the Fejér term is large
    have hlow : 2 / 5 ≤ fejerK (Mk k0) β := by
      apply LKM_fejer_lower (Mk k0) (hMk1 k0) β
      rw [← hd]
      have e : (2 : ℝ) * ((Mk k0 : ℕ) : ℝ) * (2 : ℝ) ^ k0 = (2 : ℝ) ^ L := by
        simp only [hMk]; push_cast
        rw [← pow_succ', ← pow_add]; congr 1; omega
      have : d * (2 * ((Mk k0 : ℕ) : ℝ)) ≤ (2 : ℝ) ^ k0 / (2 : ℝ) ^ L * (2 * ((Mk k0 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right hk0 (by positivity)
      calc d * (2 * ((Mk k0 : ℕ) : ℝ)) ≤ (2 : ℝ) ^ k0 / (2 : ℝ) ^ L * (2 * ((Mk k0 : ℕ) : ℝ)) := this
        _ = 1 := by rw [div_mul_eq_mul_div, div_eq_one_iff_eq (h2pos L).ne', ← e]; ring
    -- |M_W|^p ≤ c k0
    have hup : ‖Mmid W β‖ ^ p ≤ c k0 := by
      have hn0 : 0 ≤ ‖Mmid W β‖ := norm_nonneg _
      have hp0 : 0 ≤ p := by linarith
      rcases Nat.eq_zero_or_pos k0 with hz | hpos
      · rw [hz]
        simp only [hcdef, Nat.cast_zero, mul_zero, neg_zero, Real.rpow_zero]
        exact Real.rpow_le_one hn0 (LKM_Mmid_le_one W hW1 β) hp0
      · have hnot : ¬ d ≤ (2 : ℝ) ^ (k0 - 1) / (2 : ℝ) ^ L := Nat.find_min hex (by omega)
        push_neg at hnot
        have hdpos : 0 < d := lt_of_le_of_lt (by positivity) hnot
        have hM : ‖Mmid W β‖ ≤ 1 / (2 : ℝ) ^ k0 := by
          calc ‖Mmid W β‖ ≤ 1 / (2 * W * d) := LKM_Mmid_le W hW1 β hdpos
            _ ≤ 1 / (2 * W * ((2 : ℝ) ^ (k0 - 1) / (2 : ℝ) ^ L)) := by
                apply one_div_le_one_div_of_le (by positivity)
                exact mul_le_mul_of_nonneg_left hnot.le (by positivity)
            _ ≤ 1 / (2 : ℝ) ^ k0 := by
                apply one_div_le_one_div_of_le (by positivity)
                have e : (2 : ℝ) ^ k0 = 2 * (2 : ℝ) ^ (k0 - 1) := by
                  rw [← pow_succ']; congr 1; omega
                rw [e, mul_div_assoc', le_div_iff₀ (h2pos L)]
                have := mul_le_mul_of_nonneg_left hLR (show (0 : ℝ) ≤ 2 * (2 : ℝ) ^ (k0 - 1) by positivity)
                nlinarith
        calc ‖Mmid W β‖ ^ p ≤ (1 / (2 : ℝ) ^ k0) ^ p := Real.rpow_le_rpow hn0 hM hp0
          _ = c k0 := LKM_pow_rpow k0 p
    have hk0mem : k0 ∈ range L := Finset.mem_range.2 (by omega)
    have hterm : c k0 ≤ (5 / 2 * c k0) * fejerK (Mk k0) β := by
      have := hc0 k0
      nlinarith
    have hsingle : (5 / 2 * c k0) * fejerK (Mk k0) β ≤ ∑ k ∈ range L, (5 / 2 * c k) * fejerK (Mk k) β :=
      Finset.single_le_sum (f := fun k => (5 / 2 * c k) * fejerK (Mk k) β)
        (fun k _ => mul_nonneg (by have := hc0 k; positivity) (LK01_fejerK_nonneg _ (hMk1 k) β)) hk0mem
    linarith
  · -- κ₀
    have hκ0 : κ 0 = ∑ k ∈ range L, (5 / 2 * c k) * (1 / ((Mk k : ℕ) : ℝ)) := by
      simp [hκ, fejTau]
    rw [hκ0]
    have hp0 : 0 < p := by linarith
    have hWp : (2 : ℝ) ^ (-(p * ((L : ℝ) + 1))) ≤ (W : ℝ) ^ (-p) := by
      have h1 : ((W : ℝ)) ^ p ≤ ((2 : ℝ) ^ (L + 1)) ^ p :=
        Real.rpow_le_rpow hWR.le (by exact_mod_cast hL'.le) hp0.le
      rw [Real.rpow_neg hWR.le, Real.rpow_neg (by norm_num)]
      have e : ((2 : ℝ) ^ (L + 1)) ^ p = (2 : ℝ) ^ (p * ((L : ℝ) + 1)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; push_cast; ring_nf
      rw [← e]
      exact inv_anti₀ (Real.rpow_pos_of_pos hWR p) h1
    have hterm : ∀ k ∈ range L, (5 / 2 * c k) * (1 / ((Mk k : ℕ) : ℝ)) ≤ 10 * (W : ℝ) ^ (-p) := by
      intro k hk
      have hk' := Finset.mem_range.1 hk
      have hMkR : ((Mk k : ℕ) : ℝ) = (2 : ℝ) ^ (((L - 1 - k : ℕ) : ℝ)) := by
        simp only [hMk]; push_cast; rw [Real.rpow_natCast]
      have hsub : (((L - 1 - k : ℕ) : ℝ)) = (L : ℝ) - 1 - k := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
      have h1 : c k * (1 / ((Mk k : ℕ) : ℝ)) = (2 : ℝ) ^ (-(p * k) - ((L : ℝ) - 1 - k)) := by
        rw [hMkR, Real.rpow_sub (by norm_num : (0 : ℝ) < 2) (-(p * k)) ((L : ℝ) - 1 - k), ← hsub]
        simp only [hcdef]; ring
      have h2 : (2 : ℝ) ^ (-(p * k) - ((L : ℝ) - 1 - k)) ≤ (2 : ℝ) ^ ((2 : ℝ) + -(p * ((L : ℝ) + 1))) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have hkL : (k : ℝ) + 1 ≤ L := by exact_mod_cast (show k + 1 ≤ L by omega)
        nlinarith
      have h3 : (2 : ℝ) ^ ((2 : ℝ) + -(p * ((L : ℝ) + 1))) = 4 * (2 : ℝ) ^ (-(p * ((L : ℝ) + 1))) := by
        rw [Real.rpow_add (by norm_num)]; norm_num
      have : c k * (1 / ((Mk k : ℕ) : ℝ)) ≤ 4 * (W : ℝ) ^ (-p) := by
        rw [h1]; linarith
      nlinarith
    have hsum := Finset.sum_le_sum hterm
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    have hlog : (L : ℝ) * Real.log 2 ≤ Real.log W := by
      rw [← Real.log_pow]
      exact Real.log_le_log (by positivity) hLR
    have hl2 := Real.log_two_gt_d9
    have hLlog : (L : ℝ) ≤ 3 / 2 * Real.log W := by nlinarith
    have hlogW : 0 ≤ Real.log W := Real.log_nonneg (by exact_mod_cast hW1)
    have hWp0 : 0 ≤ (W : ℝ) ^ (-p) := Real.rpow_nonneg hWR.le _
    calc _ ≤ (L : ℝ) * (10 * (W : ℝ) ^ (-p)) := hsum
      _ ≤ (3 / 2 * Real.log W) * (10 * (W : ℝ) ^ (-p)) := by
          apply mul_le_mul_of_nonneg_right hLlog (by positivity)
      _ ≤ 100 * (1 + Real.log W) * (W : ℝ) ^ (-p) := by nlinarith
  · -- mass
    rw [LKM_mass_eq _ _ hκnn, hval]
    have hx : (2 : ℝ) ^ (-p) ≤ 3 / 4 := by
      have h1 : (2 : ℝ) ^ (-p) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      have h2 : ((2 : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = 1 / 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
      have h3 : 0 ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by norm_num) _
      nlinarith
    have hx0 : 0 ≤ (2 : ℝ) ^ (-p) := Real.rpow_nonneg (by norm_num) _
    have hck : ∀ k : ℕ, c k = ((2 : ℝ) ^ (-p)) ^ k := by
      intro k
      simp only [hcdef]
      rw [show -(p * (k : ℝ)) = (-p) * (k : ℝ) by ring, Real.rpow_mul (by norm_num), Real.rpow_natCast]
    have hgeom : ∑ k ∈ range L, c k ≤ 4 := by
      simp only [hck]
      have h := geom_sum_mul_neg ((2 : ℝ) ^ (-p)) L
      have hxL : 0 ≤ ((2 : ℝ) ^ (-p)) ^ L := pow_nonneg hx0 L
      have hs0 : 0 ≤ ∑ i ∈ range L, ((2 : ℝ) ^ (-p)) ^ i := Finset.sum_nonneg (fun i _ => pow_nonneg hx0 i)
      nlinarith
    have hle : ∀ k ∈ range L, (5 / 2 * c k) * fejerK (Mk k) 0 ≤ 5 / 2 * c k := by
      intro k _
      have h1 := LK06_fejer_le_one (Mk k) (hMk1 k) 0
      have := hc0 k
      nlinarith
    calc _ ≤ ∑ k ∈ range L, 5 / 2 * c k := Finset.sum_le_sum hle
      _ = 5 / 2 * ∑ k ∈ range L, c k := by rw [Finset.mul_sum]
      _ ≤ 100 := by nlinarith

end KappaOmega2
