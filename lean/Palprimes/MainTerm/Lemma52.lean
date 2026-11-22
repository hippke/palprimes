import Palprimes.MainTerm.Simplex
import Palprimes.MainTerm.Lemma52Comb

/-! # Greaves Lemma 5.2

For `1/8 ≤ x ≤ 1/2`:
`Σ_{r=1}^{8} (−1)^{r+1} k_r(x, G_r) = 2e^γ x (1/(1 − x) − h_2(x, 1) − h_4(x, 1))`,
with `k_r = 0` for `r ≥ 9` and `h_{2k} = 0` for `k ≥ 3`.

Route. `k_r` is written (Lemma 5.1 + `u_i = x v_i` + Fubini, Greaves p. 318) as a sum over `t`
of simplex integrals `SxP n a x` (`n + 1 = r − 1 + t` free variables, `a = r − 1`) against the
measure `smeas (1 − x) n` of `Simplex.lean`, and `h_{2m}` likewise. For fixed `n = 2m` the
alternating sum over `a` is symmetrised (`integral_sort`) and vanishes pointwise by
`rosser_alternating_identity` (the interleaving identity (5.11) and the inclusion–exclusion
(5.9)–(5.18) in pointwise form). The case `n = 0` gives `1/(1 − x)`, odd `n` do not occur,
and `n ≥ 6` vanish for `x ≥ 1/8`. -/

set_option linter.style.longLine false

open MeasureTheory Finset Real Filter

namespace Palprimes.MT

/-! ## The integrands -/

/-- Integrand of the `(r, t)` term, `a = r − 1`. -/
noncomputable def gP {N : ℕ} (a : ℕ) (x : ℝ) (y : Fin N → ℝ) : ℝ :=
  open Classical in if PReg a x y then 1 / ∏ i, y i else 0

/-- Integrand of `h_{2m}`. -/
noncomputable def gH (m : ℕ) (x : ℝ) (y : Fin (2 * m + 1) → ℝ) : ℝ :=
  open Classical in if HReg m x y then 1 / ∏ i, y i else 0

/-- The simplex integral of the `(r, t)` term: `n + 1` variables, `a` of them in the x-chain. -/
noncomputable def SxP (n a : ℕ) (x : ℝ) : ℝ := ∫ w : Fin n → ℝ, gP a x (zvec (1 - x) w)

/-! ## Measurability -/

lemma measurable_ext_apply {α : Type*} [MeasurableSpace α] {N : ℕ} {f : α → Fin N → ℝ}
    (hf : ∀ i, Measurable fun a => f a i) (k : ℕ) : Measurable fun a => ext (f a) k := by
  unfold ext
  by_cases h : k < N
  · simp only [h, dif_pos]; exact hf _
  · simp only [h, dif_neg, not_false_eq_true]; exact measurable_const

lemma measurable_chainX {α : Type*} [MeasurableSpace α] {L : ℕ} (x : ℝ) {f : α → Fin L → ℝ}
    (hf : ∀ i, Measurable fun a => f a i) (k : ℕ) : Measurable fun a => chainX x (f a) k := by
  unfold chainX
  by_cases h : k < L
  · simp only [h, dif_pos]; exact hf _
  · simp only [h, dif_neg, not_false_eq_true]; exact measurable_const

lemma measurable_condX {α : Type*} [MeasurableSpace α] {L : ℕ} (x : ℝ) {f : α → Fin L → ℝ}
    (hf : ∀ i, Measurable fun a => f a i) (j : ℕ) :
    Measurable fun a => (∑ i ∈ Finset.range (2 * j - 1), chainX x (f a) i) + 3 * chainX x (f a) (2 * j - 1) := by
  have h1 : Measurable fun a => ∑ i ∈ Finset.range (2 * j - 1), chainX x (f a) i :=
    Finset.measurable_sum _ fun i _ => measurable_chainX x hf i
  exact h1.add ((measurable_chainX x hf _).const_mul 3)

lemma measurable_rosserX {α : Type*} [MeasurableSpace α] {L : ℕ} (x : ℝ) {f : α → Fin L → ℝ}
    (hf : ∀ i, Measurable fun a => f a i) : Measurable fun a => RosserX x (f a) := by
  unfold RosserX
  refine Measurable.forall fun j => measurable_const.imp (measurable_const.imp ?_)
  exact measurable_le_fun (measurable_condX x hf j) measurable_const

lemma measurable_hRegion {α : Type*} [MeasurableSpace α] {k : ℕ} (x : ℝ) {f : α → Fin (2 * k) → ℝ}
    (hf : ∀ i, Measurable fun a => f a i) : Measurable fun a => HRegion k x (f a) := by
  unfold HRegion
  refine (measurable_strictAnti_comp hf).and ((Measurable.forall fun i => measurable_lt_fun measurable_const (hf i)).and
    ((Measurable.forall fun i => measurable_lt_fun (hf i) measurable_const).and
    ((Measurable.forall fun j => measurable_const.imp (measurable_const.imp
      (measurable_le_fun (measurable_condX x hf j) measurable_const))).and
    ((measurable_lt_fun measurable_const (measurable_condX x hf k)).and ?_))))
  have h1 : Measurable fun a => ∑ i, f a i := Finset.measurable_sum _ fun i _ => hf i
  exact measurable_lt_fun (measurable_chainX x hf _) (measurable_const.sub h1)

lemma measurable_PReg {N a : ℕ} (x : ℝ) : Measurable fun y : Fin N → ℝ => PReg a x y := by
  have hc : ∀ i : Fin N, Measurable fun y : Fin N → ℝ => y i := fun i => measurable_pi_apply i
  unfold PReg BlockMono
  refine (Measurable.forall fun i => measurable_lt_fun measurable_const (hc i)).and
    ((Measurable.forall fun i => Measurable.forall fun j => measurable_const.imp (measurable_const.imp
      (measurable_const.imp (measurable_lt_fun (measurable_ext_apply hc j) (measurable_ext_apply hc i))))).and ?_)
  exact measurable_rosserX x fun k => measurable_ext_apply hc k

lemma measurable_HReg (m : ℕ) (x : ℝ) : Measurable fun y : Fin (2 * m + 1) → ℝ => HReg m x y := by
  unfold HReg
  exact (Measurable.forall fun i => measurable_lt_fun measurable_const (measurable_pi_apply i)).and
    (measurable_hRegion x fun i => measurable_pi_apply _)

lemma measurable_one_div_prod {N : ℕ} : Measurable fun y : Fin N → ℝ => 1 / ∏ i, y i := by
  have hp : Measurable fun y : Fin N → ℝ => ∏ i, y i := Finset.measurable_prod _ fun i _ => measurable_pi_apply i
  exact measurable_const.div hp

lemma measurable_gP {N a : ℕ} (x : ℝ) : Measurable (gP (N := N) a x) := by
  unfold gP
  exact Measurable.ite (measurableSet_setOfPred.mpr (measurable_PReg x)) measurable_one_div_prod measurable_const

lemma measurable_gH (m : ℕ) (x : ℝ) : Measurable (gH m x) := by
  unfold gH
  exact Measurable.ite (measurableSet_setOfPred.mpr (measurable_HReg m x)) measurable_one_div_prod measurable_const

/-! ## Bounds and integrability -/

lemma one_div_prod_le {N : ℕ} {x : ℝ} (hx : 0 < x) {y : Fin N → ℝ} (hy : ∀ i, x < y i) :
    0 < 1 / ∏ i, y i ∧ 1 / ∏ i, y i ≤ 1 / x ^ N := by
  have hp : 0 < ∏ i, y i := Finset.prod_pos fun i _ => lt_trans hx (hy i)
  refine ⟨by positivity, ?_⟩
  have : x ^ N ≤ ∏ i, y i := by
    have := Finset.prod_le_prod₀ (s := Finset.univ) (f := fun _ => x) (g := y) (h0 := fun i _ => hx.le)
      (h1 := fun i _ => (hy i).le)
    simpa using this
  exact one_div_le_one_div_of_le (by positivity) this

lemma integrable_gP {n a : ℕ} {x : ℝ} (hx : 0 < x) (c : ℝ) : Integrable (gP a x) (smeas c n) := by
  refine integrable_smeas_of_bound hx (measurable_gP x) (C := 1 / x ^ (n + 1)) ?_ ?_
  · intro y
    unfold gP
    split_ifs with h
    · obtain ⟨h1, h2⟩ := one_div_prod_le hx h.1
      rw [abs_of_pos h1]; exact h2
    · simp; positivity
  · intro y hy
    unfold gP at hy
    split_ifs at hy with h
    · exact h.1
    · exact absurd rfl hy

lemma integrable_gH {m : ℕ} {x : ℝ} (hx : 0 < x) (c : ℝ) : Integrable (gH m x) (smeas c (2 * m)) := by
  refine integrable_smeas_of_bound hx (measurable_gH m x) (C := 1 / x ^ (2 * m + 1)) ?_ ?_
  · intro y
    unfold gH
    split_ifs with h
    · obtain ⟨h1, h2⟩ := one_div_prod_le hx h.1
      rw [abs_of_pos h1]; exact h2
    · simp; positivity
  · intro y hy
    unfold gH at hy
    split_ifs at hy with h
    · exact h.1
    · exact absurd rfl hy

/-! ## The pointwise symmetrised identity -/

lemma blk_castSucc {m : ℕ} (z : Fin (2 * m + 1) → ℝ) : blk (2 * m) z = fun i => z i.castSucc := by
  funext i
  simp only [blk, ext]
  rw [dif_pos (by omega)]
  rfl

lemma hReg_iff {m : ℕ} {x : ℝ} (z : Fin (2 * m + 1) → ℝ) :
    HReg m x z ↔ (∀ i, x < z i) ∧ (BlockMono (2 * m) z ∧ HRegion m x (blk (2 * m) z)) := by
  rw [HReg, blk_castSucc]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_, h2⟩
    intro i j hij hj hb
    rcases hb with hb | hb
    · have hi : i < 2 * m := lt_trans hij hb
      simp only [ext, dif_pos hj, dif_pos (lt_trans hij hj)]
      exact h2.1 (show (⟨i, hi⟩ : Fin (2 * m)) < ⟨j, hb⟩ from hij)
    · omega
  · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩

lemma sum_perm_ite_div {N : ℕ} (y : Fin N → ℝ) (P : Equiv.Perm (Fin N) → Prop) [DecidablePred P] :
    ∑ σ : Equiv.Perm (Fin N), (if P σ then 1 / ∏ i, (y ∘ σ) i else 0) =
      ((Finset.univ.filter P).card : ℝ) * (1 / ∏ i, y i) := by
  have : ∀ σ : Equiv.Perm (Fin N), ∏ i, (y ∘ σ) i = ∏ i, y i := fun σ => Equiv.prod_comp σ y
  simp only [this]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]

/-- The alternating sum over `a` of the `n = 2m` simplex integrals is `−h_{2m}`. -/
theorem alt_sum_SxP {m : ℕ} (hm : 1 ≤ m) {x : ℝ} (hx : 0 < x) :
    ∑ a ∈ Finset.range (2 * m + 1), (-1 : ℝ) ^ a * SxP (2 * m) a x +
      ∫ w : Fin (2 * m) → ℝ, gH m x (zvec (1 - x) w) = 0 := by
  classical
  set c := 1 - x with hc
  set μ := smeas c (2 * m)
  have hSx : ∀ a, SxP (2 * m) a x = ∫ y, gP a x y ∂μ := fun a => (integral_smeas c _).symm
  simp only [hSx]
  rw [← integral_smeas c (gH m x)]
  have hiP : ∀ a, Integrable (gP (N := 2 * m + 1) a x) μ := fun a => integrable_gP hx c
  have hiH : Integrable (gH m x) μ := integrable_gH hx c
  set G : (Fin (2 * m + 1) → ℝ) → ℝ := fun y =>
    ∑ a ∈ Finset.range (2 * m + 1), (-1 : ℝ) ^ a * gP a x y + gH m x y with hG
  have hiG : Integrable G μ :=
    (integrable_finsetSum _ fun a _ => (hiP a).const_mul _).add hiH
  have hLG : ∑ a ∈ Finset.range (2 * m + 1), (-1 : ℝ) ^ a * ∫ y, gP a x y ∂μ + ∫ y, gH m x y ∂μ = ∫ y, G y ∂μ := by
    rw [hG, integral_add (integrable_finsetSum _ fun a _ => (hiP a).const_mul _) hiH,
      integral_finsetSum _ fun a _ => (hiP a).const_mul _]
    simp only [integral_const_mul]
  rw [hLG, integral_sort μ (smeas_perm c) (ae_injective_smeas c) hiG]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [ae_smeas_sum c] with y hy
  split_ifs with hSA
  swap
  · rfl
  simp only [Pi.zero_apply]
  -- expand the sum over permutations
  have hexp : ∑ σ : Equiv.Perm (Fin (2 * m + 1)), G (y ∘ σ) =
      (∑ a ∈ Finset.range (2 * m + 1), (-1 : ℝ) ^ a *
        ((Finset.univ.filter fun σ : Equiv.Perm (Fin (2 * m + 1)) => PReg a x (y ∘ σ)).card : ℝ) +
        ((Finset.univ.filter fun σ : Equiv.Perm (Fin (2 * m + 1)) => HReg m x (y ∘ σ)).card : ℝ)) *
      (1 / ∏ i, y i) := by
    simp only [hG, Finset.sum_add_distrib]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, gP, gH, sum_perm_ite_div]
    rw [add_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [hexp]
  by_cases hyx : ∀ i, x < y i
  · have hcomb := rosser_alternating_identity hm hx hSA hyx (by rw [hy, hc]; ring)
    have hP : ∀ a ∈ Finset.range (2 * m + 1),
        (Finset.univ.filter fun σ : Equiv.Perm (Fin (2 * m + 1)) => PReg a x (y ∘ σ)).card =
        (Finset.univ.filter fun A : Finset (Fin (2 * m + 1)) =>
          ∃ h : A.card = a, RosserX x (fun k => y (A.orderEmbOfFin h k))).card := by
      intro a ha
      rw [← card_perm_blockMono hSA (by simp at ha; omega) (fun v => RosserX x v)]
      congr 1
      apply Finset.filter_congr
      intro σ _
      simp only [PReg, Function.comp]
      exact ⟨fun h => h.2, fun h => ⟨fun i => hyx _, h⟩⟩
    have hH : (Finset.univ.filter fun σ : Equiv.Perm (Fin (2 * m + 1)) => HReg m x (y ∘ σ)).card =
        (Finset.univ.filter fun A : Finset (Fin (2 * m + 1)) =>
          ∃ h : A.card = 2 * m, HRegion m x (fun k => y (A.orderEmbOfFin h k))).card := by
      rw [← card_perm_blockMono hSA (by omega) (fun v => HRegion m x v)]
      congr 1
      apply Finset.filter_congr
      intro σ _
      rw [hReg_iff]
      exact ⟨fun h => h.2, fun h => ⟨fun i => hyx _, h⟩⟩
    rw [Finset.sum_congr rfl fun a ha => by rw [hP a ha], hH, hcomb, zero_mul]
  · have hP : ∀ a, (Finset.univ.filter fun σ : Equiv.Perm (Fin (2 * m + 1)) => PReg a x (y ∘ σ)).card = 0 := by
      intro a
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro σ _ h
      apply hyx
      intro i
      have := h.1 (σ.symm i)
      simpa using this
    have hH : (Finset.univ.filter fun σ : Equiv.Perm (Fin (2 * m + 1)) => HReg m x (y ∘ σ)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro σ _ h
      apply hyx
      intro i
      have := h.1 (σ.symm i)
      simpa using this
    simp [hP, hH]

/-! ## `h_{2m}(x, 1)` as a simplex integral -/

lemma hRegion_zvec_gt {m : ℕ} {x : ℝ} {v : Fin (2 * m) → ℝ} (h : HRegion m x v) :
    ∀ i, x < zvec (1 - x) v i := by
  intro i
  induction i using Fin.lastCases with
  | last =>
    simp only [zvec_last]
    have h6 := h.2.2.2.2.2
    have : x ≤ chainX x v (2 * m - 1) := by
      unfold chainX; split_ifs with hlt
      · exact (h.2.1 _).le
      · exact le_rfl
    linarith
  | cast j => simpa using h.2.1 j

theorem hk_eq_gH (m : ℕ) (x : ℝ) : hk m x = ∫ w : Fin (2 * m) → ℝ, gH m x (zvec (1 - x) w) := by
  unfold hk
  congr 1; funext v
  have hiff : HReg m x (zvec (1 - x) v) ↔ HRegion m x v := by
    simp only [HReg, zvec_castSucc]
    exact ⟨fun h => h.2, fun h => ⟨hRegion_zvec_gt h, h⟩⟩
  unfold gH
  by_cases h : HRegion m x v
  · rw [if_pos h, if_pos (hiff.mpr h), prod_zvec]
  · rw [if_neg h, if_neg (fun h' => h (hiff.mp h'))]

/-! ## Scaling `u_i = x v_i` in `I_t` -/

lemma Iint_scale {b : ℕ} {x : ℝ} (hx : 0 < x) (s : ℝ) :
    Iint (b + 1) s = x * ∫ u : Fin b → ℝ, (open Classical in
      if IRegion b s (x⁻¹ • u) then 1 / ((∏ i, u i) * (x * s - ∑ i, u i)) else 0) := by
  classical
  have hx0 : x ≠ 0 := hx.ne'
  have hpt : ∀ u : Fin b → ℝ, Ifun b s (x⁻¹ • u) = x ^ (b + 1) *
      (if IRegion b s (x⁻¹ • u) then 1 / ((∏ i, u i) * (x * s - ∑ i, u i)) else 0) := by
    intro u
    unfold Ifun
    split_ifs with h
    · simp only [lastU, Pi.smul_apply, smul_eq_mul]
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        ← Finset.mul_sum]
      have : s - x⁻¹ * ∑ i, u i = x⁻¹ * (x * s - ∑ i, u i) := by field_simp
      rw [this]
      simp only [one_div, mul_inv, inv_pow, inv_inv]
      ring
    · simp
  have hsc := Measure.integral_comp_smul (μ := (volume : Measure (Fin b → ℝ))) (Ifun b s) x⁻¹
  rw [Module.finrank_fin_fun] at hsc
  simp only [hpt, integral_const_mul] at hsc
  have habs : |((x⁻¹) ^ b)⁻¹| = x ^ b := by rw [inv_pow, inv_inv, abs_of_pos (pow_pos hx b)]
  rw [habs, smul_eq_mul] at hsc
  rw [Iint_succ']
  have hxb : x ^ b ≠ 0 := pow_ne_zero _ hx0
  apply mul_left_cancel₀ hxb
  rw [← hsc]
  ring

/-! ## `k_r(x, 1, G_r)` as a sum of simplex integrals -/

/-- The `t`-range in Lemma 5.1 (with the cut-off `t < 8`, enough for `s < 8`). -/
def Tset (r : ℕ) : Finset ℕ :=
  if Odd r then (Finset.range 8).filter Odd else (Finset.range 8).filter (fun t => Even t ∧ 2 ≤ t)

lemma one_le_of_mem_Tset {r t : ℕ} (ht : t ∈ Tset r) : 1 ≤ t := by
  unfold Tset at ht
  split_ifs at ht
  · simp only [Finset.mem_filter] at ht; exact ht.2.pos
  · simp only [Finset.mem_filter] at ht; omega

lemma Gr_eq_sum {r : ℕ} {s : ℝ} (hs : s < 8) :
    Gr r s = 2 * Real.exp Real.eulerMascheroniConstant * ∑ t ∈ Tset r, Iint t s := by
  unfold Gr Tset
  split_ifs
  · exact Fjr_eq_sum (M := 8) (by norm_num) (by exact_mod_cast hs)
  · exact fjr_eq_sum (M := 8) (by norm_num) (by exact_mod_cast hs)

noncomputable def appendE (a b : ℕ) : (Fin a → ℝ) × (Fin b → ℝ) ≃ᵐ (Fin (a + b) → ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin a ⊕ Fin b => ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ => ℝ) finSumFinEquiv)

lemma appendE_apply (a b : ℕ) (p : (Fin a → ℝ) × (Fin b → ℝ)) : appendE a b p = Fin.append p.1 p.2 := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · rw [Fin.append_left]
    have := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin (a + b) => ℝ) finSumFinEquiv
      ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin a ⊕ Fin b => ℝ)).symm p) (Sum.inl i)
    simp only [finSumFinEquiv_apply_left] at this
    rw [appendE, MeasurableEquiv.trans_apply, this]
    rfl
  · rw [Fin.append_right]
    have := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin (a + b) => ℝ) finSumFinEquiv
      ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin a ⊕ Fin b => ℝ)).symm p) (Sum.inr j)
    simp only [finSumFinEquiv_apply_right] at this
    rw [appendE, MeasurableEquiv.trans_apply, this]
    rfl

lemma measurePreserving_appendE (a b : ℕ) : MeasurePreserving (appendE a b) (volume.prod volume) volume :=
  (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin a ⊕ Fin b => ℝ)).trans
    (volume_measurePreserving_piCongrLeft (fun _ => ℝ) finSumFinEquiv)

lemma forall_fin_iff_ext {N : ℕ} (y : Fin N → ℝ) (P : ℝ → Prop) :
    (∀ i, P (y i)) ↔ ∀ k (_ : k < N), P (ext y k) := by
  constructor
  · intro h k hk; rw [ext, dif_pos hk]; exact h _
  · intro h i; have := h i i.isLt; rwa [ext, dif_pos i.isLt] at this

/-- The pointwise identification of the `(r, t)` integrand after `u_i = x v_i` and Fubini. -/
lemma key_pointwise {a b : ℕ} {x : ℝ} (hx : 0 < x) (v : Fin a → ℝ) (u : Fin b → ℝ) :
    (open Classical in (if KRegion a x v then 1 / ∏ i, v i else 0) *
      (if IRegion b ((1 - x - ∑ i, v i) / x) (x⁻¹ • u) then
        1 / ((∏ i, u i) * (x * ((1 - x - ∑ i, v i) / x) - ∑ i, u i)) else 0)) =
    gP a x (zvec (1 - x) (Fin.append v u)) := by
  classical
  set y := zvec (1 - x) (Fin.append v u) with hy
  set L := 1 - x - ∑ i, v i - ∑ i, u i with hL
  have hx0 : x ≠ 0 := hx.ne'
  have hxs : x * ((1 - x - ∑ i, v i) / x) - ∑ i, u i = L := by field_simp; ring
  have hsumw : ∑ i, Fin.append v u i = ∑ i, v i + ∑ i, u i := by
    rw [Fin.sum_univ_add]; simp [Fin.append_left, Fin.append_right]
  have hylast : y (Fin.last _) = L := by
    rw [hy, zvec_last, hsumw]; ring
  have hprod : ∏ i, y i = (∏ i, v i) * (∏ i, u i) * L := by
    rw [hy, prod_zvec, hsumw, Fin.prod_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [hL]; ring
  have hE1 : ∀ k (hk : k < a), ext y k = v ⟨k, hk⟩ := by
    intro k hk
    rw [ext, dif_pos (by omega)]
    have : (⟨k, by omega⟩ : Fin (a + b + 1)) = (Fin.castAdd b ⟨k, hk⟩).castSucc := Fin.ext rfl
    rw [this, hy, zvec_castSucc, Fin.append_left]
  have hE2 : ∀ j (hj : j < b), ext y (a + j) = u ⟨j, hj⟩ := by
    intro j hj
    rw [ext, dif_pos (by omega)]
    have : (⟨a + j, by omega⟩ : Fin (a + b + 1)) = (Fin.natAdd a ⟨j, hj⟩).castSucc := Fin.ext rfl
    rw [this, hy, zvec_castSucc, Fin.append_right]
  have hE3 : ext y (a + b) = L := by
    rw [ext, dif_pos (by omega)]
    have : (⟨a + b, by omega⟩ : Fin (a + b + 1)) = Fin.last _ := Fin.ext rfl
    rw [this, hylast]
  -- all coordinates `> x`
  have hall : (∀ i, x < y i) ↔ (∀ i, x < v i) ∧ (∀ j, x < u j) ∧ x < L := by
    rw [forall_fin_iff_ext y (fun t => x < t)]
    constructor
    · intro h
      refine ⟨fun i => ?_, fun j => ?_, ?_⟩
      · have := h i (by omega); rwa [hE1 i i.isLt] at this
      · have := h (a + j) (by omega); rwa [hE2 j j.isLt] at this
      · have := h (a + b) (by omega); rwa [hE3] at this
    · rintro ⟨h1, h2, h3⟩ k hk
      by_cases hka : k < a
      · rw [hE1 k hka]; exact h1 _
      · by_cases hkb : k < a + b
        · obtain ⟨j, rfl⟩ : ∃ j, k = a + j := ⟨k - a, by omega⟩
          rw [hE2 j (by omega)]; exact h2 _
        · have : k = a + b := by omega
          rw [this, hE3]; exact h3
  -- block monotonicity
  have hbm : BlockMono a y ↔ StrictAnti v ∧ StrictAnti u ∧ ∀ j, L < u j := by
    constructor
    · intro h
      refine ⟨fun i j hij => ?_, fun i j hij => ?_, fun j => ?_⟩
      · have := h i j hij (by omega) (Or.inl j.isLt)
        rwa [hE1 j j.isLt, hE1 i i.isLt] at this
      · have := h (a + i) (a + j) (by have : i.val < j.val := hij; omega) (by omega) (Or.inr (by omega))
        rwa [hE2 j j.isLt, hE2 i i.isLt] at this
      · have := h (a + j) (a + b) (by omega) (by omega) (Or.inr (by omega))
        rwa [hE3, hE2 j j.isLt] at this
    · rintro ⟨hv, hu, hLu⟩ i j hij hj hb
      rcases hb with hb | hb
      · rw [hE1 j hb, hE1 i (by omega)]
        exact hv (show (⟨i, by omega⟩ : Fin a) < ⟨j, hb⟩ from hij)
      · obtain ⟨i', rfl⟩ : ∃ i', i = a + i' := ⟨i - a, by omega⟩
        by_cases hjb : j < a + b
        · obtain ⟨j', rfl⟩ : ∃ j', j = a + j' := ⟨j - a, by omega⟩
          rw [hE2 j' (by omega), hE2 i' (by omega)]
          exact hu (show (⟨i', by omega⟩ : Fin b) < ⟨j', by omega⟩ from by
            rw [Fin.lt_def]; simp only; omega)
        · have : j = a + b := by omega
          rw [this, hE3, hE2 i' (by omega)]
          exact hLu _
  -- the scaled `I`-region
  have hir : IRegion b ((1 - x - ∑ i, v i) / x) (x⁻¹ • u) ↔
      StrictAnti u ∧ (∀ j, x < u j) ∧ x < L ∧ ∀ j, L < u j := by
    have hsc : ∀ j, (x⁻¹ • u) j = u j / x := fun j => by simp [div_eq_inv_mul]
    have hlast : lastU ((1 - x - ∑ i, v i) / x) (x⁻¹ • u) = L / x := by
      simp only [lastU, hsc, ← Finset.sum_div, hL]; field_simp
    simp only [IRegion, hlast, hsc]
    have hSA : StrictAnti (fun j => u j / x) ↔ StrictAnti u := by
      constructor
      · intro h i j hij; have := h hij; exact (div_lt_div_iff_of_pos_right hx).mp this
      · intro h i j hij; exact (div_lt_div_iff_of_pos_right hx).mpr (h hij)
    have hfun : (x⁻¹ • u) = fun j => u j / x := funext hsc
    rw [hfun, hSA]
    simp only [one_lt_div hx, div_lt_div_iff_of_pos_right hx]
  have hblk : blk a y = v := by
    funext k; exact hE1 k k.isLt
  have hiff : PReg a x y ↔ KRegion a x v ∧ IRegion b ((1 - x - ∑ i, v i) / x) (x⁻¹ • u) := by
    rw [PReg, hall, hbm, hir, hblk, KRegion]
    tauto
  rw [hxs]
  unfold gP
  by_cases hK : KRegion a x v
  · by_cases hI : IRegion b ((1 - x - ∑ i, v i) / x) (x⁻¹ • u)
    · rw [if_pos hK, if_pos hI, if_pos (hiff.mpr ⟨hK, hI⟩), hprod, one_div_mul_one_div, mul_assoc]
    · rw [if_neg hI, if_neg (fun h => hI (hiff.mp h).2), mul_zero]
  · rw [if_neg hK, if_neg (fun h => hK (hiff.mp h).1), zero_mul]

/-- One `t`-term of `k_r`. -/
lemma kr_term (a b : ℕ) {x : ℝ} (hx : 0 < x) :
    Integrable (fun v : Fin a → ℝ => (open Classical in if KRegion a x v then 1 / ∏ i, v i else 0) *
      Iint (b + 1) ((1 - x - ∑ i, v i) / x)) ∧
    ∫ v : Fin a → ℝ, (open Classical in if KRegion a x v then 1 / ∏ i, v i else 0) *
      Iint (b + 1) ((1 - x - ∑ i, v i) / x) = x * SxP (a + b) a x := by
  classical
  set F : (Fin a → ℝ) → (Fin b → ℝ) → ℝ := fun v u =>
    (if KRegion a x v then 1 / ∏ i, v i else 0) *
      (if IRegion b ((1 - x - ∑ i, v i) / x) (x⁻¹ • u) then
        1 / ((∏ i, u i) * (x * ((1 - x - ∑ i, v i) / x) - ∑ i, u i)) else 0) with hF
  have hrep : ∀ v : Fin a → ℝ, (if KRegion a x v then 1 / ∏ i, v i else 0) *
      Iint (b + 1) ((1 - x - ∑ i, v i) / x) = x * ∫ u, F v u := by
    intro v
    rw [Iint_scale hx, hF]
    simp only
    rw [integral_const_mul]
    ring
  have hFG : ∀ p : (Fin a → ℝ) × (Fin b → ℝ), F p.1 p.2 = gP a x (zvec (1 - x) (appendE a b p)) := by
    intro p
    rw [appendE_apply, hF]
    exact key_pointwise hx p.1 p.2
  have hint : Integrable (fun p : (Fin a → ℝ) × (Fin b → ℝ) => F p.1 p.2) (volume.prod volume) := by
    have h0 : Integrable (fun w : Fin (a + b) → ℝ => gP a x (zvec (1 - x) w)) :=
      (integrable_smeas_iff (1 - x)).mp (integrable_gP hx (1 - x))
    have := ((measurePreserving_appendE a b).integrable_comp_emb
      (appendE a b).measurableEmbedding).mpr h0
    convert this using 1
    funext p
    exact hFG p
  refine ⟨?_, ?_⟩
  · simp_rw [hrep]
    exact hint.integral_prod_left.const_mul x
  · simp_rw [hrep]
    rw [integral_const_mul]
    congr 1
    rw [← integral_prod (fun p : (Fin a → ℝ) × (Fin b → ℝ) => F p.1 p.2) hint]
    simp_rw [hFG]
    exact (measurePreserving_appendE a b).integral_comp' (fun w => gP a x (zvec (1 - x) w))

/-- Greaves p. 318: `k_r(x, G_r) = 2e^γ x Σ_t {x = x_r < ⋯ < x_1; x < u_t < ⋯ < u_1}`. -/
theorem kr_eq_sum {a : ℕ} {x : ℝ} (hx8 : 1 / 8 ≤ x) (hx2 : x ≤ 1 / 2) :
    kr (a + 1) x = 2 * Real.exp Real.eulerMascheroniConstant * x *
      ∑ t ∈ Tset (a + 1), SxP (a + (t - 1)) a x := by
  classical
  have hx : 0 < x := by linarith
  set K : (Fin a → ℝ) → ℝ := fun v => if KRegion a x v then 1 / ∏ i, v i else 0 with hK
  have h1 : kr (a + 1) x = ∫ v : Fin a → ℝ, ∑ t ∈ Tset (a + 1),
      2 * Real.exp Real.eulerMascheroniConstant * (K v * Iint t ((1 - x - ∑ i, v i) / x)) := by
    rw [kr, if_neg (Nat.succ_ne_zero a)]
    show ∫ v : Fin a → ℝ, (if KRegion a x v then Gr (a + 1) ((1 - x - ∑ i, v i) / x) / (∏ i, v i) else 0) = _
    congr 1; funext v
    by_cases hKv : KRegion a x v
    · have hs8 : (1 - x - ∑ i, v i) / x < 8 := by
        have hpos : 0 ≤ ∑ i, v i := Finset.sum_nonneg fun i _ => (lt_trans hx (hKv.2.1 i)).le
        rw [div_lt_iff₀ hx]; linarith
      rw [if_pos hKv, Gr_eq_sum hs8, Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [hK, if_pos hKv]
      ring
    · simp [hK, hKv]
  rw [h1]
  have hterm : ∀ t ∈ Tset (a + 1),
      Integrable (fun v : Fin a → ℝ => K v * Iint t ((1 - x - ∑ i, v i) / x)) ∧
      ∫ v : Fin a → ℝ, K v * Iint t ((1 - x - ∑ i, v i) / x) = x * SxP (a + (t - 1)) a x := by
    intro t ht
    obtain ⟨b, rfl⟩ : ∃ b, t = b + 1 := ⟨t - 1, by have := one_le_of_mem_Tset ht; omega⟩
    simpa [hK] using kr_term a b hx
  rw [integral_finsetSum _ fun t ht => (hterm t ht).1.const_mul _, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [integral_const_mul, (hterm t ht).2]
  ring

/-! ## Vanishing for `x ≥ 1/8` and the term `n = 0` -/

theorem kr_eq_zero {r : ℕ} {x : ℝ} (hx8 : 1 / 8 ≤ x) (hr : 9 ≤ r) : kr r x = 0 := by
  classical
  have hx : 0 < x := by linarith
  rw [kr, if_neg (by omega)]
  refine integral_eq_zero_of_ae (ae_of_all _ fun v => ?_)
  simp only [Pi.zero_apply]
  split_ifs with hK
  · have hsum : ((r - 1 : ℕ) : ℝ) * x ≤ ∑ i, v i := by
      have := Finset.sum_le_sum (s := Finset.univ) (fun i _ => (hK.2.1 i).le)
      simpa [mul_comm] using this
    have hr' : (8 : ℝ) ≤ ((r - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 8 ≤ r - 1)
    have hneg : (1 - x - ∑ i, v i) / x ≤ 1 := by
      rw [div_le_iff₀ hx]; nlinarith
    have : Gr r ((1 - x - ∑ i, v i) / x) = 0 := by
      unfold Gr
      split_ifs
      · exact Fjr_le_one hneg
      · exact fjr_le_two (by linarith)
    rw [this, zero_div]
  · rfl

theorem hk_eq_zero {k : ℕ} {x : ℝ} (hx8 : 1 / 8 ≤ x) (hk3 : 3 ≤ k) : hk k x = 0 := by
  classical
  unfold hk
  refine integral_eq_zero_of_ae (ae_of_all _ fun v => ?_)
  simp only [Pi.zero_apply]
  split_ifs with h
  · exfalso
    have hl := hRegion_zvec_gt h (Fin.last _)
    simp only [zvec_last] at hl
    have hsum : ((2 * k : ℕ) : ℝ) * x ≤ ∑ i, v i := by
      have := Finset.sum_le_sum (s := Finset.univ) (fun i _ => (h.2.1 i).le)
      simpa [mul_comm] using this
    have hk' : (6 : ℝ) ≤ ((2 * k : ℕ) : ℝ) := by exact_mod_cast (by omega : 6 ≤ 2 * k)
    nlinarith
  · rfl

theorem SxP_eq_zero {n a : ℕ} {x : ℝ} (hx8 : 1 / 8 ≤ x) (hn : 6 ≤ n) : SxP n a x = 0 := by
  have hx : 0 < x := by linarith
  unfold SxP
  refine integral_eq_zero_of_ae (ae_of_all _ fun w => ?_)
  simp only [Pi.zero_apply, gP]
  split_ifs with h
  · exfalso
    have hs := sum_zvec (1 - x) w
    have hlt : ∑ _i : Fin (n + 1), x < ∑ i, zvec (1 - x) w i :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => h.1 i
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlt
    have hn' : (6 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    push_cast at hlt
    nlinarith
  · rfl

theorem SxP_zero_zero {x : ℝ} (hx : 0 < x) (hx2 : x < 1 / 2) : SxP 0 0 x = 1 / (1 - x) := by
  unfold SxP
  rw [integral_fin_zero]
  have hreg : PReg 0 x (zvec (1 - x) Fin.elim0) := by
    refine ⟨fun i => ?_, fun i j hij hj _ => by omega, fun j _ hj => by omega⟩
    have : i = Fin.last 0 := Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
    rw [this, zvec_last]; simp; linarith
  simp only [gP, if_pos hreg, prod_zvec]
  simp

/-! ## Assembly -/

lemma Tset_odd {r : ℕ} (hr : Odd r) : Tset r = {1, 3, 5, 7} := by
  unfold Tset; rw [if_pos hr]; decide

lemma Tset_even {r : ℕ} (hr : ¬ Odd r) : Tset r = {2, 4, 6} := by
  unfold Tset; rw [if_neg hr]; decide

lemma sum_1357 (f : ℕ → ℝ) : ∑ t ∈ ({1, 3, 5, 7} : Finset ℕ), f t = f 1 + f 3 + f 5 + f 7 := by
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_pair (by decide)]; ring

lemma sum_246 (f : ℕ → ℝ) : ∑ t ∈ ({2, 4, 6} : Finset ℕ), f t = f 2 + f 4 + f 6 := by
  rw [Finset.sum_insert (by decide), Finset.sum_pair (by decide)]; ring

/-- The alternating sum, with the `n = 0` term `SxP 0 0 x` left unevaluated (valid on `[1/8, 1/2]`). -/
theorem alt_sum_kr_general {x : ℝ} (hx8 : 1 / 8 ≤ x) (hx2 : x ≤ 1 / 2) :
    ∑ r ∈ Finset.Icc 1 8, (-1 : ℝ) ^ (r + 1) * kr r x =
      2 * Real.exp Real.eulerMascheroniConstant * x * (SxP 0 0 x - hk 1 x - hk 2 x) := by
  have hx : 0 < x := by linarith
  set C := 2 * Real.exp Real.eulerMascheroniConstant * x with hC
  have hz : ∀ n a, 6 ≤ n → SxP n a x = 0 := fun n a hn => SxP_eq_zero hx8 hn
  have k1 : kr 1 x = C * (SxP 0 0 x + SxP 2 0 x + SxP 4 0 x) := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, kr_eq_sum hx8 hx2, Tset_odd (by decide), sum_1357]
    norm_num [hz 6 0 (by norm_num)]
    try exact Or.inl hC.symm
  have k2 : kr 2 x = C * (SxP 2 1 x + SxP 4 1 x) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, kr_eq_sum hx8 hx2, Tset_even (by decide), sum_246]
    norm_num [hz 6 1 (by norm_num)]
    try exact Or.inl hC.symm
  have k3 : kr 3 x = C * (SxP 2 2 x + SxP 4 2 x) := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, kr_eq_sum hx8 hx2, Tset_odd (by decide), sum_1357]
    norm_num [hz 6 2 (by norm_num), hz 8 2 (by norm_num)]
    try exact Or.inl hC.symm
  have k4 : kr 4 x = C * SxP 4 3 x := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, kr_eq_sum hx8 hx2, Tset_even (by decide), sum_246]
    norm_num [hz 6 3 (by norm_num), hz 8 3 (by norm_num)]
    try exact Or.inl hC.symm
  have k5 : kr 5 x = C * SxP 4 4 x := by
    rw [show (5 : ℕ) = 4 + 1 from rfl, kr_eq_sum hx8 hx2, Tset_odd (by decide), sum_1357]
    norm_num [hz 6 4 (by norm_num), hz 8 4 (by norm_num), hz 10 4 (by norm_num)]
    try exact Or.inl hC.symm
  have k6 : kr 6 x = 0 := by
    rw [show (6 : ℕ) = 5 + 1 from rfl, kr_eq_sum hx8 hx2, Tset_even (by decide), sum_246]
    norm_num [hz 6 5 (by norm_num), hz 8 5 (by norm_num), hz 10 5 (by norm_num)]
  have k7 : kr 7 x = 0 := by
    rw [show (7 : ℕ) = 6 + 1 from rfl, kr_eq_sum hx8 hx2, Tset_odd (by decide), sum_1357]
    norm_num [hz 6 6 (by norm_num), hz 8 6 (by norm_num), hz 10 6 (by norm_num), hz 12 6 (by norm_num)]
  have k8 : kr 8 x = 0 := by
    rw [show (8 : ℕ) = 7 + 1 from rfl, kr_eq_sum hx8 hx2, Tset_even (by decide), sum_246]
    norm_num [hz 8 7 (by norm_num), hz 10 7 (by norm_num), hz 12 7 (by norm_num)]
  have e2 := alt_sum_SxP (m := 1) le_rfl hx
  rw [← hk_eq_gH] at e2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at e2
  norm_num at e2
  have e4 := alt_sum_SxP (m := 2) (by norm_num) hx
  rw [← hk_eq_gH] at e4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at e4
  norm_num at e4
  rw [Finset.sum_Icc_succ_top (by norm_num), Finset.sum_Icc_succ_top (by norm_num),
    Finset.sum_Icc_succ_top (by norm_num), Finset.sum_Icc_succ_top (by norm_num),
    Finset.sum_Icc_succ_top (by norm_num), Finset.sum_Icc_succ_top (by norm_num),
    Finset.sum_Icc_succ_top (by norm_num), Finset.Icc_self, Finset.sum_singleton]
  norm_num
  rw [k1, k2, k3, k4, k5, k6, k7, k8]
  linear_combination C * (e2 + e4)

/-- **Greaves, Lemma 5.2** (for `1/8 ≤ x < 1/2`, where `h = h_2 + h_4`). -/
theorem lemma52 {x : ℝ} (hx8 : 1 / 8 ≤ x) (hx2 : x < 1 / 2) :
    ∑ r ∈ Finset.Icc 1 8, (-1 : ℝ) ^ (r + 1) * kr r x =
      2 * Real.exp Real.eulerMascheroniConstant * x * (1 / (1 - x) - hk 1 x - hk 2 x) := by
  rw [alt_sum_kr_general hx8 hx2.le, SxP_zero_zero (by linarith) hx2]

/-- At the endpoint `x = 1/2` the identity fails with the definitions of `Defs.lean`:
`Fjr 1 = 0` there (strict `1 < u_t` in `I_1`), while Greaves has `F(1) = 2e^γ`. -/
theorem lemma52_fails_at_half :
    ∑ r ∈ Finset.Icc 1 8, (-1 : ℝ) ^ (r + 1) * kr r (1 / 2) = 0 ∧
    2 * Real.exp Real.eulerMascheroniConstant * (1 / 2) * (1 / (1 - 1 / 2) - hk 1 (1 / 2) - hk 2 (1 / 2)) =
      2 * Real.exp Real.eulerMascheroniConstant := by
  have hS : SxP 0 0 (1 / 2) = 0 := by
    unfold SxP
    rw [integral_fin_zero]
    have : ¬ PReg 0 (1 / 2) (zvec (1 - 1 / 2) Fin.elim0) := by
      intro h; have := h.1 (Fin.last 0); rw [zvec_last] at this; norm_num at this
    simp only [gP, if_neg this]
  have h1 : hk 1 (1 / 2) = 0 := by
    rw [hk_eq_gH]
    refine integral_eq_zero_of_ae (ae_of_all _ fun w => ?_)
    simp only [Pi.zero_apply, gH]
    split_ifs with h
    · exfalso
      have hs := sum_zvec (1 - 1 / 2) w
      have hlt : ∑ _i : Fin (2 * 1 + 1), (1 / 2 : ℝ) < ∑ i, zvec (1 - 1 / 2) w i :=
        Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => h.1 i
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlt
      push_cast at hlt; linarith
    · rfl
  have h2 : hk 2 (1 / 2) = 0 := by
    rw [hk_eq_gH]
    refine integral_eq_zero_of_ae (ae_of_all _ fun w => ?_)
    simp only [Pi.zero_apply, gH]
    split_ifs with h
    · exfalso
      have hs := sum_zvec (1 - 1 / 2) w
      have hlt : ∑ _i : Fin (2 * 2 + 1), (1 / 2 : ℝ) < ∑ i, zvec (1 - 1 / 2) w i :=
        Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => h.1 i
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlt
      push_cast at hlt; linarith
    · rfl
  refine ⟨?_, ?_⟩
  · rw [alt_sum_kr_general (by norm_num) le_rfl, hS, h1, h2]; ring
  · rw [h1, h2]; ring

/-- `k_r(x) = 0` for `r ≥ 9` and `h_{2k}(x, 1) = 0` for `k ≥ 3` when `x ≥ 1/8` (restated). -/
theorem kr_hk_vanish {x : ℝ} (hx8 : 1 / 8 ≤ x) :
    (∀ r, 9 ≤ r → kr r x = 0) ∧ (∀ k, 3 ≤ k → hk k x = 0) :=
  ⟨fun _ hr => kr_eq_zero hx8 hr, fun _ hk => hk_eq_zero hx8 hk⟩

end Palprimes.MT
