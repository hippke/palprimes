import Omega3.Statements
import Palprimes.Sieve.SelbergSum

/-!
# S05: the route's weight satisfies (1.8), (3.10) for odd ν ≥ 3, Lemma 4 (iii), φ ≥ 0 on 𝒟

Plan in `S05_PLAN.md`. With `t_p = log p/log y`, `W1 = U − m = 1 − 3m`: the conjuncts 6 and 7 follow from `key`
(the Jurkat–Richert condition of `δ/p(δ)` applied to the product of the prime factors of `δ/p(δ)` with `t_p > m`).
-/

namespace Omega3

open Finset Palprimes Palprimes.Greaves
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius

set_option linter.style.longLine false

namespace S05

lemma mem (y : ℝ) (δ : ℕ) (h : δ ∈ Dset y (y ^ UU) mm) :
    δ ∣ primorialLt (y ^ UU) ∧ δ ≠ 1 ∧ chibar y mm δ = 1 ∧ Odd (ω δ) ∧ (ω δ : ℝ) ≤ 1 / mm := by
  classical
  unfold Dset at h
  rw [Finset.mem_filter, Nat.mem_divisors] at h
  exact ⟨h.1.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

lemma chi_of (y m : ℝ) (δ : ℕ) (h1 : δ ≠ 1) (h : chibar y m δ = 1) :
    chiProp y m (δ / δ.minFac) := by
  classical
  unfold chibar at h
  rw [if_neg h1] at h
  unfold chi at h
  by_contra ha
  by_cases hb : chiProp y m δ
  · simp [ha, hb] at h; norm_num at h
  · simp [ha, hb] at h

lemma primorial_sqf (z : ℝ) (δ : ℕ) (h : δ ∣ primorialLt z) : Squarefree δ :=
  (SelbergPort.prod_primes_squarefree (primesBelow z) (fun p hp => ((mem_primesBelow z p).1 hp).1)).squarefree_of_dvd h

lemma primorial_ne_zero (z : ℝ) : primorialLt z ≠ 0 := by
  unfold primorialLt
  exact Finset.prod_ne_zero_iff.2 (fun p hp => ((mem_primesBelow _ p).1 hp).1.ne_zero)

lemma minFac_prod {E : Finset ℕ} (hE : ∀ p ∈ E, p.Prime) (q : ℕ) (hq : q ∈ E) (hmin : ∀ x ∈ E, q ≤ x) :
    (∏ p ∈ E, p).minFac = q := by
  have h1 : (∏ p ∈ E, p) ≠ 1 := by
    intro h
    have := Finset.dvd_prod_of_mem (fun p => p) hq
    rw [h] at this
    exact (hE q hq).ne_one (Nat.dvd_one.1 this)
  have hpos : 0 < ∏ p ∈ E, p := Finset.prod_pos (fun p hp => (hE p hp).pos)
  apply le_antisymm
  · exact Nat.minFac_le_of_dvd (hE q hq).two_le (Finset.dvd_prod_of_mem _ hq)
  · have hmem : (∏ p ∈ E, p).minFac ∈ (∏ p ∈ E, p).primeFactors :=
      Nat.mem_primeFactors.2 ⟨Nat.minFac_prime h1, Nat.minFac_dvd _, hpos.ne'⟩
    rw [Nat.primeFactors_prod hE] at hmem
    exact hmin _ hmem

/-! ## The weight -/

lemma W_zero (t : ℝ) (h : t ≤ mm) : Wf t = 0 := by
  unfold Wf; rw [if_pos h]

lemma W_lin (t : ℝ) (h : mm < t) : Wf t ≤ t - mm := by
  unfold Wf
  rw [if_neg (not_le.2 h)]
  split_ifs with h1 h2
  · exact min_le_right _ _
  · exact le_rfl
  · unfold W1 mm UU at *; push Not at h2; linarith

lemma W_nonneg (t : ℝ) : 0 ≤ Wf t := by
  unfold Wf
  split_ifs with h1 h2 h3
  · exact le_rfl
  · exact le_min (by unfold kSq; positivity) (by linarith)
  · linarith
  · unfold W1; norm_num

lemma W_le (t : ℝ) : Wf t ≤ W1 := by
  unfold Wf
  split_ifs with h1 h2 h3
  · unfold W1; norm_num
  · exact (min_le_right _ _).trans (by unfold W1 mm at *; linarith)
  · unfold W1 mm UU at *; linarith
  · exact le_rfl

lemma W_bound (s a : ℝ) (hs : s < a) (ha : mm < a) : Wf s ≤ a - mm := by
  by_cases h : s ≤ mm
  · rw [W_zero s h]; linarith
  · have := W_lin s (not_le.1 h); linarith

lemma W1_eq : W1 = 1 - 3 * mm := by unfold W1 mm; norm_num

lemma arith (G : Finset ℕ) (t : ℕ → ℝ) (a0 : ℕ) (ha0 : a0 ∈ G) (hG : ∀ p ∈ G, mm < t p)
    (hsum : ∑ p ∈ G, t p + 2 * t a0 < 1) (u1 u2 : ℝ) (hu1 : u1 ≤ t a0 - mm) (hu2 : u2 ≤ t a0 - mm) :
    u1 + u2 + ∑ p ∈ G, Wf (t p) ≤ W1 := by
  have h1 : ∑ p ∈ G, Wf (t p) ≤ ∑ p ∈ G, (t p - mm) := Finset.sum_le_sum (fun p hp => W_lin _ (hG p hp))
  have h2 : ∑ p ∈ G, (t p - mm) = ∑ p ∈ G, t p - G.card * mm := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  have h3 : (1 : ℝ) ≤ G.card := by exact_mod_cast Finset.card_pos.2 ⟨a0, ha0⟩
  have hm : 0 < mm := by unfold mm; norm_num
  have h4 : mm ≤ (G.card : ℝ) * mm := by nlinarith
  rw [W1_eq]
  linarith

/-- The Jurkat–Richert condition on `δ'` applied to `Π G` for `G ⊆` prime factors of `δ'`. -/
lemma good (y : ℝ) (hy : 1 < y) (δ' : ℕ) (hδ'0 : δ' ≠ 0) (hc : chiProp y mm δ') (G : Finset ℕ)
    (hGsub : G ⊆ δ'.primeFactors) (a0 : ℕ) (ha0 : a0 ∈ G) (hmin : ∀ p ∈ G, a0 ≤ p)
    (hpar : Even G.card ∨ (G.card : ℝ) ≤ 1 / mm) :
    ∑ p ∈ G, Real.log p / Real.log y + 2 * (Real.log a0 / Real.log y) < 1 := by
  have hP : ∀ p ∈ G, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hGsub hp)
  have hly : 0 < Real.log y := Real.log_pos hy
  have hdvd : (∏ p ∈ G, p) ∣ δ' :=
    (Finset.prod_dvd_prod_of_subset _ _ (fun p => p) hGsub).trans (Nat.prod_primeFactors_dvd δ')
  have hpf : (∏ p ∈ G, p).primeFactors = G := Nat.primeFactors_prod hP
  have hne1 : (∏ p ∈ G, p) ≠ 1 := by
    intro h
    rw [h, Nat.primeFactors_one] at hpf
    rw [← hpf] at ha0; simp at ha0
  have hω : ω (∏ p ∈ G, p) = G.card := by
    rw [ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors, hpf]
  have hmf := minFac_prod hP a0 ha0 hmin
  have key := hc (∏ p ∈ G, p) (Nat.mem_divisors.2 ⟨hdvd, hδ'0⟩) hne1 (by rw [hω]; exact hpar)
  rw [hmf] at key
  have hpos : ∀ p ∈ G, (0 : ℝ) < p := fun p hp => by exact_mod_cast (hP p hp).pos
  have ha0pos : (0 : ℝ) < a0 := hpos a0 ha0
  have hprodpos : (0 : ℝ) < ((∏ p ∈ G, p : ℕ) : ℝ) := by
    rw [Nat.cast_prod]; exact Finset.prod_pos hpos
  have hlog := Real.log_lt_log (by positivity) key
  rw [Real.log_mul hprodpos.ne' (by positivity), Real.log_pow, Nat.cast_prod,
    Real.log_prod (fun p hp => (hpos p hp).ne')] at hlog
  rw [← Finset.sum_div, mul_div_assoc', ← add_div, div_lt_one hly]
  push_cast at hlog
  linarith

lemma tlt (y : ℝ) (hy : 1 < y) {a b : ℕ} (ha : 0 < a) (hab : a < b) :
    Real.log a / Real.log y < Real.log b / Real.log y :=
  (div_lt_div_iff_of_pos_right (Real.log_pos hy)).2
    (Real.log_lt_log (by exact_mod_cast ha) (by exact_mod_cast hab))

/-- Main lemma for conjuncts 6 and 7. -/
lemma key (y : ℝ) (hy : 1 < y) (δ : ℕ) (hsq : Squarefree δ) (h1 : δ ≠ 1)
    (hc1 : chiProp y mm (δ / δ.minFac)) (u : ℝ)
    (hu : ∀ a : ℝ, mm < a → Real.log δ.minFac / Real.log y < a → u ≤ a - mm)
    (hus : Real.log δ.minFac / Real.log y ≤ mm → u = 0)
    (hq : 2 ≤ δ.primeFactors.card ∨ u = 0) (h85 : (δ.primeFactors.card : ℝ) ≤ 1 / mm ∨ u = 0) :
    u + ∑ p ∈ δ.primeFactors, wy y p ≤ W1 := by
  classical
  set t : ℕ → ℝ := fun p => Real.log p / Real.log y with htdef
  have hwy : ∀ p, wy y p = Wf (t p) := fun p => rfl
  set p1 := δ.minFac with hp1def
  set δ' := δ / p1 with hδ'def
  have hp1 : p1.Prime := Nat.minFac_prime h1
  have hδ0 : δ ≠ 0 := hsq.ne_zero
  have hδ : δ = p1 * δ' := (Nat.mul_div_cancel' (Nat.minFac_dvd δ)).symm
  have hδ'0 : δ' ≠ 0 := by intro h; rw [h, mul_zero] at hδ; exact hδ0 hδ
  have hnd : ¬ p1 ∣ δ' := by
    intro hd
    have : p1 * p1 ∣ δ := by rw [hδ]; exact Nat.mul_dvd_mul_left p1 hd
    exact hp1.one_lt.ne' (Nat.isUnit_iff.1 (hsq p1 this))
  have hpf : δ.primeFactors = insert p1 δ'.primeFactors := by
    rw [hδ, Nat.primeFactors_mul hp1.ne_zero hδ'0, hp1.primeFactors, Finset.insert_eq]
  have hp1n : p1 ∉ δ'.primeFactors := fun h => hnd (Nat.dvd_of_mem_primeFactors h)
  have hlt : ∀ p ∈ δ'.primeFactors, p1 < p := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd : p ∣ δ := (Nat.dvd_of_mem_primeFactors hp).trans (by rw [hδ]; exact Dvd.intro_left p1 rfl)
    have hle : p1 ≤ p := Nat.minFac_le_of_dvd hpp.two_le hpd
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exact absurd (h ▸ Nat.dvd_of_mem_primeFactors hp) hnd
  have htlt : ∀ p ∈ δ'.primeFactors, t p1 < t p := fun p hp => tlt y hy hp1.pos (hlt p hp)
  have hcardle : δ'.primeFactors.card ≤ δ.primeFactors.card := by
    rw [hpf]; exact Finset.card_le_card (Finset.subset_insert _ _)
  rw [hpf, Finset.sum_insert hp1n]
  set F := δ'.primeFactors.filter (fun p => mm < t p) with hFdef
  have hsF : ∑ p ∈ δ'.primeFactors, wy y p = ∑ p ∈ F, Wf (t p) := by
    rw [← Finset.sum_filter_add_sum_filter_not δ'.primeFactors (fun p => mm < t p)]
    have : ∑ p ∈ δ'.primeFactors.filter (fun p => ¬ mm < t p), wy y p = 0 :=
      Finset.sum_eq_zero (fun p hp => by
        rw [Finset.mem_filter] at hp
        rw [hwy]; exact W_zero _ (not_lt.1 hp.2))
    rw [this, add_zero]
    exact Finset.sum_congr rfl (fun p _ => hwy p)
  rw [hsF, hwy]
  have hFsub : F ⊆ δ'.primeFactors := Finset.filter_subset _ _
  have hFm : ∀ p ∈ F, mm < t p := fun p hp => (Finset.mem_filter.1 hp).2
  have hc' : chiProp y mm δ' := hc1
  rcases Finset.eq_empty_or_nonempty F with hF | hF
  · rw [hF, Finset.sum_empty, add_zero]
    by_cases ht1 : t p1 ≤ mm
    · rw [hus ht1, W_zero _ ht1]; unfold W1; norm_num
    · -- all prime factors of `δ'` would lie in `F`, so `δ' = 1`
      have hempty : δ'.primeFactors = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro p hp
        have : p ∈ F := Finset.mem_filter.2 ⟨hp, lt_trans (not_le.1 ht1) (htlt p hp)⟩
        rw [hF] at this; simp at this
      have hc1' : δ.primeFactors.card = 1 := by rw [hpf, hempty]; simp
      have hu0 : u = 0 := hq.resolve_left (by omega)
      rw [hu0, zero_add]; exact W_le _
  · set a0 := F.min' hF with ha0def
    have ha0 : a0 ∈ F := Finset.min'_mem F hF
    have ha0min : ∀ p ∈ F, a0 ≤ p := fun p hp => Finset.min'_le F p hp
    have hcardF : F.card ≤ δ.primeFactors.card := (Finset.card_le_card hFsub).trans hcardle
    by_cases hpar : Even F.card ∨ (F.card : ℝ) ≤ 1 / mm
    · have hg := good y hy δ' hδ'0 hc' F hFsub a0 ha0 ha0min hpar
      have hg' : ∑ p ∈ F, t p + 2 * t a0 < 1 := hg
      have hta0 := hFm a0 ha0
      have hu1 : Wf (t p1) ≤ t a0 - mm := W_bound _ _ (htlt a0 (hFsub ha0)) hta0
      have hu2 : u ≤ t a0 - mm := hu _ hta0 (htlt a0 (hFsub ha0))
      have := arith F t a0 ha0 hFm hg' (Wf (t p1)) u hu1 hu2
      linarith
    · -- `|F|` odd and `> 85`: then `u = 0`; drop `a0`
      push Not at hpar
      obtain ⟨hodd, hbig⟩ := hpar
      have hu0 : u = 0 := by
        rcases h85 with h | h
        · exfalso
          have : (F.card : ℝ) ≤ δ.primeFactors.card := by exact_mod_cast hcardF
          linarith
        · exact h
      have hmm : (1 : ℝ) / mm = 85 := by unfold mm; norm_num
      have hF2 : 2 ≤ F.card := by
        have : (85 : ℝ) < F.card := by rw [← hmm]; exact hbig
        have : 85 < F.card := by exact_mod_cast this
        omega
      set G := F.erase a0 with hGdef
      have hGcard : G.card = F.card - 1 := Finset.card_erase_of_mem ha0
      have hGne : G.Nonempty := by
        rw [← Finset.card_pos, hGcard]; omega
      set a1 := G.min' hGne with ha1def
      have ha1 : a1 ∈ G := Finset.min'_mem G hGne
      have ha1min : ∀ p ∈ G, a1 ≤ p := fun p hp => Finset.min'_le G p hp
      have hGsub : G ⊆ F := Finset.erase_subset _ _
      have hGeven : Even G.card := by
        rw [hGcard]
        obtain ⟨k, hk⟩ := hodd
        exact ⟨k, by omega⟩
      have hg := good y hy δ' hδ'0 hc' G (hGsub.trans hFsub) a1 ha1 ha1min (Or.inl hGeven)
      have hg' : ∑ p ∈ G, t p + 2 * t a1 < 1 := hg
      have hta1 := hFm a1 (hGsub ha1)
      have ha01 : a0 < a1 := lt_of_le_of_ne (ha0min a1 (hGsub ha1)) (Ne.symm (Finset.ne_of_mem_erase ha1))
      have hP0 : 0 < a0 := (Nat.prime_of_mem_primeFactors (hFsub ha0)).pos
      have hu1 : Wf (t p1) ≤ t a1 - mm := W_bound _ _ (htlt a1 (hFsub (hGsub ha1))) hta1
      have hu2 : Wf (t a0) ≤ t a1 - mm := W_bound _ _ (tlt y hy hP0 ha01) hta1
      have := arith G t a1 ha1 (fun p hp => hFm p (hGsub hp)) hg' (Wf (t p1)) (Wf (t a0)) hu1 hu2
      have hsplit : ∑ p ∈ F, Wf (t p) = Wf (t a0) + ∑ p ∈ G, Wf (t p) := by
        exact (Finset.add_sum_erase F (fun p => Wf (t p)) ha0).symm
      rw [hu0, hsplit]
      linarith

end S05

open S05

theorem itemS05 : ItemS05 := by
  classical
  intro y hy
  have hy0 : 0 < y := by linarith
  have hly : 0 < Real.log y := Real.log_pos hy
  have hwy : ∀ p, wy y p = Wf (Real.log p / Real.log y) := fun p => rfl
  -- `t_p` against powers of `y`
  have hge : ∀ (p : ℕ) (c : ℝ), p.Prime → y ^ c ≤ (p : ℝ) → c ≤ Real.log p / Real.log y := by
    intro p c hp h
    rw [le_div_iff₀ hly, ← Real.log_rpow hy0]
    exact Real.log_le_log (Real.rpow_pos_of_pos hy0 _) h
  have hle : ∀ (p : ℕ) (c : ℝ), p.Prime → (p : ℝ) ≤ y ^ c → Real.log p / Real.log y ≤ c := by
    intro p c hp h
    rw [div_le_iff₀ hly, ← Real.log_rpow hy0]
    exact Real.log_le_log (by exact_mod_cast hp.pos) h
  have hlt : ∀ (p : ℕ) (c : ℝ), y ^ c < (p : ℝ) → c < Real.log p / Real.log y := by
    intro p c h
    rw [lt_div_iff₀ hly, ← Real.log_rpow hy0]
    exact Real.log_lt_log (Real.rpow_pos_of_pos hy0 _) h
  refine ⟨fun p => W_nonneg _, fun p _ => W_le _, ?_, ?_, ?_, ?_, ?_⟩
  · -- (3) `w = W1` from `y^U` on
    intro p hp h
    have ht := hge p UU hp h
    rw [hwy]
    set t := Real.log p / Real.log y
    unfold Wf
    have h1 : ¬ t ≤ mm := by unfold mm UU at *; intro h'; linarith
    have h2 : ¬ t ≤ 1 / 3 := by unfold UU at *; intro h'; linarith
    rw [if_neg h1, if_neg h2]
    split_ifs with h3
    · have : t = UU := le_antisymm h3 ht
      rw [this]; unfold UU mm W1; norm_num
    · rfl
  · -- (4) `w = 0` up to `y^m`
    intro p hp h
    rw [hwy]; exact W_zero _ (hle p mm hp h)
  · -- (5) the line `W(t) ≤ t − m`
    intro p hp h _
    rw [hwy]; exact W_lin _ (hlt p mm h)
  · -- (6) `φ ≥ 0` on `𝒟` and (3.10) for odd `ν ≥ 3`
    intro δ hδ
    obtain ⟨hdvd, h1, hchi, _, hω⟩ := mem y δ hδ
    have hδ0 : δ ≠ 0 := fun h => S05.primorial_ne_zero _ (zero_dvd_iff.1 (h ▸ hdvd))
    have hsq := primorial_sqf _ δ hdvd
    have hc1 := chi_of y mm δ h1 hchi
    have hω' : ω δ = δ.primeFactors.card := ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors
    have h85 : (δ.primeFactors.card : ℝ) ≤ 1 / mm := by rw [← hω']; exact hω
    unfold phiW
    refine ⟨?_, ?_⟩
    · have := key y hy δ hsq h1 hc1 0 (fun a ha _ => by linarith) (fun _ => rfl) (Or.inr rfl) (Or.inr rfl)
      linarith
    · intro h3 q hq hqlt
      have hp1 : δ.minFac.Prime := Nat.minFac_prime h1
      have htq : Real.log q / Real.log y < Real.log δ.minFac / Real.log y := tlt y hy hq.pos hqlt
      have := key y hy δ hsq h1 hc1 (wy y q)
        (fun a ha hta => by rw [hwy]; exact W_bound _ _ (htq.trans hta) ha)
        (fun ht => by rw [hwy]; exact W_zero _ (htq.le.trans ht))
        (Or.inl (by rw [← hω']; omega)) (Or.inl h85)
      linarith
  · -- (7) Lemma 4 (iii)
    intro δ hδ hev h2 hchi
    have hdvd : δ ∣ primorialLt (y ^ UU) := Nat.dvd_of_mem_divisors hδ
    have hsq := primorial_sqf _ δ hdvd
    have h1 : δ ≠ 1 := by
      rintro rfl
      simp at h2
    have hc1 := chi_of y mm δ h1 hchi
    have := key y hy δ hsq h1 hc1 0 (fun a ha _ => by linarith) (fun _ => rfl) (Or.inr rfl) (Or.inr rfl)
    linarith

end Omega3
