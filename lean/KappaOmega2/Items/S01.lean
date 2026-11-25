import KappaOmega2.Statements

namespace KappaOmega2

open Finset Palprimes Palprimes.Greaves

set_option linter.style.longLine false

/-! Item S01 (Greaves Lemma 1, radical form).  `P` = primes of `a` below `z`, `Â = ∏ P`. -/

lemma s01_pf (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) : (∏ p ∈ P, p).primeFactors = P :=
  Nat.primeFactors_prod hP

lemma s01_radLt_idem (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (z : ℝ) (hz : ∀ p ∈ P, (p : ℝ) < z) :
    radLt (∏ p ∈ P, p) z = ∏ p ∈ P, p := by
  classical
  unfold radLt
  rw [s01_pf P hP, Finset.filter_true_of_mem hz]

lemma s01_div (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (p1 p2 : ℕ) (h1 : p1 ∈ P) (h2 : p2 ∈ P.erase p1) :
    (∏ p ∈ P, p) / (p1 * p2) = ∏ p ∈ (P.erase p1).erase p2, p := by
  have e : (∏ p ∈ P, p) = (p1 * p2) * ∏ p ∈ (P.erase p1).erase p2, p := by
    rw [mul_assoc, Finset.mul_prod_erase (P.erase p1) (fun x => x) h2, Finset.mul_prod_erase P (fun x => x) h1]
  have hpos : 0 < p1 * p2 :=
    Nat.mul_pos (hP p1 h1).pos (hP p2 (Finset.mem_of_mem_erase h2)).pos
  rw [e]
  exact Nat.mul_div_cancel_left _ hpos

lemma s01_Ssv (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (p1 p2 : ℕ) (h1 : p1 ∈ P) (h2 : p2 ∈ P.erase p1) (t : ℝ) :
    Ssv ((∏ p ∈ P, p) / (p1 * p2)) t = if ∀ q ∈ (P.erase p1).erase p2, t ≤ (q : ℝ) then 1 else 0 := by
  classical
  unfold Ssv
  rw [s01_div P hP p1 p2 h1 h2, Nat.primeFactors_prod (fun q hq => hP q (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hq)))]

lemma s01_mem_P (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (p : ℕ) (hp : p.Prime) (hd : p ∣ ∏ q ∈ P, q) : p ∈ P := by
  obtain ⟨q, hq, hpq⟩ := Prime.exists_mem_finset_dvd hp.prime hd
  have := (Nat.prime_dvd_prime_iff_eq hp (hP q hq)).1 hpq
  rw [this]; exact hq

lemma s01_Lam2 (y z W1' : ℝ) (w : ℕ → ℝ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hz : ∀ p ∈ P, (p : ℝ) < z)
    (m : ℕ) (hm : m ∈ P) (hmin : ∀ p ∈ P, m ≤ p) :
    Lam2 y z W1' w (∏ p ∈ P, p) =
      ∑ p1 ∈ P.filter (fun p => p ≠ m ∧ y ≤ (m : ℝ) ^ 2 * p),
        ((W1' - w p1) - w m * (if ∀ q ∈ (P.erase p1).erase m, (p1 : ℝ) ≤ q then 1 else 0)) := by
  classical
  unfold Lam2
  have hout : (primesBelow z).filter (· ∣ ∏ q ∈ P, q) = P := by
    ext p
    simp only [Finset.mem_filter, mem_primesBelow]
    constructor
    · rintro ⟨⟨hp, _⟩, hd⟩; exact s01_mem_P P hP p hp hd
    · intro hp; exact ⟨⟨hP p hp, hz p hp⟩, Finset.dvd_prod_of_mem _ hp⟩
  rw [hout, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p1 hp1
  -- inner sum
  have hI : ∀ p2 ∈ (primesBelow (p1 : ℝ)).filter (fun p2 : ℕ => p2 ∣ ∏ q ∈ P, q ∧ y ≤ (p2 : ℝ) ^ 2 * p1),
      p2 ∈ P.erase p1 ∧ (p2 : ℝ) < p1 := by
    intro p2 hp2
    rw [Finset.mem_filter, mem_primesBelow] at hp2
    refine ⟨Finset.mem_erase.2 ⟨?_, s01_mem_P P hP p2 hp2.1.1 hp2.2.1⟩, hp2.1.2⟩
    intro h; rw [h] at hp2; exact lt_irrefl _ hp2.1.2
  have hT : ∀ p2 ∈ (primesBelow (p1 : ℝ)).filter (fun p2 : ℕ => p2 ∣ ∏ q ∈ P, q ∧ y ≤ (p2 : ℝ) ^ 2 * p1), p2 ≠ m →
      ((W1' - w p1) * Ssv ((∏ q ∈ P, q) / (p1 * p2)) p2 - w p2 * Ssv ((∏ q ∈ P, q) / (p1 * p2)) p1) = 0 := by
    intro p2 hp2 hne
    obtain ⟨he, hlt⟩ := hI p2 hp2
    have hp2P := Finset.mem_of_mem_erase he
    have hmp2 : m < p2 := lt_of_le_of_ne (hmin p2 hp2P) (Ne.symm hne)
    have hmem : m ∈ (P.erase p1).erase p2 := by
      refine Finset.mem_erase.2 ⟨ne_of_lt hmp2, Finset.mem_erase.2 ⟨?_, hm⟩⟩
      intro h
      have : (p2 : ℝ) < p2 := by
        have := hlt
        rw [← h] at this
        have h2 : (m : ℝ) < p2 := by exact_mod_cast hmp2
        linarith
      exact lt_irrefl _ this
    rw [s01_Ssv P hP p1 p2 hp1 he, s01_Ssv P hP p1 p2 hp1 he]
    have n1 : ¬ ∀ q ∈ (P.erase p1).erase p2, (p2 : ℝ) ≤ q := by
      intro h
      have := h m hmem
      have h2 : (m : ℝ) < p2 := by exact_mod_cast hmp2
      linarith
    have n2 : ¬ ∀ q ∈ (P.erase p1).erase p2, (p1 : ℝ) ≤ q := by
      intro h
      have := h m hmem
      have h2 : (m : ℝ) < p2 := by exact_mod_cast hmp2
      linarith
    rw [if_neg n1, if_neg n2]; ring
  set I := (primesBelow (p1 : ℝ)).filter (fun p2 : ℕ => p2 ∣ ∏ q ∈ P, q ∧ y ≤ (p2 : ℝ) ^ 2 * p1) with hIdef
  set Tf : ℕ → ℝ := fun p2 => ((W1' - w p1) * Ssv ((∏ q ∈ P, q) / (p1 * p2)) p2 - w p2 * Ssv ((∏ q ∈ P, q) / (p1 * p2)) p1) with hTf
  have h1 : ∑ p2 ∈ I, Tf p2 = ∑ p2 ∈ I, (if p2 = m then Tf m else 0) := by
    apply Finset.sum_congr rfl
    intro p2 hp2
    by_cases h : p2 = m
    · subst h; simp
    · rw [if_neg h]; exact hT p2 hp2 h
  rw [h1, Finset.sum_ite_eq']
  by_cases hc : p1 ≠ m ∧ y ≤ (m : ℝ) ^ 2 * p1
  · have hmI : m ∈ I := by
      rw [hIdef, Finset.mem_filter, mem_primesBelow]
      refine ⟨⟨hP m hm, ?_⟩, Finset.dvd_prod_of_mem _ hm, hc.2⟩
      have : m < p1 := lt_of_le_of_ne (hmin p1 hp1) (Ne.symm hc.1)
      exact_mod_cast this
    rw [if_pos hmI, if_pos hc]
    have hme : m ∈ P.erase p1 := Finset.mem_erase.2 ⟨Ne.symm hc.1, hm⟩
    simp only [hTf]
    rw [s01_Ssv P hP p1 m hp1 hme, s01_Ssv P hP p1 m hp1 hme]
    have : ∀ q ∈ (P.erase p1).erase m, (m : ℝ) ≤ q := by
      intro q hq
      exact_mod_cast hmin q (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hq))
    rw [if_pos this]; ring
  · have hmI : m ∉ I := by
      intro hmI
      rw [hIdef, Finset.mem_filter, mem_primesBelow] at hmI
      apply hc
      refine ⟨?_, hmI.2.2⟩
      intro h
      have := hmI.1.2
      rw [h] at this
      exact lt_irrefl _ this
    rw [if_neg hmI, if_neg hc]

/-- Core inequality for `|P| ≥ 2`. -/
lemma s01_core (y z c : ℝ) (w : ℕ → ℝ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hz : ∀ p ∈ P, (p : ℝ) < z)
    (m : ℕ) (hm : m ∈ P) (hmin : ∀ p ∈ P, m ≤ p) (hw0 : ∀ p ∈ P, 0 ≤ w p) (hwle : ∀ p ∈ P, w p ≤ c)
    (hν : Prop) [Decidable hν] (hK : ¬ hν → w m ≤ ∑ p ∈ P.erase m, (c - w p)) :
    -(Lam2 y z c w (∏ p ∈ P, p)) ≤ if hν then w m else 0 := by
  classical
  rw [s01_Lam2 y z c w P hP hz m hm hmin]
  set J := P.filter (fun p => p ≠ m ∧ y ≤ (m : ℝ) ^ 2 * p) with hJ
  set S2 : ℕ → Prop := fun p => ∀ q ∈ (P.erase p).erase m, (p : ℝ) ≤ q with hS2
  have hsplit : ∑ p1 ∈ J, ((c - w p1) - w m * (if S2 p1 then 1 else 0)) =
      ∑ p1 ∈ J, (c - w p1) - w m * ∑ p1 ∈ J, (if S2 p1 then (1 : ℝ) else 0) := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hsplit]
  have hnn : 0 ≤ ∑ p1 ∈ J, (c - w p1) :=
    Finset.sum_nonneg (fun p hp => by
      have := Finset.mem_filter.1 hp
      linarith [hwle p this.1])
  have hwm0 : 0 ≤ w m := hw0 m hm
  have huniq : ∀ p ∈ P.erase m, ∀ p' ∈ P.erase m, S2 p → S2 p' → p = p' := by
    intro p hp p' hp' h h'
    by_contra hne
    have h1 : p' ∈ (P.erase p).erase m := Finset.mem_erase.2 ⟨(Finset.mem_erase.1 hp').1, Finset.mem_erase.2 ⟨Ne.symm hne, (Finset.mem_erase.1 hp').2⟩⟩
    have h2 : p ∈ (P.erase p').erase m := Finset.mem_erase.2 ⟨(Finset.mem_erase.1 hp).1, Finset.mem_erase.2 ⟨hne, (Finset.mem_erase.1 hp).2⟩⟩
    have a1 := h p' h1
    have a2 := h' p h2
    exact hne (le_antisymm (by exact_mod_cast a1) (by exact_mod_cast a2))
  by_cases hex : ∃ p ∈ J, S2 p
  · obtain ⟨ps, hps, hS2ps⟩ := hex
    have hpsP := Finset.mem_filter.1 hps
    have hJeq : J = P.erase m := by
      ext p
      constructor
      · intro hp
        have := Finset.mem_filter.1 hp
        exact Finset.mem_erase.2 ⟨this.2.1, this.1⟩
      · intro hp
        have hpm := Finset.mem_erase.1 hp
        rw [hJ, Finset.mem_filter]
        refine ⟨hpm.2, hpm.1, ?_⟩
        by_cases hpp : p = ps
        · rw [hpp]; exact hpsP.2.2
        · have hle : (ps : ℝ) ≤ p := hS2ps p (Finset.mem_erase.2 ⟨hpm.1, Finset.mem_erase.2 ⟨hpp, hpm.2⟩⟩)
          calc y ≤ (m : ℝ) ^ 2 * ps := hpsP.2.2
            _ ≤ (m : ℝ) ^ 2 * p := by gcongr
    have hone : ∑ p1 ∈ J, (if S2 p1 then (1 : ℝ) else 0) = 1 := by
      rw [Finset.sum_eq_single ps]
      · rw [if_pos hS2ps]
      · intro p hp hne
        rw [if_neg]
        intro h
        exact hne (huniq p (by rw [← hJeq]; exact hp) ps (by rw [← hJeq]; exact hps) h hS2ps)
      · intro h; exact absurd hps h
    rw [hone, mul_one, hJeq]
    by_cases hv : hν
    · rw [if_pos hv]
      have : 0 ≤ ∑ p1 ∈ P.erase m, (c - w p1) := hJeq ▸ hnn
      linarith
    · rw [if_neg hv]
      linarith [hK hv]
  · have hz0 : ∑ p1 ∈ J, (if S2 p1 then (1 : ℝ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      rw [if_neg]
      intro h; exact hex ⟨p, hp, h⟩
    rw [hz0, mul_zero, sub_zero]
    by_cases hv : hν
    · rw [if_pos hv]; linarith
    · rw [if_neg hv]; linarith

theorem itemS01 : ItemS01 := by
  classical
  intro y U V z g' w a hy hU1 hU2 hV hz hg ha2 hag hw0 hwle hwbig hwsmall hwmid
  set Y : ℝ := y ^ U with hY
  have hL : 0 < Real.log y := Real.log_pos hy
  have hYy : Y ≤ y := by
    calc Y ≤ y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hy.le hU2.le
      _ = y := Real.rpow_one y
  have hlogY : Real.log Y = U * Real.log y := by rw [hY, Real.log_rpow (by linarith)]
  have hYpos : 0 < Y := Real.rpow_pos_of_pos (by linarith) _
  set tt : ℕ → ℝ := fun p => Real.log p / Real.log y with htt
  set P : Finset ℕ := a.primeFactors.filter (fun p => (p : ℝ) < z) with hP
  have hPprime : ∀ p ∈ P, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1
  have hPz : ∀ p ∈ P, (p : ℝ) < z := fun p hp => (Finset.mem_filter.1 hp).2
  have hPa : ∀ p ∈ P, p ∣ a := fun p hp => Nat.dvd_of_mem_primeFactors (Finset.mem_filter.1 hp).1
  have ha0 : a ≠ 0 := by omega
  have hrad : radLt a z = ∏ p ∈ P, p := by
    unfold radLt; congr
  unfold SigmaG
  rw [hrad, s01_radLt_idem P hPprime z hPz]
  have hptn : 0 ≤ ptarget y U w a := by
    unfold ptarget
    split_ifs
    · exact hw0 _ (Nat.minFac_prime (by omega))
    · exact le_rfl
  have hmfp : a.minFac.Prime := Nat.minFac_prime (by omega)
  -- the counting step
  have hS0eq : (Aset a y).filter (fun p : ℕ => (p : ℝ) < y ^ U) = P.filter (fun p : ℕ => (p : ℝ) < Y) := by
    ext p
    simp only [Finset.mem_filter, mem_Aset, hP]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨⟨h1, lt_of_lt_of_le h2 (hY ▸ hz)⟩, h2⟩
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨⟨h1, lt_of_lt_of_le h2 hYy⟩, h2⟩
  have hnuS : ¬ nu a Y ≤ 2 → U - V ≤ ∑ p ∈ P.filter (fun p : ℕ => (p : ℝ) < Y), (U - tt p) := by
    intro hn
    by_contra hlt
    push Not at hlt
    apply hn
    have := nu_le a (by omega) y U V g' 2 hy (by linarith) hU2.le hag (by simpa using hg)
      (by rw [hS0eq]; exact hlt)
    simpa using this
  have hm1 : ∀ p : ℕ, p.Prime → (y ^ V < p) → U - tt p ≤ (U - V) - w p := by
    intro p hp hVp
    by_cases hpY : (p : ℝ) < Y
    · have := hwmid p hp hVp hpY
      simp only [htt]; linarith
    · push Not at hpY
      have h1 := hwbig p hp hpY
      have h2 : U ≤ tt p := by
        simp only [htt]
        rw [le_div_iff₀ hL]
        have := Real.log_le_log hYpos hpY
        rw [hlogY] at this; exact this
      rw [h1]; linarith
  have hwc : ∀ p ∈ P, 0 ≤ (U - V) - w p := fun p hp => by linarith [hwle p (hPprime p hp)]
  by_cases hPe : P = ∅
  · -- no prime factor below z
    rw [hPe, Finset.prod_empty]
    have hL2 : Lam2 y z (U - V) w 1 = 0 := by
      unfold Lam2
      apply Finset.sum_eq_zero
      intro p1 hp1
      rw [Finset.mem_filter, mem_primesBelow] at hp1
      exact absurd (Nat.le_of_dvd one_pos hp1.2) (by have := hp1.1.1.two_le; omega)
    have hLA : LamA 1 (U - V) w = U - V := by unfold LamA; rw [if_pos rfl]
    rw [hLA, hL2, sub_zero]
    have hmf : Y ≤ (a.minFac : ℝ) := by
      by_contra hlt
      push Not at hlt
      have hmem : a.minFac ∈ P := Finset.mem_filter.2 ⟨Nat.mem_primeFactors.2 ⟨hmfp, Nat.minFac_dvd a, ha0⟩, lt_of_lt_of_le hlt hz⟩
      rw [hPe] at hmem; simp at hmem
    by_cases hUV : U - V ≤ 0
    · linarith
    · push Not at hUV
      have hnu : nu a Y ≤ 2 := by
        by_contra hn
        have := hnuS hn
        rw [hPe] at this; simp at this; linarith
      unfold ptarget
      rw [if_pos hnu, hwbig a.minFac hmfp hmf]
  · -- P nonempty
    obtain ⟨p0, hp0⟩ := Finset.nonempty_of_ne_empty hPe
    set q1 := a.minFac with hq1
    have hq1P : q1 ∈ P := by
      refine Finset.mem_filter.2 ⟨Nat.mem_primeFactors.2 ⟨hmfp, Nat.minFac_dvd a, ha0⟩, ?_⟩
      have : q1 ≤ p0 := Nat.minFac_le_of_dvd (hPprime p0 hp0).two_le (hPa p0 hp0)
      have h2 : (q1 : ℝ) ≤ p0 := by exact_mod_cast this
      linarith [hPz p0 hp0]
    have hmin : ∀ p ∈ P, q1 ≤ p := fun p hp => Nat.minFac_le_of_dvd (hPprime p hp).two_le (hPa p hp)
    -- Key lemma K
    have hK : ¬ nu a Y ≤ 2 → w q1 ≤ ∑ p ∈ P.erase q1, ((U - V) - w p) := by
      intro hn
      have hnS := hnuS hn
      have hnn : 0 ≤ ∑ p ∈ P.erase q1, ((U - V) - w p) :=
        Finset.sum_nonneg (fun p hp => hwc p (Finset.mem_of_mem_erase hp))
      by_cases hwq : w q1 = 0
      · rw [hwq]; exact hnn
      · have hwq' : 0 < w q1 := lt_of_le_of_ne (hw0 q1 hmfp) (Ne.symm hwq)
        have hVq : y ^ V < (q1 : ℝ) := by
          by_contra hle
          push Not at hle
          exact hwq (hwsmall q1 hmfp hle)
        by_cases hq : (q1 : ℝ) < Y
        · have hq1S : q1 ∈ P.filter (fun p : ℕ => (p : ℝ) < Y) := Finset.mem_filter.2 ⟨hq1P, hq⟩
          rw [← Finset.add_sum_erase _ _ hq1S] at hnS
          have hwq2 := hwmid q1 hmfp hVq hq
          have hsub : ∑ p ∈ (P.filter (fun p : ℕ => (p : ℝ) < Y)).erase q1, (U - tt p) ≤
              ∑ p ∈ P.erase q1, ((U - V) - w p) := by
            calc _ ≤ ∑ p ∈ (P.filter (fun p : ℕ => (p : ℝ) < Y)).erase q1, ((U - V) - w p) := by
                  apply Finset.sum_le_sum
                  intro p hp
                  have hpP := Finset.mem_filter.1 (Finset.mem_of_mem_erase hp)
                  have hpne := (Finset.mem_erase.1 hp).1
                  have hpq1 : q1 < p := lt_of_le_of_ne (hmin p hpP.1) (Ne.symm hpne)
                  have : (q1 : ℝ) < p := by exact_mod_cast hpq1
                  exact hm1 p (hPprime p hpP.1) (by linarith)
              _ ≤ _ := by
                  apply Finset.sum_le_sum_of_subset_of_nonneg
                  · intro p hp
                    exact Finset.mem_erase.2 ⟨(Finset.mem_erase.1 hp).1, (Finset.mem_filter.1 (Finset.mem_of_mem_erase hp)).1⟩
                  · intro p hp _; exact hwc p (Finset.mem_of_mem_erase hp)
          simp only [htt] at hnS hwq2 hsub
          linarith
        · push Not at hq
          have h1 := hwbig q1 hmfp hq
          have : P.filter (fun p : ℕ => (p : ℝ) < Y) = ∅ := by
            apply Finset.filter_eq_empty_iff.2
            intro p hp
            have : (q1 : ℝ) ≤ p := by exact_mod_cast hmin p hp
            linarith
          rw [this] at hnS
          simp at hnS
          linarith
    have hmin' : q1 = a.minFac := rfl
    unfold ptarget
    rw [← hmin']
    have hL2 := s01_Lam2 y z (U - V) w P hPprime hPz q1 hq1P hmin
    by_cases hc1 : P.card = 1
    · obtain ⟨x, hx⟩ := Finset.card_eq_one.1 hc1
      have hxq : q1 = x := by rw [hx] at hq1P; simpa using hq1P
      have hPeq : P = {q1} := by rw [hx, hxq]
      have hprod : ∏ p ∈ P, p = q1 := by rw [hPeq]; simp
      have hLam2 : Lam2 y z (U - V) w (∏ p ∈ P, p) = 0 := by
        rw [hL2]
        apply Finset.sum_eq_zero
        intro p hp
        rw [Finset.mem_filter, hPeq, Finset.mem_singleton] at hp
        exact absurd hp.1 hp.2.1
      have hLA : LamA (∏ p ∈ P, p) (U - V) w = w q1 := by
        rw [hprod]; unfold LamA
        rw [if_neg hmfp.one_lt.ne', if_pos hmfp]
      rw [hLam2, hLA, sub_zero]
      by_cases hn : nu a Y ≤ 2
      · rw [if_pos hn]
      · rw [if_neg hn]
        have := hK hn
        rw [hPeq] at this
        simpa using this
    · have hc2 : 2 ≤ P.card := by
        have : 0 < P.card := Finset.card_pos.2 ⟨p0, hp0⟩
        omega
      have hLA : LamA (∏ p ∈ P, p) (U - V) w = 0 := by
        unfold LamA
        have hpf := s01_pf P hPprime
        have h1 : ∏ p ∈ P, p ≠ 1 := by
          intro h; rw [h] at hpf; simp at hpf; rw [← hpf] at hPe; exact hPe rfl
        have h2 : ¬ (∏ p ∈ P, p).Prime := by
          intro h
          rw [h.primeFactors] at hpf
          rw [← hpf] at hc2; simp at hc2
        rw [if_neg h1, if_neg h2]
      rw [hLA, zero_sub]
      have := s01_core y z (U - V) w P hPprime hPz q1 hq1P hmin (fun p hp => hw0 p (hPprime p hp))
        (fun p hp => hwle p (hPprime p hp)) (nu a Y ≤ 2) hK
      exact this

end KappaOmega2
