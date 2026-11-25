import KappaOmega2.Items.M10_Sets

/-!
# M10 helper: P2 (factorisation of `χ⁻_y(d₁ p d₂)`, Greaves p. 92), set form
-/

set_option linter.style.longLine false

open Finset Real
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius

namespace KappaOmega2.M10

open Palprimes Palprimes.Greaves
open Classical

theorem prod_le_prod_subset {E F : Finset ℕ} (hF : ∀ p ∈ F, p.Prime) (h : E ⊆ F) :
    ((∏ p ∈ E, p : ℕ) : ℝ) ≤ ((∏ p ∈ F, p : ℕ) : ℝ) := by
  exact_mod_cast Nat.le_of_dvd (prod_pos_of_primes hF) (prod_dvd_prod_of_subset _ _ _ h)

theorem prod_mul_le_of_mem {E F : Finset ℕ} {r : ℕ} (hF : ∀ p ∈ F, p.Prime) (h : E ⊆ F) (hr : r ∈ F) (hrE : r ∉ E) :
    ((∏ p ∈ E, p : ℕ) : ℝ) * r ≤ ((∏ p ∈ F, p : ℕ) : ℝ) := by
  have hsub : insert r E ⊆ F := insert_subset hr h
  have := prod_le_prod_subset hF hsub
  rw [prod_insert hrE] at this
  push_cast at this ⊢; linarith

theorem minFac_prod_insert_below {p : ℕ} (hp : p.Prime) {D : Finset ℕ} (hD : ∀ q ∈ D, q.Prime) (h : ∀ q ∈ D, p < q) :
    (∏ q ∈ insert p D, q).minFac = p := by
  have hall : ∀ q ∈ insert p D, q.Prime := by
    intro q hq; rcases mem_insert.1 hq with rfl | hq
    · exact hp
    · exact hD q hq
  obtain ⟨hm, hmin⟩ := minFac_prod hall (insert_nonempty p D)
  apply le_antisymm (hmin p (mem_insert_self p D))
  rcases mem_insert.1 hm with h' | h'
  · rw [h']
  · exact (h _ h').le

/-- P2 in set form: for primes `D₁ > p > D₂`,
`χ⁻_Y(D₁ ∪ {p} ∪ D₂) ↔ χ⁻_Y(D₁ ∪ {p}) ∧ χ^{ε}_{Y/(p ΠD₁)}(D₂)`, `ε = +` iff `|D₁|` even. -/
theorem P2 {Y : ℝ} {p : ℕ} (hp : p.Prime) {D₁ D₂ : Finset ℕ} (hD₁ : ∀ q ∈ D₁, q.Prime) (hD₂ : ∀ q ∈ D₂, q.Prime)
    (h₁ : ∀ q ∈ D₁, p < q) (h₂ : ∀ q ∈ D₂, q < p) :
    ChiS false Y (D₁ ∪ insert p D₂) ↔
      ChiS false Y (insert p D₁) ∧ ChiS (decide (Even D₁.card)) (Y / (p * ((∏ q ∈ D₁, q : ℕ) : ℝ))) D₂ := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hP1 : (0 : ℝ) < ((∏ q ∈ D₁, q : ℕ) : ℝ) := by exact_mod_cast prod_pos_of_primes hD₁
  have hpD₁ : p ∉ D₁ := fun h => lt_irrefl p (h₁ p h)
  have hpD₂ : p ∉ D₂ := fun h => lt_irrefl p (h₂ p h)
  have hdisj : Disjoint D₁ (insert p D₂) := by
    rw [disjoint_left]; intro q hq hq'
    rcases mem_insert.1 hq' with rfl | hq'
    · exact hpD₁ hq
    · exact lt_asymm (h₁ q hq) (h₂ q hq')
  have hall : ∀ q ∈ D₁ ∪ insert p D₂, q.Prime := by
    intro q hq; rcases mem_union.1 hq with hq | hq
    · exact hD₁ q hq
    · rcases mem_insert.1 hq with rfl | hq
      · exact hp
      · exact hD₂ q hq
  have hallA : ∀ q ∈ insert p D₁, q.Prime := by
    intro q hq; rcases mem_insert.1 hq with rfl | hq
    · exact hp
    · exact hD₁ q hq
  have hcardA : (insert p D₁).card = D₁.card + 1 := card_insert_of_notMem hpD₁
  have hprodA : ((∏ q ∈ insert p D₁, q : ℕ) : ℝ) = p * ((∏ q ∈ D₁, q : ℕ) : ℝ) := by
    rw [prod_insert hpD₁]; push_cast; ring
  constructor
  · intro H
    refine ⟨fun E hE hne hpar => H E (hE.trans (by
      intro q hq; rcases mem_insert.1 hq with rfl | hq
      · exact mem_union_right _ (mem_insert_self _ _)
      · exact mem_union_left _ hq)) hne hpar, ?_⟩
    intro E₂ hE₂ hne hpar
    have hE₂p : ∀ q ∈ E₂, q.Prime := fun q hq => hD₂ q (hE₂ hq)
    set E := insert p D₁ ∪ E₂ with hE
    have hdisj2 : Disjoint (insert p D₁) E₂ := by
      rw [disjoint_left]; intro q hq hq'
      have := h₂ q (hE₂ hq')
      rcases mem_insert.1 hq with rfl | hq
      · exact lt_irrefl _ this
      · exact lt_asymm (h₁ q hq) this
    have hEsub : E ⊆ D₁ ∪ insert p D₂ := by
      intro q hq; rcases mem_union.1 hq with hq | hq
      · rcases mem_insert.1 hq with rfl | hq
        · exact mem_union_right _ (mem_insert_self _ _)
        · exact mem_union_left _ hq
      · exact mem_union_right _ (mem_insert_of_mem (hE₂ hq))
    have hcard : E.card = D₁.card + 1 + E₂.card := by rw [hE, card_union_of_disjoint hdisj2, hcardA]
    have hEpar : Even E.card := by
      rw [hcard]
      by_cases he : Even D₁.card
      · simp only [he, decide_true, par, if_true] at hpar
        exact (he.add_one).add_odd hpar
      · simp only [he, decide_false, par, Bool.false_eq_true, if_false] at hpar
        exact ((Nat.not_even_iff_odd.1 he).add_one).add hpar
    have h1 := H E hEsub (hne.mono subset_union_right) (by simp only [par, Bool.false_eq_true, if_false]; exact hEpar)
    -- minFac and product
    have hEp : ∀ q ∈ E, q.Prime := fun q hq => hall q (hEsub hq)
    obtain ⟨hmE, hminE⟩ := minFac_prod hEp (hne.mono subset_union_right)
    obtain ⟨hm2, hmin2⟩ := minFac_prod hE₂p hne
    have hmf : (∏ q ∈ E, q).minFac = (∏ q ∈ E₂, q).minFac := by
      apply le_antisymm (hminE _ (mem_union_right _ hm2))
      rcases mem_union.1 hmE with h | h
      · exfalso
        have a := hminE _ (mem_union_right _ hm2)
        have b := h₂ _ (hE₂ hm2)
        rcases mem_insert.1 h with h' | h'
        · rw [h'] at a; omega
        · have := h₁ _ h'; omega
      · exact hmin2 _ h
    rw [hmf, hE, prod_union hdisj2, Nat.cast_mul, hprodA] at h1
    rw [lt_div_iff₀ (by positivity)]
    exact lt_of_eq_of_lt (by ring) h1
  · rintro ⟨HA, H2⟩ E hE hne hpar
    simp only [par, Bool.false_eq_true, if_false] at hpar
    have hEp : ∀ q ∈ E, q.Prime := fun q hq => hall q (hE hq)
    set E₂ := E.filter (· < p) with hE₂
    set Ea := E.filter (fun q => ¬ q < p) with hEa
    have hEaA : Ea ⊆ insert p D₁ := by
      intro q hq
      rw [hEa, mem_filter] at hq
      rcases mem_union.1 (hE hq.1) with h | h
      · exact mem_insert_of_mem h
      · rcases mem_insert.1 h with rfl | h
        · exact mem_insert_self _ _
        · exact absurd (h₂ q h) hq.2
    have hE₂D : E₂ ⊆ D₂ := by
      intro q hq
      rw [hE₂, mem_filter] at hq
      rcases mem_union.1 (hE hq.1) with h | h
      · exact absurd (lt_trans (h₁ q h) hq.2) (lt_irrefl _)
      · rcases mem_insert.1 h with rfl | h
        · exact absurd hq.2 (lt_irrefl _)
        · exact h
    have hsplitE : E = Ea ∪ E₂ := by
      rw [hEa, hE₂, union_comm]; exact (filter_union_filter_not_eq (fun x : ℕ => x < p) E).symm
    have hdisjE : Disjoint Ea E₂ := by
      rw [hEa, hE₂]; exact (disjoint_filter_filter_not E E _).symm
    have hcardE : E.card = Ea.card + E₂.card := by rw [hsplitE, card_union_of_disjoint hdisjE]
    have hprodE : ((∏ q ∈ E, q : ℕ) : ℝ) = ((∏ q ∈ Ea, q : ℕ) : ℝ) * ((∏ q ∈ E₂, q : ℕ) : ℝ) := by
      rw [hsplitE, prod_union hdisjE]; push_cast; ring
    have hEap : ∀ q ∈ Ea, q.Prime := fun q hq => hallA q (hEaA hq)
    have hE₂p : ∀ q ∈ E₂, q.Prime := fun q hq => hD₂ q (hE₂D hq)
    have hPa0 : (0 : ℝ) < ((∏ q ∈ Ea, q : ℕ) : ℝ) := by exact_mod_cast prod_pos_of_primes hEap
    have hPaA : ((∏ q ∈ Ea, q : ℕ) : ℝ) ≤ p * ((∏ q ∈ D₁, q : ℕ) : ℝ) := by
      rw [← hprodA]; exact prod_le_prod_subset hallA hEaA
    by_cases he2 : E₂ = ∅
    · have hEA : E ⊆ insert p D₁ := by rw [hsplitE, he2, union_empty]; exact hEaA
      exact HA E hEA hne (by simp only [par, Bool.false_eq_true, if_false]; exact hpar)
    have hne2 : E₂.Nonempty := nonempty_iff_ne_empty.2 he2
    obtain ⟨hmE, hminE⟩ := minFac_prod hEp hne
    obtain ⟨hm2, hmin2⟩ := minFac_prod hE₂p hne2
    set q := (∏ x ∈ E₂, x).minFac with hq
    have hqE : q ∈ E := (mem_filter.1 hm2).1
    have hmf : (∏ x ∈ E, x).minFac = q := by
      apply le_antisymm (hminE _ hqE)
      by_cases hlt : (∏ x ∈ E, x).minFac < p
      · exact hmin2 _ (mem_filter.2 ⟨hmE, hlt⟩)
      · exfalso
        have a := hminE _ hqE
        have b : q < p := (mem_filter.1 hm2).2
        omega
    rw [hmf, hprodE]
    have hqp : q < p := (mem_filter.1 hm2).2
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (hE₂p q hm2).pos
    have hqp' : (q : ℝ) < p := by exact_mod_cast hqp
    by_cases hpar2 : par (decide (Even D₁.card)) E₂.card
    · have h1 := H2 E₂ hE₂D hne2 hpar2
      rw [lt_div_iff₀ (by positivity)] at h1
      have hP2 : (0 : ℝ) < ((∏ x ∈ E₂, x : ℕ) : ℝ) := by exact_mod_cast prod_pos_of_primes hE₂p
      calc ((∏ q ∈ Ea, q : ℕ) : ℝ) * ((∏ q ∈ E₂, q : ℕ) : ℝ) * (q : ℝ) ^ 2
          ≤ (p * ((∏ q ∈ D₁, q : ℕ) : ℝ)) * ((∏ q ∈ E₂, q : ℕ) : ℝ) * (q : ℝ) ^ 2 := by gcongr
        _ < Y := by rw [← hq] at h1; exact lt_of_eq_of_lt (by ring) h1
    · -- Ea ≠ insert p D₁: a prime r ≥ p of insert p D₁ outside Ea
      have hparity : ¬ (Ea.card % 2 = (D₁.card + 1) % 2) := by
        intro hc
        apply hpar2
        have hE2 : E₂.card % 2 = (D₁.card + 1) % 2 := by
          have := Nat.even_iff.1 hpar; omega
        by_cases he : Even D₁.card
        · simp only [he, decide_true, par, if_true]; rw [Nat.odd_iff]; have := Nat.even_iff.1 he; omega
        · simp only [he, decide_false, par, Bool.false_eq_true, if_false]; rw [Nat.even_iff]
          have := Nat.odd_iff.1 (Nat.not_even_iff_odd.1 he); omega
      have hex : ∃ r ∈ insert p D₁, r ∉ Ea := by
        by_contra hcon; push_neg at hcon
        have : Ea = insert p D₁ := le_antisymm hEaA hcon
        apply hparity; rw [this, hcardA]
      obtain ⟨r, hrA, hrEa⟩ := hex
      have hrp : p ≤ r := by
        rcases mem_insert.1 hrA with rfl | h
        · exact le_rfl
        · exact (h₁ r h).le
      have hrp' : (p : ℝ) ≤ r := by exact_mod_cast hrp
      have hPar : ((∏ q ∈ Ea, q : ℕ) : ℝ) * r ≤ p * ((∏ q ∈ D₁, q : ℕ) : ℝ) := by
        rw [← hprodA]; exact prod_mul_le_of_mem hallA hEaA hrA hrEa
      by_cases hsing : E₂.card = 1
      · -- E₂ = {q}; then |D₁| odd and the even set insert p D₁ gives p ΠD₁ p² < Y
        obtain ⟨a, ha⟩ := card_eq_one.1 hsing
        have hqa : q = a := by
          have := hm2; rw [ha, mem_singleton] at this; exact this
        have hP2 : ((∏ x ∈ E₂, x : ℕ) : ℝ) = q := by rw [ha, prod_singleton, hqa]
        have hD₁odd : Even (insert p D₁).card := by
          by_contra hc
          apply hpar2
          rw [hcardA] at hc
          have hev : Even D₁.card := by
            rcases Nat.even_or_odd D₁.card with h | h
            · exact h
            · exact absurd h.add_one hc
          simp only [hev, decide_true, par, if_true, hsing]; exact odd_one
        have hA := HA (insert p D₁) subset_rfl (insert_nonempty _ _) (by
          simp only [par, Bool.false_eq_true, if_false]; exact hD₁odd)
        rw [minFac_prod_insert_below hp hD₁ h₁, hprodA] at hA
        rw [hP2]
        have : (q : ℝ) ^ 3 < r * (p : ℝ) ^ 2 := by
          have : (q : ℝ) ^ 2 < (p : ℝ) ^ 2 := by nlinarith
          nlinarith
        calc ((∏ q ∈ Ea, q : ℕ) : ℝ) * (q : ℝ) * (q : ℝ) ^ 2 = ((∏ q ∈ Ea, q : ℕ) : ℝ) * (q : ℝ) ^ 3 := by ring
          _ < ((∏ q ∈ Ea, q : ℕ) : ℝ) * (r * (p : ℝ) ^ 2) := mul_lt_mul_of_pos_left this hPa0
          _ = (((∏ q ∈ Ea, q : ℕ) : ℝ) * r) * (p : ℝ) ^ 2 := by ring
          _ ≤ (p * ((∏ q ∈ D₁, q : ℕ) : ℝ)) * (p : ℝ) ^ 2 := by gcongr
          _ < Y := by linarith
      · -- |E₂| ≥ 2: drop q
        set E₂' := E₂.erase q with hE₂'
        have hcard2 : E₂.card = E₂'.card + 1 := by rw [hE₂', card_erase_of_mem hm2]; have := hne2.card_pos; omega
        have hne2' : E₂'.Nonempty := by
          rw [← card_pos]; have := hne2.card_pos; omega
        have hE₂'D : E₂' ⊆ D₂ := (erase_subset _ _).trans hE₂D
        have hE₂'p : ∀ x ∈ E₂', x.Prime := fun x hx => hD₂ x (hE₂'D hx)
        have hpar2' : par (decide (Even D₁.card)) E₂'.card := by
          have hE2 : E₂.card % 2 = D₁.card % 2 := by
            by_contra hc
            apply hpar2
            have := Nat.even_iff.1 hpar
            by_cases he : Even D₁.card
            · simp only [he, decide_true, par, if_true]; rw [Nat.odd_iff]; have := Nat.even_iff.1 he; omega
            · simp only [he, decide_false, par, Bool.false_eq_true, if_false]; rw [Nat.even_iff]
              have := Nat.odd_iff.1 (Nat.not_even_iff_odd.1 he); omega
          by_cases he : Even D₁.card
          · simp only [he, decide_true, par, if_true]; rw [Nat.odd_iff]; have := Nat.even_iff.1 he; omega
          · simp only [he, decide_false, par, Bool.false_eq_true, if_false]; rw [Nat.even_iff]
            have := Nat.odd_iff.1 (Nat.not_even_iff_odd.1 he); omega
        have h1 := H2 E₂' hE₂'D hne2' hpar2'
        rw [lt_div_iff₀ (by positivity)] at h1
        obtain ⟨hm2', _⟩ := minFac_prod hE₂'p hne2'
        set q' := (∏ x ∈ E₂', x).minFac with hq'
        have hqq' : q < q' := by
          have hne' : q' ≠ q := ne_of_mem_erase hm2'
          exact lt_of_le_of_ne (hmin2 q' (mem_of_mem_erase hm2')) (Ne.symm hne')
        have hqq'' : (q : ℝ) < q' := by exact_mod_cast hqq'
        have hP2 : ((∏ x ∈ E₂, x : ℕ) : ℝ) = q * ((∏ x ∈ E₂', x : ℕ) : ℝ) := by
          rw [hE₂', ← mul_prod_erase E₂ (fun x => x) hm2]; push_cast; ring
        have hP2' : (0 : ℝ) < ((∏ x ∈ E₂', x : ℕ) : ℝ) := by exact_mod_cast prod_pos_of_primes hE₂'p
        rw [hP2]
        have : (q : ℝ) ^ 3 < r * (q' : ℝ) ^ 2 := by
          have a : (q : ℝ) < r := by linarith
          have b : (q : ℝ) ^ 2 < (q' : ℝ) ^ 2 := by nlinarith
          nlinarith
        calc ((∏ q ∈ Ea, q : ℕ) : ℝ) * (q * ((∏ x ∈ E₂', x : ℕ) : ℝ)) * (q : ℝ) ^ 2
            = ((∏ q ∈ Ea, q : ℕ) : ℝ) * ((∏ x ∈ E₂', x : ℕ) : ℝ) * (q : ℝ) ^ 3 := by ring
          _ < ((∏ q ∈ Ea, q : ℕ) : ℝ) * ((∏ x ∈ E₂', x : ℕ) : ℝ) * (r * (q' : ℝ) ^ 2) :=
              mul_lt_mul_of_pos_left this (by positivity)
          _ = (((∏ q ∈ Ea, q : ℕ) : ℝ) * r) * ((∏ x ∈ E₂', x : ℕ) : ℝ) * (q' : ℝ) ^ 2 := by ring
          _ ≤ (p * ((∏ q ∈ D₁, q : ℕ) : ℝ)) * ((∏ x ∈ E₂', x : ℕ) : ℝ) * (q' : ℝ) ^ 2 := by gcongr
          _ < Y := lt_of_eq_of_lt (by ring) h1

end KappaOmega2.M10
