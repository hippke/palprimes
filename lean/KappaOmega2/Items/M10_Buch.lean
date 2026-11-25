import KappaOmega2.Items.M10_Sets

/-!
# M10 helper: Buchstab steps for `T^±` (`M10_PLAN.md` §4.3, §4.4)

P1′: `χ⁺_Y(M·ΠD) ↔ M³ < Y ∧ χ⁻_{Y/M}(ΠD)`; the head sum `Σ_{D ⊆ P(M)} μγ/·(M·ΠD) χ^σ_Y(M·ΠD) = −γ(M)/M [cond] T^{¬σ}(Y/M, M)`;
`T^σ(Y, ζ') − T^σ(Y, ζ) = Σ_{ζ ≤ M < ζ'} (head sum at M)`.
-/

set_option linter.style.longLine false

open Finset Real
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius

namespace KappaOmega2.M10

open Palprimes Palprimes.Greaves
open Classical

/-- P1′: `χ⁺_Y(M · Π D) ↔ M³ < Y ∧ χ⁻_{Y/M}(Π D)` for a prime `M` above `D`. -/
theorem chiS_plus_insert {Y : ℝ} {M : ℕ} {D : Finset ℕ} (hD : ∀ p ∈ D, p.Prime) (hM : M.Prime)
    (hlt : ∀ q ∈ D, q < M) : ChiS true Y (insert M D) ↔ (M : ℝ) ^ 3 < Y ∧ ChiS false (Y / M) D := by
  have hMD : M ∉ D := fun h => lt_irrefl _ (hlt M h)
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM.pos
  constructor
  · intro H
    refine ⟨?_, ?_⟩
    · have h1 := H {M} (singleton_subset_iff.2 (mem_insert_self M D)) (singleton_nonempty M) (by simp [par])
      rw [prod_singleton, Nat.Prime.minFac_eq hM] at h1
      nlinarith
    · intro E hED hne hpar
      have hEp : ∀ p ∈ E, p.Prime := fun p hp => hD p (hED hp)
      have hME : M ∉ E := fun h => hMD (hED h)
      have h1 := H (insert M E) (insert_subset_insert M hED) (insert_nonempty M E) (by
        simp only [par, if_true] at hpar ⊢; rw [card_insert_of_notMem hME]
        simp only [par, Bool.false_eq_true, if_false] at hpar; exact hpar.add_one)
      rw [minFac_prod_insert hEp hM (fun q hq => hlt q (hED hq)) hne, prod_insert hME] at h1
      rw [lt_div_iff₀ hM0]; push_cast at h1 ⊢; linarith
  · rintro ⟨hM3, H⟩ E hED hne hpar
    simp only [par, if_true] at hpar
    by_cases hME : M ∈ E
    · set E₀ := E.erase M with hE₀
      have hE₀D : E₀ ⊆ D := by
        intro q hq; rw [mem_erase] at hq
        rcases mem_insert.1 (hED hq.2) with h | h
        · exact absurd h hq.1
        · exact h
      have hE : E = insert M E₀ := (insert_erase hME).symm
      have hc : E.card = E₀.card + 1 := by rw [hE, card_insert_of_notMem (notMem_erase M E)]
      by_cases hne₀ : E₀.Nonempty
      · have hev : Even E₀.card := by
          rw [hc] at hpar
          rcases Nat.even_or_odd E₀.card with h | h
          · exact h
          · exact absurd hpar (by rw [Nat.odd_add_one]; exact not_not.2 h)
        have hE₀p : ∀ p ∈ E₀, p.Prime := fun p hp => hD p (hE₀D hp)
        have h1 := H E₀ hE₀D hne₀ (by simp only [par, Bool.false_eq_true, if_false]; exact hev)
        rw [hE, minFac_prod_insert hE₀p hM (fun q hq => hlt q (hE₀D hq)) hne₀, prod_insert (notMem_erase M E)]
        rw [lt_div_iff₀ hM0] at h1; push_cast at h1 ⊢; linarith
      · have hE₀e : E₀ = ∅ := not_nonempty_iff_eq_empty.1 hne₀
        rw [hE, hE₀e, insert_empty, prod_singleton, Nat.Prime.minFac_eq hM]
        nlinarith
    · have hED' : E ⊆ D := by
        intro q hq; rcases mem_insert.1 (hED hq) with h | h
        · exact absurd (h ▸ hq) hME
        · exact h
      have hEp : ∀ p ∈ E, p.Prime := fun p hp => hD p (hED' hp)
      obtain ⟨hqE, hqmin⟩ := minFac_prod hEp hne
      set q := (∏ p ∈ E, p).minFac with hq
      have hqM : (q : ℝ) < M := by exact_mod_cast hlt q (hED' hqE)
      have hq0 : (0 : ℝ) < q := by exact_mod_cast (hEp q hqE).pos
      have hPM : ((∏ p ∈ E, p : ℕ) : ℝ) ≤ ((∏ p ∈ D, p : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_of_dvd (prod_pos_of_primes hD) (prod_dvd_prod_of_subset _ _ _ hED')
      -- E odd: if |E| = 1 then q³ < M³ < Y; otherwise drop q (E₀ even, nonempty)
      set E₀ := E.erase q with hE₀
      have hE : E = insert q E₀ := (insert_erase hqE).symm
      have hc : E.card = E₀.card + 1 := by rw [hE, card_insert_of_notMem (notMem_erase q E)]
      by_cases hne₀ : E₀.Nonempty
      · have hev : Even E₀.card := by
          rw [hc] at hpar
          rcases Nat.even_or_odd E₀.card with h | h
          · exact h
          · exact absurd hpar (by rw [Nat.odd_add_one]; exact not_not.2 h)
        have hE₀D : E₀ ⊆ D := fun x hx => hED' (mem_of_mem_erase hx)
        have hE₀p : ∀ p ∈ E₀, p.Prime := fun p hp => hD p (hE₀D hp)
        have h1 := H E₀ hE₀D hne₀ (by simp only [par, Bool.false_eq_true, if_false]; exact hev)
        obtain ⟨hq0E, _⟩ := minFac_prod hE₀p hne₀
        set q₀ := (∏ p ∈ E₀, p).minFac with hq₀
        have hqq₀ : (q : ℝ) < q₀ := by
          have hne' : q₀ ≠ q := ne_of_mem_erase hq0E
          exact_mod_cast lt_of_le_of_ne (hqmin q₀ (mem_of_mem_erase hq0E)) (Ne.symm hne')
        have hprodE : ((∏ p ∈ E, p : ℕ) : ℝ) = q * ((∏ p ∈ E₀, p : ℕ) : ℝ) := by
          rw [hE, prod_insert (notMem_erase q E)]; push_cast; ring
        have hP0 : (0 : ℝ) < ((∏ p ∈ E₀, p : ℕ) : ℝ) := by exact_mod_cast prod_pos_of_primes hE₀p
        rw [hprodE]
        rw [lt_div_iff₀ hM0] at h1
        have : (q : ℝ) * (q : ℝ) ^ 2 < (q₀ : ℝ) ^ 2 * M := by
          have a : (q : ℝ) ^ 2 < (q₀ : ℝ) ^ 2 := by nlinarith
          nlinarith
        calc (q : ℝ) * ((∏ p ∈ E₀, p : ℕ) : ℝ) * (q : ℝ) ^ 2 = ((∏ p ∈ E₀, p : ℕ) : ℝ) * ((q : ℝ) * (q : ℝ) ^ 2) := by ring
          _ < ((∏ p ∈ E₀, p : ℕ) : ℝ) * ((q₀ : ℝ) ^ 2 * M) := mul_lt_mul_of_pos_left this hP0
          _ = ((∏ p ∈ E₀, p : ℕ) : ℝ) * (q₀ : ℝ) ^ 2 * M := by ring
          _ < Y := h1
      · have hE₀e : E₀ = ∅ := not_nonempty_iff_eq_empty.1 hne₀
        have hEq : E = {q} := by rw [hE, hE₀e, insert_empty]
        rw [hEq, prod_singleton]
        have : (q : ℝ) ^ 3 < (M : ℝ) ^ 3 := by
          have := pow_lt_pow_left₀ hqM hq0.le (by norm_num : (3 : ℕ) ≠ 0); exact this
        nlinarith

/-- Head sum at `M`: `Σ_{D ⊆ P(M)} μγ/·(M ΠD) χ^σ_Y(M ΠD) = −γ(M)/M · [σ → M³ < Y] · T^{¬σ}(Y/M, M)`. -/
theorem head_sum (b : ℕ) (σ : Bool) (Y : ℝ) {M : ℕ} (hM : M.Prime) :
    ∑ D ∈ (primesBelow (M : ℝ)).powerset, fm b (∏ p ∈ insert M D, p) * (if ChiS σ Y (insert M D) then 1 else 0) =
      -(rhoB b M / M) * (if σ = true → (M : ℝ) ^ 3 < Y then 1 else 0) * Tpm b (!σ) (Y / M) M := by
  rw [Tpm_set, mul_sum]
  apply sum_congr rfl; intro D hD
  have hDp : ∀ p ∈ D, p.Prime := fun p hp => primes_PB _ p (mem_powerset.1 hD hp)
  have hlt : ∀ q ∈ D, q < M := by
    intro q hq
    have := ((mem_primesBelow _ q).1 (mem_powerset.1 hD hq)).2
    exact_mod_cast this
  have hMD : M ∉ D := fun h => lt_irrefl _ (hlt M h)
  rw [fm_insert b hM hDp hMD]
  cases σ with
  | false =>
    have h := chiS_minus_insert (Y := Y) hDp hM hlt
    simp only [Bool.not_false, Bool.false_eq_true, false_implies, if_true, mul_one]
    by_cases hc : ChiS true (Y / M) D
    · rw [if_pos (h.2 hc), if_pos hc]; ring
    · rw [if_neg (mt h.1 hc), if_neg hc]; ring
  | true =>
    have h := chiS_plus_insert (Y := Y) hDp hM hlt
    simp only [Bool.not_true, forall_const]
    by_cases h3 : (M : ℝ) ^ 3 < Y
    · by_cases hc : ChiS false (Y / M) D
      · rw [if_pos (h.2 ⟨h3, hc⟩), if_pos h3, if_pos hc]; ring
      · rw [if_neg (fun h' => hc (h.1 h').2), if_pos h3, if_neg hc]; ring
    · rw [if_neg (fun h' => h3 (h.1 h').1), if_neg h3]; ring

/-- Buchstab difference: `T^σ(Y, ζ') − T^σ(Y, ζ) = Σ_{ζ ≤ M < ζ'} (head sum at M)`. -/
theorem Tpm_diff (b : ℕ) (σ : Bool) (Y : ℝ) {ζ ζ' : ℝ} (h : ζ ≤ ζ') :
    Tpm b σ Y ζ' - Tpm b σ Y ζ = ∑ M ∈ (primesBelow ζ').filter (fun M : ℕ => ζ ≤ (M : ℝ)),
      -(rhoB b M / M) * (if σ = true → (M : ℝ) ^ 3 < Y then 1 else 0) * Tpm b (!σ) (Y / M) M := by
  rw [Tpm_max, Tpm_max]
  have hsplit := (sum_filter_add_sum_filter_not (primesBelow ζ') (fun M : ℕ => (M : ℝ) < ζ)
    (fun M => ∑ D ∈ (primesBelow (M : ℝ)).powerset, fm b (∏ p ∈ insert M D, p) * (if ChiS σ Y (insert M D) then 1 else 0)))
  have hPB : (primesBelow ζ').filter (fun M : ℕ => (M : ℝ) < ζ) = primesBelow ζ := by
    ext q; simp only [mem_filter, mem_primesBelow]
    constructor
    · rintro ⟨⟨hq, _⟩, h2⟩; exact ⟨hq, h2⟩
    · rintro ⟨hq, h2⟩; exact ⟨⟨hq, lt_of_lt_of_le h2 h⟩, h2⟩
  rw [hPB] at hsplit
  rw [← hsplit]
  have hnot : (primesBelow ζ').filter (fun M : ℕ => ¬ (M : ℝ) < ζ) = (primesBelow ζ').filter (fun M : ℕ => ζ ≤ (M : ℝ)) := by
    congr 1; ext M; exact not_lt
  rw [hnot]
  have : ∀ M ∈ (primesBelow ζ').filter (fun M : ℕ => ζ ≤ (M : ℝ)),
      ∑ D ∈ (primesBelow (M : ℝ)).powerset, fm b (∏ p ∈ insert M D, p) * (if ChiS σ Y (insert M D) then 1 else 0) =
      -(rhoB b M / M) * (if σ = true → (M : ℝ) ^ 3 < Y then 1 else 0) * Tpm b (!σ) (Y / M) M :=
    fun M hM => head_sum b σ Y (primes_PB _ M (mem_filter.1 hM).1)
  rw [sum_congr rfl this]; ring

end KappaOmega2.M10
