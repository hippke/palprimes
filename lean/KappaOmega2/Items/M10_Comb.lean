import KappaOmega2.Items.M10_Defs
import Palprimes.Sieve.SelbergSum

/-!
# M10 helper: set form of the Rosser sums and the head recursion (`M10_PLAN.md` §2, P1)

Divisors of `P(w)` ↔ subsets of `primesBelow w` (Palprimes `sum_divisors_primes`). `χ^±` in set form (`ChiS`).
P1: `χ⁻_Y(M·Π D) ↔ χ⁺_{Y/M}(Π D)` for a prime `M` above `D`.
(The same set-form approach is used independently in the M08 helper; nothing is imported from it.)
-/

set_option linter.style.longLine false

open Finset Real
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius

namespace KappaOmega2.M10

open Palprimes Palprimes.Greaves

/-! ## Grouping subsets by their maximum -/

theorem sum_powerset_max (S : Finset ℕ) (F : Finset ℕ → ℝ) :
    ∑ D ∈ S.powerset, F D = F ∅ + ∑ M ∈ S, ∑ D ∈ (S.filter (· < M)).powerset, F (insert M D) := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a S ha ih =>
    have haS : a ∉ S := fun h => lt_irrefl a (ha a h)
    have e1 : (insert a S).filter (· < a) = S := by
      ext x; simp only [mem_filter, mem_insert]; constructor
      · rintro ⟨rfl | hx, hlt⟩
        · exact absurd hlt (lt_irrefl _)
        · exact hx
      · intro hx; exact ⟨Or.inr hx, ha x hx⟩
    have e2 : ∀ M ∈ S, (insert a S).filter (· < M) = S.filter (· < M) := by
      intro M hM; ext x; simp only [mem_filter, mem_insert]; constructor
      · rintro ⟨rfl | hx, hlt⟩
        · exact absurd (lt_trans hlt (ha M hM)) (lt_irrefl _)
        · exact ⟨hx, hlt⟩
      · rintro ⟨hx, hlt⟩; exact ⟨Or.inr hx, hlt⟩
    have e3 : ∑ M ∈ S, ∑ D ∈ ((insert a S).filter (· < M)).powerset, F (insert M D) =
        ∑ M ∈ S, ∑ D ∈ (S.filter (· < M)).powerset, F (insert M D) :=
      sum_congr rfl (fun M hM => by rw [e2 M hM])
    rw [powerset_insert, sum_union, sum_image, ih, sum_insert haS, e1, e3]
    · ring
    · intro T1 hT1 T2 hT2 h
      have h1 : a ∉ T1 := fun h' => haS (mem_powerset.1 hT1 h')
      have h2 : a ∉ T2 := fun h' => haS (mem_powerset.1 hT2 h')
      rw [← erase_insert h1, ← erase_insert h2]
      exact congrArg (fun T => Finset.erase T a) h
    · rw [disjoint_left]
      intro T hT hT'
      obtain ⟨T', _, rfl⟩ := mem_image.1 hT'
      exact haS (mem_powerset.1 hT (mem_insert_self a T'))

theorem sum_powerset_of_support {A C : Finset ℕ} (hCA : C ⊆ A) (F : Finset ℕ → ℝ)
    (hF : ∀ E ⊆ A, F E ≠ 0 → E ⊆ C) : ∑ E ∈ A.powerset, F E = ∑ E ∈ C.powerset, F E := by
  symm
  apply sum_subset (powerset_mono.2 hCA)
  intro E hEA hEC
  by_contra h
  exact hEC (mem_powerset.2 (hF E (mem_powerset.1 hEA) h))

/-! ## Products of primes -/

theorem primes_of_primesBelow {w : ℝ} {D : Finset ℕ} (hD : D ⊆ primesBelow w) : ∀ p ∈ D, p.Prime :=
  fun p hp => ((mem_primesBelow w p).1 (hD hp)).1

theorem prod_pos_of_primes {E : Finset ℕ} (hE : ∀ p ∈ E, p.Prime) : 0 < ∏ p ∈ E, p :=
  prod_pos fun p hp => (hE p hp).pos

theorem omega_prod {E : Finset ℕ} (hE : ∀ p ∈ E, p.Prime) : ω (∏ p ∈ E, p) = E.card := by
  rw [ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors, Nat.primeFactors_prod hE]

theorem minFac_prod {E : Finset ℕ} (hE : ∀ p ∈ E, p.Prime) (hne : E.Nonempty) :
    (∏ p ∈ E, p).minFac ∈ E ∧ ∀ q ∈ E, (∏ p ∈ E, p).minFac ≤ q := by
  have h1 : (∏ p ∈ E, p) ≠ 1 := by
    obtain ⟨q, hq⟩ := hne
    intro h
    have := Finset.dvd_prod_of_mem (fun p => p) hq
    rw [h] at this
    exact (hE q hq).ne_one (Nat.dvd_one.1 this)
  have hmem : (∏ p ∈ E, p).minFac ∈ (∏ p ∈ E, p).primeFactors := by
    rw [Nat.mem_primeFactors]
    exact ⟨Nat.minFac_prime h1, Nat.minFac_dvd _, (prod_pos_of_primes hE).ne'⟩
  rw [Nat.primeFactors_prod hE] at hmem
  exact ⟨hmem, fun q hq => Nat.minFac_le_of_dvd (hE q hq).two_le (Finset.dvd_prod_of_mem _ hq)⟩

theorem minFac_prod_insert {E : Finset ℕ} {M : ℕ} (hE : ∀ p ∈ E, p.Prime) (hM : M.Prime)
    (hlt : ∀ q ∈ E, q < M) (hne : E.Nonempty) :
    (∏ p ∈ insert M E, p).minFac = (∏ p ∈ E, p).minFac := by
  have hE' : ∀ p ∈ insert M E, p.Prime := by
    intro p hp; rcases mem_insert.1 hp with rfl | hp
    · exact hM
    · exact hE p hp
  obtain ⟨h1, h2⟩ := minFac_prod hE' (insert_nonempty M E)
  obtain ⟨h3, h4⟩ := minFac_prod hE hne
  apply le_antisymm
  · exact h2 _ (mem_insert_of_mem h3)
  · rcases mem_insert.1 h1 with h | h
    · exfalso
      have := h4 _ h3
      have := hlt _ h3
      have := h2 _ (mem_insert_of_mem h3)
      omega
    · exact h4 _ h

/-! ## Rosser's conditions in set form -/

/-- Parity selector: `σ = true` constrains odd sizes (`χ⁺`), `σ = false` even sizes (`χ⁻`). -/
def par (σ : Bool) (n : ℕ) : Prop := if σ then Odd n else Even n

/-- `χ^σ_Y(Π D)` in set form. -/
def ChiS (σ : Bool) (Y : ℝ) (D : Finset ℕ) : Prop :=
  ∀ E ⊆ D, E.Nonempty → par σ E.card →
    ((∏ p ∈ E, p : ℕ) : ℝ) * (((∏ p ∈ E, p).minFac : ℕ) : ℝ) ^ 2 < Y

theorem chi_iff (σ : Bool) (Y : ℝ) {D : Finset ℕ} (hD : ∀ p ∈ D, p.Prime) :
    (if σ then chiPlusProp Y (∏ p ∈ D, p) else chiMinusProp Y (∏ p ∈ D, p)) ↔ ChiS σ Y D := by
  have hD0 : (∏ p ∈ D, p) ≠ 0 := (prod_pos_of_primes hD).ne'
  have hsq : Squarefree (∏ p ∈ D, p) := SelbergPort.prod_primes_squarefree D hD
  have key : (∀ h ∈ (∏ p ∈ D, p).divisors, h ≠ 1 → par σ (ω h) → (h : ℝ) * (h.minFac : ℝ) ^ 2 < Y) ↔
      ChiS σ Y D := by
    constructor
    · intro H E hED hne hpar
      have hEp : ∀ p ∈ E, p.Prime := fun p hp => hD p (hED hp)
      apply H
      · rw [Nat.mem_divisors]; exact ⟨prod_dvd_prod_of_subset _ _ _ hED, hD0⟩
      · obtain ⟨q, hq⟩ := hne
        intro h
        have := Finset.dvd_prod_of_mem (fun p => p) hq
        rw [h] at this
        exact (hEp q hq).ne_one (Nat.dvd_one.1 this)
      · rwa [omega_prod hEp]
    · intro H h hh h1 hpar
      rw [Nat.mem_divisors] at hh
      have hsub : h.primeFactors ⊆ D := by
        have := Nat.primeFactors_mono hh.1 hD0
        rwa [Nat.primeFactors_prod hD] at this
      have hprod : ∏ p ∈ h.primeFactors, p = h := Nat.prod_primeFactors_of_squarefree (hsq.squarefree_of_dvd hh.1)
      have hne : h.primeFactors.Nonempty := by
        rw [Nat.nonempty_primeFactors]
        have : h ≠ 0 := fun h0 => hD0 (by rw [h0] at hh; exact Nat.eq_zero_of_zero_dvd hh.1)
        omega
      have := H _ hsub hne (by
        rw [ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors] at hpar; exact hpar)
      rwa [hprod] at this
  rw [← key]
  cases σ <;> simp [chiPlusProp, chiMinusProp, par]

/-- P1: `χ⁻_Y(M · Π D) ↔ χ⁺_{Y/M}(Π D)` for a prime `M` above the primes `D`. -/
theorem chiS_minus_insert {Y : ℝ} {M : ℕ} {D : Finset ℕ} (hD : ∀ p ∈ D, p.Prime) (hM : M.Prime)
    (hlt : ∀ q ∈ D, q < M) : ChiS false Y (insert M D) ↔ ChiS true (Y / M) D := by
  have hMD : M ∉ D := fun h => lt_irrefl _ (hlt M h)
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM.pos
  constructor
  · intro H E hED hne hpar
    have hEp : ∀ p ∈ E, p.Prime := fun p hp => hD p (hED hp)
    have hME : M ∉ E := fun h => hMD (hED h)
    have h1 := H (insert M E) (insert_subset_insert M hED) (insert_nonempty M E) (by
      simp only [par] at hpar ⊢; rw [card_insert_of_notMem hME]; exact hpar.add_one)
    rw [minFac_prod_insert hEp hM (fun q hq => hlt q (hED hq)) hne, prod_insert hME] at h1
    rw [lt_div_iff₀ hM0]; push_cast at h1 ⊢; linarith
  · intro H E hED hne hpar
    simp only [par, Bool.false_eq_true, ite_false] at hpar
    by_cases hME : M ∈ E
    · set E₀ := E.erase M with hE₀
      have hE₀D : E₀ ⊆ D := by
        intro q hq; rw [mem_erase] at hq
        rcases mem_insert.1 (hED hq.2) with h | h
        · exact absurd h hq.1
        · exact h
      have hE : E = insert M E₀ := (insert_erase hME).symm
      have hc : E.card = E₀.card + 1 := by rw [hE, card_insert_of_notMem (notMem_erase M E)]
      have hodd : Odd E₀.card := by
        rw [hc] at hpar; exact (Nat.even_add_one.1 hpar) |> Nat.not_even_iff_odd.1
      have hne₀ : E₀.Nonempty := by
        rw [← card_pos]; exact hodd.pos
      have hE₀p : ∀ p ∈ E₀, p.Prime := fun p hp => hD p (hE₀D hp)
      have h1 := H E₀ hE₀D hne₀ (by simp only [par]; exact hodd)
      rw [hE, minFac_prod_insert hE₀p hM (fun q hq => hlt q (hE₀D hq)) hne₀,
        prod_insert (notMem_erase M E)]
      rw [lt_div_iff₀ hM0] at h1; push_cast at h1 ⊢; linarith
    · have hED' : E ⊆ D := by
        intro q hq; rcases mem_insert.1 (hED hq) with h | h
        · exact absurd (h ▸ hq) hME
        · exact h
      have hEp : ∀ p ∈ E, p.Prime := fun p hp => hD p (hED' hp)
      obtain ⟨hqE, hqmin⟩ := minFac_prod hEp hne
      set q := (∏ p ∈ E, p).minFac with hq
      set E₀ := E.erase q with hE₀
      have hE : E = insert q E₀ := (insert_erase hqE).symm
      have hc : E.card = E₀.card + 1 := by rw [hE, card_insert_of_notMem (notMem_erase q E)]
      have hodd : Odd E₀.card := by
        rw [hc] at hpar; exact (Nat.even_add_one.1 hpar) |> Nat.not_even_iff_odd.1
      have hne₀ : E₀.Nonempty := by rw [← card_pos]; exact hodd.pos
      have hE₀D : E₀ ⊆ D := fun x hx => hED' (mem_of_mem_erase hx)
      have hE₀p : ∀ p ∈ E₀, p.Prime := fun p hp => hD p (hE₀D hp)
      have h1 := H E₀ hE₀D hne₀ (by simp only [par]; exact hodd)
      obtain ⟨hq0E, hq0min⟩ := minFac_prod hE₀p hne₀
      set q₀ := (∏ p ∈ E₀, p).minFac with hq₀
      have hqq₀ : q < q₀ := by
        have hne' : q₀ ≠ q := (ne_of_mem_erase hq0E)
        exact lt_of_le_of_ne (hqmin q₀ (mem_of_mem_erase hq0E)) (Ne.symm hne')
      have hqM : q < M := hlt q (hED' hqE)
      have hprodE : (∏ p ∈ E, p) = q * ∏ p ∈ E₀, p := by
        rw [hE, prod_insert (notMem_erase q E)]
      have hP0 : (0 : ℝ) < ((∏ p ∈ E₀, p : ℕ) : ℝ) := by exact_mod_cast prod_pos_of_primes hE₀p
      have hq0' : (0 : ℝ) < q := by exact_mod_cast (hEp q hqE).pos
      have hqq₀' : (q : ℝ) < q₀ := by exact_mod_cast hqq₀
      have hqM' : (q : ℝ) < M := by exact_mod_cast hqM
      rw [lt_div_iff₀ hM0] at h1
      rw [hprodE]; push_cast
      have hprodE' : ((∏ p ∈ E₀, p : ℕ) : ℝ) = ∏ p ∈ E₀, (p : ℝ) := by push_cast; rfl
      rw [← hprodE']
      have hmf : ((q : ℕ) : ℝ) = (((∏ p ∈ E, p).minFac : ℕ) : ℝ) := by rw [hq]
      -- q · Π E₀ · q² < Π E₀ · q₀² · M
      have : (q : ℝ) * ((∏ p ∈ E₀, p : ℕ) : ℝ) * (q : ℝ) ^ 2 < ((∏ p ∈ E₀, p : ℕ) : ℝ) * (q₀ : ℝ) ^ 2 * M := by
        have a1 : (q : ℝ) ^ 2 < (q₀ : ℝ) ^ 2 := by nlinarith
        have a2 : (q : ℝ) * (q : ℝ) ^ 2 < M * (q₀ : ℝ) ^ 2 := by nlinarith
        nlinarith
      push_cast at h1 this ⊢
      linarith

end KappaOmega2.M10
