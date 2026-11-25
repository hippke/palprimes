import KappaOmega2.Statements
import Palprimes.E1.Main
import Palprimes.Sieve.SelbergSum

/-!
# M07 helper: the Jurkat–Richert conditions in set form for an arbitrary class of sizes

`ChiG C Y D`: every nonempty `E ⊆ D` with `C |E|` has `Π E · p(Π E)² < Y`. Peeling the largest prime
(`chiG_insert`, generalising M08's `chi_insert`), unions with a lower block (`chiG_union`), and the
translation of `chiProp`, `chiMinusProp`, `chiStarProp`, `chiPlusProp` (see `M07_PLAN.md` §0, §1).
-/

set_option linter.style.longLine false

open Finset Real
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius

namespace KappaOmega2.M07

open Palprimes Palprimes.Greaves Palprimes.MT

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
  refine ⟨hmem, fun q hq => Nat.minFac_le_of_dvd (hE q hq).two_le (Finset.dvd_prod_of_mem _ hq)⟩

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

/-- The generalised Jurkat–Richert condition in set form. -/
def ChiG (C : ℕ → Prop) (Y : ℝ) (D : Finset ℕ) : Prop :=
  ∀ E ⊆ D, E.Nonempty → C E.card →
    ((∏ p ∈ E, p : ℕ) : ℝ) * (((∏ p ∈ E, p).minFac : ℕ) : ℝ) ^ 2 < Y

theorem chiG_empty (C : ℕ → Prop) (Y : ℝ) : ChiG C Y ∅ := fun E hE hne _ => by
  rw [subset_empty] at hE; subst hE; exact absurd hne (by simp)

theorem chiG_mono {C : ℕ → Prop} {Y : ℝ} {D D' : Finset ℕ} (h : D' ⊆ D) (H : ChiG C Y D) : ChiG C Y D' :=
  fun E hE hne hc => H E (hE.trans h) hne hc

theorem chiG_mono_class {C C' : ℕ → Prop} {Y : ℝ} {D : Finset ℕ} (h : ∀ j, C' j → C j) (H : ChiG C Y D) :
    ChiG C' Y D := fun E hE hne hc => H E hE hne (h _ hc)

theorem chiG_congr_class {C C' : ℕ → Prop} {Y : ℝ} {D : Finset ℕ} (h : ∀ j, C' j ↔ C j) :
    ChiG C' Y D ↔ ChiG C Y D :=
  ⟨chiG_mono_class (fun j hj => (h j).2 hj), chiG_mono_class (fun j hj => (h j).1 hj)⟩

/-- Divisor form ↔ set form. -/
theorem chiG_iff (C : ℕ → Prop) (Y : ℝ) {D : Finset ℕ} (hD : ∀ p ∈ D, p.Prime) :
    (∀ h ∈ (∏ p ∈ D, p).divisors, h ≠ 1 → C (ω h) → (h : ℝ) * (h.minFac : ℝ) ^ 2 < Y) ↔ ChiG C Y D := by
  have hD0 : (∏ p ∈ D, p) ≠ 0 := (prod_pos_of_primes hD).ne'
  have hsq : Squarefree (∏ p ∈ D, p) := SelbergPort.prod_primes_squarefree D hD
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

/-- Class of `χ`: `ν` even or `ν ≤ 1/m`. -/
def Cchi (j : ℕ) : Prop := Even j ∨ (j : ℝ) ≤ 1 / mm
/-- Class of `χ*`: `ν` odd and `ν ≤ 1/m`. -/
def Cst (j : ℕ) : Prop := Odd j ∧ (j : ℝ) ≤ 1 / mm

theorem chi_iff' (y : ℝ) {D : Finset ℕ} (hD : ∀ p ∈ D, p.Prime) :
    chiProp y mm (∏ p ∈ D, p) ↔ ChiG Cchi y D := by
  rw [← chiG_iff Cchi y hD]; rfl

theorem chiMinus_iff' (y : ℝ) {D : Finset ℕ} (hD : ∀ p ∈ D, p.Prime) :
    chiMinusProp y (∏ p ∈ D, p) ↔ ChiG Even y D := by
  rw [← chiG_iff Even y hD]; rfl

theorem chiPlus_iff' (y : ℝ) {D : Finset ℕ} (hD : ∀ p ∈ D, p.Prime) :
    chiPlusProp y (∏ p ∈ D, p) ↔ ChiG Odd y D := by
  rw [← chiG_iff Odd y hD]; rfl

theorem chiStar_iff' (y : ℝ) {D : Finset ℕ} (hD : ∀ p ∈ D, p.Prime) :
    chiStarProp y mm (∏ p ∈ D, p) ↔ ChiG Cst y D := by
  rw [← chiG_iff Cst y hD]
  unfold chiStarProp Cst
  constructor
  · intro H h hh h1 hc; exact H h hh h1 hc.1 hc.2
  · intro H h hh h1 hc1 hc2; exact H h hh h1 ⟨hc1, hc2⟩

/-- `χ = χ⁻ ∧ χ*`. -/
theorem chiG_chi_iff (Y : ℝ) (D : Finset ℕ) : ChiG Cchi Y D ↔ ChiG Even Y D ∧ ChiG Cst Y D := by
  constructor
  · intro H
    exact ⟨chiG_mono_class (fun j hj => Or.inl hj) H, chiG_mono_class (fun j hj => Or.inr hj.2) H⟩
  · rintro ⟨H1, H2⟩ E hE hne hc
    rcases hc with hc | hc
    · exact H1 E hE hne hc
    · rcases Nat.even_or_odd E.card with he | ho
      · exact H1 E hE hne he
      · exact H2 E hE hne ⟨ho, hc⟩

/-- Peeling the largest prime. -/
theorem chiG_insert (C : ℕ → Prop) (Y : ℝ) {D : Finset ℕ} {M : ℕ} (hD : ∀ p ∈ D, p.Prime) (hM : M.Prime)
    (hlt : ∀ q ∈ D, q < M) :
    ChiG C Y (insert M D) ↔ ((C 1 → (M : ℝ) ^ 3 < Y) ∧ ChiG (fun j => C (j + 1)) (Y / M) D) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM.pos
  have hMD : M ∉ D := fun h => lt_irrefl M (hlt M h)
  have conv : ∀ E' ⊆ D, E'.Nonempty →
      ((((∏ p ∈ insert M E', p : ℕ) : ℝ) * (((∏ p ∈ insert M E', p).minFac : ℕ) : ℝ) ^ 2 < Y) ↔
        (((∏ p ∈ E', p : ℕ) : ℝ) * (((∏ p ∈ E', p).minFac : ℕ) : ℝ) ^ 2 < Y / M)) := by
    intro E' hE' hne
    have hE'p : ∀ p ∈ E', p.Prime := fun p hp => hD p (hE' hp)
    have hME' : M ∉ E' := fun h => hMD (hE' h)
    rw [minFac_prod_insert hE'p hM (fun q hq => hlt q (hE' hq)) hne, prod_insert hME', lt_div_iff₀ hM0]
    push_cast
    constructor <;> intro h <;> linarith
  have single : (((∏ p ∈ ({M} : Finset ℕ), p : ℕ) : ℝ) * (((∏ p ∈ ({M} : Finset ℕ), p).minFac : ℕ) : ℝ) ^ 2) =
      (M : ℝ) ^ 3 := by
    rw [prod_singleton, hM.minFac_eq]; ring
  constructor
  · intro H
    refine ⟨fun hσ => ?_, fun E' hE' hne hpar => ?_⟩
    · have := H {M} (by simp) (singleton_nonempty M) (by simpa using hσ)
      rwa [single] at this
    · have hME' : M ∉ E' := fun h => hMD (hE' h)
      have := H (insert M E') (insert_subset_insert M hE') (insert_nonempty M E') (by
        rw [card_insert_of_notMem hME']; exact hpar)
      exact (conv E' hE' hne).1 this
  · rintro ⟨hc, H⟩
    have A : ∀ E' ⊆ D, C (E'.card + 1) →
        ((∏ p ∈ insert M E', p : ℕ) : ℝ) * (((∏ p ∈ insert M E', p).minFac : ℕ) : ℝ) ^ 2 < Y := by
      intro E' hE' hpar
      rcases E'.eq_empty_or_nonempty with rfl | hne
      · rw [insert_empty, single]; exact hc (by simpa using hpar)
      · exact (conv E' hE' hne).2 (H E' hE' hne hpar)
    intro E hE hne hpar
    by_cases hME : M ∈ E
    · have hEe : E = insert M (E.erase M) := (insert_erase hME).symm
      have hsub : E.erase M ⊆ D := by
        intro x hx
        rcases mem_insert.1 (hE (mem_of_mem_erase hx)) with h | h
        · exact absurd h (ne_of_mem_erase hx)
        · exact h
      have hcard : E.card = (E.erase M).card + 1 := (card_erase_add_one hME).symm
      rw [hcard] at hpar
      rw [hEe]; exact A _ hsub hpar
    · have hED : E ⊆ D := by
        intro x hx
        rcases mem_insert.1 (hE hx) with h | h
        · exact absurd (h ▸ hx) hME
        · exact h
      have hEp : ∀ p ∈ E, p.Prime := fun p hp => hD p (hED hp)
      set q := E.max' hne with hq
      have hqE : q ∈ E := max'_mem E hne
      have hcard : E.card = (E.erase q).card + 1 := (card_erase_add_one hqE).symm
      rw [hcard] at hpar
      have hsub : E.erase q ⊆ D := fun x hx => hED (mem_of_mem_erase hx)
      have hA := A _ hsub hpar
      have hMer : M ∉ E.erase q := fun h => hMD (hsub h)
      have hIp : ∀ p ∈ insert M (E.erase q), p.Prime := by
        intro p hp; rcases mem_insert.1 hp with rfl | hp
        · exact hM
        · exact hEp p (mem_of_mem_erase hp)
      have hprod : (∏ p ∈ E, p) ≤ ∏ p ∈ insert M (E.erase q), p := by
        rw [(mul_prod_erase E (fun p => p) hqE).symm, prod_insert hMer]
        exact Nat.mul_le_mul_right _ (hlt q (hED hqE)).le
      have hmf : (∏ p ∈ E, p).minFac ≤ (∏ p ∈ insert M (E.erase q), p).minFac := by
        obtain ⟨h1, _⟩ := minFac_prod hIp (insert_nonempty M _)
        obtain ⟨_, h4⟩ := minFac_prod hEp hne
        rcases mem_insert.1 h1 with h | h
        · rw [h]; exact le_trans (h4 q hqE) (hlt q (hED hqE)).le
        · exact h4 _ (mem_of_mem_erase h)
      have hmf' : (((∏ p ∈ E, p).minFac : ℕ) : ℝ) ≤ (((∏ p ∈ insert M (E.erase q), p).minFac : ℕ) : ℝ) := by
        exact_mod_cast hmf
      have hprod' : ((∏ p ∈ E, p : ℕ) : ℝ) ≤ ((∏ p ∈ insert M (E.erase q), p : ℕ) : ℝ) := by
        exact_mod_cast hprod
      calc ((∏ p ∈ E, p : ℕ) : ℝ) * (((∏ p ∈ E, p).minFac : ℕ) : ℝ) ^ 2
          ≤ ((∏ p ∈ insert M (E.erase q), p : ℕ) : ℝ) *
              (((∏ p ∈ insert M (E.erase q), p).minFac : ℕ) : ℝ) ^ 2 := by
            apply mul_le_mul hprod' (pow_le_pow_left₀ (by positivity) hmf' 2) (by positivity) (by positivity)
        _ < Y := hA

/-- Singleton: `ChiG C Y {q} ↔ (C 1 → q³ < Y)`. -/
theorem chiG_singleton (C : ℕ → Prop) (Y : ℝ) {q : ℕ} (hq : q.Prime) :
    ChiG C Y {q} ↔ (C 1 → (q : ℝ) ^ 3 < Y) := by
  rw [← insert_empty, chiG_insert C Y (by simp) hq (by simp)]
  simp [chiG_empty]

/-- Union with a block of smaller primes. -/
theorem chiG_union (C : ℕ → Prop) (Y : ℝ) {Δ T : Finset ℕ} (hΔ : ∀ p ∈ Δ, p.Prime) (hT : ∀ p ∈ T, p.Prime)
    (hlt : ∀ t ∈ T, ∀ p ∈ Δ, t < p) :
    ChiG C Y (Δ ∪ T) ↔ ChiG C Y Δ ∧ ChiG (fun j => C (j + Δ.card)) (Y / ((∏ p ∈ Δ, p : ℕ) : ℝ)) T := by
  induction Δ using Finset.induction_on_max generalizing C Y with
  | empty =>
    simp only [empty_union, card_empty, add_zero, prod_empty, Nat.cast_one, div_one]
    exact ⟨fun h => ⟨chiG_empty _ _, h⟩, fun h => h.2⟩
  | insert M Δ' hM ih =>
    have hMp : M.Prime := hΔ M (mem_insert_self _ _)
    have hΔ' : ∀ p ∈ Δ', p.Prime := fun p hp => hΔ p (mem_insert_of_mem hp)
    have hMΔ' : M ∉ Δ' := fun h => lt_irrefl M (hM M h)
    have hlt' : ∀ t ∈ T, ∀ p ∈ Δ', t < p := fun t ht p hp => hlt t ht p (mem_insert_of_mem hp)
    have hU : ∀ p ∈ Δ' ∪ T, p.Prime := by
      intro p hp; rcases mem_union.1 hp with h | h
      · exact hΔ' p h
      · exact hT p h
    have hUlt : ∀ q ∈ Δ' ∪ T, q < M := by
      intro q hq; rcases mem_union.1 hq with h | h
      · exact hM q h
      · exact hlt q h M (mem_insert_self _ _)
    rw [insert_union, chiG_insert C Y hU hMp hUlt, chiG_insert C Y hΔ' hMp hM, ih _ _ hΔ' hlt']
    have hM0 : (0 : ℝ) < M := by exact_mod_cast hMp.pos
    have e1 : Y / M / ((∏ p ∈ Δ', p : ℕ) : ℝ) = Y / ((∏ p ∈ insert M Δ', p : ℕ) : ℝ) := by
      rw [prod_insert hMΔ']; push_cast; rw [div_div]
    have e2 : (fun j => (fun j => C (j + 1)) (j + Δ'.card)) = (fun j => C (j + (insert M Δ').card)) := by
      funext j; rw [card_insert_of_notMem hMΔ']; ring_nf
    rw [e1, e2]
    tauto

end KappaOmega2.M07
