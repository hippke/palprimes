import KappaOmega2.Statements
import Palprimes.E1.Main
import Palprimes.Sieve.SelbergSum

/-!
# M08 helper: combinatorics of `Tpm` and of the `t`-sums of Lemma 9 (see `M08_PLAN.md`, Steps 1–4)
-/

set_option linter.style.longLine false

open Finset Real
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius

namespace KappaOmega2.M08

open Palprimes Palprimes.Greaves Palprimes.MT

/-! ## Grouping subsets by their maximum / minimum -/

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

theorem sum_powerset_min (S : Finset ℕ) (F : Finset ℕ → ℝ) :
    ∑ D ∈ S.powerset, F D = F ∅ + ∑ m ∈ S, ∑ D ∈ (S.filter (m < ·)).powerset, F (insert m D) := by
  induction S using Finset.induction_on_min with
  | empty => simp
  | insert a S ha ih =>
    have haS : a ∉ S := fun h => lt_irrefl a (ha a h)
    have e1 : (insert a S).filter (a < ·) = S := by
      ext x; simp only [mem_filter, mem_insert]; constructor
      · rintro ⟨rfl | hx, hlt⟩
        · exact absurd hlt (lt_irrefl _)
        · exact hx
      · intro hx; exact ⟨Or.inr hx, ha x hx⟩
    have e2 : ∀ M ∈ S, (insert a S).filter (M < ·) = S.filter (M < ·) := by
      intro M hM; ext x; simp only [mem_filter, mem_insert]; constructor
      · rintro ⟨rfl | hx, hlt⟩
        · exact absurd (lt_trans hlt (ha M hM)) (lt_irrefl _)
        · exact ⟨hx, hlt⟩
      · rintro ⟨hx, hlt⟩; exact ⟨Or.inr hx, hlt⟩
    have e3 : ∑ M ∈ S, ∑ D ∈ ((insert a S).filter (M < ·)).powerset, F (insert M D) =
        ∑ M ∈ S, ∑ D ∈ (S.filter (M < ·)).powerset, F (insert M D) :=
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

/-- If `F` vanishes outside the subsets of `C ⊆ A`, the powerset sums over `A` and over `C` agree. -/
theorem sum_powerset_of_support {A C : Finset ℕ} (hCA : C ⊆ A) (F : Finset ℕ → ℝ)
    (hF : ∀ E ⊆ A, F E ≠ 0 → E ⊆ C) : ∑ E ∈ A.powerset, F E = ∑ E ∈ C.powerset, F E := by
  symm
  apply sum_subset (powerset_mono.2 hCA)
  intro E hEA hEC
  by_contra h
  exact hEC (mem_powerset.2 (hF E (mem_powerset.1 hEA) h))

/-! ## Products of sets of primes -/

theorem prod_pos_of_primes {E : Finset ℕ} (hE : ∀ p ∈ E, p.Prime) : 0 < ∏ p ∈ E, p :=
  prod_pos fun p hp => (hE p hp).pos

theorem omega_prod {E : Finset ℕ} (hE : ∀ p ∈ E, p.Prime) : ω (∏ p ∈ E, p) = E.card := by
  rw [ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors, Nat.primeFactors_prod hE]

/-- `minFac (Π E)` is an element of `E` below every element of `E`. -/
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

/-- `minFac (Π (insert M E)) = minFac (Π E)` when `E ≠ ∅` and `M` is above `E`. -/
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

theorem par_succ (σ : Bool) (n : ℕ) : par σ (n + 1) ↔ par (!σ) n := by
  cases σ <;> simp [par, Nat.even_add_one, Nat.odd_add_one]

theorem chi_insert (σ : Bool) (Y : ℝ) {D : Finset ℕ} {M : ℕ} (hD : ∀ p ∈ D, p.Prime) (hM : M.Prime)
    (hlt : ∀ q ∈ D, q < M) :
    ChiS σ Y (insert M D) ↔ ((σ = true → (M : ℝ) ^ 3 < Y) ∧ ChiS (!σ) (Y / M) D) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM.pos
  have hMD : M ∉ D := fun h => lt_irrefl M (hlt M h)
  -- the inequality for `insert M E'` versus the one for `E'` at level `Y / M`
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
    · have := H {M} (by simp) (singleton_nonempty M) (by subst hσ; simp [par])
      rwa [single] at this
    · have hME' : M ∉ E' := fun h => hMD (hE' h)
      have := H (insert M E') (insert_subset_insert M hE') (insert_nonempty M E') (by
        rw [card_insert_of_notMem hME', par_succ]; exact hpar)
      exact (conv E' hE' hne).1 this
  · rintro ⟨hc, H⟩
    -- claim A: subsets containing `M`
    have A : ∀ E' ⊆ D, par (!σ) E'.card →
        ((∏ p ∈ insert M E', p : ℕ) : ℝ) * (((∏ p ∈ insert M E', p).minFac : ℕ) : ℝ) ^ 2 < Y := by
      intro E' hE' hpar
      rcases E'.eq_empty_or_nonempty with rfl | hne
      · have hσ : σ = true := by cases σ <;> simp_all [par]
        rw [insert_empty, single]; exact hc hσ
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
      rw [hcard, par_succ] at hpar
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
      rw [hcard, par_succ] at hpar
      have hsub : E.erase q ⊆ D := fun x hx => hED (mem_of_mem_erase hx)
      have hA := A _ hsub hpar
      have hMer : M ∉ E.erase q := fun h => hMD (hsub h)
      have hIp : ∀ p ∈ insert M (E.erase q), p.Prime := by
        intro p hp; rcases mem_insert.1 hp with rfl | hp
        · exact hM
        · exact hEp p (mem_of_mem_erase hp)
      -- `Π E ≤ Π (insert M (E \ {q}))` and the same for `minFac`
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

/-! ## Set form of `Tpm` and Rosser's recursion -/

/-- `γ(Π D)/Π D` as a product. -/
noncomputable def gD (b : ℕ) (D : Finset ℕ) : ℝ := ∏ p ∈ D, gB b p

theorem gD_nonneg (b : ℕ) (D : Finset ℕ) : 0 ≤ gD b D := prod_nonneg fun p _ => gB_nonneg b p

/-- The set form of `T^σ(Y, ·)` over a set `S` of primes. -/
noncomputable def TS (b : ℕ) (σ : Bool) (Y : ℝ) (S : Finset ℕ) : ℝ :=
  open Classical in ∑ D ∈ S.powerset, (-1 : ℝ) ^ D.card * gD b D * (if ChiS σ Y D then 1 else 0)

theorem rho_div_prod (b : ℕ) {D : Finset ℕ} (hD : ∀ p ∈ D, p.Prime) :
    rhoB b (∏ p ∈ D, p) / ((∏ p ∈ D, p : ℕ) : ℝ) = gD b D := by
  unfold rhoB gD gB
  by_cases h : Nat.Coprime (∏ p ∈ D, p) (bigB b)
  · rw [if_pos h]
    have h' : ∀ p ∈ D, Nat.Coprime p (bigB b) := fun p hp =>
      Nat.Coprime.coprime_dvd_left (dvd_prod_of_mem _ hp) h
    rw [prod_congr rfl (fun p hp => if_pos ⟨hD p hp, h' p hp⟩), Nat.cast_prod, one_div, ← prod_inv_distrib]
    simp [one_div]
  · rw [if_neg h, zero_div]
    rw [Nat.coprime_prod_left_iff] at h
    push_neg at h
    obtain ⟨p, hp, hpc⟩ := h
    symm
    apply prod_eq_zero hp
    rw [if_neg]
    rintro ⟨_, h2⟩
    exact hpc h2

theorem moebius_prod {D : Finset ℕ} (hD : ∀ p ∈ D, p.Prime) :
    ((μ (∏ p ∈ D, p) : ℤ) : ℝ) = (-1 : ℝ) ^ D.card := by
  have h := ArithmeticFunction.IsMultiplicative.map_prod_of_subset_primeFactors
    ArithmeticFunction.isMultiplicative_moebius (∏ p ∈ D, p) D (by rw [Nat.primeFactors_prod hD])
  rw [h, prod_congr rfl (fun p hp => ArithmeticFunction.moebius_apply_prime (hD p hp)), prod_const]
  push_cast; ring

theorem primesBelow_prime {w : ℝ} {p : ℕ} (hp : p ∈ primesBelow w) : p.Prime :=
  ((mem_primesBelow w p).1 hp).1

theorem Tpm_eq_TS (b : ℕ) (σ : Bool) (Y w : ℝ) : Tpm b σ Y w = TS b σ Y (primesBelow w) := by
  classical
  unfold Tpm primorialLt TS
  rw [sum_divisors_primes _ (fun p hp => primesBelow_prime hp)]
  apply sum_congr rfl
  intro D hD
  have hDp : ∀ p ∈ D, p.Prime := fun p hp => primesBelow_prime (mem_powerset.1 hD hp)
  rw [moebius_prod hDp, mul_assoc, mul_div_assoc, rho_div_prod b hDp]
  have hc := chi_iff σ Y hDp
  by_cases h : ChiS σ Y D
  · rw [if_pos (hc.2 h), if_pos h]; ring
  · rw [if_neg (fun h' => h (hc.1 h')), if_neg h]; ring

/-- Rosser's recursion from the largest prime, set form. -/
theorem TS_rec (b : ℕ) (σ : Bool) (Y : ℝ) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    TS b σ Y S = 1 - ∑ M ∈ S, (if (σ = true → (M : ℝ) ^ 3 < Y) then
      gB b M * TS b (!σ) (Y / M) (S.filter (· < M)) else 0) := by
  classical
  have hF := sum_powerset_max S (fun D => (-1 : ℝ) ^ D.card * gD b D * (if ChiS σ Y D then 1 else 0))
  have h0 : ChiS σ Y ∅ := fun E hE hne _ => by
    rw [subset_empty] at hE; subst hE; exact absurd hne (by simp)
  have key : ∀ M ∈ S, ∑ D ∈ (S.filter (· < M)).powerset,
      (-1 : ℝ) ^ (insert M D).card * gD b (insert M D) * (if ChiS σ Y (insert M D) then 1 else 0) =
      -(if (σ = true → (M : ℝ) ^ 3 < Y) then gB b M * TS b (!σ) (Y / M) (S.filter (· < M)) else 0) := by
    intro M hM
    have hMp := hS M hM
    by_cases hc : (σ = true → (M : ℝ) ^ 3 < Y)
    · rw [if_pos hc]
      unfold TS
      rw [mul_sum, ← sum_neg_distrib]
      apply sum_congr rfl
      intro D hD
      have hDS := mem_powerset.1 hD
      have hlt : ∀ q ∈ D, q < M := fun q hq => (mem_filter.1 (hDS hq)).2
      have hDp : ∀ p ∈ D, p.Prime := fun p hp => hS p (mem_filter.1 (hDS hp)).1
      have hMD : M ∉ D := fun h => lt_irrefl M (hlt M h)
      have hci := chi_insert σ Y hDp hMp hlt
      unfold gD
      rw [card_insert_of_notMem hMD, prod_insert hMD, pow_succ]
      by_cases hC : ChiS (!σ) (Y / M) D
      · rw [if_pos (hci.2 ⟨hc, hC⟩), if_pos hC]; ring
      · rw [if_neg (fun h => hC (hci.1 h).2), if_neg hC]; ring
    · rw [if_neg hc, neg_zero]
      apply sum_eq_zero
      intro D hD
      have hDS := mem_powerset.1 hD
      have hlt : ∀ q ∈ D, q < M := fun q hq => (mem_filter.1 (hDS hq)).2
      have hDp : ∀ p ∈ D, p.Prime := fun p hp => hS p (mem_filter.1 (hDS hp)).1
      rw [if_neg (fun h => hc ((chi_insert σ Y hDp hMp hlt).1 h).1)]; ring
  rw [show TS b σ Y S = ∑ D ∈ S.powerset, (-1 : ℝ) ^ D.card * gD b D * (if ChiS σ Y D then 1 else 0) from rfl,
    hF, sum_congr rfl key, sum_neg_distrib, if_pos h0, card_empty, pow_zero]
  simp only [gD, prod_empty]
  ring

theorem primesBelow_filter_lt (w : ℝ) {P : ℕ} (hP : P ∈ primesBelow w) :
    (primesBelow w).filter (· < P) = primesBelow (P : ℝ) := by
  ext q
  rw [mem_filter, mem_primesBelow, mem_primesBelow]
  have hPw := ((mem_primesBelow w P).1 hP).2
  constructor
  · rintro ⟨⟨hq, _⟩, hqP⟩; exact ⟨hq, by exact_mod_cast hqP⟩
  · rintro ⟨hq, hqP⟩
    have hqP' : q < P := by exact_mod_cast hqP
    exact ⟨⟨hq, lt_trans hqP hPw⟩, hqP'⟩

/-- **(A)** Rosser's recursion for `Tpm`. -/
theorem Tpm_rec (b : ℕ) (σ : Bool) (Y w : ℝ) :
    Tpm b σ Y w = 1 - ∑ p ∈ primesBelow w, (if (σ = true → (p : ℝ) ^ 3 < Y) then
      gB b p * Tpm b (!σ) (Y / p) p else 0) := by
  rw [Tpm_eq_TS, TS_rec b σ Y (fun p hp => primesBelow_prime hp)]
  congr 1
  apply sum_congr rfl
  intro p hp
  rw [primesBelow_filter_lt w hp, Tpm_eq_TS]

theorem lt_cbrt_iff {Y p : ℝ} (hY : 0 ≤ Y) (hp : 0 ≤ p) : p < Y ^ ((1 : ℝ) / 3) ↔ p ^ 3 < Y := by
  have e : (Y ^ ((1 : ℝ) / 3)) ^ 3 = Y := by
    rw [show ((1 : ℝ) / 3) = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.rpow_inv_natCast_pow hY (by norm_num)
  conv_rhs => rw [← e]
  exact (pow_lt_pow_iff_left₀ hp (Real.rpow_nonneg hY _) (by norm_num)).symm

/-- **(I1)** `T⁺(Y, w) = σ⁺(Y) + Σ_{w ≤ p, p³ < Y} g(p) T⁻(Y/p, p)`. -/
theorem I1 (b : ℕ) {Y : ℝ} (hY : 0 < Y) (w : ℝ) :
    Tpm b true Y w = sigmaP b Y +
      ∑ p ∈ (primesBelow (Y ^ ((1 : ℝ) / 3))).filter (fun p : ℕ => w ≤ (p : ℝ)),
        gB b p * Tpm b false (Y / p) p := by
  classical
  set f : ℕ → ℝ := fun p => gB b p * Tpm b false (Y / p) p with hf
  have hA := Tpm_rec b true Y w
  have hB := Tpm_rec b true Y (Y ^ ((1 : ℝ) / 3))
  simp only [forall_const, Bool.not_true] at hA hB
  unfold sigmaP
  rw [hA, hB]
  have e1 : ∑ p ∈ primesBelow w, (if (p : ℝ) ^ 3 < Y then gB b p * Tpm b false (Y / p) p else 0) =
      ∑ p ∈ (primesBelow (Y ^ ((1 : ℝ) / 3))).filter (fun p : ℕ => ¬ w ≤ (p : ℝ)), f p := by
    rw [← sum_filter]
    apply sum_congr _ (fun _ _ => rfl)
    ext p
    simp only [mem_filter, mem_primesBelow, not_le]
    rw [lt_cbrt_iff hY.le (Nat.cast_nonneg p)]
    tauto
  have e2 : ∑ p ∈ primesBelow (Y ^ ((1 : ℝ) / 3)), (if (p : ℝ) ^ 3 < Y then gB b p * Tpm b false (Y / p) p else 0) =
      ∑ p ∈ primesBelow (Y ^ ((1 : ℝ) / 3)), f p := by
    apply sum_congr rfl
    intro p hp
    rw [if_pos ((lt_cbrt_iff hY.le (Nat.cast_nonneg p)).1 ((mem_primesBelow _ p).1 hp).2)]
  rw [e1, e2, ← sum_filter_add_sum_filter_not (primesBelow (Y ^ ((1 : ℝ) / 3))) (fun p : ℕ => w ≤ (p : ℝ)) f]
  ring

/-- **(I2)** `T⁻(Y, w) = T⁻(Y, √Y) + Σ_{w ≤ p, p² < Y} g(p) T⁺(Y/p, p)` for `w ≤ √Y`. -/
theorem I2 (b : ℕ) (Y : ℝ) {w : ℝ} (hw : w ≤ Real.sqrt Y) :
    Tpm b false Y w = Tpm b false Y (Real.sqrt Y) +
      ∑ p ∈ (primesBelow (Real.sqrt Y)).filter (fun p : ℕ => w ≤ (p : ℝ)),
        gB b p * Tpm b true (Y / p) p := by
  classical
  set f : ℕ → ℝ := fun p => gB b p * Tpm b true (Y / p) p with hf
  have hA := Tpm_rec b false Y w
  have hB := Tpm_rec b false Y (Real.sqrt Y)
  simp only [Bool.false_eq_true, IsEmpty.forall_iff, if_true, Bool.not_false] at hA hB
  rw [hA, hB]
  have e1 : primesBelow w = (primesBelow (Real.sqrt Y)).filter (fun p : ℕ => ¬ w ≤ (p : ℝ)) := by
    ext p
    simp only [mem_filter, mem_primesBelow, not_le]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, lt_of_lt_of_le h2 hw⟩, h2⟩
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
  rw [e1, ← sum_filter_add_sum_filter_not (primesBelow (Real.sqrt Y)) (fun p : ℕ => w ≤ (p : ℝ)) f]
  ring

/-! ## Crude bound `|T| ≤ 1/V` -/

theorem abs_TS_le (b : ℕ) (σ : Bool) (Y : ℝ) (S : Finset ℕ) : |TS b σ Y S| ≤ ∏ p ∈ S, (1 + gB b p) := by
  classical
  unfold TS
  rw [prod_one_add]
  refine le_trans (abs_sum_le_sum_abs _ _) (sum_le_sum fun D _ => ?_)
  rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg (gD_nonneg b D)]
  unfold gD
  have : |(if ChiS σ Y D then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
  nlinarith [gD_nonneg b D, show (0 : ℝ) ≤ ∏ p ∈ D, gB b p from gD_nonneg b D]

theorem prod_one_add_le_inv_VB (b : ℕ) (x : ℝ) : ∏ p ∈ primesBelow x, (1 + gB b p) ≤ 1 / VB b x := by
  have hV := Palprimes.E1.VB_pos' b x
  rw [le_div_iff₀ hV]
  unfold VB
  rw [← prod_mul_distrib]
  apply prod_le_one₀
  · intro p _
    have h1 := gB_nonneg b p
    have h2 := Palprimes.E1.gB_le_half' b p
    nlinarith
  · intro p _
    have h1 := gB_nonneg b p
    have h2 := Palprimes.E1.gB_le_half' b p
    nlinarith

theorem abs_Tpm_le (b : ℕ) (σ : Bool) (Y x : ℝ) : |Tpm b σ Y x| ≤ 1 / VB b x := by
  rw [Tpm_eq_TS]
  exact le_trans (abs_TS_le b σ Y _) (prod_one_add_le_inv_VB b x)

/-! ## The `t`-sums of Lemma 9 and their recursion (smallest prime) -/

/-- `S9(Y, w, σ)`: the `t`-set of Lemma 9 at general level `Y` and lower bound `w` (same shape as `T9set`). -/
noncomputable def S9 (Y w : ℝ) (plus : Bool) : Finset ℕ :=
  open Classical in
  (primorialLt Y).divisors.filter (fun t : ℕ => (∀ p ∈ t.primeFactors, w < (p : ℝ)) ∧
    (∀ p ∈ t.primeFactors, (p : ℝ) < Y / t) ∧ (if plus then Even (ω t) else Odd (ω t)))

/-- `R^σ(Y, w) = Σ_{t ∈ S9(Y, w, σ)} γ(t)/t σ⁺(Y/t)`. -/
noncomputable def R (b : ℕ) (σ : Bool) (Y w : ℝ) : ℝ :=
  ∑ t ∈ S9 Y w σ, rhoB b t / t * sigmaP b (Y / t)

theorem T9sum_eq_R (b : ℕ) (y s : ℝ) (plus : Bool) : T9sum b y s plus = R b plus y (y ^ (1 / s)) := rfl

/-- Set form of the membership condition of `S9`. -/
def cond9 (σ : Bool) (Y w : ℝ) (E : Finset ℕ) : Prop :=
  (∀ p ∈ E, w < (p : ℝ)) ∧ (∀ p ∈ E, (p : ℝ) < Y / ((∏ q ∈ E, q : ℕ) : ℝ)) ∧
    (if σ then Even E.card else Odd E.card)

/-- Set form of `R`. -/
noncomputable def RS (b : ℕ) (σ : Bool) (Y w : ℝ) : ℝ :=
  open Classical in
  ∑ E ∈ (primesBelow Y).powerset,
    if cond9 σ Y w E then gD b E * sigmaP b (Y / ((∏ q ∈ E, q : ℕ) : ℝ)) else 0

theorem R_eq_RS (b : ℕ) (σ : Bool) (Y w : ℝ) : R b σ Y w = RS b σ Y w := by
  classical
  unfold R S9 RS
  rw [sum_filter]
  unfold primorialLt
  rw [sum_divisors_primes _ (fun p hp => primesBelow_prime hp)]
  apply sum_congr rfl
  intro E hE
  have hEp : ∀ p ∈ E, p.Prime := fun p hp => primesBelow_prime (mem_powerset.1 hE hp)
  have hc : ((∀ p ∈ (∏ p ∈ E, p).primeFactors, w < (p : ℝ)) ∧
      (∀ p ∈ (∏ p ∈ E, p).primeFactors, (p : ℝ) < Y / ((∏ p ∈ E, p : ℕ) : ℝ)) ∧
        (if σ then Even (ω (∏ p ∈ E, p)) else Odd (ω (∏ p ∈ E, p)))) ↔ cond9 σ Y w E := by
    rw [Nat.primeFactors_prod hEp, omega_prod hEp]; rfl
  by_cases h : cond9 σ Y w E
  · rw [if_pos (hc.2 h), if_pos h, rho_div_prod b hEp]
  · rw [if_neg (fun h' => h (hc.1 h')), if_neg h]

theorem one_le_prod_cast {E : Finset ℕ} (hE : ∀ p ∈ E, p.Prime) : (1 : ℝ) ≤ ((∏ q ∈ E, q : ℕ) : ℝ) := by
  have := prod_pos_of_primes hE
  exact_mod_cast this

theorem le_prod_cast {E : Finset ℕ} (hE : ∀ p ∈ E, p.Prime) {q : ℕ} (hq : q ∈ E) :
    (q : ℝ) ≤ ((∏ q ∈ E, q : ℕ) : ℝ) := by
  have := Nat.le_of_dvd (prod_pos_of_primes hE) (dvd_prod_of_mem (fun p => p) hq)
  exact_mod_cast this

/-- Membership of `insert m E'` (`m` below `E'`) in terms of the child condition. -/
theorem cond9_insert (σ : Bool) {Y w : ℝ} (hY : 0 < Y) {m : ℕ} {E : Finset ℕ} (hm : m.Prime)
    (hE : ∀ p ∈ E, p.Prime) (hlt : ∀ p ∈ E, m < p) :
    cond9 σ Y w (insert m E) ↔
      ((w < m ∧ (if σ then (m : ℝ) ^ 3 < Y else (m : ℝ) ^ 2 < Y)) ∧ cond9 (!σ) (Y / m) m E) := by
  have hmE : m ∉ E := fun h => lt_irrefl m (hlt m h)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm.one_lt.le
  have hm0 : (0 : ℝ) < m := by linarith
  set P : ℝ := ((∏ q ∈ E, q : ℕ) : ℝ) with hP
  have hP1 : 1 ≤ P := one_le_prod_cast hE
  have hprod : ((∏ q ∈ insert m E, q : ℕ) : ℝ) = m * P := by
    rw [prod_insert hmE, Nat.cast_mul, hP]
  have hdiv : Y / (m * P) = Y / m / P := by rw [div_div]
  have hpar : (if σ then Even (insert m E).card else Odd (insert m E).card) ↔
      (if (!σ) then Even E.card else Odd E.card) := by
    rw [card_insert_of_notMem hmE]
    cases σ <;> simp [Nat.even_add_one, Nat.odd_add_one]
  unfold cond9
  rw [hprod, hpar, hdiv]
  constructor
  · rintro ⟨hA, hB, hC⟩
    have hwm : w < m := hA m (mem_insert_self m E)
    refine ⟨⟨hwm, ?_⟩, fun p hp => by exact_mod_cast hlt p hp, fun p hp => hB p (mem_insert_of_mem hp), hC⟩
    have hmB : (m : ℝ) < Y / m / P := hB m (mem_insert_self m E)
    rw [lt_div_iff₀ (by linarith), lt_div_iff₀ hm0] at hmB
    cases σ with
    | false => simp only [Bool.false_eq_true, if_false]; nlinarith
    | true =>
      simp only [if_true]
      simp only [Bool.not_true, Bool.false_eq_true, if_false] at hC
      obtain ⟨q, hq⟩ : E.Nonempty := by
        rcases E.eq_empty_or_nonempty with h | h
        · rw [h] at hC; simp at hC
        · exact h
      have hmq : (m : ℝ) < q := by exact_mod_cast hlt q hq
      have hqP : (q : ℝ) ≤ P := le_prod_cast hE hq
      have hqB : (q : ℝ) < Y / m / P := hB q (mem_insert_of_mem hq)
      rw [lt_div_iff₀ (by linarith), lt_div_iff₀ hm0] at hqB
      have hmm : (m : ℝ) * m < q * q := by nlinarith
      have h1 : (m : ℝ) ^ 3 < m * q * q := by
        have := mul_lt_mul_of_pos_left hmm hm0; nlinarith
      have h2 : (m : ℝ) * q * q ≤ q * P * m := by
        have := mul_le_mul_of_nonneg_left hqP (by positivity : (0 : ℝ) ≤ m * q); nlinarith
      linarith
  · rintro ⟨⟨hwm, hcm⟩, hA, hB, hC⟩
    refine ⟨?_, ?_, hC⟩
    · intro p hp
      rcases mem_insert.1 hp with rfl | hp
      · exact hwm
      · exact lt_trans hwm (hA p hp)
    · intro p hp
      rcases mem_insert.1 hp with rfl | hp
      · rcases E.eq_empty_or_nonempty with h | ⟨q, hq⟩
        · have hP' : P = 1 := by rw [hP, h]; simp
          rw [hP', div_one, lt_div_iff₀ hm0]
          cases σ with
          | false => simp only [Bool.false_eq_true, if_false] at hcm; nlinarith
          | true =>
            simp only [if_true] at hcm
            have : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ 3 := by nlinarith
            nlinarith
        · exact lt_trans (hA q hq) (hB q hq)
      · exact hB p hp

theorem mem_primesBelow_of_cond9 {σ : Bool} {Y w : ℝ} (hY : 0 < Y) {E : Finset ℕ} (hE : ∀ p ∈ E, p.Prime)
    (h : cond9 σ Y w E) : ∀ p ∈ E, (p : ℝ) < Y := by
  intro p hp
  have h1 := h.2.1 p hp
  have hP1 := one_le_prod_cast hE
  calc (p : ℝ) < Y / ((∏ q ∈ E, q : ℕ) : ℝ) := h1
    _ ≤ Y := div_le_self hY.le hP1

/-- General recursion of `RS` from the smallest prime. -/
theorem RS_rec (b : ℕ) (σ : Bool) {Y : ℝ} (hY : 0 < Y) (w : ℝ) :
    RS b σ Y w = (if σ then sigmaP b Y else 0) +
      ∑ m ∈ (primesBelow Y).filter (fun m : ℕ => w < (m : ℝ) ∧
          (if σ then (m : ℝ) ^ 3 < Y else (m : ℝ) ^ 2 < Y)),
        gB b m * RS b (!σ) (Y / m) m := by
  classical
  rw [show RS b σ Y w = ∑ E ∈ (primesBelow Y).powerset, (if cond9 σ Y w E then
      gD b E * sigmaP b (Y / ((∏ q ∈ E, q : ℕ) : ℝ)) else 0) from rfl, sum_powerset_min]
  congr 1
  · have h0 : cond9 σ Y w ∅ ↔ σ = true := by
      unfold cond9; cases σ <;> simp
    cases σ
    · rw [if_neg (by rw [h0]; simp)]; simp
    · rw [if_pos (h0.2 rfl)]; simp [gD]
  · rw [sum_filter]
    apply sum_congr rfl
    intro m hm
    have hmp := primesBelow_prime hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hmp.pos
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hmp.one_lt.le
    have hYm : 0 < Y / m := div_pos hY hm0
    -- the inner sums over `E'`
    set C := (primesBelow (Y / m)).filter (fun p : ℕ => m < p) with hC
    have hCA : C ⊆ (primesBelow Y).filter (fun p : ℕ => m < p) := by
      intro p hp
      rw [hC, mem_filter, mem_primesBelow] at hp
      rw [mem_filter, mem_primesBelow]
      exact ⟨⟨hp.1.1, lt_of_lt_of_le hp.1.2 (div_le_self hY.le hm1)⟩, hp.2⟩
    have hCB : C ⊆ primesBelow (Y / m) := filter_subset _ _
    set G : Finset ℕ → ℝ := fun E => if cond9 (!σ) (Y / m) m E then
      gD b E * sigmaP b (Y / m / ((∏ q ∈ E, q : ℕ) : ℝ)) else 0 with hG
    have hsupp : ∀ A : Finset ℕ, (∀ p ∈ A, p.Prime) → ∀ E ⊆ A, G E ≠ 0 → E ⊆ C := by
      intro A hA E hEA hGE
      have hc : cond9 (!σ) (Y / m) m E := by
        by_contra h; exact hGE (by rw [hG]; simp only [if_neg h])
      intro p hp
      rw [hC, mem_filter, mem_primesBelow]
      exact ⟨⟨hA p (hEA hp), mem_primesBelow_of_cond9 hYm (fun q hq => hA q (hEA hq)) hc p hp⟩,
        by exact_mod_cast hc.1 p hp⟩
    have hRS : RS b (!σ) (Y / m) m = ∑ E ∈ C.powerset, G E := by
      unfold RS
      exact sum_powerset_of_support hCB G (hsupp _ (fun p hp => primesBelow_prime hp))
    have hinner : ∑ E ∈ ((primesBelow Y).filter (fun p : ℕ => m < p)).powerset, G E = ∑ E ∈ C.powerset, G E :=
      sum_powerset_of_support hCA G (hsupp _ (fun p hp => primesBelow_prime (mem_filter.1 hp).1))
    rw [show (if w < (m : ℝ) ∧ (if σ then (m : ℝ) ^ 3 < Y else (m : ℝ) ^ 2 < Y) then
        gB b m * RS b (!σ) (Y / m) m else 0) =
        ∑ E ∈ ((primesBelow Y).filter (fun p : ℕ => m < p)).powerset,
          (if w < (m : ℝ) ∧ (if σ then (m : ℝ) ^ 3 < Y else (m : ℝ) ^ 2 < Y) then gB b m * G E else 0) by
      by_cases hc : w < (m : ℝ) ∧ (if σ then (m : ℝ) ^ 3 < Y else (m : ℝ) ^ 2 < Y)
      · simp only [if_pos hc]; rw [hRS, ← hinner, mul_sum]
      · simp only [if_neg hc, sum_const_zero]]
    apply sum_congr rfl
    intro E hE
    have hEA := mem_powerset.1 hE
    have hEp : ∀ p ∈ E, p.Prime := fun p hp => primesBelow_prime (mem_filter.1 (hEA hp)).1
    have hlt : ∀ p ∈ E, m < p := fun p hp => (mem_filter.1 (hEA hp)).2
    have hmE : m ∉ E := fun h => lt_irrefl m (hlt m h)
    have hci := cond9_insert σ (w := w) hY hmp hEp hlt
    have hval : gD b (insert m E) * sigmaP b (Y / ((∏ q ∈ insert m E, q : ℕ) : ℝ)) =
        gB b m * (gD b E * sigmaP b (Y / m / ((∏ q ∈ E, q : ℕ) : ℝ))) := by
      unfold gD
      rw [prod_insert hmE, prod_insert hmE, div_div]
      push_cast; ring
    by_cases h1 : cond9 σ Y w (insert m E)
    · obtain ⟨h2, h3⟩ := hci.1 h1
      rw [if_pos h1, if_pos h2, hG]
      simp only [if_pos h3]
      exact hval
    · rw [if_neg h1]
      by_cases h2 : w < (m : ℝ) ∧ (if σ then (m : ℝ) ^ 3 < Y else (m : ℝ) ^ 2 < Y)
      · rw [if_pos h2, hG]
        simp only
        rw [if_neg (fun h3 => h1 (hci.2 ⟨h2, h3⟩)), mul_zero]
      · rw [if_neg h2]

theorem filter_cube (Y w : ℝ) (hY : 0 < Y) :
    (primesBelow Y).filter (fun m : ℕ => w < (m : ℝ) ∧ (m : ℝ) ^ 3 < Y) =
      (primesBelow (Y ^ ((1 : ℝ) / 3))).filter (fun m : ℕ => w < (m : ℝ)) := by
  ext m
  simp only [mem_filter, mem_primesBelow]
  rw [lt_cbrt_iff hY.le (Nat.cast_nonneg m)]
  constructor
  · rintro ⟨⟨h1, _⟩, h3, h4⟩; exact ⟨⟨h1, h4⟩, h3⟩
  · rintro ⟨⟨h1, h4⟩, h3⟩
    refine ⟨⟨h1, ?_⟩, h3, h4⟩
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast h1.one_lt.le
    have : (m : ℝ) ^ 1 ≤ (m : ℝ) ^ 3 := pow_le_pow_right₀ hm1 (by norm_num)
    rw [pow_one] at this
    linarith

theorem filter_sq (Y w : ℝ) (hY : 0 < Y) :
    (primesBelow Y).filter (fun m : ℕ => w < (m : ℝ) ∧ (m : ℝ) ^ 2 < Y) =
      (primesBelow (Real.sqrt Y)).filter (fun m : ℕ => w < (m : ℝ)) := by
  ext m
  simp only [mem_filter, mem_primesBelow]
  rw [Real.lt_sqrt (Nat.cast_nonneg m)]
  constructor
  · rintro ⟨⟨h1, _⟩, h3, h4⟩; exact ⟨⟨h1, h4⟩, h3⟩
  · rintro ⟨⟨h1, h4⟩, h3⟩
    refine ⟨⟨h1, ?_⟩, h3, h4⟩
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast h1.one_lt.le
    have : (m : ℝ) ^ 1 ≤ (m : ℝ) ^ 2 := pow_le_pow_right₀ hm1 (by norm_num)
    rw [pow_one] at this
    linarith

/-- **(R1)** -/
theorem R1 (b : ℕ) {Y : ℝ} (hY : 0 < Y) (w : ℝ) :
    R b true Y w = sigmaP b Y +
      ∑ m ∈ (primesBelow (Y ^ ((1 : ℝ) / 3))).filter (fun m : ℕ => w < (m : ℝ)), gB b m * R b false (Y / m) m := by
  rw [R_eq_RS, RS_rec b true hY w]
  simp only [if_true, Bool.not_true]
  rw [filter_cube Y w hY]
  simp only [R_eq_RS]

/-- **(R2)** -/
theorem R2 (b : ℕ) {Y : ℝ} (hY : 0 < Y) (w : ℝ) :
    R b false Y w =
      ∑ m ∈ (primesBelow (Real.sqrt Y)).filter (fun m : ℕ => w < (m : ℝ)), gB b m * R b true (Y / m) m := by
  rw [R_eq_RS, RS_rec b false hY w]
  simp only [Bool.false_eq_true, if_false, Bool.not_false, zero_add]
  rw [filter_sq Y w hY]
  simp only [R_eq_RS]

/-! ## Bridge to Palprimes' Rosser sums (non-strict conditions at level `z = ⌈Y⌉₊ − 1`) -/

theorem TS_insert_max (b : ℕ) (σ : Bool) (Y : ℝ) {S : Finset ℕ} {M : ℕ} (hS : ∀ p ∈ S, p.Prime)
    (hMp : M.Prime) (hM : ∀ x ∈ S, x < M) :
    TS b σ Y (insert M S) = TS b σ Y S -
      (if (σ = true → (M : ℝ) ^ 3 < Y) then gB b M * TS b (!σ) (Y / M) S else 0) := by
  have hMS : M ∉ S := fun h => lt_irrefl M (hM M h)
  have hS' : ∀ p ∈ insert M S, p.Prime := by
    intro p hp; rcases mem_insert.1 hp with rfl | hp
    · exact hMp
    · exact hS p hp
  have e1 : (insert M S).filter (· < M) = S := by
    ext x; simp only [mem_filter, mem_insert]; constructor
    · rintro ⟨rfl | hx, hlt⟩
      · exact absurd hlt (lt_irrefl _)
      · exact hx
    · intro hx; exact ⟨Or.inr hx, hM x hx⟩
  have e2 : ∀ P ∈ S, (insert M S).filter (· < P) = S.filter (· < P) := by
    intro P hP; ext x; simp only [mem_filter, mem_insert]; constructor
    · rintro ⟨rfl | hx, hlt⟩
      · exact absurd (lt_trans hlt (hM P hP)) (lt_irrefl _)
      · exact ⟨hx, hlt⟩
    · rintro ⟨hx, hlt⟩; exact ⟨Or.inr hx, hlt⟩
  rw [TS_rec b σ Y hS', TS_rec b σ Y hS, sum_insert hMS, e1,
    sum_congr rfl (fun P hP => by rw [e2 P hP])]
  ring

theorem TS_empty (b : ℕ) (σ : Bool) (Y : ℝ) : TS b σ Y ∅ = 1 := by
  rw [TS_rec b σ Y (fun p hp => absurd hp (notMem_empty p))]; simp

theorem Sg_eq_TS (b : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∀ (σ : Bool) (Y z : ℝ), (∀ N : ℕ, (N : ℝ) < Y ↔ (N : ℝ) ≤ z) →
      Sg (gB b) σ z (toDec S) = TS b σ Y S := by
  induction S using Finset.induction_on_max with
  | empty =>
    intro σ Y z _
    rw [toDec_empty, TS_empty]; rfl
  | insert M S hM ih =>
    intro σ Y z hrel
    have hS' : ∀ p ∈ S, p.Prime := fun p hp => hS p (mem_insert_of_mem hp)
    have hMp : M.Prime := hS M (mem_insert_self M S)
    have hM0 : (0 : ℝ) < M := by exact_mod_cast hMp.pos
    rw [toDec_insert_max M S hM, TS_insert_max b σ Y hS' hMp hM]
    show Sg (gB b) σ z (toDec S) - (if headOK σ z M then gB b M * Sg (gB b) (!σ) (z / M) (toDec S) else 0) = _
    have hrel' : ∀ N : ℕ, (N : ℝ) < Y / M ↔ (N : ℝ) ≤ z / M := by
      intro N
      rw [lt_div_iff₀ hM0, le_div_iff₀ hM0]
      have := hrel (N * M)
      push_cast at this
      exact this
    rw [ih hS' σ Y z hrel, ih hS' (!σ) (Y / M) (z / M) hrel']
    have hh : headOK σ z M ↔ (σ = true → (M : ℝ) ^ 3 < Y) := by
      cases σ
      · simp [headOK]
      · simp only [headOK, forall_const]
        have := hrel (M ^ 3)
        push_cast at this
        exact this.symm
    by_cases hc : (σ = true → (M : ℝ) ^ 3 < Y)
    · rw [if_pos (hh.2 hc), if_pos hc]
    · rw [if_neg (fun h => hc (hh.1 h)), if_neg hc]

theorem ceil_rel {Y : ℝ} (hY : 0 ≤ Y) : ∀ N : ℕ, (N : ℝ) < Y ↔ (N : ℝ) ≤ (⌈Y⌉₊ : ℝ) - 1 := by
  intro N
  rw [← Nat.lt_ceil]
  constructor
  · intro h
    have : N + 1 ≤ ⌈Y⌉₊ := h
    have : ((N + 1 : ℕ) : ℝ) ≤ (⌈Y⌉₊ : ℝ) := by exact_mod_cast this
    push_cast at this; linarith
  · intro h
    have : ((N + 1 : ℕ) : ℝ) ≤ (⌈Y⌉₊ : ℝ) := by push_cast; linarith
    have : N + 1 ≤ ⌈Y⌉₊ := by exact_mod_cast this
    omega

/-- The leaf `T⁻(Y, √Y)` is Palprimes' `S⁻(z, 2)` up to one prime `p = √z`. -/
theorem leaf_bound (b : ℕ) {Y : ℝ} (hY : 2 ≤ Y) :
    |Tpm b false Y (Real.sqrt Y)| ≤ |Sminus b ((⌈Y⌉₊ : ℝ) - 1) 2| +
      1 / (Real.sqrt ((⌈Y⌉₊ : ℝ) - 1) * VB b (Real.sqrt ((⌈Y⌉₊ : ℝ) - 1))) := by
  set z : ℝ := (⌈Y⌉₊ : ℝ) - 1 with hz
  have hrel := ceil_rel (by linarith : (0 : ℝ) ≤ Y)
  have hz1 : 1 ≤ z := by
    have := (hrel 1).1 (by push_cast; linarith)
    push_cast at this; linarith
  have hsz : 0 < Real.sqrt z := Real.sqrt_pos.2 (by linarith)
  have hV := Palprimes.E1.VB_pos' b (Real.sqrt z)
  have hSm : Sminus b z 2 = TS b false Y (primesBelow (Real.sqrt z)) := by
    unfold Sminus
    rw [← Real.sqrt_eq_rpow]
    exact Sg_eq_TS b _ (fun p hp => primesBelow_prime hp) false Y z hrel
  rw [Tpm_eq_TS, hSm]
  have hextra : 0 ≤ 1 / (Real.sqrt z * VB b (Real.sqrt z)) := by positivity
  -- primes below `√Y` are those below `√z` and possibly `p = √z`
  have hmemY : ∀ p : ℕ, p ∈ primesBelow (Real.sqrt Y) ↔ p.Prime ∧ ((p : ℝ) ^ 2 ≤ z) := by
    intro p
    rw [mem_primesBelow, Real.lt_sqrt (Nat.cast_nonneg p)]
    have := hrel (p ^ 2)
    push_cast at this
    rw [this]
  have hmemz : ∀ p : ℕ, p ∈ primesBelow (Real.sqrt z) ↔ p.Prime ∧ ((p : ℝ) ^ 2 < z) := by
    intro p
    rw [mem_primesBelow, Real.lt_sqrt (Nat.cast_nonneg p)]
  by_cases hp : ∃ p : ℕ, p.Prime ∧ (p : ℝ) ^ 2 = z
  · obtain ⟨p, hpp, hpz⟩ := hp
    have hps : (p : ℝ) = Real.sqrt z := by
      rw [← hpz, Real.sqrt_sq (Nat.cast_nonneg p)]
    have hlt : ∀ x ∈ primesBelow (Real.sqrt z), x < p := by
      intro x hx
      have hx2 := ((hmemz x).1 hx).2
      rw [← hpz] at hx2
      have : (x : ℝ) < p := by
        exact (pow_lt_pow_iff_left₀ (Nat.cast_nonneg x) (Nat.cast_nonneg p) (by norm_num)).1 hx2
      exact_mod_cast this
    have hset : primesBelow (Real.sqrt Y) = insert p (primesBelow (Real.sqrt z)) := by
      ext q
      rw [hmemY, mem_insert, hmemz]
      constructor
      · rintro ⟨hq, hq2⟩
        rcases lt_or_eq_of_le hq2 with h | h
        · exact Or.inr ⟨hq, h⟩
        · left
          rw [← hpz] at h
          have : (q : ℝ) = p := by
            exact (pow_left_inj₀ (Nat.cast_nonneg q) (Nat.cast_nonneg p) (by norm_num)).1 h
          exact_mod_cast this
      · rintro (rfl | ⟨hq, hq2⟩)
        · exact ⟨hpp, hpz.le⟩
        · exact ⟨hq, hq2.le⟩
    rw [hset, TS_insert_max b false Y (fun q hq => primesBelow_prime hq) hpp hlt]
    simp only [Bool.false_eq_true, IsEmpty.forall_iff, if_true, Bool.not_false]
    have h1 := abs_TS_le b true (Y / p) (primesBelow (Real.sqrt z))
    have h2 := prod_one_add_le_inv_VB b (Real.sqrt z)
    have hg : gB b p ≤ 1 / Real.sqrt z := by
      rw [← hps]; unfold gB; split_ifs
      · exact le_rfl
      · positivity
    have hg0 := gB_nonneg b p
    have h3 : |gB b p * TS b true (Y / p) (primesBelow (Real.sqrt z))| ≤
        1 / (Real.sqrt z * VB b (Real.sqrt z)) := by
      rw [abs_mul, abs_of_nonneg hg0]
      calc gB b p * |TS b true (Y / p) (primesBelow (Real.sqrt z))|
          ≤ (1 / Real.sqrt z) * (1 / VB b (Real.sqrt z)) :=
            mul_le_mul hg (le_trans h1 h2) (abs_nonneg _) (by positivity)
        _ = 1 / (Real.sqrt z * VB b (Real.sqrt z)) := by rw [one_div_mul_one_div]
    calc |TS b false Y (primesBelow (Real.sqrt z)) - gB b p * TS b true (Y / p) (primesBelow (Real.sqrt z))|
        ≤ |TS b false Y (primesBelow (Real.sqrt z))| + |gB b p * TS b true (Y / p) (primesBelow (Real.sqrt z))| :=
          abs_sub _ _
      _ ≤ _ := by linarith
  · have hset : primesBelow (Real.sqrt Y) = primesBelow (Real.sqrt z) := by
      ext q
      rw [hmemY, hmemz]
      constructor
      · rintro ⟨hq, hq2⟩
        exact ⟨hq, lt_of_le_of_ne hq2 (fun h => hp ⟨q, hq, h⟩)⟩
      · rintro ⟨hq, hq2⟩; exact ⟨hq, hq2.le⟩
    rw [hset]
    linarith

end KappaOmega2.M08
