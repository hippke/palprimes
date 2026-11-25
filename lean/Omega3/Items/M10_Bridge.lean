import Omega3.Items.M10_XB
import Palprimes.E1.Main

/-!
# M10 helper: bridge to Palprimes' Rosser sums `Sg` (non-strict conditions) and `σ⁺(u) ≤ C V(u)`
-/

set_option linter.style.longLine false

open Finset Real
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius

namespace Omega3.M10

open Palprimes Palprimes.Greaves
open Classical

/-- `χ^σ` with non-strict conditions (Palprimes' `headOK`). -/
def ChiSn (σ : Bool) (Y : ℝ) (D : Finset ℕ) : Prop :=
  ∀ E ⊆ D, E.Nonempty → par σ E.card →
    ((∏ p ∈ E, p : ℕ) : ℝ) * (((∏ p ∈ E, p).minFac : ℕ) : ℝ) ^ 2 ≤ Y

/-- P1: `χ⁻_Y(M · Π D) ↔ χ⁺_{Y/M}(Π D)` for a prime `M` above the primes `D`. -/
theorem chiSn_minus_insert {Y : ℝ} {M : ℕ} {D : Finset ℕ} (hD : ∀ p ∈ D, p.Prime) (hM : M.Prime)
    (hlt : ∀ q ∈ D, q < M) : ChiSn false Y (insert M D) ↔ ChiSn true (Y / M) D := by
  have hMD : M ∉ D := fun h => lt_irrefl _ (hlt M h)
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM.pos
  constructor
  · intro H E hED hne hpar
    have hEp : ∀ p ∈ E, p.Prime := fun p hp => hD p (hED hp)
    have hME : M ∉ E := fun h => hMD (hED h)
    have h1 := H (insert M E) (insert_subset_insert M hED) (insert_nonempty M E) (by
      simp only [par] at hpar ⊢; rw [card_insert_of_notMem hME]; exact hpar.add_one)
    rw [minFac_prod_insert hEp hM (fun q hq => hlt q (hED hq)) hne, prod_insert hME] at h1
    rw [le_div_iff₀ hM0]; push_cast at h1 ⊢; linarith
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
      rw [le_div_iff₀ hM0] at h1; push_cast at h1 ⊢; linarith
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
      rw [le_div_iff₀ hM0] at h1
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


/-- P1′: `χ⁺_Y(M · Π D) ↔ M³ < Y ∧ χ⁻_{Y/M}(Π D)` for a prime `M` above `D`. -/
theorem chiSn_plus_insert {Y : ℝ} {M : ℕ} {D : Finset ℕ} (hD : ∀ p ∈ D, p.Prime) (hM : M.Prime)
    (hlt : ∀ q ∈ D, q < M) : ChiSn true Y (insert M D) ↔ (M : ℝ) ^ 3 ≤ Y ∧ ChiSn false (Y / M) D := by
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
      rw [le_div_iff₀ hM0]; push_cast at h1 ⊢; linarith
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
        rw [le_div_iff₀ hM0] at h1; push_cast at h1 ⊢; linarith
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
        rw [le_div_iff₀ hM0] at h1
        have : (q : ℝ) * (q : ℝ) ^ 2 < (q₀ : ℝ) ^ 2 * M := by
          have a : (q : ℝ) ^ 2 < (q₀ : ℝ) ^ 2 := by nlinarith
          nlinarith
        apply le_of_lt
        calc (q : ℝ) * ((∏ p ∈ E₀, p : ℕ) : ℝ) * (q : ℝ) ^ 2 = ((∏ p ∈ E₀, p : ℕ) : ℝ) * ((q : ℝ) * (q : ℝ) ^ 2) := by ring
          _ < ((∏ p ∈ E₀, p : ℕ) : ℝ) * ((q₀ : ℝ) ^ 2 * M) := mul_lt_mul_of_pos_left this hP0
          _ = ((∏ p ∈ E₀, p : ℕ) : ℝ) * (q₀ : ℝ) ^ 2 * M := by ring
          _ ≤ Y := h1
      · have hE₀e : E₀ = ∅ := not_nonempty_iff_eq_empty.1 hne₀
        have hEq : E = {q} := by rw [hE, hE₀e, insert_empty]
        rw [hEq, prod_singleton]
        have : (q : ℝ) ^ 3 < (M : ℝ) ^ 3 := by
          have := pow_lt_pow_left₀ hqM hq0.le (by norm_num : (3 : ℕ) ≠ 0); exact this
        nlinarith


theorem chiSn_empty (σ : Bool) (Y : ℝ) : ChiSn σ Y ∅ := by
  intro E hE hne; exact absurd (subset_empty.1 hE) (nonempty_iff_ne_empty.1 hne)

/-- Palprimes' `Sg` over a set of primes is the subset sum with non-strict Rosser conditions. -/
theorem Sg_eq_set (b : ℕ) : ∀ (S : Finset ℕ), (∀ p ∈ S, p.Prime) → ∀ (σ : Bool) (z : ℝ),
    Sg (MT.gB b) σ z (toDec S) = ∑ D ∈ S.powerset, fm b (∏ p ∈ D, p) * (if ChiSn σ z D then 1 else 0) := by
  intro S
  induction S using Finset.induction_on_max with
  | empty =>
    intro _ σ z
    rw [toDec_empty, powerset_empty, sum_singleton, prod_empty, if_pos (chiSn_empty σ z)]
    simp [Sg, fm, rhoB]
  | insert a S ha ih =>
    intro hS σ z
    have haS : a ∉ S := fun h => lt_irrefl a (ha a h)
    have hap : a.Prime := hS a (mem_insert_self a S)
    have hSp : ∀ p ∈ S, p.Prime := fun p hp => hS p (mem_insert_of_mem hp)
    rw [toDec_insert_max a S ha, sum_powerset_insert haS]
    simp only [Sg]
    rw [ih hSp σ z]
    congr 1
    have hg : MT.gB b a = rhoB b a / a := (rhoB_div_eq_gB b hap).symm
    have e : ∀ D ∈ S.powerset, fm b (∏ p ∈ insert a D, p) * (if ChiSn σ z (insert a D) then 1 else 0) =
        -(rhoB b a / a) * ((if headOK σ z a then 1 else 0) * (fm b (∏ p ∈ D, p) * (if ChiSn (!σ) (z / a) D then 1 else 0))) := by
      intro D hD
      have hDp : ∀ p ∈ D, p.Prime := fun p hp => hSp p (mem_powerset.1 hD hp)
      have hlt : ∀ q ∈ D, q < a := fun q hq => ha q (mem_powerset.1 hD hq)
      have haD : a ∉ D := fun h => lt_irrefl _ (hlt a h)
      rw [fm_insert b hap hDp haD]
      cases σ with
      | false =>
        have h := chiSn_minus_insert (Y := z) hDp hap hlt
        have hh : headOK false z a := trivial
        rw [if_pos hh, one_mul]
        simp only [Bool.not_false]
        by_cases hc : ChiSn true (z / a) D
        · rw [if_pos (h.2 hc), if_pos hc]; ring
        · rw [if_neg (mt h.1 hc), if_neg hc]; ring
      | true =>
        have h := chiSn_plus_insert (Y := z) hDp hap hlt
        simp only [Bool.not_true]
        by_cases h3 : (a : ℝ) ^ 3 ≤ z
        · have hh : headOK true z a := h3
          by_cases hc : ChiSn false (z / a) D
          · rw [if_pos (h.2 ⟨h3, hc⟩), if_pos hh, if_pos hc]; ring
          · rw [if_neg (fun h' => hc (h.1 h').2), if_pos hh, if_neg hc]; ring
        · have hh : ¬ headOK true z a := h3
          rw [if_neg (fun h' => h3 (h.1 h').1), if_neg hh]; ring
    rw [sum_congr rfl e, ← mul_sum, ← mul_sum, ← ih hSp (!σ) (z / a), hg]
    split_ifs <;> ring

/-- Shift: strict conditions at `u` = non-strict conditions at some `u' ∈ (u/2, u)`. -/
theorem shift (S : Finset ℕ) {u : ℝ} (hu : 0 < u) :
    ∃ u' : ℝ, u / 2 < u' ∧ u' < u ∧ ∀ D ⊆ S, (ChiS true u D ↔ ChiSn true u' D) := by
  set v : Finset ℕ → ℝ := fun E => ((∏ p ∈ E, p : ℕ) : ℝ) * (((∏ p ∈ E, p).minFac : ℕ) : ℝ) ^ 2 with hv
  set low : Finset ℝ := insert (u / 2) ((S.powerset.image v).filter (· < u)) with hlow
  have hne : low.Nonempty := insert_nonempty _ _
  set m := low.max' hne with hm
  have hmu : m < u := by
    rw [hm, Finset.max'_lt_iff]
    intro x hx
    rw [hlow, mem_insert] at hx
    rcases hx with h | h
    · rw [h]; linarith
    · exact (mem_filter.1 h).2
  have hm2 : u / 2 ≤ m := le_max' low _ (mem_insert_self _ _)
  refine ⟨(m + u) / 2, by linarith, by linarith, fun D hD => ?_⟩
  have key : ∀ E ⊆ D, (v E < u ↔ v E ≤ (m + u) / 2) := by
    intro E hE
    constructor
    · intro h
      have : v E ∈ low := mem_insert_of_mem (mem_filter.2 ⟨mem_image.2 ⟨E, mem_powerset.2 (hE.trans hD), rfl⟩, h⟩)
      have := le_max' low _ this
      linarith
    · intro h; linarith
  constructor
  · intro H E hE hne' hpar; exact (key E hE).1 (H E hE hne' hpar)
  · intro H E hE hne' hpar; exact (key E hE).2 (H E hE hne' hpar)

/-- Rosser upper bound at `s = 3`: `σ⁺(u) ≤ C₁ V(u)` for large `u` (Palprimes `E1.rosserAsymp_of_two_le`). -/
theorem sigma_upper (b : ℕ) (hb : 2 ≤ b) : ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∃ u₁ : ℝ, ∀ u ≥ u₁, sigmaP b u ≤ C₁ * MT.VB b u := by
  obtain ⟨z₀, hz₀⟩ := (E1.rosserAsymp_of_two_le b hb) 1 one_pos
  obtain ⟨y₃, hy₃, hr⟩ := E1.VB_ratio' b hb (1 / 3) (by norm_num) (by norm_num) 1 one_pos
  set eg := Real.exp Real.eulerMascheroniConstant with heg
  have heg0 : 0 < eg := Real.exp_pos _
  refine ⟨4 * (2 * eg * 8 ^ 10 + 2 * eg + 1), by positivity, max (max (2 * z₀) y₃) 64, fun u hu => ?_⟩
  have hu64 : (64 : ℝ) ≤ u := le_trans (le_max_right _ _) hu
  have huz : 2 * z₀ ≤ u := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hu
  have huy : y₃ ≤ u := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hu
  have hu0 : 0 < u := by linarith
  set ζ := u ^ ((1 : ℝ) / 3) with hζ
  have hζ3 : ζ ^ 3 = u := by
    rw [hζ, show (1 : ℝ) / 3 = ((3 : ℕ) : ℝ)⁻¹ by norm_num]; exact Real.rpow_inv_natCast_pow hu0.le (by norm_num)
  have hζ0 : 0 < ζ := Real.rpow_pos_of_pos hu0 _
  have hζ4 : 4 ≤ ζ := by
    by_contra h; push_neg at h
    have : ζ ^ 3 < 4 ^ 3 := pow_lt_pow_left₀ h hζ0.le (by norm_num)
    rw [hζ3] at this; norm_num at this; linarith
  obtain ⟨u', hu'1, hu'2, hsh⟩ := shift (primesBelow ζ) hu0
  -- σ⁺(u) as a Palprimes Rosser sum
  have hσ : sigmaP b u = Sg (MT.gB b) true u' (toDec (primesBelow ζ)) := by
    unfold sigmaP
    rw [← hζ, Tpm_set, Sg_eq_set b _ (primes_PB ζ)]
    apply sum_congr rfl; intro D hD
    by_cases h : ChiS true u D
    · rw [if_pos h, if_pos ((hsh D (mem_powerset.1 hD)).1 h)]
    · rw [if_neg h, if_neg (fun h' => h ((hsh D (mem_powerset.1 hD)).2 h'))]
  -- the exponent s'
  have hu'1' : 1 < u' := by linarith
  have hζu' : ζ ≤ u' := by
    by_contra h; push_neg at h
    have : u' ^ 3 < ζ ^ 3 := pow_lt_pow_left₀ h (by linarith) (by norm_num)
    rw [hζ3] at this
    have h5 : (u / 2) ^ 3 < u := lt_trans (pow_lt_pow_left₀ hu'1 (by linarith) (by norm_num)) this
    have e : (u / 2) ^ 3 = u * (u * u / 8) := by ring
    rw [e] at h5
    have h6 : u * (u * u / 8) < u * 1 := by linarith
    have h7 := lt_of_mul_lt_mul_left h6 hu0.le
    nlinarith
  set s' := Real.log u' / Real.log ζ with hs'
  have hlζ : 0 < Real.log ζ := Real.log_pos (by linarith)
  have hlu' : 0 < Real.log u' := Real.log_pos hu'1'
  have hs'1 : 1 ≤ s' := by
    rw [hs', le_div_iff₀ hlζ, one_mul]; exact Real.log_le_log hζ0 hζu'
  have hs'9 : s' ≤ 9 := by
    rw [hs', div_le_iff₀ hlζ]
    have : Real.log u' ≤ Real.log u := Real.log_le_log (by linarith) hu'2.le
    have hlu : Real.log u = 3 * Real.log ζ := by rw [← hζ3, Real.log_pow]; norm_num
    linarith
  have hroot : u' ^ (1 / s') = ζ := by
    rw [Real.rpow_def_of_pos (by linarith), hs', one_div_div, mul_div_assoc', mul_comm, mul_div_assoc,
      div_self hlu'.ne', mul_one, Real.exp_log hζ0]
  have hA := (hz₀ u' (by linarith)).1 s' hs'1 hs'9
  have hSplus : MT.Splus b u' s' = Sg (MT.gB b) true u' (toDec (primesBelow ζ)) := by
    unfold MT.Splus; rw [hroot]
  rw [hSplus, hroot, ← hσ] at hA
  have hF : MT.FjrC s' ≤ 2 * eg * 8 ^ 10 + 2 * eg := by
    unfold MT.FjrC
    split_ifs
    · have : (0 : ℝ) ≤ 2 * eg * 8 ^ 10 := by positivity
      linarith
    · have := MT.Fjr_le hs'9; linarith
  have hVζ := E1.VB_pos' b ζ
  have hσle : sigmaP b u ≤ (2 * eg * 8 ^ 10 + 2 * eg + 1) * MT.VB b ζ := by
    have := (abs_le.1 hA).2
    nlinarith
  -- V(u^{1/3}) ≤ 4 V(u)
  have hle : ζ ≤ u := Real.rpow_le_self_of_one_le (by linarith) (by norm_num)
  have h := hr u huy ζ le_rfl hle
  have hl : Real.log u / Real.log ζ = 3 := by
    have hlu : Real.log u = 3 * Real.log ζ := by rw [← hζ3, Real.log_pow]; norm_num
    rw [hlu]; field_simp
  rw [hl] at h
  have hVu := E1.VB_pos' b u
  have h4 : MT.VB b ζ ≤ 4 * MT.VB b u := by
    have h' : MT.VB b ζ / MT.VB b u ≤ 4 := by have := (abs_le.1 h).2; linarith
    rw [div_le_iff₀ hVu] at h'; linarith
  calc sigmaP b u ≤ (2 * eg * 8 ^ 10 + 2 * eg + 1) * MT.VB b ζ := hσle
    _ ≤ (2 * eg * 8 ^ 10 + 2 * eg + 1) * (4 * MT.VB b u) := mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = 4 * (2 * eg * 8 ^ 10 + 2 * eg + 1) * MT.VB b u := by ring

end Omega3.M10
