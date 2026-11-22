import Palprimes.Greaves.Lemma32

/-! # Greaves' weighted sieve inequality (finite form)

For a finite set `𝒜` of positive integers below `y^g`:
`Σ_{a∈𝒜, ν(a) ≤ R} w(q_a) ≥ Σ_{T ⊆ primes < y} term(T) · #{a ∈ 𝒜 : Π T ∣ a}`,
`term(T) = [T ∈ ℬ] (−1)^{|T|} (w(1) − Σ_{p∈T} w p)`. Also `Π T ≤ y` for `T ∈ ℬ` (Greaves (3.2)). -/

set_option linter.style.longLine false

open Finset Real

namespace Palprimes.Greaves

/-- Primes below `y`. -/
noncomputable def primesBelow (y : ℝ) : Finset ℕ :=
  open Classical in (Finset.range (⌈y⌉₊ + 1)).filter (fun p => p.Prime ∧ (p : ℝ) < y)

theorem mem_primesBelow (y : ℝ) (p : ℕ) : p ∈ primesBelow y ↔ p.Prime ∧ (p : ℝ) < y := by
  classical
  unfold primesBelow
  simp only [mem_filter, mem_range, and_iff_right_iff_imp]
  intro ⟨_, hpy⟩
  have : (p : ℝ) < ⌈y⌉₊ + 1 := by linarith [Nat.le_ceil y]
  exact_mod_cast this

theorem subset_primeFactors_iff (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) (a : ℕ) (ha : a ≠ 0) :
    T ⊆ a.primeFactors ↔ (∏ p ∈ T, p) ∣ a := by
  constructor
  · intro h
    exact Finset.prod_primes_dvd a (fun p hp => (hT p hp).prime)
      (fun p hp => Nat.dvd_of_mem_primeFactors (h hp))
  · intro h p hp
    rw [Nat.mem_primeFactors]
    exact ⟨hT p hp, (Finset.dvd_prod_of_mem _ hp).trans h, ha⟩

/-- `T ⊆ Aset a y ↔ T ⊆ primes < y ∧ Π T ∣ a`. -/
theorem subset_Aset_iff (T : Finset ℕ) (y : ℝ) (a : ℕ) (ha : a ≠ 0) :
    T ⊆ Aset a y ↔ T ⊆ primesBelow y ∧ (∏ p ∈ T, p) ∣ a := by
  constructor
  · intro h
    have hT : ∀ p ∈ T, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors ((mem_Aset a y p).1 (h hp)).1
    refine ⟨fun p hp => (mem_primesBelow y p).2 ⟨hT p hp, ((mem_Aset a y p).1 (h hp)).2⟩, ?_⟩
    exact (subset_primeFactors_iff T hT a ha).1 (fun p hp => ((mem_Aset a y p).1 (h hp)).1)
  · rintro ⟨h1, h2⟩ p hp
    have hT : ∀ p ∈ T, p.Prime := fun p hp => ((mem_primesBelow y p).1 (h1 hp)).1
    rw [mem_Aset]
    exact ⟨(subset_primeFactors_iff T hT a ha).2 h2 hp, ((mem_primesBelow y p).1 (h1 hp)).2⟩

variable (P : WPar)

/-- **Greaves' sieve inequality, finite form.** -/
theorem sieve_ineq (y g : ℝ) (R : ℕ) (hy : 1 < y) (hg : g ≤ P.V + R * P.U)
    (𝒜 : Finset ℕ) (h𝒜 : ∀ a ∈ 𝒜, 1 ≤ a ∧ (a : ℝ) < y ^ g) :
    ∑ T ∈ (primesBelow y).powerset, term (P.wn y) false y (P.wn y 1) T *
        #(𝒜.filter (fun a => (∏ p ∈ T, p) ∣ a)) ≤
      ∑ a ∈ 𝒜, (if nu a (y ^ P.U) ≤ R then P.wn y a.minFac else 0) := by
  classical
  have hpt : ∀ a ∈ 𝒜, ∑ T ∈ (Aset a y).powerset, term (P.wn y) false y (P.wn y 1) T ≤
      (if nu a (y ^ P.U) ≤ R then P.wn y a.minFac else 0) := by
    intro a ha
    rw [← G_eq_sum]
    have hU0 : 0 < P.U := by linarith [P.hU]
    apply lemma31 (P.wn y) y P.U P.V g R a (h𝒜 a ha).1 hy hU0 P.hU1.le (h𝒜 a ha).2 hg
    · intro p; unfold WPar.wn; split_ifs
      · exact P.UV_pos.le
      · exact P.W_nonneg _
    · intro p; rw [P.wn_one]; unfold WPar.wn; split_ifs
      · exact le_rfl
      · exact P.W_le _
    · exact P.wn_one y
    · intro p hp hpY hwp
      rw [P.wn_prime y p hp] at hwp ⊢
      have hL : 0 < Real.log y := Real.log_pos hy
      have ht : Real.log p / Real.log y < P.U := by
        rw [div_lt_iff₀ hL]
        have := Real.log_lt_log (by exact_mod_cast hp.pos) hpY
        rwa [Real.log_rpow (by linarith)] at this
      have hcV := P.c_ge_V
      unfold WPar.W at hwp ⊢
      rw [if_neg (not_lt.2 ht.le)] at hwp ⊢
      split_ifs at hwp ⊢ with h1 h2
      · exact le_rfl
      · linarith
      · simp at hwp
    · intro p hp hpy
      rw [P.wn_prime y p hp, P.wn_one]
      have hL : 0 < Real.log y := Real.log_pos hy
      have ht : 1 ≤ Real.log p / Real.log y := by
        rw [le_div_iff₀ hL, one_mul]; exact Real.log_le_log (by linarith) hpy
      unfold WPar.W; rw [if_pos (by linarith [P.hU1])]
    · apply P.hypTop y hy
      · exact toDec_pairwise _
      · intro p hp
        rw [mem_toDec, mem_Aset] at hp
        exact ⟨Nat.prime_of_mem_primeFactors hp.1, hp.2⟩
  calc ∑ T ∈ (primesBelow y).powerset, term (P.wn y) false y (P.wn y 1) T *
        #(𝒜.filter (fun a => (∏ p ∈ T, p) ∣ a))
      = ∑ a ∈ 𝒜, ∑ T ∈ (Aset a y).powerset, term (P.wn y) false y (P.wn y 1) T := by
        simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
          Finset.mul_sum, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro a ha
        rw [← Finset.sum_filter]
        apply Finset.sum_congr _ (fun _ _ => rfl)
        ext T
        simp only [mem_filter, mem_powerset]
        rw [subset_Aset_iff T y a (by have := (h𝒜 a ha).1; omega)]
    _ ≤ _ := Finset.sum_le_sum hpt

/-! ## Greaves (3.2): Rosser sets have `Π T ≤ y` -/

/-- Mutual statement on decreasing lists of positive naturals. -/
theorem prod_le_of_RosOK : ∀ (l : List ℕ) (z : ℝ), l.Pairwise (· > ·) → (∀ p ∈ l, 0 < p) →
    (RosOK true z l → ((l.map (fun p : ℕ => (p : ℝ))).prod ≤ z ∨ l = [])) ∧
    (RosOK false z l → (∀ p ∈ l, (p : ℝ) < z) → (l.map (fun p : ℕ => (p : ℝ))).prod ≤ z ∨ l = []) := by
  intro l
  induction l with
  | nil => intro z _ _; simp
  | cons P l ih =>
    intro z hsort hpos
    have hP : (0 : ℝ) < P := by exact_mod_cast hpos P (by simp)
    have hsort' := (List.pairwise_cons.1 hsort)
    have hpos' : ∀ p ∈ l, 0 < p := fun p hp => hpos p (by simp [hp])
    have hlP : ∀ p ∈ l, (p : ℝ) < P := fun p hp => by exact_mod_cast hsort'.1 p hp
    constructor
    · -- plus state: `P³ ≤ z`, then the minus state at `z/P`
      intro hR
      simp only [RosOK, headOK, Bool.not_true] at hR
      obtain ⟨h3, hR⟩ := hR
      left
      rcases (ih (z / P) hsort'.2 hpos').2 hR (fun p hp => by
          have h1 := hlP p hp
          have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast hpos P (by simp)
          rw [lt_div_iff₀ hP]
          have e1 : (p : ℝ) * P < P * P := mul_lt_mul_of_pos_right h1 hP
          have e2 : (P : ℝ) * P ≤ P ^ 3 := by
            have := le_self_pow₀ hP1 (by norm_num : (2 : ℕ) ≠ 0)
            nlinarith
          linarith) with h | h
      · simp only [List.map_cons, List.prod_cons]
        rw [le_div_iff₀ hP] at h; linarith
      · subst h; simp
        have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast hpos P (by simp)
        have := le_self_pow₀ hP1 (by norm_num : (3 : ℕ) ≠ 0)
        linarith
    · intro hR hlt
      simp only [RosOK, Bool.not_false] at hR
      obtain ⟨_, hR⟩ := hR
      left
      rcases (ih (z / P) hsort'.2 hpos').1 hR with h | h
      · simp only [List.map_cons, List.prod_cons]
        rw [le_div_iff₀ hP] at h; linarith
      · subst h; simp; exact (hlt P (by simp)).le

/-- Greaves (3.2): `T ∈ ℬ ⇒ Π T ≤ y`. -/
theorem prod_le_of_mem (y : ℝ) (T : Finset ℕ) (hT : T ⊆ primesBelow y) (hR : RosOK false y (toDec T)) :
    ((∏ p ∈ T, p : ℕ) : ℝ) ≤ y ∨ T = ∅ := by
  have hpr : ∀ p ∈ T, p.Prime ∧ (p : ℝ) < y := fun p hp => (mem_primesBelow y p).1 (hT hp)
  have h := (prod_le_of_RosOK (toDec T) y (toDec_pairwise T)
    (fun p hp => (hpr p ((mem_toDec T p).1 hp)).1.pos)).2 hR
    (fun p hp => (hpr p ((mem_toDec T p).1 hp)).2)
  have hprod : ((toDec T).map (fun p : ℕ => (p : ℝ))).prod = ((∏ p ∈ T, p : ℕ) : ℝ) := by
    push_cast
    rw [← Finset.prod_map_toList]
    exact List.Perm.prod_eq (List.Perm.map _ (Finset.sort_perm_toList T _))
  rcases h with h | h
  · left; rw [← hprod]; exact h
  · right; ext p; constructor
    · intro hp; have := (mem_toDec T p).2 hp; rw [h] at this; simp at this
    · simp

end Palprimes.Greaves
