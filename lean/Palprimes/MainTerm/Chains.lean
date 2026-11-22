import Palprimes.MainTerm.Comb

/-! # Subset form of the chain sums `CS`

`CS leaf σ z (toDec S) = −Σ_{T ⊆ S, RosOK σ z (toDec T ++ [p])} (−1)^{|T|} g(T) g(p) leaf(st, z/(ΠT · p))`
with `st = σ` flipped `|T|+1` times. -/

set_option linter.style.longLine false

open Finset

namespace Palprimes.Greaves

variable (g : ℕ → ℝ)

/-- `σ` flipped `n` times. -/
def stF (σ : Bool) : ℕ → Bool
  | 0 => σ
  | n + 1 => !(stF σ n)

theorem stF_succ' (σ : Bool) (n : ℕ) : stF σ (n + 1) = stF (!σ) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [stF] at ih ⊢; rw [ih]

/-- The summand of the subset form. -/
noncomputable def csTerm (p : ℕ) (leaf : Bool → ℝ → ℝ) (σ : Bool) (z : ℝ) (T : Finset ℕ) : ℝ :=
  open Classical in
  if RosOK σ z (toDec T ++ [p]) then
    (-1) ^ T.card * (∏ q ∈ T, g q) * g p * leaf (stF σ (T.card + 1)) (z / ((∏ q ∈ T, (q : ℝ)) * p))
  else 0

theorem RosOK_append_single (σ : Bool) (z : ℝ) (p : ℕ) (M : ℕ) (l : List ℕ) :
    RosOK σ z (M :: l ++ [p]) ↔ headOK σ z M ∧ RosOK (!σ) (z / M) (l ++ [p]) := Iff.rfl

/-- **Subset form of `CS`.** -/
theorem CS_eq_sum (p : ℕ) (leaf : Bool → ℝ → ℝ) (S : Finset ℕ) : ∀ (σ : Bool) (z : ℝ),
    CS g p leaf σ z (toDec S) = -∑ T ∈ S.powerset, csTerm g p leaf σ z T := by
  classical
  induction S using Finset.induction_on_max with
  | empty =>
    intro σ z
    simp only [toDec_empty, CS, Finset.powerset_empty, Finset.sum_singleton, csTerm]
    simp only [toDec_empty, List.nil_append, Finset.card_empty, pow_zero, Finset.prod_empty, one_mul,
      mul_one, zero_add]
    have : RosOK σ z [p] ↔ headOK σ z p := by simp [RosOK]
    by_cases h : headOK σ z p
    · rw [if_pos h, if_pos (this.2 h)]; rfl
    · rw [if_neg h, if_neg (fun h' => h (this.1 h'))]
  | insert M S hM ih =>
    intro σ z
    have hMS : M ∉ S := fun h => lt_irrefl M (hM M h)
    rw [toDec_insert_max M S hM, Finset.powerset_insert, Finset.sum_union]
    · rw [Finset.sum_image]
      · simp only [CS]
        rw [ih σ z]
        have hsub : ∀ T ∈ S.powerset, csTerm g p leaf σ z (insert M T) =
            -(if headOK σ z M then g M * csTerm g p leaf (!σ) (z / M) T else 0) := by
          intro T hT
          have hTS : T ⊆ S := Finset.mem_powerset.1 hT
          have hMT : M ∉ T := fun h => hMS (hTS h)
          have hTM : ∀ x ∈ T, x < M := fun x hx => hM x (hTS hx)
          unfold csTerm
          rw [toDec_insert_max M T hTM, Finset.card_insert_of_notMem hMT, Finset.prod_insert hMT,
            Finset.prod_insert hMT]
          simp only [RosOK_append_single]
          by_cases hh : headOK σ z M
          · simp only [hh, true_and, if_true]
            rw [show T.card + 1 + 1 = (T.card + 1) + 1 from rfl, stF_succ']
            have e : z / (((M : ℝ) * ∏ q ∈ T, (q : ℝ)) * p) = z / M / ((∏ q ∈ T, (q : ℝ)) * p) := by
              rw [div_div, mul_assoc]
            split_ifs
            · rw [e]; ring
            · simp
          · simp [hh]
        rw [Finset.sum_congr rfl hsub, Finset.sum_neg_distrib]
        by_cases hh : headOK σ z M
        · simp only [hh, if_true]
          rw [ih (!σ) (z / M), ← Finset.mul_sum]; ring
        · simp only [hh, if_false]; simp
      · intro T1 hT1 T2 hT2 h
        have h1 : M ∉ T1 := fun h' => hMS (Finset.mem_powerset.1 hT1 h')
        have h2 : M ∉ T2 := fun h' => hMS (Finset.mem_powerset.1 hT2 h')
        rw [← Finset.erase_insert h1, ← Finset.erase_insert h2, h]
    · rw [Finset.disjoint_left]
      intro T hT hT'
      rw [Finset.mem_image] at hT'
      obtain ⟨T', _, rfl⟩ := hT'
      exact hMS (Finset.mem_powerset.1 hT (Finset.mem_insert_self M T'))

/-! ## Subset form of `Gw` and the split of a decreasing list at `p` -/

/-- The summand of the subset form of `Gw`. -/
noncomputable def gwTerm (w : ℕ → ℝ) (σ : Bool) (z c : ℝ) (T : Finset ℕ) : ℝ :=
  open Classical in
  if RosOK σ z (toDec T) then (-1) ^ T.card * (∏ q ∈ T, g q) * (c - ∑ q ∈ T, w q) else 0

/-- **Subset form of `Gw`.** -/
theorem Gw_eq_sum (w : ℕ → ℝ) (S : Finset ℕ) : ∀ (σ : Bool) (z c : ℝ),
    Gw g w σ z (toDec S) c = ∑ T ∈ S.powerset, gwTerm g w σ z c T := by
  classical
  induction S using Finset.induction_on_max with
  | empty =>
    intro σ z c
    simp [toDec_empty, Gw, gwTerm, RosOK]
  | insert M S hM ih =>
    intro σ z c
    have hMS : M ∉ S := fun h => lt_irrefl M (hM M h)
    rw [toDec_insert_max M S hM, Finset.powerset_insert, Finset.sum_union]
    · rw [Finset.sum_image]
      · simp only [Gw]
        rw [ih σ z c]
        have hsub : ∀ T ∈ S.powerset, gwTerm g w σ z c (insert M T) =
            -(if headOK σ z M then g M * gwTerm g w (!σ) (z / M) (c - w M) T else 0) := by
          intro T hT
          have hTS : T ⊆ S := Finset.mem_powerset.1 hT
          have hMT : M ∉ T := fun h => hMS (hTS h)
          have hTM : ∀ x ∈ T, x < M := fun x hx => hM x (hTS hx)
          unfold gwTerm
          rw [toDec_insert_max M T hTM, Finset.card_insert_of_notMem hMT, Finset.prod_insert hMT,
            Finset.sum_insert hMT]
          simp only [RosOK]
          by_cases hh : headOK σ z M
          · simp only [hh, true_and, if_true]
            split_ifs <;> ring
          · simp [hh]
        rw [Finset.sum_congr rfl hsub, Finset.sum_neg_distrib]
        by_cases hh : headOK σ z M
        · simp only [hh, if_true]
          rw [ih (!σ) (z / M) (c - w M), ← Finset.mul_sum]; ring
        · simp only [hh, if_false]; simp
      · intro T1 hT1 T2 hT2 h
        have h1 : M ∉ T1 := fun h' => hMS (Finset.mem_powerset.1 hT1 h')
        have h2 : M ∉ T2 := fun h' => hMS (Finset.mem_powerset.1 hT2 h')
        rw [← Finset.erase_insert h1, ← Finset.erase_insert h2, h]
    · rw [Finset.disjoint_left]
      intro T hT hT'
      rw [Finset.mem_image] at hT'
      obtain ⟨T', _, rfl⟩ := hT'
      exact hMS (Finset.mem_powerset.1 hT (Finset.mem_insert_self M T'))

/-- A decreasing listing splits at each of its elements. -/
theorem toDec_split (S : Finset ℕ) : ∀ p ∈ S,
    toDec S = toDec (S.filter (fun q => p < q)) ++ p :: toDec (S.filter (fun q => q < p)) := by
  classical
  induction S using Finset.induction_on_max with
  | empty => intro p hp; simp at hp
  | insert M S hM ih =>
    intro p hp
    rw [toDec_insert_max M S hM]
    rcases Finset.mem_insert.1 hp with rfl | hpS
    · have h1 : (insert p S).filter (fun q => p < q) = ∅ := by
        ext q; simp only [mem_filter, mem_insert, Finset.notMem_empty, iff_false, not_and]
        rintro (rfl | hq) h
        · exact lt_irrefl _ h
        · exact absurd (hM q hq) (not_lt.2 h.le)
      have h2 : (insert p S).filter (fun q => q < p) = S := by
        ext q; simp only [mem_filter, mem_insert]
        constructor
        · rintro ⟨rfl | hq, h⟩
          · exact absurd h (lt_irrefl _)
          · exact hq
        · intro hq; exact ⟨Or.inr hq, hM q hq⟩
      rw [h1, h2, toDec_empty, List.nil_append]
    · have hpM : p < M := hM p hpS
      have h1 : (insert M S).filter (fun q => p < q) = insert M (S.filter (fun q => p < q)) := by
        rw [Finset.filter_insert, if_pos hpM]
      have h2 : (insert M S).filter (fun q => q < p) = S.filter (fun q => q < p) := by
        rw [Finset.filter_insert, if_neg (not_lt.2 hpM.le)]
      rw [h1, h2, toDec_insert_max M _ (fun x hx => hM x (Finset.mem_of_mem_filter x hx)), ih p hpS]
      rfl

end Palprimes.Greaves
