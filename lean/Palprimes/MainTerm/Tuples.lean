import Palprimes.Greaves.Lemma31

/-! # Chains as strictly decreasing tuples

* `toDec_insert_min`: `toDec (insert p T) = toDec T ++ [p]` when `p` is below `T`;
* `sum_chains_eq`: `Σ_{p∈S} Σ_{T ⊆ S_{>p}} H(toDec T ++ [p]) = Σ_{U ⊆ S, U ≠ ∅} H(toDec U)`;
* `sum_powersetCard_tuples`: `Σ_{|U| = n+1} K(toDec U) = Σ_{q ∈ S^{n+1}, q strictly decreasing} K(ofFn q)`;
* `sum_powerset_range`: if `f ∅ = 0` and `f U = 0` for `|U| > 8`, `Σ_{U⊆S} f = Σ_{n<8} Σ_{|U|=n+1} f`. -/

set_option linter.style.longLine false

open Finset Real

namespace Palprimes.MT

open Palprimes.Greaves

theorem toDec_insert_min (p : ℕ) (T : Finset ℕ) (h : ∀ x ∈ T, p < x) :
    toDec (insert p T) = toDec T ++ [p] := by
  classical
  induction T using Finset.induction_on_max with
  | empty => rw [toDec_insert_max p ∅ (by simp), toDec_empty]; rfl
  | insert M T hM ih =>
    have hpM : p < M := h M (mem_insert_self _ _)
    rw [Finset.insert_comm, toDec_insert_max M (insert p T) ?_, ih (fun x hx => h x (mem_insert_of_mem hx)),
      toDec_insert_max M T hM, List.cons_append]
    intro x hx
    rcases mem_insert.1 hx with rfl | hx
    · exact hpM
    · exact hM x hx

theorem sum_chains_eq (H : List ℕ → ℝ) : ∀ (S : Finset ℕ),
    ∑ p ∈ S, ∑ T ∈ (S.filter (fun q => p < q)).powerset, H (toDec T ++ [p]) =
      ∑ U ∈ S.powerset, (if U = ∅ then 0 else H (toDec U)) := by
  classical
  intro S
  induction S using Finset.induction_on_min with
  | empty => simp
  | insert m S hm ih =>
    have hmS : m ∉ S := fun h => lt_irrefl m (hm m h)
    rw [Finset.sum_insert hmS, Finset.powerset_insert, Finset.sum_union, Finset.sum_image]
    · have e1 : (insert m S).filter (fun q => m < q) = S := by
        ext q; simp only [mem_filter, mem_insert]
        constructor
        · rintro ⟨rfl | hq, h⟩
          · exact absurd h (lt_irrefl _)
          · exact hq
        · intro hq; exact ⟨Or.inr hq, hm q hq⟩
      have e2 : ∀ p ∈ S, (insert m S).filter (fun q => p < q) = S.filter (fun q => p < q) := by
        intro p hp
        rw [Finset.filter_insert, if_neg (not_lt.2 (hm p hp).le)]
      have e3 : ∑ x ∈ S, ∑ T ∈ ((insert m S).filter (fun q => x < q)).powerset, H (toDec T ++ [x]) =
          ∑ x ∈ S, ∑ T ∈ (S.filter (fun q => x < q)).powerset, H (toDec T ++ [x]) :=
        Finset.sum_congr rfl (fun p hp => by rw [e2 p hp])
      rw [e1, e3, ih, add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro T hT
      have hTS := Finset.mem_powerset.1 hT
      rw [if_neg (Finset.insert_ne_empty m T), toDec_insert_min m T (fun x hx => hm x (hTS hx))]
    · intro T1 hT1 T2 hT2 h
      have h1 : m ∉ T1 := fun h' => hmS (Finset.mem_powerset.1 hT1 h')
      have h2 : m ∉ T2 := fun h' => hmS (Finset.mem_powerset.1 hT2 h')
      rw [← Finset.erase_insert h1, ← Finset.erase_insert h2, h]
    · rw [Finset.disjoint_left]
      intro T hT hT'
      rw [Finset.mem_image] at hT'
      obtain ⟨T', _, rfl⟩ := hT'
      exact hmS (Finset.mem_powerset.1 hT (Finset.mem_insert_self m T'))

theorem image_eq_toFinset {n : ℕ} (q : Fin n → ℕ) :
    Finset.univ.image q = (List.ofFn q).toFinset := by
  ext a; simp [List.mem_ofFn]

theorem toDec_image (n : ℕ) (q : Fin n → ℕ) (hq : StrictAnti q) :
    toDec (Finset.univ.image q) = List.ofFn q := by
  classical
  apply List.Perm.eq_of_pairwise' (r := (· ≥ ·))
  · exact Finset.pairwise_sort _ _
  · rw [List.pairwise_ofFn]; intro i j hij; exact (hq hij).le
  · refine (List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _) (List.nodup_ofFn.2 hq.injective)).2 ?_
    intro a
    rw [Finset.mem_sort, image_eq_toFinset, List.mem_toFinset]

/-- The tuple of a finite set, read off its decreasing listing. -/
def tupOf (n : ℕ) (U : Finset ℕ) : Fin n → ℕ := fun k => (toDec U).getD k 0

theorem ofFn_tupOf (n : ℕ) (U : Finset ℕ) (hU : U.card = n) : List.ofFn (tupOf n U) = toDec U := by
  apply List.ext_getElem
  · rw [List.length_ofFn]; unfold toDec; rw [Finset.length_sort, hU]
  · intro k h1 h2
    rw [List.getElem_ofFn]
    unfold tupOf
    rw [List.getD_eq_getElem _ _ h2]

theorem sum_powersetCard_tuples (S : Finset ℕ) (n : ℕ) (K : List ℕ → ℝ) :
    ∑ U ∈ S.powersetCard (n + 1), K (toDec U) =
      ∑ q ∈ Fintype.piFinset (fun _ : Fin (n + 1) => S), (if StrictAnti q then K (List.ofFn q) else 0) := by
  classical
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij' (fun q _ => Finset.univ.image q) (fun U _ => tupOf (n + 1) U)
  · intro q hq
    rw [Finset.mem_filter, Fintype.mem_piFinset] at hq
    rw [Finset.mem_powersetCard]
    refine ⟨?_, ?_⟩
    · intro a ha
      rw [Finset.mem_image] at ha
      obtain ⟨i, _, rfl⟩ := ha
      exact hq.1 i
    · rw [Finset.card_image_of_injective _ hq.2.injective, Finset.card_univ, Fintype.card_fin]
  · intro U hU
    rw [Finset.mem_powersetCard] at hU
    have hL := ofFn_tupOf (n + 1) U hU.2
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨fun k => ?_, ?_⟩
    · have : tupOf (n + 1) U k ∈ List.ofFn (tupOf (n + 1) U) := List.mem_ofFn.2 ⟨k, rfl⟩
      rw [hL, mem_toDec] at this
      exact hU.1 this
    · intro i j hij
      have hp := toDec_pairwise U
      rw [← hL, List.pairwise_ofFn] at hp
      exact hp hij
  · intro q hq
    rw [Finset.mem_filter] at hq
    funext k
    unfold tupOf
    rw [toDec_image _ q hq.2, List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact k.2), List.getElem_ofFn]
  · intro U hU
    rw [Finset.mem_powersetCard] at hU
    rw [image_eq_toFinset, ofFn_tupOf (n + 1) U hU.2]
    unfold toDec; exact Finset.sort_toFinset _ _
  · intro q hq
    rw [Finset.mem_filter] at hq
    rw [toDec_image _ q hq.2]

theorem sum_powerset_range (S : Finset ℕ) (f : Finset ℕ → ℝ) (h0 : f ∅ = 0)
    (hbig : ∀ U ⊆ S, 8 < U.card → f U = 0) :
    ∑ U ∈ S.powerset, f U = ∑ n ∈ Finset.range 8, ∑ U ∈ S.powersetCard (n + 1), f U := by
  classical
  simp only [Finset.powersetCard_eq_filter, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro U hU
  have hUS := Finset.mem_powerset.1 hU
  by_cases hc : 1 ≤ U.card ∧ U.card ≤ 8
  · rw [Finset.sum_eq_single (U.card - 1)]
    · rw [if_pos (by omega)]
    · intro n _ hn; rw [if_neg (by omega)]
    · intro h; exfalso; exact h (Finset.mem_range.2 (by omega))
  · have : f U = 0 := by
      rcases Nat.lt_or_ge U.card 1 with h | h
      · rw [Finset.card_eq_zero.1 (show U.card = 0 by omega)]; exact h0
      · exact hbig U hUS (by omega)
    simp [this]

end Palprimes.MT
