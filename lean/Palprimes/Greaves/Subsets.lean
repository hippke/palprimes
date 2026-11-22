import Palprimes.Greaves.Brun

/-! # From the list recursion to sums over sets of primes

`toDec S` lists a finite set of naturals in decreasing order. `G_eq_sum`:
`G σ z (toDec S) c = Σ_{T ⊆ S, RosOK σ z (toDec T)} (-1)^{|T|} (c − Σ_{p∈T} w p)`. -/

set_option linter.style.longLine false

open Finset

namespace Palprimes.Greaves

/-- Decreasing listing of a finite set. -/
def toDec (S : Finset ℕ) : List ℕ := S.sort (· ≥ ·)

theorem toDec_insert_max (M : ℕ) (S : Finset ℕ) (hM : ∀ x ∈ S, x < M) :
    toDec (insert M S) = M :: toDec S := by
  unfold toDec
  exact Finset.sort_insert (s := S) (r := (· ≥ ·)) (fun b hb => (hM b hb).le) (fun h => lt_irrefl M (hM M h))

theorem toDec_empty : toDec ∅ = [] := by simp [toDec]

variable (w : ℕ → ℝ)

/-- The summand of the subset form. -/
noncomputable def term (σ : Bool) (z c : ℝ) (T : Finset ℕ) : ℝ :=
  open Classical in if RosOK σ z (toDec T) then (-1) ^ T.card * (c - ∑ p ∈ T, w p) else 0

/-- **Subset form of `G`.** -/
theorem G_eq_sum (S : Finset ℕ) : ∀ (σ : Bool) (z c : ℝ),
    G w σ z (toDec S) c = ∑ T ∈ S.powerset, term w σ z c T := by
  classical
  induction S using Finset.induction_on_max with
  | empty =>
    intro σ z c
    simp [toDec_empty, G, term, RosOK]
  | insert M S hM ih =>
    intro σ z c
    have hMS : M ∉ S := fun h => lt_irrefl M (hM M h)
    rw [toDec_insert_max M S hM, Finset.powerset_insert, Finset.sum_union]
    · rw [Finset.sum_image]
      · simp only [G]
        rw [ih σ z c]
        congr 1
        have hsub : ∀ T ∈ S.powerset, term w σ z c (insert M T) =
            -(if headOK σ z M then term w (!σ) (z / M) (c - w M) T else 0) := by
          intro T hT
          have hTS : T ⊆ S := Finset.mem_powerset.1 hT
          have hMT : M ∉ T := fun h => hMS (hTS h)
          have hTM : ∀ x ∈ T, x < M := fun x hx => hM x (hTS hx)
          unfold term
          rw [toDec_insert_max M T hTM, Finset.card_insert_of_notMem hMT, Finset.sum_insert hMT]
          simp only [RosOK]
          by_cases hh : headOK σ z M
          · simp only [hh, true_and, if_true]
            split_ifs <;> ring
          · simp [hh]
        rw [Finset.sum_congr rfl hsub, Finset.sum_neg_distrib]
        split_ifs with hh
        · rw [ih (!σ) (z / M) (c - w M)]; ring
        · simp
      · intro T1 hT1 T2 hT2 h
        have h1 : M ∉ T1 := fun h' => hMS (Finset.mem_powerset.1 hT1 h')
        have h2 : M ∉ T2 := fun h' => hMS (Finset.mem_powerset.1 hT2 h')
        rw [← Finset.erase_insert h1, ← Finset.erase_insert h2, h]
    · rw [Finset.disjoint_left]
      intro T hT hT'
      rw [Finset.mem_image] at hT'
      obtain ⟨T', _, rfl⟩ := hT'
      exact hMS (Finset.mem_powerset.1 hT (Finset.mem_insert_self M T'))

end Palprimes.Greaves
