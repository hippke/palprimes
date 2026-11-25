import Omega3.Statements

namespace Omega3

open Finset Palprimes.Greaves

theorem itemS15 : ItemS15 := by
  unfold ItemS15
  intro a z ha
  set S := a.primeFactors.filter (fun p : ℕ => (p : ℝ) < z) with hSdef
  have hR : radLt a z = ∏ p ∈ S, p := rfl
  have hS : ∀ p ∈ S, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  have hSz : ∀ p ∈ S, (p : ℝ) < z := fun p hp => (Finset.mem_filter.mp hp).2
  have hSub : S ⊆ a.primeFactors := Finset.filter_subset _ _
  have hPF : (∏ p ∈ S, p).primeFactors = S := Nat.primeFactors_prod hS
  have hdvdA : (∏ p ∈ S, p) ∣ a :=
    (Finset.prod_dvd_prod_of_subset _ _ _ hSub).trans (Nat.prod_primeFactors_dvd a)
  have hprim : (∏ p ∈ S, p) ∣ primorialLt z := by
    unfold primorialLt
    apply Finset.prod_dvd_prod_of_subset
    intro p hp
    unfold primesBelow
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, hS p hp, hSz p hp⟩
    have := (Nat.lt_ceil).mpr (hSz p hp)
    omega
  have hSqf : Squarefree (∏ p ∈ S, p) := by
    have h := Nat.squarefree_prod_primeFactors (∏ p ∈ S, p)
    rwa [hPF] at h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hR]
    exact hSqf
  · intro p hp
    rw [hR, hPF] at hp
    exact ⟨hSz p hp, Nat.dvd_of_mem_primeFactors (hSub hp)⟩
  · rw [hR]
    exact hprim
  · rw [hR]
    exact hdvdA
  · rw [hR]
    unfold radLt
    rw [hPF, Finset.filter_true_of_mem (fun p hp => hSz p hp)]
  · intro d hd hdz
    constructor
    · intro hda
      rw [hR]
      have hsub' : d.primeFactors ⊆ S := by
        intro p hp
        have hpp := Nat.prime_of_mem_primeFactors hp
        have hpd := Nat.dvd_of_mem_primeFactors hp
        exact Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hpp, hpd.trans hda, by omega⟩, hdz p hp⟩
      have key : ∏ p ∈ d.primeFactors, p ∣ ∏ p ∈ S, p :=
        Finset.prod_dvd_prod_of_subset _ _ _ hsub'
      rw [Nat.prod_primeFactors_of_squarefree hd] at key
      exact key
    · intro hdR
      rw [hR] at hdR
      exact hdR.trans hdvdA

end Omega3
