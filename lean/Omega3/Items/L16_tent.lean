import Omega3.Statements

namespace Omega3

open Finset

lemma L16_count_pairs (m a : ℕ) :
    (∑ i ∈ range m, ∑ j ∈ range m, if i + j = a then 1 else 0 : ℕ) = min (a + 1) (2 * m - 1 - a) := by
  have inner : ∀ i ∈ range m, (∑ j ∈ range m, if i + j = a then 1 else 0 : ℕ) =
      if (i ≤ a ∧ a < i + m) then 1 else 0 := by
    intro i _
    by_cases h : i ≤ a
    · have hj : ∀ j : ℕ, (i + j = a ↔ j = a - i) := fun j => by omega
      simp only [hj, Finset.sum_ite_eq', Finset.mem_range]
      split_ifs <;> omega
    · have hz : ∀ j ∈ range m, (if i + j = a then (1 : ℕ) else 0) = 0 :=
        fun j _ => if_neg (by omega)
      rw [Finset.sum_eq_zero hz, if_neg (by omega : ¬ (i ≤ a ∧ a < i + m))]
  rw [Finset.sum_congr rfl inner, ← Finset.card_filter]
  have hf : (range m).filter (fun i => i ≤ a ∧ a < i + m) =
      Finset.Ico (a + 1 - m) (min m (a + 1)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hf, Nat.card_Ico, min_def, min_def]
  split_ifs <;> omega

lemma L16_sum_pairs {R : Type*} [CommSemiring R] (m : ℕ) (G : ℕ → R) :
    ∑ i ∈ range m, ∑ j ∈ range m, G (i + j) =
      ∑ a ∈ range (2 * m - 1), ((min (a + 1) (2 * m - 1 - a) : ℕ) : R) * G a := by
  have hc : ∀ a : ℕ, ((min (a + 1) (2 * m - 1 - a) : ℕ) : R) =
      ∑ i ∈ range m, ∑ j ∈ range m, if i + j = a then (1 : R) else 0 := by
    intro a
    have h := congrArg (fun k : ℕ => (k : R)) (L16_count_pairs m a)
    push_cast at h
    exact h.symm
  have hL : ∀ i ∈ range m, ∀ j ∈ range m, G (i + j) =
      ∑ a ∈ range (2 * m - 1), if i + j = a then G a else 0 := by
    intro i hi j hj
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr (show i + j < 2 * m - 1 by omega))]
  calc ∑ i ∈ range m, ∑ j ∈ range m, G (i + j)
      = ∑ i ∈ range m, ∑ a ∈ range (2 * m - 1), ∑ j ∈ range m, if i + j = a then G a else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun j hj => hL i hi j hj)
    _ = ∑ a ∈ range (2 * m - 1), ∑ i ∈ range m, ∑ j ∈ range m, if i + j = a then G a else 0 :=
        Finset.sum_comm
    _ = ∑ a ∈ range (2 * m - 1), ((min (a + 1) (2 * m - 1 - a) : ℕ) : R) * G a := by
        apply Finset.sum_congr rfl
        intro a _
        rw [hc a, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        simp only [ite_mul, one_mul, zero_mul]


lemma L16_tent_sum (m : ℕ) :
    ∑ a ∈ range (2 * m - 1), min (a + 1) (2 * m - 1 - a) = m * m := by
  have h := L16_sum_pairs (R := ℕ) m (fun _ => 1)
  simp only [mul_one, Finset.sum_const, Finset.card_range, smul_eq_mul] at h
  rw [h]
  simp

end Omega3
