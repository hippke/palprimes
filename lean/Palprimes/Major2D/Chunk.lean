import Mathlib.Data.List.Basic
import Palprimes.Major2D.Code

/-! # Combining chunked cell certificates -/

namespace Palprimes.M2

/-- the chunks are consecutive and cover `[o, len)`. -/
def chainOK : ℕ → List (ℕ × ℕ) → ℕ → Bool
  | o, [], len => Nat.ble len o
  | o, c :: rest, len => Nat.beq c.1 o && chainOK (o + c.2) rest len

theorem all_chunks2 {α : Type} (p : α → Bool) (L : List α) : ∀ (cs : List (ℕ × ℕ)) (o : ℕ),
    (∀ c ∈ cs, ((L.drop c.1).take c.2).all p = true) → chainOK o cs L.length = true → (L.drop o).all p = true := by
  intro cs
  induction cs with
  | nil =>
    intro o _ h
    simp only [chainOK, Nat.ble_eq] at h
    rw [List.drop_eq_nil_of_le h]; rfl
  | cons c rest ih =>
    intro o h hc
    simp only [chainOK, Bool.and_eq_true, Nat.beq_eq] at hc
    obtain ⟨h1, h2⟩ := hc
    rw [← List.take_append_drop c.2 (L.drop o), List.all_append, Bool.and_eq_true, List.drop_drop]
    constructor
    · have := h c List.mem_cons_self; rwa [h1] at this
    · exact ih (o + c.2) (fun d hd => h d (List.mem_cons_of_mem _ hd)) h2

end Palprimes.M2
