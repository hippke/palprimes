import Palprimes.E1.Constants
import Palprimes.E1.IintRec
import Palprimes.MainTerm.E1

set_option linter.style.longLine false

/-! # E1, phase E11: identification `F_I = FjrC`, `f_I = fjr` (blueprint D6)

Blueprint `lean/e1/E1_BLUEPRINT.md` §5.3, D6. With `A_I = 2e^γ` and `B_I = 0` (E9), the limit functions
`F_I`, `f_I` (E7, D3 in integral form) and the Lemma 5.1 series `Fjr`, `fjr` (E10, D5′) satisfy the
same delay equations
`s F(s) = 2e^γ + ∫_3^s f(u − 1) du` (`s > 1`) and `s f(s) = ∫_2^s F(u − 1) du` (`s ≥ 2`),
with `f = 0` on `(−∞, 2]` (`fIext`, `fjr_le_two`). Stepping through unit intervals:
* `stepF`: `fIext = fjr` on `(−∞, a]` (`a ≥ 2`) gives `F_I = Fjr` on `(1, a + 1]`;
* `stepf`: `F_I = Fjr` on `(1, a]` gives `fIext = fjr` on `(−∞, a + 1]`
  (the single point `u − 1 = 1`, where `F_I(1) = 2e^γ ≠ 0 = Fjr 1`, is avoided by integrating over `Ioc`).
The induction runs over all `s`, so the results hold for every `s ≥ 1` (resp. `s ≥ 2`);
the `[1, 9]` forms needed by `RosserAsymp` are `FI_eq_FjrC_of_le_nine`, `fI_eq_fjr_of_le_nine`. -/

open MeasureTheory Set Real Filter Topology

namespace Palprimes.E1

open Palprimes.MT

/-- `fIext = fjr` on `(−∞, 2]` (both vanish there). -/
lemma fIext_eq_fjr_of_le_two {x : ℝ} (hx : x ≤ 2) : fIext x = fjr x := by
  rw [fjr_le_two hx, fIext_of_le_two hx]

/-- Step for `F`: `fIext = fjr` on `(−∞, a]` gives `F_I = Fjr` on `(1, a + 1]`. -/
lemma stepF {a : ℝ} (ha : 2 ≤ a) (hf : ∀ x, x ≤ a → fIext x = fjr x) {s : ℝ} (h1 : 1 < s)
    (hs : s ≤ a + 1) : FI s = Fjr s := by
  have hint : ∫ u in (3 : ℝ)..s, fIext (u - 1) = ∫ u in (3 : ℝ)..s, fjr (u - 1) := by
    refine intervalIntegral.integral_congr fun u hu => hf _ ?_
    rcases mem_uIcc.mp hu with ⟨_, hu2⟩ | ⟨_, hu2⟩ <;> linarith
  refine mul_left_cancel₀ (ne_of_gt (by linarith : (0 : ℝ) < s)) ?_
  rw [mul_FI_eq_ext h1.le, Fjr_dde h1, hint, AI_eq_two_mul_exp]

/-- Step for `f`: `F_I = Fjr` on `(1, a]` gives `fIext = fjr` on `(−∞, a + 1]`. -/
lemma stepf {a : ℝ} (hF : ∀ x, 1 < x → x ≤ a → FI x = Fjr x) {s : ℝ} (hs : s ≤ a + 1) :
    fIext s = fjr s := by
  rcases lt_or_ge s 2 with h2 | h2
  · exact fIext_eq_fjr_of_le_two h2.le
  rw [fIext_of_two_le h2]
  have hint : ∫ u in (2 : ℝ)..s, FI (u - 1) = ∫ u in (2 : ℝ)..s, Fjr (u - 1) := by
    refine intervalIntegral.integral_congr_ae (ae_of_all _ fun u hu => ?_)
    rw [uIoc_of_le h2] at hu
    exact hF _ (by linarith [hu.1]) (by linarith [hu.2])
  refine mul_left_cancel₀ (ne_of_gt (by linarith : (0 : ℝ) < s)) ?_
  rw [mul_fI h2, fjr_dde h2, hint, BI_eq_zero, zero_add]

lemma fIext_eq_fjr_of_le_nat (n : ℕ) : ∀ x : ℝ, x ≤ (n : ℝ) + 2 → fIext x = fjr x := by
  induction n with
  | zero => intro x hx; exact fIext_eq_fjr_of_le_two (by simpa using hx)
  | succ n ih =>
    intro x hx
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    push_cast at hx
    exact stepf (a := (n : ℝ) + 3)
      (fun y hy1 hy => stepF (a := (n : ℝ) + 2) (by linarith) ih hy1 (by linarith)) (by linarith)

/-- `fIext = fjr` everywhere (`f_I = fjr` on `[2, ∞)`, both `0` below `2`). -/
theorem fIext_eq_fjr (x : ℝ) : fIext x = fjr x := by
  obtain ⟨n, hn⟩ := exists_nat_ge x
  exact fIext_eq_fjr_of_le_nat n x (by linarith)

/-- **D6 (−)**: `f_I(s) = fjr(s)` for `s ≥ 2`. -/
theorem fI_eq_fjr {s : ℝ} (h2 : 2 ≤ s) : fI s = fjr s := by
  rw [← fIext_of_two_le h2]; exact fIext_eq_fjr s

/-- `F_I(s) = Fjr(s)` for `s > 1`. -/
theorem FI_eq_Fjr {s : ℝ} (h1 : 1 < s) : FI s = Fjr s :=
  stepF (a := max 2 s) (le_max_left _ _) (fun x _ => fIext_eq_fjr x) h1
    (by linarith [le_max_right 2 s])

/-- **D6 (+)**: `F_I(s) = FjrC(s)` for `s ≥ 1` (at `s = 1`: `F_I(1) = A_I = 2e^γ = FjrC 1`). -/
theorem FI_eq_FjrC {s : ℝ} (h1 : 1 ≤ s) : FI s = FjrC s := by
  rcases h1.lt_or_eq with h | rfl
  · have hC : FjrC s = Fjr s := by simp [FjrC, ne_of_gt h]
    rw [hC]; exact FI_eq_Fjr h
  · have hC : FjrC 1 = 2 * exp eulerMascheroniConstant := by simp [FjrC]
    rw [hC, FI_one, AI_eq_two_mul_exp]

/-- **D6 (+)** on `[1, 9]` (the range of `RosserAsymp`). -/
theorem FI_eq_FjrC_of_le_nine {s : ℝ} (h1 : 1 ≤ s) (_h9 : s ≤ 9) : FI s = FjrC s := FI_eq_FjrC h1

/-- **D6 (−)** on `[2, 9]` (the range of `RosserAsymp`). -/
theorem fI_eq_fjr_of_le_nine {s : ℝ} (h2 : 2 ≤ s) (_h9 : s ≤ 9) : fI s = fjr s := fI_eq_fjr h2

end Palprimes.E1
