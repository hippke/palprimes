import Omega3.Statements
import Omega3.Items.M10_Analytic

/-!
# M10: Greaves 1986 Lemma 11, `M*(y^U) = E11(y) + o(V(y))`

Proof plan in `Omega3/Items/M10_PLAN.md`: the exact split `M* − E11 = Σ_{p < y^{1/4}} w(p) Δ_p` (`M10_Exact`)
and the bound `|Σ w(p) Δ_p| ≤ ε V(y)` (`M10_Analytic`).
-/

namespace Omega3

theorem itemM10 : ItemM10 := by
  intro b hb h9 h10 ε hε
  obtain ⟨y₀, hy₀⟩ := analytic_bound b hb h9 h10 ε hε
  refine ⟨max y₀ 16, fun y hy => ?_⟩
  rw [exact_split b (le_trans (le_max_right _ _) hy)]
  exact hy₀ y (le_trans (le_max_left _ _) hy)

end Omega3

namespace Omega3

/-- M10 with the uniform Lemma 9 (`Lemma9UStmt`) and Lemma 10 for `p < y` (`Lemma10LtStmt`). -/
theorem itemM10_of_uniform : ∀ b : ℕ, 2 ≤ b → Lemma9UStmt b → Lemma10LtStmt → ∀ ε : ℝ, 0 < ε →
    ∃ y₀ : ℝ, ∀ y ≥ y₀, |Mstar b y (y ^ UU) - E11 b y| ≤ ε * Palprimes.MT.VB b y := by
  intro b hb h9U h10 ε hε
  obtain ⟨y₀, hy₀⟩ := analytic_bound_U b hb h9U h10 ε hε
  refine ⟨max y₀ 16, fun y hy => ?_⟩
  rw [exact_split b (le_trans (le_max_right _ _) hy)]
  exact hy₀ y (le_trans (le_max_left _ _) hy)

end Omega3

namespace Omega3

/-- M10 from the Rosser–Iwaniec upper bounds (`RosserBoundStmt`), the frozen hypotheses otherwise. -/
theorem itemM10_of_rosser (hR : ∀ b : ℕ, 2 ≤ b → RosserBoundStmt b) : ItemM10 := by
  intro b hb h9 h10 ε hε
  obtain ⟨y₀, hy₀⟩ := analytic_bound_U b hb (M10.lemma9U_of_RB b hb h9 (hR b hb)) (lemma10Lt_of h10) ε hε
  refine ⟨max y₀ 16, fun y hy => ?_⟩
  rw [exact_split b (le_trans (le_max_right _ _) hy)]
  exact hy₀ y (le_trans (le_max_left _ _) hy)

end Omega3
