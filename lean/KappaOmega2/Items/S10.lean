import KappaOmega2.Statements

/-!
# Item S10: the Σ₂ band certificate at R = 2 (no bands)

At `U = 99/103`, `kSq = 582/103` Greaves' plain weights already cover `p₁ ≥ y^{1/3}`: with the empty band list
`B = ⟨[1/3], [], []⟩` the last edge is `x_n = 1/3` and `kSq (1 − 1/3)² = 4(U − 1/3)` holds with equality, so
`BandOK B` holds, `BandAllow B` and the `c_η` bounds are vacuous and `bandCost B = 0`.
(The five-band certificate of Ω ≤ 3 is kept in `omega-2/logs/sieve_port/S10_old/`.)
-/

set_option linter.style.longLine false

namespace KappaOmega2

namespace S10

/-- The band data: no bands. -/
def BD : BandData where
  xs := [1 / 3]
  etas := []
  cs := []

lemma xn_eq : BD.xn = 1 / 3 := rfl

end S10

open S10

theorem itemS10 : ItemS10 := by
  refine ⟨BD, 1, one_pos, ?_, ?_, ?_, ?_⟩
  · refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simp [BD]
    · intro e he; simp [BD] at he
    · intro c hc; simp [BD] at hc
    · rw [xn_eq]; norm_num [UU]
    · rw [xn_eq]; norm_num [UU, kSq]
  · intro i hi; simp [BD] at hi
  · intro i hi; simp [BD] at hi
  · simp [bandCost, BD]; norm_num

end KappaOmega2
