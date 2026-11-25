import Omega3.Statements
namespace Omega3
theorem itemL02 : ItemL02 := by
  intro t p ht0 ht1 hp0 hp1
  have h := Real.geom_mean_le_arith_mean2_weighted hp0 (by linarith : (0:ℝ) ≤ 1 - p) ht0 zero_le_one (by ring : p + (1 - p) = 1)
  rw [Real.one_rpow, mul_one] at h
  linarith
end Omega3
