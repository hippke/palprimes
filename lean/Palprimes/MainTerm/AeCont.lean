import Palprimes.MainTerm.JR

/-! # Null sets in log-log coordinates and a.e. continuity

* `expLevel_null`: `{σ : Σ a_i e^{σ_i} = c}` is Lebesgue-null for `a ≠ 0` (image of a hyperplane
  under the componentwise logarithm);
* `ae_continuousAt_of_bad`: a function continuous off finitely many such sets is a.e. continuous. -/

set_option linter.style.longLine false

open Finset Real MeasureTheory Filter Topology

namespace Palprimes.MT

/-- Componentwise logarithm. -/
noncomputable def logv {m : ℕ} (w : Fin m → ℝ) : Fin m → ℝ := fun i => Real.log (w i)

theorem expLevel_null {m : ℕ} (a : Fin m → ℝ) (ha : a ≠ 0) (c : ℝ) :
    volume {σ : Fin m → ℝ | ∑ i, a i * Real.exp (σ i) = c} = 0 := by
  classical
  let L : (Fin m → ℝ) →ₗ[ℝ] ℝ := ∑ i, a i • LinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i
  have hLw : ∀ w, L w = ∑ i, a i * w i := by intro w; simp [L]
  have hL : L ≠ 0 := by
    intro h
    obtain ⟨k, hk⟩ : ∃ k, a k ≠ 0 := by
      by_contra hcon; push_neg at hcon; exact ha (funext hcon)
    have := LinearMap.congr_fun h (Pi.single k 1)
    rw [hLw] at this
    simp [Pi.single_apply] at this
    exact hk this
  have hH : volume {w : Fin m → ℝ | L w = c} = 0 := volume_linear_level_null L hL c
  set s := {w : Fin m → ℝ | L w = c} ∩ {w | ∀ i, 0 < w i}
  have hs : volume s = 0 := measure_mono_null Set.inter_subset_left hH
  have hd : DifferentiableOn ℝ (logv (m := m)) s := by
    rw [differentiableOn_pi]
    intro i
    exact DifferentiableOn.log ((differentiable_apply i).differentiableOn) (fun w hw => (hw.2 i).ne')
  have himg := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero (μ := volume) hd hs
  apply measure_mono_null _ himg
  intro σ hσ
  refine ⟨fun i => Real.exp (σ i), ⟨?_, fun i => Real.exp_pos _⟩, ?_⟩
  · show L _ = c; rw [hLw]; exact hσ
  · funext i; simp [logv]

theorem ae_continuousAt_of_bad {m : ℕ} (f : (Fin m → ℝ) → ℝ) (B : Finset ((Fin m → ℝ) × ℝ))
    (hB : ∀ p ∈ B, p.1 ≠ 0)
    (hf : ∀ σ : Fin m → ℝ, (∀ p ∈ B, ∑ i, p.1 i * Real.exp (σ i) ≠ p.2) → ContinuousAt f σ) :
    ∀ᵐ σ ∂(volume : Measure (Fin m → ℝ)), ContinuousAt f σ := by
  rw [ae_iff]
  apply measure_mono_null (t := ⋃ p ∈ B, {σ : Fin m → ℝ | ∑ i, p.1 i * Real.exp (σ i) = p.2})
  · intro σ hσ
    simp only [Set.mem_setOf_eq] at hσ
    by_contra hcon
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_and] at hcon
    exact hσ (hf σ (fun p hp => hcon p hp))
  · exact (measure_biUnion_null_iff B.countable_toSet).2 (fun p hp => expLevel_null p.1 (hB p hp) p.2)

/-- Eventual constancy of a non-strict inequality away from its boundary. -/
theorem eventually_le_iff {X : Type*} [TopologicalSpace X] (ψ : X → ℝ) (x0 : X) (hψ : ContinuousAt ψ x0)
    (c : ℝ) (h : ψ x0 ≠ c) : ∀ᶠ x in 𝓝 x0, (ψ x ≤ c ↔ ψ x0 ≤ c) := by
  rcases lt_or_gt_of_ne h with h | h
  · filter_upwards [hψ.eventually (gt_mem_nhds h)] with x hx
    exact ⟨fun _ => h.le, fun _ => hx.le⟩
  · filter_upwards [hψ.eventually (lt_mem_nhds h)] with x hx
    exact ⟨fun h' => absurd h' (not_le.2 hx), fun h' => absurd h' (not_le.2 h)⟩

theorem eventually_lt_iff {X : Type*} [TopologicalSpace X] (ψ : X → ℝ) (x0 : X) (hψ : ContinuousAt ψ x0)
    (c : ℝ) (h : ψ x0 ≠ c) : ∀ᶠ x in 𝓝 x0, (ψ x < c ↔ ψ x0 < c) := by
  filter_upwards [eventually_le_iff (fun x => -ψ x) x0 hψ.neg (-c) (by intro h'; apply h; linarith)] with x hx
  constructor
  · intro h1; by_contra h2; push_neg at h2; have := hx.2 (by linarith); linarith
  · intro h1; by_contra h2; push_neg at h2; have := hx.1 (by linarith); linarith

/-- A function equal near `x0` to `if C then g else 0` with `C` eventually constant is continuous at
`x0` when `g` is. -/
theorem continuousAt_ite_of_eventually {X : Type*} [TopologicalSpace X] (f g : X → ℝ) (C : X → Prop)
    [DecidablePred C] (x0 : X) (hfe : ∀ x, f x = if C x then g x else 0)
    (hC : ∀ᶠ x in 𝓝 x0, (C x ↔ C x0)) (hg : C x0 → ContinuousAt g x0) : ContinuousAt f x0 := by
  by_cases h : C x0
  · have : f =ᶠ[𝓝 x0] g := by
      filter_upwards [hC] with x hx
      rw [hfe, if_pos (hx.2 h)]
    exact (hg h).congr this.symm
  · have : f =ᶠ[𝓝 x0] fun _ => 0 := by
      filter_upwards [hC] with x hx
      rw [hfe, if_neg (fun h' => h (hx.1 h'))]
    exact continuousAt_const.congr this.symm

end Palprimes.MT
