import Palprimes.ExpSum.Collision

/-! # M4. Large sieve (Gallagher form) and Farey spacing

Not in mathlib. Proof without integrals: duality, averaging over pairs `(u, v) ∈ [0,M)²`
(Fejér weight), Dirichlet-kernel decay `|D_M(t)| ≤ 1/(2‖t‖)` (Jordan's inequality),
shell count of `δ`-spaced points, Schur test. Constant `4N + 3/δ + 2`. -/

set_option linter.style.longLine false

open Finset Real

namespace Palprimes

theorem ee_eq_exp (t : ℝ) : ee t = Complex.exp (Complex.I * ((2 * π * t : ℝ) : ℂ)) := by
  unfold ee; congr 1; push_cast; ring

theorem norm_ee_sub_one (t : ℝ) : ‖ee t - 1‖ = 2 * |Real.sin (π * t)| := by
  rw [ee_eq_exp, Complex.norm_exp_I_mul_ofReal_sub_one, show 2 * π * t / 2 = π * t by ring,
    Real.norm_eq_abs, abs_mul, abs_two]

theorem distZ_le (t : ℝ) (n : ℤ) : distZ t ≤ |t - n| := round_le t n

theorem distZ_le_half (t : ℝ) : distZ t ≤ 1 / 2 := abs_sub_round t

theorem distZ_neg (t : ℝ) : distZ (-t) = distZ t := by
  apply le_antisymm
  · calc distZ (-t) ≤ |-t - ((-round t : ℤ) : ℝ)| := distZ_le _ _
      _ = distZ t := by unfold distZ; push_cast; rw [show -t - -(round t : ℝ) = -(t - round t) by ring,
          abs_neg]
  · calc distZ t ≤ |t - ((-round (-t) : ℤ) : ℝ)| := distZ_le _ _
      _ = distZ (-t) := by unfold distZ; push_cast; rw [show t - -(round (-t) : ℝ) = -(-t - round (-t)) by ring,
          abs_neg]

theorem distZ_add_int (t : ℝ) (n : ℤ) : distZ (t + n) = distZ t := by
  apply le_antisymm
  · calc distZ (t + n) ≤ |t + n - ((round t + n : ℤ) : ℝ)| := distZ_le _ _
      _ = distZ t := by unfold distZ; push_cast; ring_nf
  · calc distZ t ≤ |t - ((round (t + n) - n : ℤ) : ℝ)| := distZ_le _ _
      _ = distZ (t + n) := by unfold distZ; push_cast; ring_nf

/-- Jordan: `|sin(πt)| ≥ 2‖t‖`. -/
theorem abs_sin_pi_ge (t : ℝ) : 2 * distZ t ≤ |Real.sin (π * t)| := by
  set u := t - round t with hu
  have hu2 : |u| ≤ 1 / 2 := abs_sub_round t
  have hsin : |Real.sin (π * t)| = |Real.sin (π * u)| := by
    have : π * t = π * u + (round t : ℤ) * π := by rw [hu]; ring
    rw [this, Real.sin_add_int_mul_pi, abs_mul]
    simp
  rw [hsin]
  have h1 : 0 ≤ π * |u| := by positivity
  have h2 : π * |u| ≤ π / 2 := by nlinarith [Real.pi_pos]
  have hj := Real.mul_le_sin h1 h2
  have hab : |Real.sin (π * u)| = Real.sin (π * |u|) := by
    rcases le_total 0 u with h | h
    · rw [abs_of_nonneg h, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
        (by nlinarith [Real.pi_pos, abs_of_nonneg h ▸ hu2]))]
    · rw [abs_of_nonpos h, show π * -u = -(π * u) by ring, Real.sin_neg,
        abs_of_nonpos]
      have : 0 ≤ Real.sin (π * -u) := Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [Real.pi_pos])
        (by nlinarith [Real.pi_pos, abs_of_nonpos h ▸ hu2])
      rw [show π * -u = -(π * u) by ring, Real.sin_neg] at this
      linarith
  rw [hab]
  unfold distZ
  rw [← hu]
  have : 2 / π * (π * |u|) = 2 * |u| := by field_simp
  linarith

/-- Dirichlet kernel `D_M(t) = Σ_{u<M} e(ut)`. -/
noncomputable def dirK (M : ℕ) (t : ℝ) : ℂ := ∑ u ∈ range M, ee (u * t)

theorem norm_dirK_le_M (M : ℕ) (t : ℝ) : ‖dirK M t‖ ≤ M := by
  unfold dirK
  calc _ ≤ ∑ u ∈ range M, ‖ee (u * t)‖ := norm_sum_le _ _
    _ = M := by simp [norm_ee]

theorem ee_pow (t : ℝ) (u : ℕ) : ee (u * t) = ee t ^ u := by
  unfold ee
  rw [← Complex.exp_natCast_mul]
  congr 1; push_cast; ring

theorem norm_dirK_le (M : ℕ) (t : ℝ) (ht : 0 < distZ t) : ‖dirK M t‖ ≤ 1 / (2 * distZ t) := by
  have hne : ee t - 1 ≠ 0 := by
    intro h
    have := norm_ee_sub_one t
    rw [h, norm_zero] at this
    have := abs_sin_pi_ge t
    linarith
  have hgeom : dirK M t * (ee t - 1) = ee (M * t) - 1 := by
    unfold dirK
    simp only [ee_pow]
    rw [geom_sum_mul]
  have hnum : ‖ee (M * t) - 1‖ ≤ 2 := by
    calc _ ≤ ‖ee (M * t)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_ee, norm_one]; norm_num
  have hden : 4 * distZ t ≤ ‖ee t - 1‖ := by
    rw [norm_ee_sub_one]; linarith [abs_sin_pi_ge t]
  have hpos : 0 < ‖ee t - 1‖ := norm_pos_iff.2 hne
  have : ‖dirK M t‖ = ‖ee (M * t) - 1‖ / ‖ee t - 1‖ := by
    rw [← hgeom, norm_mul, mul_div_cancel_right₀ _ hpos.ne']
  rw [this, div_le_div_iff₀ hpos (by positivity)]
  nlinarith


theorem sum_inv_sq_Icc (K : ℕ) (hK : 1 ≤ K) :
    ∑ k ∈ Icc 1 K, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 2 - 1 / K := by
  induction K with
  | zero => omega
  | succ K ih =>
    rcases Nat.eq_zero_or_pos K with h | h
    · subst h; norm_num
    · rw [Finset.sum_Icc_succ_top (by omega)]
      have hih := ih h
      have hK : (0 : ℝ) < K := by exact_mod_cast h
      push_cast
      have : 1 / ((K : ℝ) + 1) ^ 2 ≤ 1 / K - 1 / (K + 1) := by
        rw [div_sub_div _ _ hK.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      linarith

theorem sum_inv_sq_le_two (s : Finset ℕ) (hs : ∀ k ∈ s, 1 ≤ k) :
    ∑ k ∈ s, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 2 := by
  rcases s.eq_empty_or_nonempty with h | h
  · simp [h]
  · set K := s.max' h
    have hK : 1 ≤ K := hs K (s.max'_mem h)
    calc ∑ k ∈ s, (1 : ℝ) / (k : ℝ) ^ 2 ≤ ∑ k ∈ Icc 1 K, (1 : ℝ) / (k : ℝ) ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro k hk; rw [mem_Icc]; exact ⟨hs k hk, s.le_max' k hk⟩
          · intro _ _ _; positivity
      _ ≤ 2 - 1 / K := sum_inv_sq_Icc K hK
      _ ≤ 2 := by have : (0 : ℝ) ≤ 1 / K := by positivity
                  linarith

/-- One side of the shell count: points `x_j` with `y_j > 0`. -/
theorem shell_sum_pos {ι : Type*} [DecidableEq ι] (pts : Finset ι) (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ i ∈ pts, ∀ j ∈ pts, i ≠ j → δ ≤ distZ (x i - x j)) (i : ι) (_hi : i ∈ pts)
    (y : ι → ℝ) (hy : ∀ j, ∃ r : ℤ, y j = x j - x i - r) (hyd : ∀ j ∈ pts, j ≠ i → δ ≤ |y j|)
    (s : Finset ι) (hs : s ⊆ pts.erase i) (hpos : ∀ j ∈ s, 0 < y j) :
    ∑ j ∈ s, 1 / (4 * (y j) ^ 2) ≤ 1 / (2 * δ ^ 2) := by
  classical
  set k : ι → ℕ := fun j => ⌊y j / δ⌋₊ with hk
  have hk1 : ∀ j ∈ s, 1 ≤ k j := by
    intro j hj
    have hjp := hs hj
    rw [Finset.mem_erase] at hjp
    have h1 := hyd j hjp.2 hjp.1
    rw [abs_of_pos (hpos j hj)] at h1
    simp only [hk]
    rw [Nat.one_le_floor_iff, le_div_iff₀ hδ]; linarith
  have hkle : ∀ j ∈ s, (k j : ℝ) * δ ≤ y j := by
    intro j hj
    have := Nat.floor_le (div_nonneg (hpos j hj).le hδ.le)
    simp only [hk]
    rwa [le_div_iff₀ hδ] at this
  have hkinj : Set.InjOn k s := by
    intro j hj j' hj' hjj
    by_contra hne
    have hjp := hs hj; have hjp' := hs hj'
    rw [Finset.mem_erase] at hjp hjp'
    have hsp := hsep j hjp.2 j' hjp'.2 hne
    have h1 := Nat.lt_floor_add_one (y j / δ)
    have h2 := Nat.lt_floor_add_one (y j' / δ)
    have h3 := hkle j hj
    have h4 := hkle j' hj'
    simp only [hk] at hjj h3 h4
    rw [hjj] at h1 h3
    rw [div_lt_iff₀ hδ] at h1 h2
    have hlt : |y j - y j'| < δ := by rw [abs_lt]; constructor <;> nlinarith
    obtain ⟨r, hr⟩ := hy j
    obtain ⟨r', hr'⟩ := hy j'
    have : x j - x j' = (y j - y j') + ((r - r' : ℤ) : ℝ) := by rw [hr, hr']; push_cast; ring
    have hd : distZ (x j - x j') ≤ |y j - y j'| := by
      rw [this, distZ_add_int]
      calc distZ (y j - y j') ≤ |y j - y j' - ((0 : ℤ) : ℝ)| := distZ_le _ _
        _ = _ := by simp
    linarith
  calc ∑ j ∈ s, 1 / (4 * (y j) ^ 2) ≤ ∑ j ∈ s, 1 / (4 * δ ^ 2) * (1 / ((k j : ℝ)) ^ 2) := by
        apply Finset.sum_le_sum
        intro j hj
        have h1 := hkle j hj
        have h0 : (1 : ℝ) ≤ k j := by exact_mod_cast hk1 j hj
        have hyj := hpos j hj
        have hkd : 0 ≤ (k j : ℝ) * δ := by positivity
        have hsq := mul_le_mul h1 h1 hkd (by linarith)
        rw [div_mul_div_comm, one_mul, one_div_le_one_div (mul_pos (by norm_num) (pow_pos hyj 2))
          (mul_pos (mul_pos (by norm_num) (pow_pos hδ 2)) (pow_pos (by linarith) 2))]
        nlinarith
    _ = 1 / (4 * δ ^ 2) * ∑ m ∈ s.image k, (1 : ℝ) / (m : ℝ) ^ 2 := by
        rw [Finset.mul_sum, Finset.sum_image hkinj]
    _ ≤ 1 / (4 * δ ^ 2) * 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply sum_inv_sq_le_two
        intro m hm
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hm
        exact hk1 j hj
    _ = 1 / (2 * δ ^ 2) := by field_simp; ring

theorem norm_dirK_sq_le (M : ℕ) (t : ℝ) (ht : 0 < distZ t) :
    ‖dirK M t‖ ^ 2 ≤ 1 / (4 * distZ t ^ 2) := by
  have h := norm_dirK_le M t ht
  calc ‖dirK M t‖ ^ 2 ≤ (1 / (2 * distZ t)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = 1 / (4 * distZ t ^ 2) := by field_simp; ring

/-- **Row sums** of the kernel at `δ`-spaced points. -/
theorem row_sum_le {ι : Type*} (pts : Finset ι) (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ i ∈ pts, ∀ j ∈ pts, i ≠ j → δ ≤ distZ (x i - x j)) (M : ℕ) (i : ι) (hi : i ∈ pts) :
    ∑ j ∈ pts, ‖dirK M (x i - x j)‖ ^ 2 ≤ (M : ℝ) ^ 2 + 1 / δ ^ 2 := by
  classical
  rw [← Finset.add_sum_erase pts _ hi, sub_self]
  have h0 : ‖dirK M 0‖ ^ 2 ≤ (M : ℝ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_dirK_le_M M 0) 2
  set y : ι → ℝ := fun j => (x j - x i) - round (x j - x i) with hy
  have hyr : ∀ j, ∃ r : ℤ, y j = x j - x i - r := fun j => ⟨round (x j - x i), rfl⟩
  have hyabs : ∀ j, |y j| = distZ (x i - x j) := by
    intro j
    simp only [hy]
    rw [show x i - x j = -(x j - x i) by ring, distZ_neg]
    rfl
  have hyd : ∀ j ∈ pts, j ≠ i → δ ≤ |y j| := by
    intro j hj hji
    rw [hyabs]; exact hsep i hi j hj (Ne.symm hji)
  have hterm : ∀ j ∈ pts.erase i, ‖dirK M (x i - x j)‖ ^ 2 ≤ 1 / (4 * (y j) ^ 2) := by
    intro j hj
    rw [Finset.mem_erase] at hj
    have hd := hsep i hi j hj.2 (Ne.symm hj.1)
    have := norm_dirK_sq_le M (x i - x j) (lt_of_lt_of_le hδ hd)
    rwa [← hyabs, sq_abs] at this
  have hsplit : pts.erase i = (pts.erase i).filter (fun j => 0 < y j) ∪
      (pts.erase i).filter (fun j => 0 < -y j) := by
    ext j
    simp only [mem_union, mem_filter]
    constructor
    · intro hj
      have hjp := Finset.mem_erase.1 hj
      have := hyd j hjp.2 hjp.1
      rcases lt_trichotomy (y j) 0 with h | h | h
      · right; exact ⟨hj, by linarith⟩
      · rw [h, abs_zero] at this; linarith
      · left; exact ⟨hj, h⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  have hdisj : Disjoint ((pts.erase i).filter (fun j => 0 < y j))
      ((pts.erase i).filter (fun j => 0 < -y j)) := by
    rw [Finset.disjoint_filter]; intro j _ h1 h2; linarith
  have hpos := shell_sum_pos pts x δ hδ hsep i hi y hyr hyd
    ((pts.erase i).filter (fun j => 0 < y j)) (filter_subset _ _) (fun j hj => (mem_filter.1 hj).2)
  have hneg := shell_sum_pos pts (fun j => -x j) δ hδ (fun a ha c hc hac => by
      rw [show -x a - -x c = -(x a - x c) by ring, distZ_neg]; exact hsep a ha c hc hac)
    i hi (fun j => -y j) (fun j => by obtain ⟨r, hr⟩ := hyr j; exact ⟨-r, by rw [hr]; push_cast; ring⟩)
    (fun j hj hji => by rw [abs_neg]; exact hyd j hj hji)
    ((pts.erase i).filter (fun j => 0 < -y j)) (filter_subset _ _) (fun j hj => (mem_filter.1 hj).2)
  simp only [neg_sq] at hneg
  calc ‖dirK M 0‖ ^ 2 + ∑ j ∈ pts.erase i, ‖dirK M (x i - x j)‖ ^ 2
      ≤ (M : ℝ) ^ 2 + ∑ j ∈ pts.erase i, 1 / (4 * (y j) ^ 2) := by
        gcongr with j hj; exact hterm j hj
    _ = (M : ℝ) ^ 2 + (∑ j ∈ (pts.erase i).filter (fun j => 0 < y j), 1 / (4 * (y j) ^ 2) +
          ∑ j ∈ (pts.erase i).filter (fun j => 0 < -y j), 1 / (4 * (y j) ^ 2)) := by
        rw [← Finset.sum_union hdisj, ← hsplit]
    _ ≤ (M : ℝ) ^ 2 + (1 / (2 * δ ^ 2) + 1 / (2 * δ ^ 2)) := by gcongr
    _ = (M : ℝ) ^ 2 + 1 / δ ^ 2 := by field_simp; ring

theorem conj_dirK (M : ℕ) (t : ℝ) : starRingEnd ℂ (dirK M t) = dirK M (-t) := by
  unfold dirK
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [conj_ee]; congr 1; ring

theorem norm_dirK_neg (M : ℕ) (t : ℝ) : ‖dirK M (-t)‖ = ‖dirK M t‖ := by
  rw [← conj_dirK, Complex.norm_conj]

/-- `Σ_{u,v<M} e((u−v)t) = |D_M(t)|²`. -/
theorem sum_uv_ee (M : ℕ) (t : ℝ) :
    ∑ u ∈ range M, ∑ v ∈ range M, ee (((u : ℝ) - v) * t) = ((‖dirK M t‖ ^ 2 : ℝ) : ℂ) := by
  have : dirK M t * starRingEnd ℂ (dirK M t) = ((‖dirK M t‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [← this, conj_dirK]
  unfold dirK
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl; intro u _
  apply Finset.sum_congr rfl; intro v _
  rw [← ee_add]; congr 1; ring

/-- `Σ_{u,v<M} ‖Σ_i c_i e((u−v)x_i)‖² ≤ Σ_{i,j} ‖c_i‖‖c_j‖ |D_M(x_i − x_j)|²`. -/
theorem sum_uv_norm_sq_le {ι : Type*} (pts : Finset ι) (c : ι → ℂ) (x : ι → ℝ) (M : ℕ) :
    ∑ u ∈ range M, ∑ v ∈ range M, ‖∑ i ∈ pts, c i * ee (((u : ℝ) - v) * x i)‖ ^ 2 ≤
      ∑ i ∈ pts, ∑ j ∈ pts, ‖c i‖ * ‖c j‖ * ‖dirK M (x i - x j)‖ ^ 2 := by
  have hexp : ∀ m : ℝ, ‖∑ i ∈ pts, c i * ee (m * x i)‖ ^ 2 =
      (∑ i ∈ pts, ∑ j ∈ pts, c i * starRingEnd ℂ (c j) * ee (m * (x i - x j))).re := by
    intro m
    rw [← Complex.normSq_eq_norm_sq, ← Complex.ofReal_re (Complex.normSq _), ← Complex.mul_conj,
      map_sum, Finset.sum_mul_sum]
    congr 1
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [map_mul, conj_ee, show c i * ee (m * x i) * (starRingEnd ℂ (c j) * ee (-(m * x j))) =
      c i * starRingEnd ℂ (c j) * (ee (m * x i) * ee (-(m * x j))) by ring, ← ee_add]
    congr 2; ring
  simp only [hexp]
  rw [show ∑ u ∈ range M, ∑ v ∈ range M,
      (∑ i ∈ pts, ∑ j ∈ pts, c i * starRingEnd ℂ (c j) * ee (((u : ℝ) - v) * (x i - x j))).re =
      (∑ i ∈ pts, ∑ j ∈ pts, c i * starRingEnd ℂ (c j) *
        ∑ u ∈ range M, ∑ v ∈ range M, ee (((u : ℝ) - v) * (x i - x j))).re by
    simp only [← Complex.re_sum]
    congr 1
    simp only [Finset.mul_sum]
    calc _ = ∑ u ∈ range M, ∑ i ∈ pts, ∑ j ∈ pts, ∑ v ∈ range M,
          c i * starRingEnd ℂ (c j) * ee (((u : ℝ) - v) * (x i - x j)) := by
          apply Finset.sum_congr rfl; intro u _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro i _
          rw [Finset.sum_comm]
      _ = ∑ i ∈ pts, ∑ u ∈ range M, ∑ j ∈ pts, ∑ v ∈ range M,
          c i * starRingEnd ℂ (c j) * ee (((u : ℝ) - v) * (x i - x j)) := Finset.sum_comm
      _ = _ := by
          apply Finset.sum_congr rfl; intro i _
          exact Finset.sum_comm]
  simp only [sum_uv_ee]
  rw [Complex.re_sum]
  apply Finset.sum_le_sum; intro i _
  rw [Complex.re_sum]
  apply Finset.sum_le_sum; intro j _
  calc (c i * starRingEnd ℂ (c j) * ((‖dirK M (x i - x j)‖ ^ 2 : ℝ) : ℂ)).re
      ≤ ‖c i * starRingEnd ℂ (c j) * ((‖dirK M (x i - x j)‖ ^ 2 : ℝ) : ℂ)‖ := Complex.re_le_norm _
    _ = _ := by
        rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by positivity)]

/-- Averaging over the `M²` pairs dominates the first `N` frequencies. -/
theorem sum_lt_N_le (N M : ℕ) (hNM : N < M) (F : ℝ → ℝ) (hF : ∀ t, 0 ≤ F t) :
    (M - N : ℝ) * ∑ n ∈ range N, F n ≤ ∑ u ∈ range M, ∑ v ∈ range M, F ((u : ℝ) - v) := by
  have hcast : ((M - N : ℕ) : ℝ) = (M : ℝ) - N := by push_cast [hNM.le]; ring
  rw [← hcast, ← Finset.card_range (M - N), ← nsmul_eq_mul, ← Finset.sum_const,
    ← Finset.sum_product']
  rw [← Finset.sum_product']
  have hinj : Set.InjOn (fun p : ℕ × ℕ => (p.2 + p.1, p.1)) ↑(range (M - N) ×ˢ range N) := by
    intro p _ q _ h
    simp only [Prod.mk.injEq] at h
    ext <;> omega
  calc ∑ p ∈ range (M - N) ×ˢ range N, F (p.2 : ℝ)
      = ∑ p ∈ (range (M - N) ×ˢ range N).image (fun p : ℕ × ℕ => (p.2 + p.1, p.1)),
          F ((p.1 : ℝ) - p.2) := by
        rw [Finset.sum_image hinj]
        apply Finset.sum_congr rfl; intro p _; congr 1; push_cast; ring
    _ ≤ ∑ p ∈ range M ×ˢ range M, F ((p.1 : ℝ) - p.2) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro q hq
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hq
          rw [Finset.mem_product, mem_range, mem_range] at hp ⊢
          constructor <;> omega
        · intro _ _ _; exact hF _

/-- **Large sieve inequality** for `δ`-spaced points modulo 1 (constant `4N + 3/δ + 2`). -/
theorem large_sieve {ι : Type*} (pts : Finset ι) (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ i ∈ pts, ∀ j ∈ pts, i ≠ j → δ ≤ distZ (x i - x j)) (N : ℕ) (a : ℕ → ℂ) :
    ∑ i ∈ pts, ‖∑ n ∈ range N, a n * ee (n * x i)‖ ^ 2
      ≤ (4 * N + 3 / δ + 2) * ∑ n ∈ range N, ‖a n‖ ^ 2 := by
  classical
  set S : ι → ℂ := fun i => ∑ n ∈ range N, a n * ee (n * x i) with hS
  set c : ι → ℂ := fun i => starRingEnd ℂ (S i) with hc
  set Q : ℝ := ∑ i ∈ pts, ‖S i‖ ^ 2 with hQ
  set A : ℝ := ∑ n ∈ range N, ‖a n‖ ^ 2 with hA
  set T : ℝ → ℂ := fun t => ∑ i ∈ pts, c i * ee (t * x i) with hT
  have hQ0 : 0 ≤ Q := by positivity
  have hA0 : 0 ≤ A := by positivity
  -- duality
  have hdual : (Q : ℂ) = ∑ n ∈ range N, a n * T n := by
    have h1 : (Q : ℂ) = ∑ i ∈ pts, c i * S i := by
      rw [hQ]; push_cast
      apply Finset.sum_congr rfl; intro i _
      rw [hc, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
    rw [h1]
    simp only [hS, hT, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro n _
    apply Finset.sum_congr rfl; intro i _
    ring
  have hQle : Q ≤ Real.sqrt A * Real.sqrt (∑ n ∈ range N, ‖T n‖ ^ 2) := by
    have : Q = ‖(Q : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hQ0]
    rw [this, hdual]
    calc ‖∑ n ∈ range N, a n * T n‖ ≤ ∑ n ∈ range N, ‖a n‖ * ‖T n‖ := by
          refine (norm_sum_le _ _).trans ?_
          apply le_of_eq; apply Finset.sum_congr rfl; intro n _; rw [norm_mul]
      _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  -- the kernel bound
  set M : ℕ := 2 * N + ⌈1 / δ⌉₊ + 1 with hM
  have hNM : N < M := by omega
  set R : ℝ := (M : ℝ) ^ 2 + 1 / δ ^ 2 with hR
  have hTsum : ((M : ℝ) - N) * ∑ n ∈ range N, ‖T n‖ ^ 2 ≤ R * Q := by
    have h1 := sum_lt_N_le N M hNM (fun t => ‖T t‖ ^ 2) (fun t => by positivity)
    have h2 := sum_uv_norm_sq_le pts c x M
    refine h1.trans (h2.trans ?_)
    -- Schur test
    have hrow : ∀ i ∈ pts, ∑ j ∈ pts, ‖dirK M (x i - x j)‖ ^ 2 ≤ R :=
      fun i hi => row_sum_le pts x δ hδ hsep M i hi
    have hcol : ∀ j ∈ pts, ∑ i ∈ pts, ‖dirK M (x i - x j)‖ ^ 2 ≤ R := by
      intro j hj
      calc ∑ i ∈ pts, ‖dirK M (x i - x j)‖ ^ 2 = ∑ i ∈ pts, ‖dirK M (x j - x i)‖ ^ 2 := by
            apply Finset.sum_congr rfl; intro i _
            rw [show x i - x j = -(x j - x i) by ring, norm_dirK_neg]
        _ ≤ R := hrow j hj
    have hcn : ∀ i, ‖c i‖ = ‖S i‖ := fun i => Complex.norm_conj _
    calc ∑ i ∈ pts, ∑ j ∈ pts, ‖c i‖ * ‖c j‖ * ‖dirK M (x i - x j)‖ ^ 2
        ≤ ∑ i ∈ pts, ∑ j ∈ pts, ((‖c i‖ ^ 2 + ‖c j‖ ^ 2) / 2) * ‖dirK M (x i - x j)‖ ^ 2 := by
          gcongr with i hi j hj
          nlinarith [sq_nonneg (‖c i‖ - ‖c j‖)]
      _ = (1 / 2) * ∑ i ∈ pts, ‖c i‖ ^ 2 * ∑ j ∈ pts, ‖dirK M (x i - x j)‖ ^ 2 +
            (1 / 2) * ∑ j ∈ pts, ‖c j‖ ^ 2 * ∑ i ∈ pts, ‖dirK M (x i - x j)‖ ^ 2 := by
          have e1 : ∑ i ∈ pts, ∑ j ∈ pts, (‖c i‖ ^ 2 / 2) * ‖dirK M (x i - x j)‖ ^ 2 =
              (1 / 2) * ∑ i ∈ pts, ‖c i‖ ^ 2 * ∑ j ∈ pts, ‖dirK M (x i - x j)‖ ^ 2 := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
            rw [Finset.mul_sum, Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
          have e2 : ∑ i ∈ pts, ∑ j ∈ pts, (‖c j‖ ^ 2 / 2) * ‖dirK M (x i - x j)‖ ^ 2 =
              (1 / 2) * ∑ j ∈ pts, ‖c j‖ ^ 2 * ∑ i ∈ pts, ‖dirK M (x i - x j)‖ ^ 2 := by
            rw [Finset.sum_comm, Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _
            rw [Finset.mul_sum, Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
          rw [← e1, ← e2, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro i _
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro j _
          ring
      _ ≤ (1 / 2) * ∑ i ∈ pts, ‖c i‖ ^ 2 * R + (1 / 2) * ∑ j ∈ pts, ‖c j‖ ^ 2 * R := by
          gcongr with i hi j hj
          · exact hrow i hi
          · exact hcol j hj
      _ = R * Q := by
          simp only [hcn]
          rw [hQ, ← Finset.sum_mul]
          ring
  have hL : (0 : ℝ) < (M : ℝ) - N := by
    have : (N : ℝ) < M := by exact_mod_cast hNM
    linarith
  have hT2 : ∑ n ∈ range N, ‖T n‖ ^ 2 ≤ R * Q / ((M : ℝ) - N) := by
    rw [le_div_iff₀ hL]; linarith
  have hfinal : Q ≤ A * (R / ((M : ℝ) - N)) := by
    rcases eq_or_lt_of_le hQ0 with h | h
    · rw [← h]; positivity
    · have hsq : Q ^ 2 ≤ A * (R * Q / ((M : ℝ) - N)) := by
        calc Q ^ 2 ≤ (Real.sqrt A * Real.sqrt (∑ n ∈ range N, ‖T n‖ ^ 2)) ^ 2 :=
              pow_le_pow_left₀ hQ0 hQle 2
          _ = A * ∑ n ∈ range N, ‖T n‖ ^ 2 := by
              rw [mul_pow, Real.sq_sqrt hA0, Real.sq_sqrt (by positivity)]
          _ ≤ A * (R * Q / ((M : ℝ) - N)) := mul_le_mul_of_nonneg_left hT2 hA0
      have : Q * Q ≤ (A * (R / ((M : ℝ) - N))) * Q := by
        calc Q * Q = Q ^ 2 := by ring
          _ ≤ _ := hsq
          _ = _ := by ring
      exact le_of_mul_le_mul_right this h
  have hK : R / ((M : ℝ) - N) ≤ 4 * N + 3 / δ + 2 := by
    have hc1 : 1 / δ ≤ (⌈1 / δ⌉₊ : ℝ) := Nat.le_ceil _
    have hc2 : (⌈1 / δ⌉₊ : ℝ) < 1 / δ + 1 := Nat.ceil_lt_add_one (by positivity)
    have hMN : (M : ℝ) - N = N + ⌈1 / δ⌉₊ + 1 := by rw [hM]; push_cast; ring
    have hMv : (M : ℝ) = 2 * N + ⌈1 / δ⌉₊ + 1 := by rw [hM]; push_cast; ring
    rw [div_le_iff₀ hL, hMN, hR, hMv]
    set C : ℝ := (⌈1 / δ⌉₊ : ℝ)
    set d : ℝ := 1 / δ with hd
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hd0 : 0 < d := by positivity
    have hdd : 1 / δ ^ 2 = d * d := by rw [hd]; field_simp
    have h3d : 3 / δ = 3 * d := by rw [hd]; ring
    rw [hdd, h3d]
    set L : ℝ := (N : ℝ) + C + 1 with hLdef
    have hL0 : 0 ≤ L := by positivity
    have e : (2 * (N : ℝ) + C + 1) = N + L := by rw [hLdef]; ring
    rw [e]
    have h1 : (N : ℝ) * N ≤ N * L := mul_le_mul_of_nonneg_left (by rw [hLdef]; linarith) hN0
    have h2 : L * L ≤ L * (N + d + 2) := mul_le_mul_of_nonneg_left (by rw [hLdef]; linarith) hL0
    have h3 : d * d ≤ d * L := mul_le_mul_of_nonneg_left (by rw [hLdef]; linarith) hd0.le
    nlinarith
  calc ∑ i ∈ pts, ‖∑ n ∈ range N, a n * ee (n * x i)‖ ^ 2 = Q := rfl
    _ ≤ A * (R / ((M : ℝ) - N)) := hfinal
    _ ≤ A * (4 * N + 3 / δ + 2) := mul_le_mul_of_nonneg_left hK hA0
    _ = _ := by ring




/-- **Farey spacing.** -/
theorem farey_spacing (Q : ℕ) (_hQ : 1 ≤ Q) (β : ℝ) (i j : ℕ × ℕ)
    (hi : i.1 ∈ Icc Q (2 * Q) ∧ i.2 ∈ redRes i.1) (hj : j.1 ∈ Icc Q (2 * Q) ∧ j.2 ∈ redRes j.1)
    (hij : i ≠ j) :
    1 / (4 * (Q : ℝ) ^ 2) ≤ distZ (((i.2 : ℝ) / i.1 + β) - ((j.2 : ℝ) / j.1 + β)) := by
  obtain ⟨q, h⟩ := i
  obtain ⟨q', h'⟩ := j
  simp only at hi hj ⊢
  obtain ⟨hq, hh⟩ := hi
  obtain ⟨hq', hh'⟩ := hj
  rw [mem_Icc] at hq hq'
  simp only [redRes, mem_filter, mem_range] at hh hh'
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq0' : (0 : ℝ) < q' := by exact_mod_cast (by omega : 0 < q')
  set t := (h : ℝ) / q - h' / q' with ht
  rw [show (h : ℝ) / q + β - (h' / q' + β) = t by rw [ht]; ring]
  have hqq : (q : ℝ) * q' ≤ 4 * (Q : ℝ) ^ 2 := by
    have : q * q' ≤ (2 * Q) * (2 * Q) := Nat.mul_le_mul hq.2 hq'.2
    have : (q : ℝ) * q' ≤ (2 * Q) * (2 * Q) := by exact_mod_cast this
    nlinarith
  suffices hs : 1 / ((q : ℝ) * q') ≤ distZ t by
    calc 1 / (4 * (Q : ℝ) ^ 2) ≤ 1 / ((q : ℝ) * q') :=
          one_div_le_one_div_of_le (by positivity) hqq
      _ ≤ distZ t := hs
  by_contra hlt
  push Not at hlt
  set r := round t
  have hk : t * (q * q') - r * (q * q') = (((h * q' : ℕ) : ℤ) - ((h' * q : ℕ) : ℤ) - r * (q * q') : ℤ) := by
    rw [ht]; push_cast; field_simp
  have habs : |t * (q * q') - r * (q * q')| < 1 := by
    rw [show t * (q * q') - r * (q * q') = (t - r) * (q * q') by ring, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < q * q')]
    have : distZ t = |t - r| := rfl
    rw [← this]
    calc distZ t * (q * q') < 1 / (q * q') * (q * q') :=
          mul_lt_mul_of_pos_right hlt (by positivity)
      _ = 1 := by field_simp
  rw [hk] at habs
  have hz : ((h * q' : ℕ) : ℤ) - ((h' * q : ℕ) : ℤ) - r * (q * q') = 0 := by
    have : |(((h * q' : ℕ) : ℤ) - ((h' * q : ℕ) : ℤ) - r * (q * q') : ℤ)| < 1 := by exact_mod_cast habs
    exact Int.abs_lt_one_iff.1 this |> fun h => by omega
  -- t = r is an integer with |t| < 1, so r = 0
  have htr : t = r := by
    have : t * (q * q') - r * (q * q') = 0 := by rw [hk]; exact_mod_cast hz
    have hne : (q : ℝ) * q' ≠ 0 := by positivity
    have : (t - r) * (q * q') = 0 := by linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · linarith
    · exact absurd h1 hne
  have htabs : |t| < 1 := by
    rw [ht, abs_lt]
    have a1 : (h : ℝ) / q < 1 := by rw [div_lt_one hq0]; exact_mod_cast hh.1
    have a2 : (h' : ℝ) / q' < 1 := by rw [div_lt_one hq0']; exact_mod_cast hh'.1
    have a3 : (0 : ℝ) ≤ (h : ℝ) / q := by positivity
    have a4 : (0 : ℝ) ≤ (h' : ℝ) / q' := by positivity
    constructor <;> linarith
  have hr0 : r = 0 := by
    rw [htr] at htabs
    have : |(r : ℤ)| < 1 := by exact_mod_cast htabs
    exact Int.abs_lt_one_iff.1 this
  rw [hr0] at hz
  simp only [zero_mul, sub_zero, sub_eq_zero] at hz
  have hcross : h * q' = h' * q := by exact_mod_cast hz
  -- coprimality forces q = q' and h = h'
  have hdq : q ∣ q' := by
    have : q ∣ h * q' := ⟨h', by rw [hcross]; ring⟩
    exact (Nat.Coprime.symm hh.2).dvd_of_dvd_mul_left this
  have hdq' : q' ∣ q := by
    have : q' ∣ h' * q := ⟨h, by rw [← hcross]; ring⟩
    exact (Nat.Coprime.symm hh'.2).dvd_of_dvd_mul_left this
  have hqe : q = q' := Nat.dvd_antisymm hdq hdq'
  subst hqe
  have hhe : h = h' := Nat.eq_of_mul_eq_mul_right (by omega) hcross
  exact hij (by rw [hhe])

/-- **Twist.** -/
theorem twist_bij (b m q : ℕ) (hq : Nat.Coprime q b) :
    (redRes q).image (fun h => b ^ m * h % q) = redRes q := by
  rcases Nat.eq_zero_or_pos q with h0 | hpos
  · subst h0; simp [redRes]
  have hsub : (redRes q).image (fun h => b ^ m * h % q) ⊆ redRes q := by
    intro k hk
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hk
    simp only [redRes, mem_filter, mem_range] at hh ⊢
    refine ⟨Nat.mod_lt _ hpos, ?_⟩
    have hx : Nat.Coprime (b ^ m * h) q := Nat.Coprime.mul_left (Nat.Coprime.pow_left m (Nat.Coprime.symm hq)) hh.2
    rw [Nat.Coprime, ← Nat.gcd_rec q, Nat.gcd_comm]
    exact hx
  apply Finset.eq_of_subset_of_card_le hsub
  rw [Finset.card_image_of_injOn]
  intro h hh h' hh' heq
  simp only [redRes, coe_filter, mem_range] at hh hh'
  have hmod : b ^ m * h ≡ b ^ m * h' [MOD q] := heq
  have hc : Nat.Coprime (b ^ m) q := Nat.Coprime.pow_left m (Nat.Coprime.symm hq)
  have := Nat.ModEq.cancel_left_of_coprime (by rw [Nat.gcd_comm]; exact hc) hmod
  exact Nat.ModEq.eq_of_lt_of_lt this hh.1 hh'.1

end Palprimes
