import Palprimes.Digits.LemmaThree

/-! # M2a. Collision probabilities and the residue identity

* `collision_prob`: `Pr(Y = Y') = (g/b)^{|K1|} b^{−|K2|}`, `g/b = (2b²+1)/(3b³)`
  (from `sum_cK_eq_zero`).
* `fourier_yVal`: `|E e(Yα)|² = Π_{K1}ψ² Π_{K2}ψ` (independence of digits).
* `sum_sq_fourier_le_collision`: `Σ_{h mod q} |f̂(h/q+β)|² ≤ q Σ_{z ≡ z' (q)} f(z) f(z')`
  (orthogonality of additive characters mod q; equality at β = 0). Used by M6, M7 and M11.
* `prob_eq_le_l2`: `Pr(W = w) ≤ ‖f‖²` for `W = Y − Y'` (Cauchy–Schwarz). Used by M11.
Effort 300–500 lines. -/

open Finset Real

namespace Palprimes

/-! ## Exponentials and orthogonality -/

theorem ee_add (a c : ℝ) : ee (a + c) = ee a * ee c := by
  unfold ee
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem norm_ee (t : ℝ) : ‖ee t‖ = 1 := by
  unfold ee
  rw [show (2 * π * Complex.I * t : ℂ) = ((2 * π * t : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem conj_ee (t : ℝ) : starRingEnd ℂ (ee t) = ee (-t) := by
  unfold ee
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  push_cast
  ring

theorem re_ee_le_one (t : ℝ) : (ee t).re ≤ 1 :=
  (Complex.re_le_norm _).trans (norm_ee t).le

theorem ee_int_div (k : ℤ) (q : ℕ) :
    ee ((k : ℝ) / q) = Complex.exp (2 * π * Complex.I / q) ^ k := by
  unfold ee
  rw [← Complex.exp_intCast_mul]
  congr 1
  push_cast
  ring

/-- Orthogonality: `Σ_{h<q} e(kh/q) = q·[q ∣ k]`. -/
theorem sum_ee_root (q : ℕ) (hq : 0 < q) (k : ℤ) :
    ∑ h ∈ range q, ee ((k : ℝ) * h / q) = if (q : ℤ) ∣ k then (q : ℂ) else 0 := by
  set ζ := Complex.exp (2 * π * Complex.I / q) with hζdef
  have hζ : IsPrimitiveRoot ζ q := Complex.isPrimitiveRoot_exp q hq.ne'
  have hterm : ∀ h : ℕ, ee ((k : ℝ) * h / q) = (ζ ^ k) ^ h := by
    intro h
    rw [← zpow_natCast, ← zpow_mul,
      show ((k : ℝ) * h / q) = ((k * h : ℤ) : ℝ) / q by push_cast; ring]
    exact ee_int_div _ _
  simp_rw [hterm]
  split_ifs with hdvd
  · have : ζ ^ k = 1 := (hζ.zpow_eq_one_iff_dvd k).2 hdvd
    simp [this]
  · have hne : ζ ^ k ≠ 1 := fun h => hdvd ((hζ.zpow_eq_one_iff_dvd k).1 h)
    rw [geom_sum_eq hne]
    have : (ζ ^ k) ^ q = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ.pow_eq_one, one_zpow]
    rw [this, sub_self, zero_div]

/-- `‖Σ f(z) e(zx)‖² = Σ_{z,z'} f(z) f(z') Re e((z−z')x)` for real weights. -/
theorem norm_sq_sum_ee (S : Finset ℤ) (f : ℤ → ℝ) (x : ℝ) :
    ‖∑ z ∈ S, (f z : ℂ) * ee (z * x)‖ ^ 2 =
      ∑ z ∈ S, ∑ z' ∈ S, f z * f z' * (ee (((z - z' : ℤ) : ℝ) * x)).re := by
  set F := ∑ z ∈ S, (f z : ℂ) * ee (z * x)
  have h1 : ‖F‖ ^ 2 = (F * starRingEnd ℂ F).re := by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [h1, map_sum, Finset.sum_mul_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro z' _
  rw [map_mul, Complex.conj_ofReal, conj_ee,
    show (f z : ℂ) * ee (z * x) * ((f z' : ℂ) * ee (-(z' * x))) =
      ((f z * f z' : ℝ) : ℂ) * (ee (z * x) * ee (-(z' * x))) by push_cast; ring,
    ← ee_add, Complex.re_ofReal_mul]
  congr 3
  push_cast
  ring

/-- **Residue identity** (inequality form, valid for every real shift `β`). -/
theorem sum_sq_fourier_le_collision (q : ℕ) (hq : 0 < q) (S : Finset ℤ) (f : ℤ → ℝ)
    (hf : ∀ z, 0 ≤ f z) (β : ℝ) :
    ∑ h ∈ range q, ‖∑ z ∈ S, (f z : ℂ) * ee (z * ((h : ℝ) / q + β))‖ ^ 2
      ≤ q * ∑ z ∈ S, ∑ z' ∈ S, if (q : ℤ) ∣ z - z' then f z * f z' else 0 := by
  simp_rw [norm_sq_sum_ee]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z _
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z' _
  rw [← Finset.mul_sum]
  set k : ℤ := z - z'
  have hsum : ∑ h ∈ range q, (ee ((k : ℝ) * ((h : ℝ) / q + β))).re =
      (ee (k * β) * (if (q : ℤ) ∣ k then (q : ℂ) else 0)).re := by
    rw [← sum_ee_root q hq k, Finset.mul_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [← ee_add]
    congr 3
    ring
  rw [hsum]
  have hff : 0 ≤ f z * f z' := mul_nonneg (hf z) (hf z')
  split_ifs with hd
  · have : (ee (k * β) * (q : ℂ)).re ≤ q := by
      rw [show (q : ℂ) = ((q : ℝ) : ℂ) by push_cast; rfl, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]
      nlinarith [re_ee_le_one (k * β), (Nat.cast_nonneg q : (0 : ℝ) ≤ q)]
    nlinarith
  · simp

/-- **Point masses of a difference** are bounded by the collision probability. -/
theorem prob_eq_le_l2 (S : Finset ℤ) (f : ℤ → ℝ) (_hf : ∀ z, 0 ≤ f z) (w : ℤ) :
    ∑ z ∈ S, ∑ z' ∈ S, (if z - z' = w then f z * f z' else 0) ≤ ∑ z ∈ S, f z ^ 2 := by
  classical
  set g : ℤ → ℝ := fun z => if z - w ∈ S then f (z - w) ^ 2 else 0 with hg
  have h1 : ∀ z ∈ S, ∑ z' ∈ S, (if z - z' = w then f z * f z' else 0) ≤ (f z ^ 2 + g z) / 2 := by
    intro z _
    have hc : ∀ z', (z - z' = w) = (z - w = z') := fun z' => propext (by omega)
    simp only [hc]
    rw [Finset.sum_ite_eq]
    simp only [hg]
    split_ifs with h
    · nlinarith [two_mul_le_add_sq (f z) (f (z - w))]
    · nlinarith [sq_nonneg (f z)]
  have h2 : ∑ z ∈ S, g z ≤ ∑ z ∈ S, f z ^ 2 := by
    have : ∑ z ∈ S, g z = ∑ z ∈ (S.filter (fun z => z - w ∈ S)).image (· - w), f z ^ 2 := by
      rw [Finset.sum_image (fun a _ b _ h => by simpa using h), Finset.sum_filter]
    rw [this]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro y hy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy
      exact (Finset.mem_filter.1 hz).2
    · intro i _ _
      exact sq_nonneg _
  calc ∑ z ∈ S, ∑ z' ∈ S, (if z - z' = w then f z * f z' else 0)
      ≤ ∑ z ∈ S, (f z ^ 2 + g z) / 2 := Finset.sum_le_sum h1
    _ = (∑ z ∈ S, f z ^ 2 + ∑ z ∈ S, g z) / 2 := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
    _ ≤ ∑ z ∈ S, f z ^ 2 := by linarith


/-! ## Counting digit sums -/

/-- `2 Σ_{a<c} (a+1) = c(c+1)`. -/
theorem two_mul_sum_succ (c : ℕ) : 2 * ∑ a ∈ range c, (a + 1) = c * (c + 1) := by
  induction c with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, mul_add, ih]; ring

/-- `V(c) = #{(a, a') ∈ [0,c)² : a + a' < c}`, `2V(c) = c(c+1)`. -/
theorem two_mul_V (c : ℕ) :
    2 * ∑ a ∈ range c, ∑ a' ∈ range c, (if a + a' < c then 1 else 0) = c * (c + 1) := by
  have h : ∀ a ∈ range c, ∑ a' ∈ range c, (if a + a' < c then 1 else 0) = c - a := by
    intro a ha
    rw [Finset.sum_boole]
    have : (range c).filter (fun a' => a + a' < c) = range (c - a) := by
      ext a'; simp only [mem_filter, mem_range]; omega
    rw [this, card_range]
    rfl
  rw [Finset.sum_congr rfl h, ← two_mul_sum_succ c, ← Finset.sum_range_reflect]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  rw [mem_range] at ha
  omega

/-- `6 Σ_{c<b} V(c) + b = b³`. -/
theorem six_mul_sumV (b : ℕ) :
    6 * (∑ c ∈ range b, ∑ a ∈ range c, ∑ a' ∈ range c, (if a + a' < c then 1 else 0)) + b
      = b ^ 3 := by
  induction b with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h2 := two_mul_V n
    nlinarith [ih, h2]

/-- Triples with `a + a' < c`: `6 T(b) + b = b³`. -/
theorem six_mul_T (b : ℕ) :
    6 * (∑ c ∈ range b, ∑ a ∈ range b, ∑ a' ∈ range b, (if a + a' < c then 1 else 0)) + b
      = b ^ 3 := by
  have hV : ∀ c ∈ range b, ∑ a ∈ range b, ∑ a' ∈ range b, (if a + a' < c then 1 else 0) =
      ∑ a ∈ range c, ∑ a' ∈ range c, (if a + a' < c then 1 else 0) := by
    intro c hc
    rw [mem_range] at hc
    symm
    rw [Finset.sum_subset (range_subset_range.2 hc.le)]
    · apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_subset (range_subset_range.2 hc.le)]
      intro a' _ ha'
      rw [mem_range] at ha'
      rw [ite_eq_right (by omega)]
    · intro a _ ha
      rw [mem_range] at ha
      apply Finset.sum_eq_zero
      intro a' _
      rw [ite_eq_right (by omega)]
  rw [Finset.sum_congr rfl hV]
  exact six_mul_sumV b

/-- **Collision count of two-digit sums**: `3 #{a + a' = c + c'} = b(2b² + 1)`. -/
theorem three_mul_N (b : ℕ) :
    3 * (∑ a ∈ range b, ∑ a' ∈ range b, ∑ c ∈ range b, ∑ c' ∈ range b,
      (if a + a' = c + c' then 1 else 0)) = b * (2 * b ^ 2 + 1) := by
  set N := ∑ a ∈ range b, ∑ a' ∈ range b, ∑ c ∈ range b, ∑ c' ∈ range b,
      (if a + a' = c + c' then 1 else 0) with hN
  set T := ∑ c ∈ range b, ∑ a ∈ range b, ∑ a' ∈ range b, (if a + a' < c then 1 else 0) with hT
  have hinner : ∀ a a' c : ℕ, ∑ c' ∈ range b, (if a + a' = c + c' then 1 else 0) =
      if c ≤ a + a' ∧ a + a' < c + b then 1 else 0 := by
    intro a a' c
    rw [Finset.sum_boole]
    by_cases h : c ≤ a + a' ∧ a + a' < c + b
    · have : (range b).filter (fun c' => a + a' = c + c') = {a + a' - c} := by
        ext c'; simp only [mem_filter, mem_range, mem_singleton]; omega
      rw [this, ite_eq_left h]; simp
    · have : (range b).filter (fun c' => a + a' = c + c') = ∅ := by
        ext c'; simp only [mem_filter, mem_range, notMem_empty, iff_false]; omega
      rw [this, ite_eq_right h]; simp
  have hNmid : N = ∑ a ∈ range b, ∑ a' ∈ range b, ∑ c ∈ range b,
      (if c ≤ a + a' ∧ a + a' < c + b then 1 else 0) := by
    rw [hN]; simp only [hinner]
  have hsplit : b ^ 3 = N + (∑ a ∈ range b, ∑ a' ∈ range b, ∑ c ∈ range b,
      (if a + a' < c then 1 else 0)) + (∑ a ∈ range b, ∑ a' ∈ range b, ∑ c ∈ range b,
      (if c + b ≤ a + a' then 1 else 0)) := by
    rw [hNmid, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    have : b ^ 3 = ∑ a ∈ range b, ∑ a' ∈ range b, ∑ c ∈ range b, 1 := by simp; ring
    rw [this]
    apply Finset.sum_congr rfl; intro a _
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro a' _
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro c _
    split_ifs <;> omega
  have hlt : (∑ a ∈ range b, ∑ a' ∈ range b, ∑ c ∈ range b,
      (if a + a' < c then 1 else 0)) = T := by
    rw [hT]
    calc (∑ a ∈ range b, ∑ a' ∈ range b, ∑ c ∈ range b, (if a + a' < c then 1 else 0))
        = ∑ a ∈ range b, ∑ c ∈ range b, ∑ a' ∈ range b, (if a + a' < c then 1 else 0) :=
          Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
      _ = _ := Finset.sum_comm
  have hge : (∑ a ∈ range b, ∑ a' ∈ range b, ∑ c ∈ range b,
      (if c + b ≤ a + a' then 1 else 0)) =
      (∑ a ∈ range b, ∑ a' ∈ range b, ∑ c ∈ range b, (if a + a' < c then 1 else 0)) := by
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl; intro a ha
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl; intro a' ha'
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl; intro c hc
    rw [mem_range] at ha ha' hc
    congr 1
    apply propext
    omega
  rw [hge, hlt] at hsplit
  have h6 := six_mul_T b
  rw [← hT] at h6
  nlinarith [hsplit, h6]


/-! ## Laws of digit combinations -/

/-- Quadruples of digit vectors `(d, d', e, e')`. -/
abbrev Quad (b L : ℕ) := DigVec b L × DigVec b L × DigVec b L × DigVec b L

theorem ee_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ee (∑ i ∈ s, f i) = ∏ i ∈ s, ee (f i) := by
  unfold ee
  push_cast
  rw [Finset.mul_sum, Complex.exp_sum]

theorem ee_zero : ee 0 = 1 := by simp [ee]

/-- `‖Σ_{a<b} e(a t)‖ = φ_b(t)`, summing over `Fin b`. -/
theorem norm_sum_fin_ee (b : ℕ) (t : ℝ) :
    ‖∑ a : Fin b, ee ((a : ℕ) * t)‖ = phiB b t := by
  unfold phiB
  rw [Fin.sum_univ_eq_sum_range (fun a => ee (a * t)) b]

theorem phiB_zero (b : ℕ) : phiB b 0 = b := by
  simp [phiB, ee_zero]

/-- Independent digits: the exponential sum over two digit vectors factorizes. -/
theorem sum_prod_ee {n b : ℕ} (u v : Fin n → ℝ) :
    ∑ w : (Fin n → Fin b) × (Fin n → Fin b),
        ee (∑ i, (((w.1 i : ℕ) : ℝ) * u i + ((w.2 i : ℕ) : ℝ) * v i))
      = (∏ i, ∑ a : Fin b, ee ((a : ℕ) * u i)) * ∏ i, ∑ a : Fin b, ee ((a : ℕ) * v i) := by
  rw [Fintype.sum_prod_type]
  have hsplit : ∀ d d' : Fin n → Fin b,
      ee (∑ i, (((d i : ℕ) : ℝ) * u i + ((d' i : ℕ) : ℝ) * v i)) =
        (∏ i, ee ((d i : ℕ) * u i)) * ∏ i, ee ((d' i : ℕ) * v i) := by
    intro d d'
    rw [ee_sum, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => ee_add _ _)
  simp only [hsplit]
  rw [← Finset.sum_mul_sum]
  simp only [Finset.prod_univ_sum, Fintype.piFinset_univ]

theorem extDig_fin {b L : ℕ} (d : DigVec b L) (i : Fin (L + 1)) : extDig d i = (d i : ℕ) := by
  simp [extDig, i.isLt]

theorem sum_K_eq_fin (L : ℕ) (K : Finset ℕ) (hK : K ⊆ range (L + 1)) {M : Type*}
    [AddCommMonoid M] (F : ℕ → M) :
    ∑ k ∈ K, F k = ∑ i : Fin (L + 1), if (i : ℕ) ∈ K then F i else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if k ∈ K then F k else 0) (L + 1),
    Finset.sum_ite_mem, inter_eq_right.2 hK]

theorem prod_K_eq_fin (L : ℕ) (K : Finset ℕ) (hK : K ⊆ range (L + 1)) {M : Type*}
    [CommMonoid M] (F : ℕ → M) :
    ∏ k ∈ K, F k = ∏ i : Fin (L + 1), if (i : ℕ) ∈ K then F i else 1 := by
  rw [Fin.prod_univ_eq_prod_range (fun k => if k ∈ K then F k else 1) (L + 1),
    Finset.prod_ite_mem, inter_eq_right.2 hK]

/-- `Y α` as a sum over coordinates. -/
theorem yVal_mul (b L : ℕ) (K1 K2 : Finset ℕ) (hK1 : K1 ⊆ range (L + 1))
    (hK2 : K2 ⊆ range (L + 1)) (d d' : DigVec b L) (α : ℝ) :
    (yVal b L K1 K2 (extDig d) (extDig d') : ℝ) * α =
      ∑ i : Fin (L + 1), (((d i : ℕ) : ℝ) *
          (((if (i : ℕ) ∈ K1 then 1 else 0) + (if (i : ℕ) ∈ K2 then 1 else 0)) * (cK b L i * α)) +
        ((d' i : ℕ) : ℝ) * ((if (i : ℕ) ∈ K1 then 1 else 0) * (cK b L i * α))) := by
  unfold yVal
  push_cast
  rw [sum_K_eq_fin L K1 hK1, sum_K_eq_fin L K2 hK2, ← Finset.sum_add_distrib, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [extDig_fin]
  split_ifs <;> ring

/-- **Fourier transform of the law of `Y`** factorizes into `ψ`'s. -/
theorem fourier_yVal (b L : ℕ) (hb : 2 ≤ b) (K1 K2 : Finset ℕ)
    (hK1 : K1 ⊆ range (L + 1)) (hK2 : K2 ⊆ range (L + 1)) (hdisj : Disjoint K1 K2) (α : ℝ) :
    ‖(∑ w : DigVec b L × DigVec b L,
        ee (yVal b L K1 K2 (extDig w.1) (extDig w.2) * α)) / (b : ℂ) ^ (2 * (L + 1))‖ ^ 2
      = piK b L K1 α ^ 2 * piK b L K2 α := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  set u : Fin (L + 1) → ℝ := fun i =>
    ((if (i : ℕ) ∈ K1 then 1 else 0) + (if (i : ℕ) ∈ K2 then 1 else 0)) * (cK b L i * α)
  set v : Fin (L + 1) → ℝ := fun i => (if (i : ℕ) ∈ K1 then 1 else 0) * (cK b L i * α)
  have hY : ∀ w : DigVec b L × DigVec b L,
      ee (yVal b L K1 K2 (extDig w.1) (extDig w.2) * α) =
        ee (∑ i, (((w.1 i : ℕ) : ℝ) * u i + ((w.2 i : ℕ) : ℝ) * v i)) := by
    intro w
    rw [yVal_mul b L K1 K2 hK1 hK2]
  simp only [hY]
  rw [sum_prod_ee u v, norm_div, norm_mul, norm_prod, norm_prod, norm_pow, Complex.norm_natCast]
  simp only [norm_sum_fin_ee]
  -- coordinatewise values
  have hu : ∀ i : Fin (L + 1), phiB b (u i) / b =
      if (i : ℕ) ∈ K1 ∨ (i : ℕ) ∈ K2 then phiB b (cK b L i * α) / b else 1 := by
    intro i
    simp only [u]
    by_cases h1 : (i : ℕ) ∈ K1
    · have h2 : (i : ℕ) ∉ K2 := Finset.disjoint_left.1 hdisj h1
      simp [h1, h2]
    · by_cases h2 : (i : ℕ) ∈ K2
      · simp [h1, h2]
      · simp [h1, h2, phiB_zero, hb0.ne']
  have hv : ∀ i : Fin (L + 1), phiB b (v i) / b =
      if (i : ℕ) ∈ K1 then phiB b (cK b L i * α) / b else 1 := by
    intro i
    simp only [v]
    by_cases h1 : (i : ℕ) ∈ K1
    · simp [h1]
    · simp [h1, phiB_zero, hb0.ne']
  have hpow : (b : ℝ) ^ (2 * (L + 1)) =
      (∏ _i : Fin (L + 1), (b : ℝ)) * ∏ _i : Fin (L + 1), (b : ℝ) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_add]
    ring_nf
  rw [hpow, mul_div_mul_comm, ← Finset.prod_div_distrib, ← Finset.prod_div_distrib]
  simp only [hu, hv]
  unfold piK psiB
  rw [prod_K_eq_fin L K1 hK1, prod_K_eq_fin L K2 hK2, mul_pow, ← Finset.prod_pow, ← Finset.prod_pow,
    ← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases h1 : (i : ℕ) ∈ K1
  · have h2 : (i : ℕ) ∉ K2 := Finset.disjoint_left.1 hdisj h1
    simp [h1, h2]
    ring
  · by_cases h2 : (i : ℕ) ∈ K2
    · simp [h1, h2]
    · simp [h1, h2]

theorem extDig_lt {b L : ℕ} (hb : 0 < b) (d : DigVec b L) (k : ℕ) : extDig d k < b := by
  unfold extDig
  split_ifs
  · exact (d _).isLt
  · exact hb

/-- The coordinatewise condition for `Y(d, d') = Y(e, e')`. -/
def coordOK {b : ℕ} (K1 K2 : Finset ℕ) (k : ℕ) (t : Fin b × Fin b × Fin b × Fin b) : Prop :=
  (k ∈ K1 → (t.1 : ℕ) + t.2.1 = t.2.2.1 + t.2.2.2) ∧ (k ∈ K2 → (t.1 : ℕ) = t.2.2.1)

instance {b : ℕ} (K1 K2 : Finset ℕ) (k : ℕ) : DecidablePred (coordOK (b := b) K1 K2 k) :=
  fun t => by unfold coordOK; infer_instance

theorem yVal_int (b L : ℕ) (K1 K2 : Finset ℕ) (hK1 : K1 ⊆ range (L + 1))
    (hK2 : K2 ⊆ range (L + 1)) (D D' : ℕ → ℕ) :
    (yVal b L K1 K2 D D' : ℤ) = ∑ k ∈ range (L + 1),
      ((if k ∈ K1 then ((D k + D' k : ℕ) : ℤ) else 0) + (if k ∈ K2 then (D k : ℤ) else 0)) *
        (cK b L k : ℤ) := by
  unfold yVal
  push_cast
  have e1 : ∑ k ∈ K1, ((D k : ℤ) + D' k) * (cK b L k : ℤ) = ∑ k ∈ range (L + 1),
      if k ∈ K1 then ((D k : ℤ) + D' k) * (cK b L k : ℤ) else 0 := by
    rw [Finset.sum_ite_mem, inter_eq_right.2 hK1]
  have e2 : ∑ k ∈ K2, (D k : ℤ) * (cK b L k : ℤ) = ∑ k ∈ range (L + 1),
      if k ∈ K2 then (D k : ℤ) * (cK b L k : ℤ) else 0 := by
    rw [Finset.sum_ite_mem, inter_eq_right.2 hK2]
  rw [e1, e2, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> ring

/-- **Lemma 3 consequence:** `Y(d, d') = Y(e, e')` iff digit sums agree on `K1` and digits
agree on `K2`. -/
theorem yVal_eq_iff (b L : ℕ) (hb : 2 ≤ b) (K1 K2 : Finset ℕ) (hK1 : K1 ⊆ range (L + 1))
    (hK2 : K2 ⊆ range (L + 1)) (hdisj : Disjoint K1 K2) (d d' e e' : DigVec b L) :
    yVal b L K1 K2 (extDig d) (extDig d') = yVal b L K1 K2 (extDig e) (extDig e') ↔
      ∀ i : Fin (L + 1), coordOK K1 K2 i (d i, d' i, e i, e' i) := by
  constructor
  · intro h
    set s : ℕ → ℤ := fun k =>
      (if k ∈ K1 then ((extDig d k + extDig d' k : ℕ) : ℤ) - ((extDig e k + extDig e' k : ℕ) : ℤ)
        else 0) + (if k ∈ K2 then (extDig d k : ℤ) - extDig e k else 0) with hs
    have hsum : ∑ k ∈ range (L + 1), s k * (cK b L k : ℤ) = 0 := by
      have h' : (yVal b L K1 K2 (extDig d) (extDig d') : ℤ) - yVal b L K1 K2 (extDig e) (extDig e')
          = 0 := by rw [h, sub_self]
      rw [yVal_int b L K1 K2 hK1 hK2, yVal_int b L K1 K2 hK1 hK2, ← Finset.sum_sub_distrib] at h'
      rw [← h']
      apply Finset.sum_congr rfl
      intro k _
      simp only [hs]
      split_ifs <;> ring
    have hb0 : 0 < b := by omega
    have hbound : ∀ k ≤ L, |s k| ≤ 2 * (b : ℤ) - 2 := by
      intro k _
      have h1 := extDig_lt hb0 d k
      have h2 := extDig_lt hb0 d' k
      have h3 := extDig_lt hb0 e k
      have h4 := extDig_lt hb0 e' k
      simp only [hs]
      by_cases hk1 : k ∈ K1
      · have hk2 : k ∉ K2 := Finset.disjoint_left.1 hdisj hk1
        rw [ite_eq_left hk1, ite_eq_right hk2, abs_le]
        push_cast
        constructor <;> omega
      · rw [ite_eq_right hk1, abs_le]
        split_ifs <;> push_cast <;> constructor <;> omega
    have hz := sum_cK_eq_zero b L hb s hbound hsum
    intro i
    have hi := hz i (by omega)
    simp only [hs, extDig_fin] at hi
    constructor
    · intro hk1
      have hk2 : (i : ℕ) ∉ K2 := Finset.disjoint_left.1 hdisj hk1
      rw [ite_eq_left hk1, ite_eq_right hk2] at hi
      push_cast at hi
      simp only
      omega
    · intro hk2
      have hk1 : (i : ℕ) ∉ K1 := fun h1 => Finset.disjoint_left.1 hdisj h1 hk2
      rw [ite_eq_right hk1, ite_eq_left hk2] at hi
      simp only
      omega
  · intro h
    unfold yVal
    congr 1
    · apply Finset.sum_congr rfl
      intro k hk
      have hkL : k < L + 1 := Finset.mem_range.1 (hK1 hk)
      have := (h ⟨k, hkL⟩).1 hk
      simp only [extDig, hkL, dite_true]
      simp only at this
      rw [this]
    · apply Finset.sum_congr rfl
      intro k hk
      have hkL : k < L + 1 := Finset.mem_range.1 (hK2 hk)
      have := (h ⟨k, hkL⟩).2 hk
      simp only [extDig, hkL, dite_true]
      simp only at this
      rw [this]

theorem count_fin_N (b : ℕ) :
    (∑ t : Fin b × Fin b × Fin b × Fin b,
        if (t.1 : ℕ) + t.2.1 = t.2.2.1 + t.2.2.2 then 1 else 0) =
      ∑ a ∈ range b, ∑ a' ∈ range b, ∑ c ∈ range b, ∑ c' ∈ range b,
        (if a + a' = c + c' then 1 else 0) := by
  simp only [Fintype.sum_prod_type]
  rw [← Fin.sum_univ_eq_sum_range (fun a => ∑ a' ∈ range b, ∑ c ∈ range b, ∑ c' ∈ range b,
    (if a + a' = c + c' then 1 else 0))]
  apply Finset.sum_congr rfl; intro a _
  rw [← Fin.sum_univ_eq_sum_range (fun a' => ∑ c ∈ range b, ∑ c' ∈ range b,
    (if (a : ℕ) + a' = c + c' then 1 else 0))]
  apply Finset.sum_congr rfl; intro a' _
  rw [← Fin.sum_univ_eq_sum_range (fun c => ∑ c' ∈ range b,
    (if (a : ℕ) + a' = c + c' then 1 else 0))]
  apply Finset.sum_congr rfl; intro c _
  rw [← Fin.sum_univ_eq_sum_range (fun c' => (if (a : ℕ) + a' = c + c' then 1 else 0))]

/-- Per-coordinate counts. -/
theorem count_coord (b : ℕ) (K1 K2 : Finset ℕ) (hdisj : Disjoint K1 K2) (k : ℕ) :
    3 * (∑ t : Fin b × Fin b × Fin b × Fin b, if coordOK K1 K2 k t then 1 else 0) =
      if k ∈ K1 then b * (2 * b ^ 2 + 1) else if k ∈ K2 then 3 * b ^ 3 else 3 * b ^ 4 := by
  by_cases hk1 : k ∈ K1
  · have hk2 : k ∉ K2 := Finset.disjoint_left.1 hdisj hk1
    rw [ite_eq_left hk1, ← three_mul_N b, ← count_fin_N b]
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    simp [coordOK, hk1, hk2]
  · by_cases hk2 : k ∈ K2
    · rw [ite_eq_right hk1, ite_eq_left hk2]
      have : ∀ t : Fin b × Fin b × Fin b × Fin b,
          (if coordOK K1 K2 k t then 1 else 0) = if t.1 = t.2.2.1 then 1 else 0 := by
        intro t
        simp [coordOK, hk1, hk2, Fin.val_inj]
      simp only [this, Fintype.sum_prod_type]
      have hc : ∀ a c : Fin b,
          (∑ _c' : Fin b, (if a = c then 1 else 0)) = if a = c then b else 0 := by
        intro a c
        split_ifs <;> simp
      simp only [hc, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      ring
    · rw [ite_eq_right hk1, ite_eq_right hk2]
      simp [coordOK, hk1, hk2]
      ring

/-- Splitting quadruples of digit vectors coordinatewise. -/
def quadEquiv (b L : ℕ) : (Fin (L + 1) → Fin b × Fin b × Fin b × Fin b) ≃ Quad b L :=
  (Equiv.arrowProdEquivProdArrow _ _ _).trans
    (Equiv.prodCongr (Equiv.refl _) ((Equiv.arrowProdEquivProdArrow _ _ _).trans
      (Equiv.prodCongr (Equiv.refl _) (Equiv.arrowProdEquivProdArrow _ _ _))))

/-- **Collision probability** of `Y` (doubled digits on `K1`, single digits on `K2`). -/
theorem collision_prob (b L : ℕ) (hb : 2 ≤ b) (K1 K2 : Finset ℕ)
    (hK1 : K1 ⊆ range (L + 1)) (hK2 : K2 ⊆ range (L + 1)) (hdisj : Disjoint K1 K2) :
    (#((univ : Finset (Quad b L)).filter (fun w =>
        yVal b L K1 K2 (extDig w.1) (extDig w.2.1) =
          yVal b L K1 K2 (extDig w.2.2.1) (extDig w.2.2.2))) : ℝ) / (b : ℝ) ^ (4 * (L + 1))
      = ((2 * (b : ℝ) ^ 2 + 1) / (3 * (b : ℝ) ^ 3)) ^ #K1 * ((b : ℝ) ^ #K2)⁻¹ := by
  classical
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  set cnt : ℕ → ℕ := fun k =>
    ∑ t : Fin b × Fin b × Fin b × Fin b, if coordOK K1 K2 k t then 1 else 0 with hcnt
  have hcard : #((univ : Finset (Quad b L)).filter (fun w =>
        yVal b L K1 K2 (extDig w.1) (extDig w.2.1) =
          yVal b L K1 K2 (extDig w.2.2.1) (extDig w.2.2.2))) = ∏ k ∈ range (L + 1), cnt k := by
    rw [Finset.card_filter, ← (quadEquiv b L).sum_comp]
    have hP : ∀ y : Fin (L + 1) → Fin b × Fin b × Fin b × Fin b,
        (if yVal b L K1 K2 (extDig (quadEquiv b L y).1) (extDig (quadEquiv b L y).2.1) =
            yVal b L K1 K2 (extDig (quadEquiv b L y).2.2.1) (extDig (quadEquiv b L y).2.2.2)
          then 1 else 0) = ∏ i : Fin (L + 1), (if coordOK K1 K2 (i : ℕ) (y i) then 1 else 0) := by
      intro y
      rw [Finset.prod_boole]
      have := yVal_eq_iff b L hb K1 K2 hK1 hK2 hdisj (fun i => (y i).1) (fun i => (y i).2.1)
        (fun i => (y i).2.2.1) (fun i => (y i).2.2.2)
      simp only [Prod.mk.eta] at this
      simp only [quadEquiv, Equiv.trans_apply, Equiv.arrowProdEquivProdArrow_apply,
        Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_apply, id_eq]
      simp only [Finset.mem_univ, true_implies]
      exact if_congr this rfl rfl
    simp only [hP]
    have hr : ∏ k ∈ range (L + 1), cnt k = ∏ i : Fin (L + 1),
        ∑ t ∈ univ, (if coordOK K1 K2 (i : ℕ) t then 1 else 0) :=
      (Fin.prod_univ_eq_prod_range cnt (L + 1)).symm
    rw [hr, Finset.prod_univ_sum, Fintype.piFinset_univ]
  rw [hcard]
  push_cast
  have hpow : (b : ℝ) ^ (4 * (L + 1)) = ∏ _k ∈ range (L + 1), (b : ℝ) ^ 4 := by
    rw [Finset.prod_const, card_range, ← pow_mul, mul_comm]
  rw [hpow, ← Finset.prod_div_distrib]
  have hterm : ∀ k ∈ range (L + 1), (cnt k : ℝ) / (b : ℝ) ^ 4 =
      (if k ∈ K1 then (2 * (b : ℝ) ^ 2 + 1) / (3 * (b : ℝ) ^ 3) else 1) *
        (if k ∈ K2 then (b : ℝ)⁻¹ else 1) := by
    intro k _
    have h3 := count_coord b K1 K2 hdisj k
    change 3 * cnt k = _ at h3
    have h3' : (3 : ℝ) * cnt k = ((if k ∈ K1 then b * (2 * b ^ 2 + 1) else
        if k ∈ K2 then 3 * b ^ 3 else 3 * b ^ 4 : ℕ) : ℝ) := by
      exact_mod_cast h3
    by_cases hk1 : k ∈ K1
    · have hk2 : k ∉ K2 := Finset.disjoint_left.1 hdisj hk1
      rw [ite_eq_left hk1] at h3'
      push_cast at h3'
      rw [ite_eq_left hk1, ite_eq_right hk2, mul_one]
      field_simp
      nlinarith [h3']
    · by_cases hk2 : k ∈ K2
      · rw [ite_eq_right hk1, ite_eq_left hk2] at h3'
        push_cast at h3'
        rw [ite_eq_right hk1, ite_eq_left hk2, one_mul]
        field_simp
        nlinarith [h3']
      · rw [ite_eq_right hk1, ite_eq_right hk2] at h3'
        push_cast at h3'
        rw [ite_eq_right hk1, ite_eq_right hk2, one_mul]
        field_simp
        nlinarith [h3']
  rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib, Finset.prod_ite_mem,
    Finset.prod_ite_mem, inter_eq_right.2 hK1, inter_eq_right.2 hK2, Finset.prod_const,
    Finset.prod_const, inv_pow]

end Palprimes
