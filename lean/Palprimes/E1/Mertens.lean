import Palprimes.MainTerm.VB

/-! # E1, Part A.7 and the Mertens inputs (blueprint A.7, §3.2, §4.2)

* copies (renamed) of `gB_le_half`, `VB_pos`, `pIco`, `VB_split`, `VB_ratio` from `MainTerm/Approx1.lean`
  (not imported: lake import depth);
* **A.7 telescoping** `Σ_{p ∈ [a, c)} g(p) V(p) = V(a) − V(c)` (`telescope`), and `Σ_{p<w} g(p)V(p) = 1 − V(w)`;
* one-sided Mertens `(1 − η) κ_B ≤ V(x) log x ≤ (1 + η) κ_B` (`VB_log_bounds`) and its ratio form;
* the closed end `p³ ≤ D` versus the prime range `p < D^{1/3}`: a one-prime correction (`sum_filter_le_eq`,
  `sum_cube_gt_eq`, `pointSum_bounds`, `pointSum_gV_le`), and `V(D^{1/3}) = (3/s + o(1)) V(w)` (`VB_cube_ratio`),
  `V(D^{1/3}) ≤ ρ (3/s) V(w)` (`VB_cube_le`);
* bridge lemmas between `s_p = log D / log p − 1` and prime ranges. -/

set_option linter.style.longLine false

open Finset Real

namespace Palprimes.E1

open Palprimes.MT Palprimes.Greaves

/-! ## Copies from `Approx1.lean` -/

/-- Copy of `Palprimes.MT.gB_le_half`. -/
theorem gB_le_half' (b p : ℕ) : gB b p ≤ 1 / 2 := by
  unfold gB; split_ifs with h
  · have : (2 : ℝ) ≤ p := by exact_mod_cast h.1.two_le
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  · norm_num

/-- `g(p) ≤ 1/p`. -/
theorem gB_le_inv (b p : ℕ) : gB b p ≤ 1 / (p : ℝ) := by
  unfold gB; split_ifs
  · exact le_refl _
  · positivity

/-- Copy of `Palprimes.MT.VB_pos`. -/
theorem VB_pos' (b : ℕ) (w : ℝ) : 0 < VB b w := by
  unfold VB; apply Finset.prod_pos; intro p _; linarith [gB_le_half' b p]

private theorem primesBelow_filter_lt_aux (lo hi : ℝ) (h : lo ≤ hi) :
    (primesBelow hi).filter (fun q : ℕ => (q : ℝ) < lo) = primesBelow lo := by
  ext q; rw [Finset.mem_filter, mem_primesBelow, mem_primesBelow]
  constructor
  · rintro ⟨⟨hq, _⟩, h2⟩; exact ⟨hq, h2⟩
  · rintro ⟨hq, h2⟩; exact ⟨⟨hq, by linarith⟩, h2⟩

/-- The primes in `[lo, hi)` (copy of `Palprimes.MT.pIco`). -/
noncomputable def primesIco (lo hi : ℝ) : Finset ℕ := (primesBelow hi).filter (fun q : ℕ => ¬ (q : ℝ) < lo)

theorem mem_primesIco (lo hi : ℝ) (q : ℕ) : q ∈ primesIco lo hi ↔ q.Prime ∧ lo ≤ q ∧ (q : ℝ) < hi := by
  unfold primesIco; rw [Finset.mem_filter, mem_primesBelow, not_lt]; tauto

/-- Copy of `Palprimes.MT.VB_split`. -/
theorem VB_split' (b : ℕ) (lo hi : ℝ) (h : lo ≤ hi) :
    VB b hi = VB b lo * ∏ q ∈ primesIco lo hi, (1 - gB b q) := by
  unfold VB primesIco
  rw [← Finset.prod_filter_mul_prod_filter_not (primesBelow hi) (fun q : ℕ => (q : ℝ) < lo),
    primesBelow_filter_lt_aux lo hi h]

private theorem log_ge_of_rpow_le_aux (y a w : ℝ) (hy : 0 < y) (h : y ^ a ≤ w) : a * Real.log y ≤ Real.log w := by
  have := Real.log_le_log (Real.rpow_pos_of_pos hy a) h
  rwa [Real.log_rpow hy] at this

/-- Copy of `Palprimes.MT.VB_ratio`: `V(w)/V(y) = log y / log w + o(1)`, uniformly in `y^a ≤ w ≤ y`. -/
theorem VB_ratio' (b : ℕ) (hb : 2 ≤ b) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (δ : ℝ) (hδ : 0 < δ) :
    ∃ y₀ : ℝ, 1 < y₀ ∧ ∀ y : ℝ, y₀ ≤ y → ∀ w : ℝ, y ^ a ≤ w → w ≤ y →
      |VB b w / VB b y - Real.log y / Real.log w| ≤ δ := by
  obtain ⟨C, hC0, hC⟩ := VB_log b hb
  set κ := kappaB b
  have hκ : 0 < κ := kappaB_pos b
  set B4 : ℝ := (Palprimes.bigB b : ℝ) + 4
  have hB4 : 1 < B4 := by have : (0 : ℝ) ≤ Palprimes.bigB b := Nat.cast_nonneg _; simp only [B4]; linarith
  set L₀ : ℝ := max (Real.log B4 / a) (max (2 * C / κ) (2 * C * (1 / a + 1) / (a * κ * δ))) + 1
  have hL0pos : 0 < L₀ := by
    have : 0 ≤ Real.log B4 / a := div_nonneg (Real.log_nonneg hB4.le) ha.le
    have := le_max_left (Real.log B4 / a) (max (2 * C / κ) (2 * C * (1 / a + 1) / (a * κ * δ)))
    simp only [L₀] <;> linarith
  refine ⟨Real.exp L₀, by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 hL0pos, ?_⟩
  intro y hy w hw1 hw2
  have hy0 : 0 < y := lt_of_lt_of_le (Real.exp_pos _) hy
  set L := Real.log y
  have hL : L₀ ≤ L := by rw [← Real.log_exp L₀]; exact Real.log_le_log (Real.exp_pos _) hy
  have hLpos : 0 < L := by linarith
  have hlw : a * L ≤ Real.log w := log_ge_of_rpow_le_aux y a w hy0 hw1
  have hlwpos : 0 < Real.log w := by nlinarith
  have hw0 : 0 < w := lt_of_lt_of_le (Real.rpow_pos_of_pos hy0 a) hw1
  have hm1 : Real.log B4 / a ≤ L₀ - 1 := by simp only [L₀] <;> linarith [le_max_left (Real.log B4 / a) (max (2 * C / κ) (2 * C * (1 / a + 1) / (a * κ * δ)))]
  have hm2 : 2 * C / κ ≤ L₀ - 1 := by
    simp only [L₀] <;>
    linarith [le_max_left (2 * C / κ) (2 * C * (1 / a + 1) / (a * κ * δ)),
      le_max_right (Real.log B4 / a) (max (2 * C / κ) (2 * C * (1 / a + 1) / (a * κ * δ)))]
  have hm3 : 2 * C * (1 / a + 1) / (a * κ * δ) ≤ L₀ - 1 := by
    simp only [L₀] <;>
    linarith [le_max_right (2 * C / κ) (2 * C * (1 / a + 1) / (a * κ * δ)),
      le_max_right (Real.log B4 / a) (max (2 * C / κ) (2 * C * (1 / a + 1) / (a * κ * δ)))]
  have hlogB : Real.log B4 ≤ a * L := by
    have := (div_le_iff₀ ha).1 (show Real.log B4 / a ≤ L by linarith)
    linarith
  have hwB : B4 ≤ w := by
    have : Real.log B4 ≤ Real.log w := by linarith
    exact (Real.log_le_log_iff (by linarith) hw0).1 this
  have hyB : B4 ≤ y := le_trans hwB hw2
  have hρw := hC w hwB
  have hρy := hC y hyB
  set ρw := VB b w * Real.log w
  set ρy := VB b y * L
  have hCL : C / L ≤ κ / 2 := by
    rw [div_le_iff₀ hLpos]
    have := (div_le_iff₀ hκ).1 (show 2 * C / κ ≤ L by linarith)
    linarith
  have hρy_ge : κ / 2 ≤ ρy := by
    have := (abs_le.1 hρy).1; linarith
  have hρy_pos : 0 < ρy := by linarith
  have hVy := VB_pos' b y
  have hVw := VB_pos' b w
  have key : VB b w / VB b y - L / Real.log w = (L / Real.log w) * ((ρw - ρy) / ρy) := by
    simp only [ρw, ρy]; field_simp
  rw [key, abs_mul, abs_of_pos (div_pos hLpos hlwpos), abs_div, abs_of_pos hρy_pos]
  have h1 : L / Real.log w ≤ 1 / a := by
    rw [div_le_div_iff₀ hlwpos ha]; linarith
  have h2 : |ρw - ρy| ≤ C / (a * L) + C / L := by
    have e1 : C / Real.log w ≤ C / (a * L) := div_le_div_of_nonneg_left hC0 (by positivity) hlw
    have := abs_sub_le ρw κ ρy
    rw [abs_sub_comm κ ρy] at this
    linarith
  have h3 : |ρw - ρy| / ρy ≤ (C / (a * L) + C / L) / (κ / 2) := by
    calc |ρw - ρy| / ρy ≤ (C / (a * L) + C / L) / ρy := div_le_div_of_nonneg_right h2 hρy_pos.le
      _ ≤ (C / (a * L) + C / L) / (κ / 2) := div_le_div_of_nonneg_left (by positivity) (by positivity) hρy_ge
  have h4 : (1 / a) * ((C / (a * L) + C / L) / (κ / 2)) ≤ δ := by
    have e : (1 / a) * ((C / (a * L) + C / L) / (κ / 2)) = (2 * C * (1 / a + 1) / (a * κ * δ)) * δ / L := by
      field_simp
    rw [e, div_le_iff₀ hLpos]
    have : 2 * C * (1 / a + 1) / (a * κ * δ) ≤ L := by linarith
    nlinarith
  calc L / Real.log w * (|ρw - ρy| / ρy) ≤ (1 / a) * ((C / (a * L) + C / L) / (κ / 2)) :=
        mul_le_mul h1 h3 (div_nonneg (abs_nonneg _) hρy_pos.le) (by positivity)
    _ ≤ δ := h4

/-- `VB_ratio'` in multiplicative form: `|V(w) − (log y / log w) V(y)| ≤ δ V(y)` for `y ≥ y₀`, `y^a ≤ w ≤ y`. -/
theorem VB_ratio_mul (b : ℕ) (hb : 2 ≤ b) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (δ : ℝ) (hδ : 0 < δ) :
    ∃ y₀ : ℝ, 1 < y₀ ∧ ∀ y : ℝ, y₀ ≤ y → ∀ w : ℝ, y ^ a ≤ w → w ≤ y →
      |VB b w - Real.log y / Real.log w * VB b y| ≤ δ * VB b y := by
  obtain ⟨y₀, hy₀, h⟩ := VB_ratio' b hb a ha ha1 δ hδ
  refine ⟨y₀, hy₀, fun y hy w hw1 hw2 => ?_⟩
  have hV := VB_pos' b y
  have e : VB b w - Real.log y / Real.log w * VB b y = (VB b w / VB b y - Real.log y / Real.log w) * VB b y := by
    field_simp
  rw [e, abs_mul, abs_of_pos hV]
  exact mul_le_mul_of_nonneg_right (h y hy w hw1 hw2) hV.le

/-! ## A.7: telescoping -/

/-- Generic telescoping: `Σ_{p∈S} g(p) Π_{q∈S, q<p} (1 − g q) = 1 − Π_{q∈S} (1 − g q)`. -/
theorem sum_mul_prod_filter_lt (g : ℕ → ℝ) (S : Finset ℕ) :
    ∑ p ∈ S, g p * ∏ q ∈ S.filter (· < p), (1 - g q) = 1 - ∏ q ∈ S, (1 - g q) := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert M S hM ih =>
    have hMS : M ∉ S := fun h => lt_irrefl M (hM M h)
    rw [sum_insert hMS, prod_insert hMS]
    have e1 : (insert M S).filter (· < M) = S := by
      ext x; simp only [mem_filter, mem_insert]
      constructor
      · rintro ⟨rfl | hx, hlt⟩
        · exact absurd hlt (lt_irrefl _)
        · exact hx
      · intro hx; exact ⟨Or.inr hx, hM x hx⟩
    have e2 : ∀ P ∈ S, (insert M S).filter (· < P) = S.filter (· < P) := by
      intro P hP; ext x; simp only [mem_filter, mem_insert]
      constructor
      · rintro ⟨rfl | hx, hlt⟩
        · exact absurd (lt_trans hlt (hM P hP)) (lt_irrefl _)
        · exact ⟨hx, hlt⟩
      · rintro ⟨hx, hlt⟩; exact ⟨Or.inr hx, hlt⟩
    rw [e1, sum_congr rfl (fun P hP => by rw [e2 P hP]), ih]
    ring

private theorem primesBelow_filter_lt_nat (w : ℝ) (P : ℕ) (hP : P ∈ primesBelow w) :
    (primesBelow w).filter (· < P) = primesBelow (P : ℝ) := by
  ext q
  rw [mem_filter, mem_primesBelow, mem_primesBelow]
  have hPw := ((mem_primesBelow w P).1 hP).2
  constructor
  · rintro ⟨⟨hq, _⟩, hqP⟩; exact ⟨hq, by exact_mod_cast hqP⟩
  · rintro ⟨hq, hqP⟩
    have hqP' : q < P := by exact_mod_cast hqP
    exact ⟨⟨hq, lt_trans hqP hPw⟩, hqP'⟩

/-- `Σ_{p<w} g(p) V(p) = 1 − V(w)`. -/
theorem telescope_primesBelow (b : ℕ) (w : ℝ) :
    ∑ p ∈ primesBelow w, gB b p * VB b p = 1 - VB b w := by
  have := sum_mul_prod_filter_lt (gB b) (primesBelow w)
  rw [show VB b w = ∏ q ∈ primesBelow w, (1 - gB b q) from rfl, ← this]
  refine sum_congr rfl (fun p hp => ?_)
  rw [primesBelow_filter_lt_nat w p hp]; rfl

/-- **Lemma A.7 (telescoping)**: `Σ_{a ≤ p < c} g(p) V(p) = V(a) − V(c)` for `a ≤ c`. -/
theorem telescope (b : ℕ) {a c : ℝ} (h : a ≤ c) :
    ∑ p ∈ primesIco a c, gB b p * VB b p = VB b a - VB b c := by
  have hs := sum_filter_add_sum_filter_not (primesBelow c) (fun q : ℕ => (q : ℝ) < a) (fun p => gB b p * VB b p)
  rw [primesBelow_filter_lt_aux a c h, telescope_primesBelow, telescope_primesBelow] at hs
  unfold primesIco
  linarith

theorem VB_le_one (b : ℕ) (w : ℝ) : VB b w ≤ 1 := by
  have h := telescope_primesBelow b w
  have : 0 ≤ ∑ p ∈ primesBelow w, gB b p * VB b p :=
    sum_nonneg (fun p _ => mul_nonneg (gB_nonneg b p) (VB_pos' b p).le)
  linarith

/-- `V` is antitone. -/
theorem VB_anti (b : ℕ) {x y : ℝ} (h : x ≤ y) : VB b y ≤ VB b x := by
  have := telescope b h
  have : 0 ≤ ∑ p ∈ primesIco x y, gB b p * VB b p :=
    sum_nonneg (fun p _ => mul_nonneg (gB_nonneg b p) (VB_pos' b p).le)
  linarith

/-! ## One-sided Mertens -/

/-- **One-sided Mertens** (from `VB_log`): `(1 − η) κ_B ≤ V(x) log x ≤ (1 + η) κ_B` for `x ≥ x₀`. -/
theorem VB_log_bounds (b : ℕ) (hb : 2 ≤ b) {η : ℝ} (hη : 0 < η) :
    ∃ x₀ : ℝ, 1 < x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      (1 - η) * kappaB b ≤ VB b x * Real.log x ∧ VB b x * Real.log x ≤ (1 + η) * kappaB b := by
  obtain ⟨C, hC0, hC⟩ := VB_log b hb
  have hκ := kappaB_pos b
  have hB0 : (0 : ℝ) ≤ Palprimes.bigB b := Nat.cast_nonneg _
  refine ⟨max ((Palprimes.bigB b : ℝ) + 4) (Real.exp (C / (η * kappaB b))),
    lt_of_lt_of_le (by linarith) (le_max_left _ _), fun x hx => ?_⟩
  have hx1 : (Palprimes.bigB b : ℝ) + 4 ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : Real.exp (C / (η * kappaB b)) ≤ x := le_trans (le_max_right _ _) hx
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hl2 : C / (η * kappaB b) ≤ Real.log x := by
    rw [← Real.log_exp (C / (η * kappaB b))]; exact Real.log_le_log (Real.exp_pos _) hx2
  have hCη : C / Real.log x ≤ η * kappaB b := by
    rw [div_le_iff₀ hlx]
    have := (div_le_iff₀ (by positivity : 0 < η * kappaB b)).1 hl2
    linarith
  have h := abs_le.1 (le_trans (hC x hx1) hCη)
  constructor <;> nlinarith [h.1, h.2]

/-- Ratio form: `V(x) log x ≤ (1+η)/(1−η) · V(y) log y` for `x, y ≥ x₀`. -/
theorem VB_log_ratio (b : ℕ) (hb : 2 ≤ b) {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ x₀ : ℝ, 1 < x₀ ∧ ∀ x y : ℝ, x₀ ≤ x → x₀ ≤ y →
      VB b x * Real.log x ≤ (1 + η) / (1 - η) * (VB b y * Real.log y) := by
  obtain ⟨x₀, hx₀, h⟩ := VB_log_bounds b hb hη
  refine ⟨x₀, hx₀, fun x y hx hy => ?_⟩
  have hκ := kappaB_pos b
  have h1 := (h x hx).2
  have h2 := (h y hy).1
  have h1η : 0 < 1 - η := by linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ h1η]
  nlinarith

/-- Lower bound `κ_B/2 ≤ V(x) log x` for large `x` (used for `V(w) ≥ κ_B/(2 log D)`). -/
theorem VB_log_ge_half (b : ℕ) (hb : 2 ≤ b) :
    ∃ x₀ : ℝ, 1 < x₀ ∧ ∀ x : ℝ, x₀ ≤ x → kappaB b / 2 ≤ VB b x * Real.log x := by
  obtain ⟨x₀, hx₀, h⟩ := VB_log_bounds b hb (by norm_num : (0 : ℝ) < 1 / 2)
  exact ⟨x₀, hx₀, fun x hx => by linarith [(h x hx).1]⟩

/-! ## The closed end `p³ ≤ D` and the prime `D^{1/3}` -/

theorem cube_le_iff {D : ℝ} (hD : 0 ≤ D) {p : ℝ} (hp : 0 ≤ p) : p ^ 3 ≤ D ↔ p ≤ D ^ (1 / 3 : ℝ) := by
  have e : p = (p ^ 3) ^ (1 / 3 : ℝ) := by
    rw [show (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ by norm_num, Real.pow_rpow_inv_natCast hp (by norm_num)]
  conv_rhs => rw [e]
  exact (Real.rpow_le_rpow_iff (by positivity) hD (by norm_num)).symm

theorem lt_cube_iff {D : ℝ} (hD : 0 ≤ D) {p : ℝ} (hp : 0 ≤ p) : D < p ^ 3 ↔ D ^ (1 / 3 : ℝ) < p := by
  rw [← not_le, ← not_le, cube_le_iff hD hp]

/-- Primes `< w` and `≤ c` are the primes `< min w c` and possibly the prime `c` itself. -/
theorem filter_le_eq_union (w c : ℝ) :
    (primesBelow w).filter (fun p : ℕ => (p : ℝ) ≤ c) =
      primesBelow (min w c) ∪ (primesBelow w).filter (fun p : ℕ => (p : ℝ) = c) := by
  ext q
  simp only [mem_filter, mem_union, mem_primesBelow, lt_min_iff]
  constructor
  · rintro ⟨⟨hq, hqw⟩, hqc⟩
    rcases hqc.lt_or_eq with h | h
    · exact Or.inl ⟨hq, hqw, h⟩
    · exact Or.inr ⟨⟨hq, hqw⟩, h⟩
  · rintro (⟨hq, hqw, hqc⟩ | ⟨⟨hq, hqw⟩, hqc⟩)
    · exact ⟨⟨hq, hqw⟩, hqc.le⟩
    · exact ⟨⟨hq, hqw⟩, hqc.le⟩

theorem disjoint_point (w c : ℝ) :
    Disjoint (primesBelow (min w c)) ((primesBelow w).filter (fun p : ℕ => (p : ℝ) = c)) := by
  rw [Finset.disjoint_left]
  intro q h1 h2
  rw [mem_primesBelow, lt_min_iff] at h1
  rw [mem_filter] at h2
  linarith [h1.2.2, h2.2]

/-- **The one-prime correction (closed end)**: `Σ_{p<w, p≤c} f = Σ_{p<min(w,c)} f + Σ_{p<w, p=c} f`. -/
theorem sum_filter_le_eq (f : ℕ → ℝ) (w c : ℝ) :
    ∑ p ∈ (primesBelow w).filter (fun p : ℕ => (p : ℝ) ≤ c), f p =
      ∑ p ∈ primesBelow (min w c), f p + ∑ p ∈ (primesBelow w).filter (fun p : ℕ => (p : ℝ) = c), f p := by
  rw [filter_le_eq_union, sum_union (disjoint_point w c)]

/-- The cube form: `Σ_{p<w, p³≤D} f = Σ_{p<min(w,D^{1/3})} f + Σ_{p<w, p=D^{1/3}} f`. -/
theorem sum_filter_cube_le_eq (f : ℕ → ℝ) (w : ℝ) {D : ℝ} (hD : 0 ≤ D) :
    ∑ p ∈ (primesBelow w).filter (fun p : ℕ => (p : ℝ) ^ 3 ≤ D), f p =
      ∑ p ∈ primesBelow (min w (D ^ (1 / 3 : ℝ))), f p +
        ∑ p ∈ (primesBelow w).filter (fun p : ℕ => (p : ℝ) = D ^ (1 / 3 : ℝ)), f p := by
  rw [← sum_filter_le_eq]
  congr 1
  ext p
  simp only [mem_filter]
  rw [cube_le_iff hD (Nat.cast_nonneg p)]

/-- The point set `{p < w : p = c}` carries at most one prime. -/
theorem pointSum_bounds (f : ℕ → ℝ) (w c M : ℝ) (hM : 0 ≤ M)
    (hf : ∀ p : ℕ, p.Prime → (p : ℝ) = c → 0 ≤ f p ∧ f p ≤ M) :
    0 ≤ ∑ p ∈ (primesBelow w).filter (fun p : ℕ => (p : ℝ) = c), f p ∧
      ∑ p ∈ (primesBelow w).filter (fun p : ℕ => (p : ℝ) = c), f p ≤ M := by
  have hmem : ∀ p ∈ (primesBelow w).filter (fun p : ℕ => (p : ℝ) = c), p.Prime ∧ (p : ℝ) = c := by
    intro p hp; rw [mem_filter, mem_primesBelow] at hp; exact ⟨hp.1.1, hp.2⟩
  have hcard : ((primesBelow w).filter (fun p : ℕ => (p : ℝ) = c)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    have := (hmem x hx).2.trans (hmem y hy).2.symm
    exact_mod_cast this
  constructor
  · exact sum_nonneg (fun p hp => (hf p (hmem p hp).1 (hmem p hp).2).1)
  · calc _ ≤ ((primesBelow w).filter (fun p : ℕ => (p : ℝ) = c)).card • M :=
          Finset.sum_le_card_nsmul _ _ _ (fun p hp => (hf p (hmem p hp).1 (hmem p hp).2).2)
      _ ≤ 1 • M := by
          rw [nsmul_eq_mul, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hM
      _ = M := one_smul _ _

/-- The correction for `g(p)V(p)`: `0 ≤ Σ_{p<w, p=c} g(p)V(p) ≤ V(c)/c`. -/
theorem pointSum_gV_le (b : ℕ) (w : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    0 ≤ ∑ p ∈ (primesBelow w).filter (fun p : ℕ => (p : ℝ) = c), gB b p * VB b p ∧
      ∑ p ∈ (primesBelow w).filter (fun p : ℕ => (p : ℝ) = c), gB b p * VB b p ≤ VB b c / c := by
  apply pointSum_bounds _ w c _ (div_nonneg (VB_pos' b c).le hc)
  intro p hp hpc
  refine ⟨mul_nonneg (gB_nonneg b p) (VB_pos' b p).le, ?_⟩
  rw [← hpc]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  calc gB b p * VB b p ≤ 1 / (p : ℝ) * VB b p := mul_le_mul_of_nonneg_right (gB_le_inv b p) (VB_pos' b p).le
    _ = VB b p / p := by ring

/-- **B⁺₀ in closed form** (A.7 with the one-prime correction at `p = D^{1/3}`):
`Σ_{p<w, D<p³} g(p)V(p) = V(min(w, D^{1/3})) − V(w) − E`, `E = Σ_{p<w, p=D^{1/3}} g(p)V(p)`. -/
theorem sum_cube_gt_eq (b : ℕ) (w : ℝ) {D : ℝ} (hD : 0 ≤ D) :
    ∑ p ∈ (primesBelow w).filter (fun p : ℕ => D < (p : ℝ) ^ 3), gB b p * VB b p =
      VB b (min w (D ^ (1 / 3 : ℝ))) - VB b w -
        ∑ p ∈ (primesBelow w).filter (fun p : ℕ => (p : ℝ) = D ^ (1 / 3 : ℝ)), gB b p * VB b p := by
  have hs := sum_filter_add_sum_filter_not (primesBelow w) (fun p : ℕ => (p : ℝ) ^ 3 ≤ D)
    (fun p => gB b p * VB b p)
  rw [sum_filter_cube_le_eq _ w hD, telescope_primesBelow, telescope_primesBelow] at hs
  have e : (primesBelow w).filter (fun p : ℕ => ¬ (p : ℝ) ^ 3 ≤ D) =
      (primesBelow w).filter (fun p : ℕ => D < (p : ℝ) ^ 3) := by
    ext p; simp only [mem_filter, not_le]
  rw [e] at hs
  linarith

/-- The closed sum `Σ_{p<w, p³≤D} g(p)V(p) = 1 − V(min(w, D^{1/3})) + E`. -/
theorem sum_cube_le_eq (b : ℕ) (w : ℝ) {D : ℝ} (hD : 0 ≤ D) :
    ∑ p ∈ (primesBelow w).filter (fun p : ℕ => (p : ℝ) ^ 3 ≤ D), gB b p * VB b p =
      1 - VB b (min w (D ^ (1 / 3 : ℝ))) +
        ∑ p ∈ (primesBelow w).filter (fun p : ℕ => (p : ℝ) = D ^ (1 / 3 : ℝ)), gB b p * VB b p := by
  rw [sum_filter_cube_le_eq _ w hD, telescope_primesBelow]

/-- **`V(D^{1/3})` against `V(w)`** (B.3, `B⁺₀`): `|V(D^{1/3}) − (3/s) V(w)| ≤ δ V(w)` uniformly for
`D^{1/3} ≤ w ≤ D`, `s = log D / log w`. -/
theorem VB_cube_ratio (b : ℕ) (hb : 2 ≤ b) {δ : ℝ} (hδ : 0 < δ) :
    ∃ D₁ : ℝ, 1 < D₁ ∧ ∀ D : ℝ, D₁ ≤ D → ∀ w : ℝ, D ^ (1 / 3 : ℝ) ≤ w → w ≤ D →
      |VB b (D ^ (1 / 3 : ℝ)) - 3 / (Real.log D / Real.log w) * VB b w| ≤ δ * VB b w := by
  obtain ⟨y₀, hy₀, h⟩ := VB_ratio_mul b hb (1 / 3) (by norm_num) (by norm_num) δ hδ
  refine ⟨y₀ ^ (3 : ℕ), one_lt_pow₀ hy₀ (by norm_num), fun D hD w hw1 hw2 => ?_⟩
  have hD1 : 1 < D := lt_of_lt_of_le (one_lt_pow₀ hy₀ (by norm_num)) hD
  have hD0 : 0 ≤ D := by linarith
  set c := D ^ (1 / 3 : ℝ)
  have hcy : y₀ ≤ c := by
    have := (cube_le_iff hD0 (by linarith : (0 : ℝ) ≤ y₀)).1 hD
    exact this
  have hw0 : 0 ≤ w := by linarith [Real.rpow_nonneg hD0 (1 / 3 : ℝ)]
  have hwc : w ^ (1 / 3 : ℝ) ≤ c := Real.rpow_le_rpow hw0 hw2 (by norm_num)
  have key := h w (le_trans hcy hw1) c hwc hw1
  have hlc : Real.log c = 1 / 3 * Real.log D := Real.log_rpow (by linarith) _
  have hlD : 0 < Real.log D := Real.log_pos hD1
  have e : Real.log w / Real.log c = 3 / (Real.log D / Real.log w) := by
    rw [hlc]
    have hlw : 0 < Real.log w := Real.log_pos (by linarith)
    field_simp
  rw [e] at key
  exact key

/-- One-sided form (C.2 (+)): `V(D^{1/3}) ≤ ρ (3/s) V(w)` for `D ≥ D₀`, `D^{1/3} ≤ w`, `ρ = (1+η)/(1−η)`. -/
theorem VB_cube_le (b : ℕ) (hb : 2 ≤ b) {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D → ∀ w : ℝ, D ^ (1 / 3 : ℝ) ≤ w →
      VB b (D ^ (1 / 3 : ℝ)) ≤ (1 + η) / (1 - η) * (3 / (Real.log D / Real.log w)) * VB b w := by
  obtain ⟨x₀, hx₀, h⟩ := VB_log_ratio b hb hη hη1
  refine ⟨x₀ ^ (3 : ℕ), one_lt_pow₀ hx₀ (by norm_num), fun D hD w hw => ?_⟩
  have hD1 : 1 < D := lt_of_lt_of_le (one_lt_pow₀ hx₀ (by norm_num)) hD
  have hD0 : 0 ≤ D := by linarith
  set c := D ^ (1 / 3 : ℝ)
  have hcx : x₀ ≤ c := (cube_le_iff hD0 (by linarith : (0 : ℝ) ≤ x₀)).1 hD
  have key := h c w hcx (le_trans hcx hw)
  have hlc : Real.log c = 1 / 3 * Real.log D := Real.log_rpow (by linarith) _
  have hlD : 0 < Real.log D := Real.log_pos hD1
  have hlw : 0 < Real.log w := Real.log_pos (by linarith)
  rw [hlc] at key
  have e : (1 + η) / (1 - η) * (3 / (Real.log D / Real.log w)) * VB b w =
      (1 + η) / (1 - η) * (VB b w * Real.log w) / (1 / 3 * Real.log D) := by
    field_simp
  rw [e, le_div_iff₀ (by positivity)]
  linarith

/-! ## Bridge lemmas for `s = log D / log w` and `s_p = log D / log p − 1` -/

/-- `log z / log z^{1/s} = s` for `z > 1`, `s > 0`. -/
theorem log_div_log_rpow {z s : ℝ} (hz : 1 < z) (hs : 0 < s) : Real.log z / Real.log (z ^ (1 / s)) = s := by
  rw [Real.log_rpow (by linarith)]
  have := Real.log_pos hz
  field_simp

/-- `D^{1/(1+u)} ≤ p ↔ s_p ≤ u` (for `D > 0`, `p > 1`, `1 + u > 0`). -/
theorem rpow_le_iff_sp_le {D p u : ℝ} (hD : 0 < D) (hp : 1 < p) (hu : 0 < 1 + u) :
    D ^ (1 / (1 + u)) ≤ p ↔ Real.log D / Real.log p - 1 ≤ u := by
  have hlp := Real.log_pos hp
  rw [← Real.log_le_log_iff (Real.rpow_pos_of_pos hD _) (by linarith), Real.log_rpow hD,
    sub_le_iff_le_add, div_le_iff₀ hlp, add_comm u 1, one_div, inv_mul_le_iff₀ hu]

/-- `p < D^{1/(1+u)} ↔ u < s_p`. -/
theorem lt_rpow_iff_lt_sp {D p u : ℝ} (hD : 0 < D) (hp : 1 < p) (hu : 0 < 1 + u) :
    p < D ^ (1 / (1 + u)) ↔ u < Real.log D / Real.log p - 1 := by
  rw [← not_le, ← not_le, rpow_le_iff_sp_le hD hp hu]

/-- `s_p ≥ 2 ↔ p³ ≤ D` (the `headOK` convention, with `≤`). -/
theorem two_le_sp_iff {D p : ℝ} (hD : 0 < D) (hp : 1 < p) :
    2 ≤ Real.log D / Real.log p - 1 ↔ p ^ 3 ≤ D := by
  have hlp := Real.log_pos hp
  rw [le_sub_iff_add_le, show (2 : ℝ) + 1 = ((3 : ℕ) : ℝ) by norm_num, le_div_iff₀ hlp, ← Real.log_pow,
    Real.log_le_log_iff (by positivity) hD]

/-- `p < w ↔ s − 1 < s_p` (for `D > 1`, `p, w > 1`). -/
theorem lt_iff_s_sub_one_lt_sp {D p w : ℝ} (hD : 1 < D) (hp : 1 < p) (hw : 1 < w) :
    p < w ↔ Real.log D / Real.log w - 1 < Real.log D / Real.log p - 1 := by
  have hlp := Real.log_pos hp
  have hlw := Real.log_pos hw
  have hlD := Real.log_pos hD
  rw [sub_lt_sub_iff_right, div_lt_div_iff₀ hlw hlp, ← Real.log_lt_log_iff (by linarith) (by linarith)]
  constructor
  · intro h; nlinarith
  · intro h; by_contra h'; rw [not_lt] at h'; nlinarith

end Palprimes.E1
