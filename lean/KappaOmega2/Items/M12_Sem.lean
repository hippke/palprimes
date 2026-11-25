import KappaOmega2.Items.M12_G
import KappaOmega2.Items.M12_Lists

/-!
# M12 helper: soundness of the tables (`Sem`), base level, recursion step, crude tail bound
-/

set_option linter.style.longLine false

open MeasureTheory Finset Real
open scoped ENNReal

namespace KappaOmega2.M12

open KappaOmega2

/-! ## Real grid -/

noncomputable def rho (g : Grid) : ℝ := (g.A : ℝ) / g.B
noncomputable def xiR (g : Grid) (j : ℕ) : ℝ := (g.A : ℝ) ^ j / (85 * (g.B : ℝ) ^ j)
noncomputable def vR (g : Grid) (σ : ℕ) : ℝ := (vnum g σ : ℝ) / vden g σ
noncomputable def yR (g : Grid) (σ : ℕ) : ℝ := 1 - 1 / vR g σ
noncomputable def gR (g : Grid) (σ : ℕ) : ℝ := vR g σ - 1

/-- Validity of a grid (all checked by `decide` for `gF`, `gC`). -/
structure GridOK (g : Grid) : Prop where
  hB : 0 < g.B
  hBA : g.B < g.A
  hM : 0 < g.M
  hN : 85 * g.B ^ g.N ≤ 3 * g.A ^ g.N
  hSY : vnum g g.SY ≤ 3 * (vnum g g.SY - vden g g.SY)
  hSH : vnum g g.SH ≤ 2 * (vnum g g.SH - vden g g.SH)
  hS3 : 3 * (vnum g g.S3 - vden g g.S3) ≤ vnum g g.S3
  hS3H : g.S3 ≤ g.SH
  side : sideOK g = true

variable {g : Grid}

lemma cdiv_ge (a : ℕ) {b : ℕ} (hb : 0 < b) : a ≤ cdiv a b * b := by
  unfold cdiv
  have h1 := Nat.div_add_mod (a + b - 1) b
  have h2 := Nat.mod_lt (a + b - 1) hb
  have : b * ((a + b - 1) / b) = (a + b - 1) / b * b := Nat.mul_comm _ _
  omega

lemma cdiv_ge_real (a : ℕ) {b : ℕ} (hb : 0 < b) : (a : ℝ) / b ≤ cdiv a b := by
  rw [div_le_iff₀ (by exact_mod_cast hb)]
  exact_mod_cast cdiv_ge a hb

lemma div_le_real (a b : ℕ) : ((a / b : ℕ) : ℝ) ≤ (a : ℝ) / b := Nat.cast_div_le

lemma cast_sub_ge (a b : ℕ) : (a : ℝ) - b ≤ ((a - b : ℕ) : ℝ) := by
  rcases le_total b a with h | h
  · rw [Nat.cast_sub h]
  · rw [Nat.sub_eq_zero_of_le h]; simp; exact_mod_cast h

lemma TT_posR : (0 : ℝ) < TT := by exact_mod_cast TT_pos

lemma vden_pos (hg : GridOK g) (σ : ℕ) : 0 < vden g σ := by
  unfold vden; exact Nat.mul_pos (pow_pos hg.hB _) (Nat.mul_pos hg.hM hg.hB)

lemma vden_le_vnum (hg : GridOK g) (σ : ℕ) : vden g σ ≤ vnum g σ := by
  unfold vden vnum
  have h1 : g.B ^ (σ / g.M) ≤ g.A ^ (σ / g.M) := Nat.pow_le_pow_left hg.hBA.le _
  calc g.B ^ (σ / g.M) * (g.M * g.B) ≤ g.A ^ (σ / g.M) * (g.M * g.B) := Nat.mul_le_mul_right _ h1
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.le_add_right _ _)

lemma vnum_pos (hg : GridOK g) (σ : ℕ) : 0 < vnum g σ := lt_of_lt_of_le (vden_pos hg σ) (vden_le_vnum hg σ)

lemma vR_formula (hg : GridOK g) (σ : ℕ) :
    vR g σ = rho g ^ (σ / g.M) * (1 + ((σ % g.M : ℕ) : ℝ) * (rho g - 1) / g.M) := by
  have hB : (0 : ℝ) < g.B := by exact_mod_cast hg.hB
  have hM : (0 : ℝ) < g.M := by exact_mod_cast hg.hM
  unfold vR vnum vden rho
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow,
    Nat.cast_sub hg.hBA.le, div_pow]
  field_simp

lemma rho_gt_one (hg : GridOK g) : 1 < rho g := by
  unfold rho
  rw [one_lt_div (by exact_mod_cast hg.hB)]
  exact_mod_cast hg.hBA

lemma divmod_succ (M σ : ℕ) (hM : 0 < M) :
    ((σ + 1) / M = σ / M ∧ (σ + 1) % M = σ % M + 1) ∨ ((σ + 1) / M = σ / M + 1 ∧ (σ + 1) % M = 0 ∧ σ % M + 1 = M) := by
  have h1 := Nat.div_add_mod σ M
  have h2 := Nat.mod_lt σ hM
  rcases Nat.lt_or_ge (σ % M + 1) M with h | h
  · left
    have := (Nat.div_mod_unique hM).mpr ⟨(by rw [Nat.mul_comm] at h1 ⊢; omega : σ % M + 1 + M * (σ / M) = σ + 1), h⟩
    exact ⟨this.1, this.2⟩
  · right
    have := (Nat.div_mod_unique hM).mpr ⟨(by
      have : M * (σ / M + 1) = M * (σ / M) + M := by ring
      omega : 0 + M * (σ / M + 1) = σ + 1), hM⟩
    exact ⟨this.1, this.2, by omega⟩

lemma vR_lower (hg : GridOK g) (σ : ℕ) : rho g ^ (σ / g.M) ≤ vR g σ := by
  rw [vR_formula hg]
  have := rho_gt_one hg
  have hM : (0 : ℝ) < g.M := by exact_mod_cast hg.hM
  have : 0 ≤ ((σ % g.M : ℕ) : ℝ) * (rho g - 1) / g.M := by
    apply div_nonneg _ hM.le; apply mul_nonneg (by positivity); linarith
  nlinarith [pow_pos (show 0 < rho g by linarith) (σ / g.M)]

lemma vR_succ (hg : GridOK g) (σ : ℕ) :
    vR g (σ + 1) = vR g σ + rho g ^ (σ / g.M) * (rho g - 1) / g.M := by
  have hM : (0 : ℝ) < g.M := by exact_mod_cast hg.hM
  rcases divmod_succ g.M σ hg.hM with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · rw [vR_formula hg, vR_formula hg, h1, h2]; push_cast; field_simp; ring
  · rw [vR_formula hg, vR_formula hg, h1, h2]
    have h3' : ((σ % g.M : ℕ) : ℝ) = g.M - 1 := by
      have : ((σ % g.M + 1 : ℕ) : ℝ) = g.M := by rw [h3]
      push_cast at this; linarith
    rw [h3']; push_cast; field_simp; ring

lemma vR_upper (hg : GridOK g) (σ : ℕ) : vR g (σ + 1) ≤ rho g ^ (σ / g.M + 1) := by
  have hM : (0 : ℝ) < g.M := by exact_mod_cast hg.hM
  have hr := rho_gt_one hg
  rw [vR_succ hg, vR_formula hg]
  have hmod : ((σ % g.M : ℕ) : ℝ) + 1 ≤ g.M := by exact_mod_cast Nat.mod_lt σ hg.hM
  have hp : 0 < rho g ^ (σ / g.M) := pow_pos (by linarith) _
  rw [pow_succ]
  have : rho g ^ (σ / g.M) * (1 + ((σ % g.M : ℕ) : ℝ) * (rho g - 1) / g.M) + rho g ^ (σ / g.M) * (rho g - 1) / g.M
      = rho g ^ (σ / g.M) * (1 + (((σ % g.M : ℕ) : ℝ) + 1) * (rho g - 1) / g.M) := by ring
  rw [this]
  apply mul_le_mul_of_nonneg_left _ hp.le
  have : (((σ % g.M : ℕ) : ℝ) + 1) * (rho g - 1) / g.M ≤ rho g - 1 := by
    rw [div_le_iff₀ hM]; nlinarith
  linarith

lemma vR_mono (hg : GridOK g) (σ : ℕ) : vR g σ ≤ vR g (σ + 1) := by
  rw [vR_succ hg]
  have := rho_gt_one hg
  have hM : (0 : ℝ) < g.M := by exact_mod_cast hg.hM
  have : 0 ≤ rho g ^ (σ / g.M) * (rho g - 1) / g.M := by
    apply div_nonneg _ hM.le; apply mul_nonneg (pow_pos (by linarith) _).le; linarith
  linarith

lemma one_le_vR (hg : GridOK g) (σ : ℕ) : 1 ≤ vR g σ :=
  le_trans (one_le_pow₀ (rho_gt_one hg).le) (vR_lower hg σ)

lemma vR_monotone (hg : GridOK g) : Monotone (vR g) := monotone_nat_of_le_succ (vR_mono hg)

lemma yR_monotone (hg : GridOK g) : Monotone (yR g) := by
  intro a b hab
  unfold yR
  have h1 := one_le_vR hg a
  have := vR_monotone hg hab
  have : 1 / vR g b ≤ 1 / vR g a := one_div_le_one_div_of_le (by linarith) this
  linarith

lemma yR_eq (hg : GridOK g) (σ : ℕ) : yR g σ = ((vnum g σ - vden g σ : ℕ) : ℝ) / vnum g σ := by
  have h1 : (0 : ℝ) < vnum g σ := by exact_mod_cast vnum_pos hg σ
  have h2 : (0 : ℝ) < vden g σ := by exact_mod_cast vden_pos hg σ
  unfold yR vR
  rw [Nat.cast_sub (vden_le_vnum hg σ)]
  field_simp

lemma gR_eq (hg : GridOK g) (σ : ℕ) : gR g σ = ((vnum g σ - vden g σ : ℕ) : ℝ) / vden g σ := by
  have h2 : (0 : ℝ) < vden g σ := by exact_mod_cast vden_pos hg σ
  unfold gR vR
  rw [Nat.cast_sub (vden_le_vnum hg σ)]
  field_simp

lemma yR_zero (hg : GridOK g) : yR g 0 = 0 := by
  rw [yR_eq hg]; simp [vnum, vden]

lemma xiR_pos (hg : GridOK g) (j : ℕ) : 0 < xiR g j := by
  have hB : (0 : ℝ) < g.B := by exact_mod_cast hg.hB
  have hA : (0 : ℝ) < g.A := by exact_mod_cast (lt_trans hg.hB hg.hBA)
  unfold xiR; exact div_pos (pow_pos hA _) (mul_pos (by norm_num) (pow_pos hB _))

lemma xiR_add (hg : GridOK g) (j s : ℕ) : xiR g (j + s) = xiR g j * rho g ^ s := by
  have : (0 : ℝ) < g.B := by exact_mod_cast hg.hB
  unfold xiR rho; rw [pow_add, pow_add, div_pow]; field_simp

lemma xiR_mono (hg : GridOK g) : Monotone (xiR g) := by
  refine monotone_nat_of_le_succ fun j => ?_
  rw [xiR_add hg j 1, pow_one]
  have := rho_gt_one hg; have := xiR_pos hg j
  nlinarith

lemma xiR_zero : xiR g 0 = 1 / 85 := by simp [xiR]

lemma xiR_N (hg : GridOK g) : 1 / 3 ≤ xiR g g.N := by
  have hB : (0 : ℝ) < (g.B : ℝ) ^ g.N := pow_pos (by exact_mod_cast hg.hB) _
  unfold xiR
  rw [div_le_div_iff₀ (by norm_num) (by positivity)]
  have := hg.hN
  have : (85 : ℝ) * (g.B : ℝ) ^ g.N ≤ 3 * (g.A : ℝ) ^ g.N := by exact_mod_cast this
  linarith

lemma yR_SY (hg : GridOK g) : 1 / 3 ≤ yR g g.SY := by
  rw [yR_eq hg, le_div_iff₀ (by exact_mod_cast vnum_pos hg _)]
  have : ((vnum g g.SY : ℕ) : ℝ) ≤ 3 * ((vnum g g.SY - vden g g.SY : ℕ) : ℝ) := by exact_mod_cast hg.hSY
  linarith

lemma yR_SH (hg : GridOK g) : 1 / 2 ≤ yR g g.SH := by
  rw [yR_eq hg, le_div_iff₀ (by exact_mod_cast vnum_pos hg _)]
  have : ((vnum g g.SH : ℕ) : ℝ) ≤ 2 * ((vnum g g.SH - vden g g.SH : ℕ) : ℝ) := by exact_mod_cast hg.hSH
  linarith

lemma yR_S3 (hg : GridOK g) : yR g g.S3 ≤ 1 / 3 := by
  rw [yR_eq hg, div_le_iff₀ (by exact_mod_cast vnum_pos hg _)]
  have : 3 * ((vnum g g.S3 - vden g g.S3 : ℕ) : ℝ) ≤ ((vnum g g.S3 : ℕ) : ℝ) := by exact_mod_cast hg.hS3
  linarith

/-! ## The Nat checks -/

lemma yleX_sound (hg : GridOK g) {σ J : ℕ} (h : yleX g σ J = true) : yR g σ ≤ xiR g J := by
  unfold yleX at h
  have h' : ((vnum g σ - vden g σ : ℕ) : ℝ) * (85 * (g.B : ℝ) ^ J) ≤ (g.A : ℝ) ^ J * vnum g σ := by
    exact_mod_cast of_decide_eq_true h
  have h1 : (0 : ℝ) < vnum g σ := by exact_mod_cast vnum_pos hg σ
  have h2 : (0 : ℝ) < 85 * (g.B : ℝ) ^ J := mul_pos (by norm_num) (pow_pos (by exact_mod_cast hg.hB) _)
  rw [yR_eq hg]; unfold xiR
  rw [div_le_div_iff₀ h1 h2]; linarith

lemma gleY_sound (hg : GridOK g) {k t : ℕ} (h : gleY g k t = true) : gR g k ≤ yR g t := by
  unfold gleY at h
  have h' : ((vnum g k - vden g k : ℕ) : ℝ) * vnum g t ≤ ((vnum g t - vden g t : ℕ) : ℝ) * vden g k := by
    exact_mod_cast of_decide_eq_true h
  have h1 : (0 : ℝ) < vnum g t := by exact_mod_cast vnum_pos hg t
  have h2 : (0 : ℝ) < vden g k := by exact_mod_cast vden_pos hg k
  rw [gR_eq hg, yR_eq hg, div_le_div_iff₀ h2 h1]; linarith

lemma findFirst_spec (p : ℕ → Bool) : ∀ (s f : ℕ), (findFirst p s f = s + f ∨ p (findFirst p s f) = true) ∧
    s ≤ findFirst p s f ∧ findFirst p s f ≤ s + f
  | s, 0 => by simp [findFirst]
  | s, f + 1 => by
    unfold findFirst
    split_ifs with h
    · exact ⟨Or.inr h, le_rfl, by omega⟩
    · obtain ⟨h1, h2, h3⟩ := findFirst_spec p (s + 1) f
      refine ⟨?_, by omega, by omega⟩
      rcases h1 with h1 | h1
      · left; omega
      · right; exact h1

lemma JL_spec (hg : GridOK g) (σ : ℕ) : JL g σ = g.N ∨ yR g (σ + 1) ≤ xiR g (JL g σ) := by
  rcases (findFirst_spec (fun J => yleX g (σ + 1) J) 0 g.N).1 with h | h
  · left; unfold JL; simpa using h
  · right; exact yleX_sound hg h

lemma SMT_spec (hg : GridOK g) {k : ℕ} (hk : k < g.SY) : SMT g k = g.SY ∨ gR g k ≤ yR g (SMT g k) := by
  unfold SMT; rw [if_pos hk]
  rcases (findFirst_spec (gleY g k) 0 g.SY).1 with h | h
  · left; simpa using h
  · right; exact gleY_sound hg h

lemma CUT_spec (hg : GridOK g) {k : ℕ} (hk : k ≤ g.SY) :
    (CUT g k = g.SH ∨ (k < g.SY ∧ gR g k ≤ yR g (CUT g k))) ∧ g.S3 ≤ CUT g k ∧ CUT g k ≤ g.SH := by
  unfold CUT
  split_ifs with h
  · obtain ⟨h1, h2, h3⟩ := findFirst_spec (gleY g k) g.S3 (g.SH - g.S3)
    refine ⟨?_, h2, by have := hg.hS3H; omega⟩
    rcases h1 with h1 | h1
    · left; have := hg.hS3H; omega
    · right; exact ⟨h, gleY_sound hg h1⟩
  · exact ⟨Or.inl rfl, hg.hS3H, le_rfl⟩

lemma side_JL0 (hg : GridOK g) : JL g 0 = 0 := by
  have := hg.side; unfold sideOK at this
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact this.1

lemma side_pos (hg : GridOK g) {j : ℕ} (hj : j < g.N) : X1up g j + TOP g j < TT := by
  have := hg.side; unfold sideOK at this
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at this
  exact this.2 j hj

/-! ## Grid cells -/

/-- A point `y ∈ (0, y_t]` lies in some cell `σ < t`. -/
lemma exists_cell (hg : GridOK g) {y : ℝ} {t₀ t : ℕ} (h0 : yR g t₀ < y) (ht : y ≤ yR g t) :
    ∃ σ, t₀ ≤ σ ∧ σ < t ∧ yR g σ ≤ y ∧ y ≤ yR g (σ + 1) := by
  classical
  have hex : ∃ u, y ≤ yR g u := ⟨t, ht⟩
  set u := Nat.find hex with hu
  have hu1 : y ≤ yR g u := Nat.find_spec hex
  have hu2 : u ≤ t := Nat.find_min' hex ht
  have hu0 : t₀ < u := by
    by_contra hc
    push_neg at hc
    have := yR_monotone hg hc
    linarith
  refine ⟨u - 1, by omega, by omega, ?_, by rw [Nat.sub_add_cancel (by omega)]; exact hu1⟩
  have := Nat.find_min hex (show u - 1 < u by omega)
  push_neg at this; exact this.le

lemma cover_x (hg : GridOK g) {j σ : ℕ} {x y : ℝ} (hx1 : xiR g j ≤ x) (hx2 : x ≤ xiR g (j + 1))
    (hy1 : yR g σ ≤ y) (hy2 : y ≤ yR g (σ + 1)) (hy : y < 1) :
    (xiR g (σ / g.M + j) ≤ x / (1 - y) ∧ x / (1 - y) ≤ xiR g (σ / g.M + j + 1)) ∨
      (xiR g (σ / g.M + j + 1) ≤ x / (1 - y) ∧ x / (1 - y) ≤ xiR g (σ / g.M + j + 1 + 1)) := by
  have h1y : 0 < 1 - y := by linarith
  have hv1 := one_le_vR hg σ
  -- 1/(1-y) between v_σ and v_{σ+1}
  have hlo : vR g σ ≤ 1 / (1 - y) := by
    unfold yR at hy1
    rw [le_div_iff₀ h1y]
    have : 1 / vR g σ ≥ 1 - y := by linarith
    rw [ge_iff_le, le_div_iff₀ (by linarith)] at this; linarith
  have hhi : 1 / (1 - y) ≤ vR g (σ + 1) := by
    unfold yR at hy2
    have hv2 := one_le_vR hg (σ + 1)
    rw [div_le_iff₀ h1y]
    have : 1 - y ≥ 1 / vR g (σ + 1) := by linarith
    rw [ge_iff_le, div_le_iff₀ (by linarith)] at this; linarith
  have hx0 : 0 < x := lt_of_lt_of_le (xiR_pos hg j) hx1
  have eq : x / (1 - y) = x * (1 / (1 - y)) := by ring
  have hA : xiR g (σ / g.M + j) ≤ x / (1 - y) := by
    rw [Nat.add_comm, xiR_add hg, eq]
    exact mul_le_mul hx1 (le_trans (vR_lower hg σ) hlo) (pow_pos (by linarith [rho_gt_one hg]) _).le hx0.le
  have hB : x / (1 - y) ≤ xiR g (σ / g.M + j + 1 + 1) := by
    rw [show σ / g.M + j + 1 + 1 = (j + 1) + (σ / g.M + 1) by ring, xiR_add hg, eq]
    exact mul_le_mul hx2 (le_trans hhi (vR_upper hg σ)) (by positivity) (xiR_pos hg _).le
  rcases le_total (x / (1 - y)) (xiR g (σ / g.M + j + 1)) with h | h
  · exact Or.inl ⟨hA, h⟩
  · exact Or.inr ⟨h, hB⟩

/-! ## Semantics of a table -/

/-- `T k j` bounds `G_i(x, c)` on `[ξ_j, ξ_{j+1}]` for `c ≤ γ_k` (any `c` in row `SY`). -/
def Sem (g : Grid) (i : ℕ) (T : ℕ → ℕ → ℕ) : Prop :=
  ∀ k ≤ g.SY, ∀ j, ∀ x, xiR g j ≤ x → x ≤ xiR g (j + 1) → ∀ c, (k < g.SY → c ≤ gR g k) →
    G i x c ≤ ENNReal.ofReal ((T k j : ℝ) / TT)

lemma G_zero_of_large (hg : GridOK g) {i j : ℕ} (hi : 1 ≤ i) (hj : g.N ≤ j) {x c : ℝ} (hx : xiR g j ≤ x) :
    G i x c = 0 :=
  G_eq_zero hi (Or.inl (le_trans (xiR_N hg) (le_trans (xiR_mono hg hj) hx)))

lemma lintegral_sum_indicator (s : Finset ℕ) (a b C : ℕ → ℝ) :
    ∫⁻ y, ∑ σ ∈ s, (Set.Icc (a σ) (b σ)).indicator (fun _ => ENNReal.ofReal (C σ)) y =
      ∑ σ ∈ s, ENNReal.ofReal (C σ) * ENNReal.ofReal (b σ - a σ) := by
  rw [lintegral_finsetSum _ (fun σ _ => (measurable_const.indicator measurableSet_Icc))]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [lintegral_indicator_const measurableSet_Icc, Real.volume_Icc]


lemma vR_zero (hg : GridOK g) : vR g 0 = 1 := by
  rw [vR_formula hg]; simp

lemma one_lt_vR (hg : GridOK g) {σ : ℕ} (hσ : 1 ≤ σ) : 1 < vR g σ := by
  have h1 : 1 < vR g 1 := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, vR_succ hg, vR_zero hg]
    have := rho_gt_one hg
    have hM : (0 : ℝ) < g.M := by exact_mod_cast hg.hM
    have : 0 < rho g ^ (0 / g.M) * (rho g - 1) / g.M := by
      apply div_pos _ hM; apply mul_pos (pow_pos (by linarith) _); linarith
    linarith
  exact lt_of_lt_of_le h1 (vR_monotone hg hσ)

lemma yR_pos (hg : GridOK g) {σ : ℕ} (hσ : 1 ≤ σ) : 0 < yR g σ := by
  have := one_lt_vR hg hσ
  unfold yR
  have : 1 / vR g σ < 1 := by rw [div_lt_one (by linarith)]; exact this
  linarith

lemma yR_lt_one (hg : GridOK g) (σ : ℕ) : yR g σ < 1 := by
  have := one_le_vR hg σ
  unfold yR
  have : 0 < 1 / vR g σ := by positivity
  linarith

lemma inv_one_sub_le (hg : GridOK g) {σ : ℕ} {y : ℝ} (hy2 : y ≤ yR g (σ + 1)) (hy : y < 1) :
    1 / (1 - y) ≤ vR g (σ + 1) := by
  have h1y : 0 < 1 - y := by linarith
  unfold yR at hy2
  have hv2 := one_le_vR hg (σ + 1)
  rw [div_le_iff₀ h1y]
  have : 1 - y ≥ 1 / vR g (σ + 1) := by linarith
  rw [ge_iff_le, div_le_iff₀ (by linarith)] at this; linarith

lemma weight_le (hg : GridOK g) {σ : ℕ} (hσ : 1 ≤ σ) :
    (yR g (σ + 1) - yR g σ) / (yR g σ * (1 - yR g (σ + 1))) ≤ (wt g σ : ℝ) / TT := by
  have hv := one_lt_vR hg hσ
  have hv' := one_lt_vR hg (show 1 ≤ σ + 1 by omega)
  have hB : (0 : ℝ) < g.B := by exact_mod_cast hg.hB
  have hM : (0 : ℝ) < g.M := by exact_mod_cast hg.hM
  have e1 : (yR g (σ + 1) - yR g σ) / (yR g σ * (1 - yR g (σ + 1))) = (vR g (σ + 1) - vR g σ) / (vR g σ - 1) := by
    unfold yR
    have : vR g σ - 1 ≠ 0 := by linarith
    field_simp
    ring
  have hpos : 0 < vnum g σ - vden g σ := by
    have : (vden g σ : ℝ) < vnum g σ := by
      have h0 : (0 : ℝ) < vden g σ := by exact_mod_cast vden_pos hg σ
      have : 1 < (vnum g σ : ℝ) / vden g σ := hv
      rwa [one_lt_div h0] at this
    have : vden g σ < vnum g σ := by exact_mod_cast this
    omega
  have hposR : (0 : ℝ) < ((vnum g σ - vden g σ : ℕ) : ℝ) := by exact_mod_cast hpos
  have e2 : (vR g (σ + 1) - vR g σ) / (vR g σ - 1) = ((g.A ^ (σ / g.M) * (g.A - g.B) : ℕ) : ℝ) / ((vnum g σ - vden g σ : ℕ) : ℝ) := by
    rw [vR_succ hg, add_sub_cancel_left, show vR g σ - 1 = gR g σ from rfl, gR_eq hg, div_div_eq_mul_div]
    have e3 : rho g ^ (σ / g.M) * (rho g - 1) / g.M * (vden g σ : ℝ) = ((g.A ^ (σ / g.M) * (g.A - g.B) : ℕ) : ℝ) := by
      unfold rho vden
      push_cast [Nat.cast_sub hg.hBA.le]
      rw [div_pow]
      field_simp
    rw [e3]
  rw [e1, e2]
  have := cdiv_ge_real (TT * (g.A ^ (σ / g.M) * (g.A - g.B))) hpos
  rw [le_div_iff₀ TT_posR]
  unfold wt
  calc ((g.A ^ (σ / g.M) * (g.A - g.B) : ℕ) : ℝ) / ((vnum g σ - vden g σ : ℕ) : ℝ) * TT
      = ((TT * (g.A ^ (σ / g.M) * (g.A - g.B)) : ℕ) : ℝ) / ((vnum g σ - vden g σ : ℕ) : ℝ) := by
        push_cast; ring
    _ ≤ _ := this

/-! ## The recursion step -/

theorem sem_step (hg : GridOK g) {i : ℕ} (hi : 1 ≤ i) {T T' : ℕ → ℕ → ℕ} (hT : Sem g i T)
    (hT' : ∀ k ≤ g.SY, ∀ j < g.N, ∑ σ ∈ range (SMT g k),
      (if j < JL g σ then cdiv (wt g σ * max (T (σ + 1) (σ / g.M + j)) (T (σ + 1) (σ / g.M + j + 1))) TT else 0) ≤ T' k j) :
    Sem g (i + 1) T' := by
  intro k hk j x hx1 hx2 c hc
  rcases Nat.lt_or_ge j g.N with hj | hj
  swap
  · rw [G_zero_of_large hg (by omega) hj hx1]; exact zero_le
  have hx0 : 0 < x := lt_of_lt_of_le (xiR_pos hg j) hx1
  set Mx : ℕ → ℕ := fun σ => max (T (σ + 1) (σ / g.M + j)) (T (σ + 1) (σ / g.M + j + 1)) with hMx
  set C : ℕ → ℝ := fun σ => 1 / (yR g σ * (1 - yR g (σ + 1))) * ((Mx σ : ℝ) / TT) with hC
  set F := (range (SMT g k)).filter (fun σ => j < JL g σ) with hF
  have hFσ : ∀ σ ∈ F, 1 ≤ σ := by
    intro σ hσ
    simp only [hF, Finset.mem_filter] at hσ
    by_contra h0; push_neg at h0
    have : σ = 0 := by omega
    subst this; rw [side_JL0 hg] at hσ; omega
  refine (G_succ_le hi hx0.le).trans ?_
  have hpt : ∀ y, (Sy x c).indicator (fun y => ENNReal.ofReal (1 / (y * (1 - y))) * G i (x / (1 - y)) (y / (1 - y))) y ≤
      ∑ σ ∈ F, (Set.Icc (yR g σ) (yR g (σ + 1))).indicator (fun _ => ENNReal.ofReal (C σ)) y := by
    intro y
    by_cases hy : y ∈ Sy x c
    swap
    · rw [Set.indicator_of_notMem hy]; exact zero_le
    rw [Set.indicator_of_mem hy]
    obtain ⟨hxy, hy3, hyc⟩ := hy
    have hytop : y ≤ yR g (SMT g k) := by
      by_cases hkS : k < g.SY
      · rcases SMT_spec hg hkS with h | h
        · rw [h]; linarith [yR_SY hg]
        · linarith [hc hkS]
      · have hs : SMT g k = g.SY := by unfold SMT; rw [if_neg hkS]
        rw [hs]; linarith [yR_SY hg]
    have hy0 : yR g 0 < y := by rw [yR_zero hg]; linarith
    obtain ⟨σ, -, hσ, hσ1, hσ2⟩ := exists_cell hg hy0 hytop
    have hjσ : j < JL g σ := by
      by_contra hc'
      push_neg at hc'
      rcases JL_spec hg σ with h | h
      · omega
      · have := xiR_mono hg hc'
        linarith
    have hmem : σ ∈ F := by simp [hF, hσ, hjσ]
    refine le_trans ?_ (Finset.single_le_sum (f := fun σ => (Set.Icc (yR g σ) (yR g (σ + 1))).indicator (fun _ => ENNReal.ofReal (C σ)) y) (fun _ _ => zero_le) hmem)
    show _ ≤ (Set.Icc (yR g σ) (yR g (σ + 1))).indicator (fun _ => ENNReal.ofReal (C σ)) y
    rw [Set.indicator_of_mem (Set.mem_Icc.mpr ⟨hσ1, hσ2⟩)]
    have hσ1' := hFσ σ hmem
    have hya : 0 < yR g σ := yR_pos hg hσ1'
    have hyb : yR g (σ + 1) < 1 := yR_lt_one hg _
    have hy1 : y < 1 := by linarith
    have hσS : σ + 1 ≤ g.SY := le_trans hσ (SMT_le g k)
    -- the `G i` factor
    have hG : G i (x / (1 - y)) (y / (1 - y)) ≤ ENNReal.ofReal ((Mx σ : ℝ) / TT) := by
      have hcap : σ + 1 < g.SY → y / (1 - y) ≤ gR g (σ + 1) := by
        intro _
        have := inv_one_sub_le hg hσ2 hy1
        unfold gR
        have e : y / (1 - y) = 1 / (1 - y) - 1 := by field_simp; ring
        linarith
      rcases cover_x hg hx1 hx2 hσ1 hσ2 hy1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · refine (hT (σ + 1) hσS _ _ h1 h2 _ hcap).trans (ENNReal.ofReal_le_ofReal ?_)
        apply div_le_div_of_nonneg_right _ TT_posR.le
        exact_mod_cast le_max_left _ _
      · refine (hT (σ + 1) hσS _ _ h1 h2 _ hcap).trans (ENNReal.ofReal_le_ofReal ?_)
        apply div_le_div_of_nonneg_right _ TT_posR.le
        exact_mod_cast le_max_right _ _
    have hK : ENNReal.ofReal (1 / (y * (1 - y))) ≤ ENNReal.ofReal (1 / (yR g σ * (1 - yR g (σ + 1)))) := by
      apply ENNReal.ofReal_le_ofReal
      apply one_div_le_one_div_of_le (mul_pos hya (by linarith))
      exact mul_le_mul hσ1 (by linarith) (by linarith) (by linarith)
    calc ENNReal.ofReal (1 / (y * (1 - y))) * G i (x / (1 - y)) (y / (1 - y))
        ≤ ENNReal.ofReal (1 / (yR g σ * (1 - yR g (σ + 1)))) * ENNReal.ofReal ((Mx σ : ℝ) / TT) := mul_le_mul' hK hG
      _ = ENNReal.ofReal (C σ) := by
        rw [← ENNReal.ofReal_mul (by apply div_nonneg zero_le_one; exact (mul_pos hya (by linarith)).le)]
  calc ∫⁻ y, (Sy x c).indicator (fun y => ENNReal.ofReal (1 / (y * (1 - y))) * G i (x / (1 - y)) (y / (1 - y))) y
      ≤ ∫⁻ y, ∑ σ ∈ F, (Set.Icc (yR g σ) (yR g (σ + 1))).indicator (fun _ => ENNReal.ofReal (C σ)) y := lintegral_mono hpt
    _ = ∑ σ ∈ F, ENNReal.ofReal (C σ) * ENNReal.ofReal (yR g (σ + 1) - yR g σ) := lintegral_sum_indicator _ _ _ _
    _ ≤ ENNReal.ofReal ((T' k j : ℝ) / TT) := by
      have hCn : ∀ σ ∈ F, 0 ≤ C σ := by
        intro σ hσ
        have := yR_pos hg (hFσ σ hσ); have := yR_lt_one hg (σ + 1)
        simp only [hC]
        apply mul_nonneg (div_nonneg zero_le_one (mul_pos (by assumption) (by linarith)).le) (div_nonneg (by positivity) TT_posR.le)
      rw [Finset.sum_congr rfl (fun σ hσ => (ENNReal.ofReal_mul (hCn σ hσ)).symm),
        ← ENNReal.ofReal_sum_of_nonneg (fun σ hσ => mul_nonneg (hCn σ hσ) (by linarith [yR_monotone hg (Nat.le_succ σ)]))]
      apply ENNReal.ofReal_le_ofReal
      have hterm : ∀ σ ∈ F, C σ * (yR g (σ + 1) - yR g σ) ≤ ((cdiv (wt g σ * Mx σ) TT : ℕ) : ℝ) / TT := by
        intro σ hσ
        have hσ1 := hFσ σ hσ
        have hw := weight_le hg hσ1
        have hya := yR_pos hg hσ1; have hyb := yR_lt_one hg (σ + 1)
        have hMx0 : (0 : ℝ) ≤ (Mx σ : ℝ) / TT := div_nonneg (by positivity) TT_posR.le
        calc C σ * (yR g (σ + 1) - yR g σ)
            = (yR g (σ + 1) - yR g σ) / (yR g σ * (1 - yR g (σ + 1))) * ((Mx σ : ℝ) / TT) := by simp only [hC]; ring
          _ ≤ (wt g σ : ℝ) / TT * ((Mx σ : ℝ) / TT) := mul_le_mul_of_nonneg_right hw hMx0
          _ = (((wt g σ * Mx σ : ℕ) : ℝ) / TT) / TT := by push_cast; ring
          _ ≤ _ := div_le_div_of_nonneg_right (cdiv_ge_real _ TT_pos) TT_posR.le
      calc ∑ σ ∈ F, C σ * (yR g (σ + 1) - yR g σ) ≤ ∑ σ ∈ F, ((cdiv (wt g σ * Mx σ) TT : ℕ) : ℝ) / TT := Finset.sum_le_sum hterm
        _ = ((∑ σ ∈ range (SMT g k), (if j < JL g σ then cdiv (wt g σ * Mx σ) TT else 0) : ℕ) : ℝ) / TT := by
          rw [← Finset.sum_div, hF, Finset.sum_filter]; push_cast; rfl
        _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast hT' k hk j hj) TT_posR.le


/-! ## The base level -/

lemma X1up_ge (hg : GridOK g) (j : ℕ) : xiR g (j + 1) ≤ (X1up g j : ℝ) / TT := by
  have hB : (0 : ℝ) < (85 * g.B ^ (j + 1) : ℕ) := by exact_mod_cast Nat.mul_pos (by norm_num) (pow_pos hg.hB _)
  have := cdiv_ge_real (TT * g.A ^ (j + 1)) (show 0 < 85 * g.B ^ (j + 1) from Nat.mul_pos (by norm_num) (pow_pos hg.hB _))
  unfold X1up
  rw [le_div_iff₀ TT_posR]
  refine le_trans (le_of_eq ?_) this
  unfold xiR; push_cast; ring

lemma X0dn_le (hg : GridOK g) (j : ℕ) : (X0dn g j : ℝ) / TT ≤ xiR g j := by
  have h := div_le_real (TT * g.A ^ j) (85 * g.B ^ j)
  unfold X0dn
  rw [div_le_iff₀ TT_posR]
  refine le_trans h (le_of_eq ?_)
  unfold xiR; push_cast; ring

lemma TOP_ge (hg : GridOK g) (j : ℕ) : (1 - xiR g j) / 2 ≤ (TOP g j : ℝ) / TT := by
  have h1 := cdiv_ge_real (TT - X0dn g j) (show 0 < 2 by norm_num)
  have h2 := cast_sub_ge TT (X0dn g j)
  have h3 := X0dn_le hg j
  unfold TOP
  rw [le_div_iff₀ TT_posR]
  have : (X0dn g j : ℝ) ≤ xiR g j * TT := by rwa [div_le_iff₀ TT_posR] at h3
  push_cast at h1
  nlinarith [TT_posR]

lemma YDN_le (hg : GridOK g) (σ : ℕ) : (YDN g σ : ℝ) / TT ≤ yR g σ := by
  have h := div_le_real (TT * (vnum g σ - vden g σ)) (vnum g σ)
  unfold YDN
  rw [div_le_iff₀ TT_posR, yR_eq hg]
  refine le_trans h (le_of_eq ?_)
  push_cast; ring

lemma YUP_ge (hg : GridOK g) (σ : ℕ) : yR g σ ≤ (YUP g σ : ℝ) / TT := by
  have h := cdiv_ge_real (TT * (vnum g σ - vden g σ)) (vnum_pos hg σ)
  unfold YUP
  rw [le_div_iff₀ TT_posR, yR_eq hg]
  refine le_trans (le_of_eq ?_) h
  push_cast; ring

lemma THIRD_le : (THIRD : ℝ) / TT ≤ 1 / 3 := by
  have h := div_le_real TT 3
  unfold THIRD
  rw [div_le_iff₀ TT_posR]
  push_cast at h ⊢; linarith

lemma THIRD_pos : 0 < THIRD := by unfold THIRD TT PP; norm_num

theorem sem_base (hg : GridOK g) {T : ℕ → ℕ → ℕ}
    (hT : ∀ k ≤ g.SY, ∀ j < g.N, ∑ u ∈ range (CUT g k - g.S3),
      bterm (X1up g j) (TOP g j) (YDN g (g.S3 + u)) (YUP g (g.S3 + u + 1)) ≤ T k j) :
    Sem g 1 T := by
  intro k hk j x hx1 hx2 c hc
  rcases Nat.lt_or_ge j g.N with hj | hj
  swap
  · rw [G_zero_of_large hg le_rfl hj hx1]; exact zero_le
  have hx0 : 0 < x := lt_of_lt_of_le (xiR_pos hg j) hx1
  set x1 := X1up g j
  set top := TOP g j
  have hside := side_pos hg hj
  -- per-cell data
  set lo : ℕ → ℕ := fun u => max (YDN g (g.S3 + u)) THIRD with hlo
  set hi : ℕ → ℕ := fun u => min (YUP g (g.S3 + u + 1)) top with hhi
  set D : ℕ → ℕ := fun u => TT - x1 - hi u with hD
  set F := (range (CUT g k - g.S3)).filter (fun u => ¬ top ≤ YDN g (g.S3 + u)) with hF
  set C : ℕ → ℝ := fun u => (TT : ℝ) * TT / ((lo u : ℝ) * (D u : ℝ)) with hC
  have hlo_pos : ∀ u, (0 : ℝ) < lo u := fun u => by
    simp only [hlo]; exact_mod_cast lt_of_lt_of_le THIRD_pos (le_max_right _ _)
  have hD_eq : ∀ u, ((D u : ℕ) : ℝ) = TT - x1 - hi u := by
    intro u
    have : hi u ≤ top := min_le_right _ _
    simp only [hD]; rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  have hD_posN : ∀ u, 0 < D u := by
    intro u
    have : hi u ≤ top := min_le_right _ _
    simp only [hD]; omega
  have hD_pos : ∀ u, (0 : ℝ) < D u := fun u => by exact_mod_cast hD_posN u
  have hlo_posN : ∀ u, 0 < lo u := fun u => lt_of_lt_of_le THIRD_pos (le_max_right _ _)
  refine (G_one_le hx0.le).trans ?_
  have hpt : ∀ z, (S1 x c).indicator (fun z => ENNReal.ofReal (1 / (z * (1 - x - z)))) z ≤
      ∑ u ∈ F, (Set.Icc ((lo u : ℝ) / TT) ((hi u : ℝ) / TT)).indicator (fun _ => ENNReal.ofReal (C u)) z := by
    intro z
    by_cases hz : z ∈ S1 x c
    swap
    · rw [Set.indicator_of_notMem hz]; exact zero_le
    rw [Set.indicator_of_mem hz]
    obtain ⟨hz1, hz2, hz3⟩ := hz
    have hztop : z ≤ yR g (CUT g k) := by
      rcases (CUT_spec hg hk).1 with h | ⟨hkS, h⟩
      · rw [h]; linarith [yR_SH hg]
      · linarith [hc hkS]
    have hz0 : yR g g.S3 < z := by linarith [yR_S3 hg]
    obtain ⟨σ, hσ0, hσ, hσ1, hσ2⟩ := exists_cell hg hz0 hztop
    set u := σ - g.S3 with hu
    have hσu : σ = g.S3 + u := by omega
    have hTOP := TOP_ge hg j
    have hYD := YDN_le hg σ
    have hYU := YUP_ge hg (σ + 1)
    have hnot : ¬ top ≤ YDN g (g.S3 + u) := by
      rw [← hσu]
      intro h
      have : (top : ℝ) ≤ YDN g σ := by exact_mod_cast h
      have : (top : ℝ) / TT ≤ (YDN g σ : ℝ) / TT := div_le_div_of_nonneg_right this TT_posR.le
      have : (1 - xiR g j) / 2 ≤ (1 - x) / 2 := by linarith
      linarith
    have hmem : u ∈ F := by
      simp only [hF, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hnot⟩
    refine le_trans ?_ (Finset.single_le_sum (f := fun u => (Set.Icc ((lo u : ℝ) / TT) ((hi u : ℝ) / TT)).indicator (fun _ => ENNReal.ofReal (C u)) z) (fun _ _ => zero_le) hmem)
    have hzlo : (lo u : ℝ) / TT ≤ z := by
      simp only [hlo]
      rw [← hσu]
      rcases le_total (YDN g σ) THIRD with h | h
      · rw [max_eq_right h]; linarith [THIRD_le]
      · rw [max_eq_left h]; linarith
    have hzhi : z ≤ (hi u : ℝ) / TT := by
      simp only [hhi]
      rw [show g.S3 + u + 1 = σ + 1 by omega]
      rcases le_total (YUP g (σ + 1)) top with h | h
      · rw [min_eq_left h]; linarith
      · rw [min_eq_right h]; linarith
    show _ ≤ (Set.Icc ((lo u : ℝ) / TT) ((hi u : ℝ) / TT)).indicator (fun _ => ENNReal.ofReal (C u)) z
    rw [Set.indicator_of_mem (Set.mem_Icc.mpr ⟨hzlo, hzhi⟩)]
    apply ENNReal.ofReal_le_ofReal
    have hx1' : x ≤ (x1 : ℝ) / TT := le_trans hx2 (X1up_ge hg j)
    have hzpos : 0 < z := lt_of_lt_of_le (div_pos (hlo_pos u) TT_posR) hzlo
    have hden : (lo u : ℝ) / TT * ((D u : ℝ) / TT) ≤ z * (1 - x - z) := by
      rw [hD_eq]
      have : ((TT : ℝ) - x1 - hi u) / TT ≤ 1 - x - z := by
        rw [div_le_iff₀ TT_posR]
        have := (le_div_iff₀ TT_posR).mp hzhi
        have := (le_div_iff₀ TT_posR).mp hx1'
        nlinarith
      have h0 : 0 ≤ ((TT : ℝ) - x1 - hi u) / TT := by rw [← hD_eq]; exact div_nonneg (hD_pos u).le TT_posR.le
      exact mul_le_mul hzlo this h0 hzpos.le
    have hpos : 0 < (lo u : ℝ) / TT * ((D u : ℝ) / TT) := mul_pos (div_pos (hlo_pos u) TT_posR) (div_pos (hD_pos u) TT_posR)
    calc 1 / (z * (1 - x - z)) ≤ 1 / ((lo u : ℝ) / TT * ((D u : ℝ) / TT)) := one_div_le_one_div_of_le hpos hden
      _ = C u := by simp only [hC]; field_simp
  calc ∫⁻ z, (S1 x c).indicator (fun z => ENNReal.ofReal (1 / (z * (1 - x - z)))) z
      ≤ ∫⁻ z, ∑ u ∈ F, (Set.Icc ((lo u : ℝ) / TT) ((hi u : ℝ) / TT)).indicator (fun _ => ENNReal.ofReal (C u)) z := lintegral_mono hpt
    _ = ∑ u ∈ F, ENNReal.ofReal (C u) * ENNReal.ofReal ((hi u : ℝ) / TT - (lo u : ℝ) / TT) := lintegral_sum_indicator _ _ _ _
    _ ≤ ∑ u ∈ F, ENNReal.ofReal ((bterm x1 top (YDN g (g.S3 + u)) (YUP g (g.S3 + u + 1)) : ℝ) / TT) := by
      refine Finset.sum_le_sum fun u hu => ?_
      have hnot : ¬ top ≤ YDN g (g.S3 + u) := (Finset.mem_filter.mp hu).2
      have hC0 : 0 ≤ C u := by simp only [hC]; exact div_nonneg (by positivity) (mul_pos (hlo_pos u) (hD_pos u)).le
      rw [← ENNReal.ofReal_mul hC0]
      apply ENNReal.ofReal_le_ofReal
      unfold bterm
      rw [if_neg hnot]
      have hsub := cast_sub_ge (hi u) (lo u)
      change C u * ((hi u : ℝ) / TT - (lo u : ℝ) / TT) ≤ ((cdiv (TT * TT * (hi u - lo u)) (lo u * D u) : ℕ) : ℝ) / TT
      have hb' := cdiv_ge_real (TT * TT * (hi u - lo u)) (Nat.mul_pos (hlo_posN u) (hD_posN u))
      have hLD : (0 : ℝ) < (lo u : ℝ) * (D u : ℝ) := mul_pos (hlo_pos u) (hD_pos u)
      have key : C u * ((hi u : ℝ) / TT - (lo u : ℝ) / TT) ≤ ((TT * TT * (hi u - lo u) : ℕ) : ℝ) / ((lo u * D u : ℕ) : ℝ) / TT := by
        simp only [hC]
        have e : (TT : ℝ) * TT / ((lo u : ℝ) * (D u : ℝ)) * ((hi u : ℝ) / TT - (lo u : ℝ) / TT) = TT * ((hi u : ℝ) - lo u) / ((lo u : ℝ) * (D u : ℝ)) := by
          field_simp
        have e2 : ((TT * TT * (hi u - lo u) : ℕ) : ℝ) / ((lo u * D u : ℕ) : ℝ) / TT = TT * ((hi u - lo u : ℕ) : ℝ) / ((lo u : ℝ) * (D u : ℝ)) := by
          push_cast; field_simp
        rw [e, e2]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsub TT_posR.le) hLD.le
      exact key.trans (div_le_div_of_nonneg_right hb' TT_posR.le)
    _ ≤ ENNReal.ofReal ((T k j : ℝ) / TT) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun u _ => div_nonneg (by positivity) TT_posR.le)]
      apply ENNReal.ofReal_le_ofReal
      rw [← Finset.sum_div]
      apply div_le_div_of_nonneg_right _ TT_posR.le
      have := hT k hk j hj
      calc ∑ u ∈ F, ((bterm x1 top (YDN g (g.S3 + u)) (YUP g (g.S3 + u + 1)) : ℕ) : ℝ)
          ≤ ∑ u ∈ range (CUT g k - g.S3), ((bterm x1 top (YDN g (g.S3 + u)) (YUP g (g.S3 + u + 1)) : ℕ) : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
        _ ≤ _ := by exact_mod_cast this

end KappaOmega2.M12
