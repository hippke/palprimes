import Palprimes.MainTerm.JR

/-! # The simplex measure `δ(Σ z − c) dz` and its permutation symmetry

* `zvec c w = (w, c − Σ w)`: the chart of the hyperplane `Σ z = c` by its first `n` coordinates
  (Greaves eliminates one variable through (5.8));
* `smeas c n = (zvec c)_* Lebesgue` on `Fin (n + 1) → ℝ`;
* `smeas_perm`: `smeas` is invariant under every permutation of the `n + 1` coordinates
  (this is what makes Greaves' interleaving identity (5.11) work, "ties have measure zero");
* `ae_injective_smeas`: ties have measure zero;
* `integral_sort`: for an invariant measure without ties,
  `∫ g = ∫ [y strictly decreasing] Σ_σ g(y ∘ σ)`. -/

set_option linter.style.longLine false

open MeasureTheory Finset Real Filter

namespace Palprimes.MT

/-! ## The chart -/

/-- `(w, c − Σ w)`. -/
noncomputable def zvec {n : ℕ} (c : ℝ) (w : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.snoc w (c - ∑ i, w i)

@[simp] lemma zvec_castSucc {n : ℕ} (c : ℝ) (w : Fin n → ℝ) (i : Fin n) :
    zvec c w i.castSucc = w i := by simp [zvec]

@[simp] lemma zvec_last {n : ℕ} (c : ℝ) (w : Fin n → ℝ) : zvec c w (Fin.last n) = c - ∑ i, w i := by
  simp [zvec]

lemma sum_zvec {n : ℕ} (c : ℝ) (w : Fin n → ℝ) : ∑ i, zvec c w i = c := by
  rw [Fin.sum_univ_castSucc]; simp

lemma prod_zvec {n : ℕ} (c : ℝ) (w : Fin n → ℝ) : ∏ i, zvec c w i = (∏ i, w i) * (c - ∑ i, w i) := by
  rw [Fin.prod_univ_castSucc]; simp

lemma init_zvec {n : ℕ} (c : ℝ) (w : Fin n → ℝ) : Fin.init (zvec c w) = w := by
  simp [zvec]

lemma measurable_zvec {n : ℕ} (c : ℝ) : Measurable (zvec (n := n) c) := by
  refine measurable_pi_iff.mpr fun i => ?_
  induction i using Fin.lastCases with
  | last => simp only [zvec_last]; fun_prop
  | cast j => simp only [zvec_castSucc]; exact measurable_pi_apply j

lemma range_zvec {n : ℕ} (c : ℝ) : Set.range (zvec (n := n) c) = {y | ∑ i, y i = c} := by
  ext y
  constructor
  · rintro ⟨w, rfl⟩; exact sum_zvec c w
  · intro hy
    refine ⟨Fin.init y, ?_⟩
    funext i
    induction i using Fin.lastCases with
    | last =>
      simp only [zvec_last]
      have : ∑ i, y i = ∑ i : Fin n, y i.castSucc + y (Fin.last n) := Fin.sum_univ_castSucc y
      simp only [Set.mem_setOf_eq] at hy
      simp only [Fin.init]
      linarith
    | cast j => simp [Fin.init]

lemma measurableEmbedding_zvec {n : ℕ} (c : ℝ) : MeasurableEmbedding (zvec (n := n) c) := by
  refine MeasurableEmbedding.of_measurable_inverse (measurable_zvec c) ?_ (g := Fin.init) ?_ ?_
  · rw [range_zvec]
    exact (measurableSet_singleton c).preimage (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)
  · exact measurable_pi_iff.mpr fun i => measurable_pi_apply _
  · intro w; exact init_zvec c w

/-- The simplex measure on `Fin (n + 1) → ℝ`. -/
noncomputable def smeas (c : ℝ) (n : ℕ) : Measure (Fin (n + 1) → ℝ) := Measure.map (zvec c) volume

lemma integral_smeas {n : ℕ} (c : ℝ) (g : (Fin (n + 1) → ℝ) → ℝ) :
    ∫ y, g y ∂(smeas c n) = ∫ w, g (zvec c w) :=
  (measurableEmbedding_zvec c).integral_map g

lemma integrable_smeas_iff {n : ℕ} (c : ℝ) {g : (Fin (n + 1) → ℝ) → ℝ} :
    Integrable g (smeas c n) ↔ Integrable (fun w => g (zvec c w)) :=
  (measurableEmbedding_zvec c).integrable_map_iff

lemma ae_smeas_sum {n : ℕ} (c : ℝ) : ∀ᵐ y ∂(smeas c n), ∑ i, y i = c := by
  rw [smeas, (measurableEmbedding_zvec c).ae_map_iff]
  exact ae_of_all _ fun w => sum_zvec c w

/-! ## Permutations of coordinates -/

/-- `y ↦ y ∘ σ` as a measurable equivalence. -/
def permE {N : ℕ} (σ : Equiv.Perm (Fin N)) : (Fin N → ℝ) ≃ᵐ (Fin N → ℝ) where
  toFun y := y ∘ σ
  invFun y := y ∘ σ.symm
  left_inv y := by funext i; simp
  right_inv y := by funext i; simp
  measurable_toFun := measurable_pi_iff.mpr fun i => measurable_pi_apply _
  measurable_invFun := measurable_pi_iff.mpr fun i => measurable_pi_apply _

@[simp] lemma permE_apply {N : ℕ} (σ : Equiv.Perm (Fin N)) (y : Fin N → ℝ) : permE σ y = y ∘ σ := rfl

lemma permE_mul {N : ℕ} (σ τ : Equiv.Perm (Fin N)) : ⇑(permE (σ * τ)) = permE τ ∘ permE σ := by
  funext y; rfl

lemma measurePreserving_permE_volume {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    MeasurePreserving (permE σ) volume volume := by
  have h := volume_measurePreserving_piCongrLeft (fun _ : Fin N => ℝ) σ.symm
  convert h using 1
  funext y j
  have := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin N => ℝ) σ.symm y (σ j)
  simp only [Equiv.symm_apply_apply] at this
  rw [this]; rfl

/-- A permutation fixing the last coordinate acts on the chart by a permutation of `w`. -/
lemma permE_zvec_of_fix {n : ℕ} (c : ℝ) {σ : Equiv.Perm (Fin (n + 1))} (hσ : σ (Fin.last n) = Fin.last n) :
    ∃ τ : Equiv.Perm (Fin n), ∀ w, permE σ (zvec c w) = zvec c (permE τ w) := by
  have hσ' : σ.symm (Fin.last n) = Fin.last n := by rw [Equiv.symm_apply_eq]; exact hσ.symm
  have hne : ∀ i : Fin n, σ i.castSucc ≠ Fin.last n := fun i h => by
    rw [← hσ] at h; exact Fin.castSucc_ne_last i (σ.injective h)
  have hne' : ∀ i : Fin n, σ.symm i.castSucc ≠ Fin.last n := fun i h => by
    rw [← hσ'] at h; exact Fin.castSucc_ne_last i (σ.symm.injective h)
  let τ : Equiv.Perm (Fin n) :=
    { toFun := fun i => (σ i.castSucc).castPred (hne i)
      invFun := fun i => (σ.symm i.castSucc).castPred (hne' i)
      left_inv := fun i => by simp
      right_inv := fun i => by simp }
  refine ⟨τ, fun w => ?_⟩
  funext i
  induction i using Fin.lastCases with
  | last =>
    simp only [permE_apply, Function.comp, hσ, zvec_last]
    congr 1
    exact (Equiv.sum_comp τ w).symm
  | cast j =>
    simp only [permE_apply, Function.comp, zvec_castSucc]
    have : σ j.castSucc = (τ j).castSucc := by simp [τ]
    rw [this, zvec_castSucc]

/-- The swap of the last two coordinates in the chart. -/
noncomputable def swapW {m : ℕ} (c : ℝ) (w : Fin (m + 1) → ℝ) : Fin (m + 1) → ℝ :=
  Fin.snoc (Fin.init w) (c - ∑ i, w i)

lemma swapW_involutive {m : ℕ} (c : ℝ) : Function.Involutive (swapW (m := m) c) := by
  intro w
  have hs : ∑ i, w i = ∑ i : Fin m, Fin.init w i + w (Fin.last m) := by
    rw [Fin.sum_univ_castSucc]; rfl
  funext i
  induction i using Fin.lastCases with
  | last =>
    simp only [swapW, Fin.snoc_last, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.init_snoc]
    simp only [Fin.init] at hs ⊢
    linarith
  | cast j => simp [swapW, Fin.init]

lemma measurable_swapW {m : ℕ} (c : ℝ) : Measurable (swapW (m := m) c) := by
  refine measurable_pi_iff.mpr fun i => ?_
  induction i using Fin.lastCases with
  | last => simp only [swapW, Fin.snoc_last]; fun_prop
  | cast j => simp only [swapW, Fin.snoc_castSucc, Fin.init]; exact measurable_pi_apply _

lemma measurePreserving_swapW {m : ℕ} (c : ℝ) :
    MeasurePreserving (swapW (m := m) c) volume volume := by
  -- split off the last coordinate
  let E := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m)
  have hE : MeasurePreserving E volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m)
  -- the map in the split coordinates
  let T : (Fin m → ℝ) × ℝ → (Fin m → ℝ) × ℝ := fun p => (p.1, (c - ∑ i, p.1 i) - p.2)
  have hT : MeasurePreserving T (volume.prod volume) (volume.prod volume) := by
    refine (MeasurePreserving.id volume).skew_product (g := fun (v : Fin m → ℝ) (y : ℝ) => (c - ∑ i, v i) - y) ?_ ?_
    · have : Measurable (fun p : (Fin m → ℝ) × ℝ => (c - ∑ i, p.1 i) - p.2) := by fun_prop
      exact this
    · exact ae_of_all _ fun v => (volume.measurePreserving_sub_left (c - ∑ i, v i)).map_eq
  let S : ℝ × (Fin m → ℝ) → ℝ × (Fin m → ℝ) := Prod.swap ∘ T ∘ Prod.swap
  have hS : MeasurePreserving S volume volume := by
    have h1 : MeasurePreserving (Prod.swap : ℝ × (Fin m → ℝ) → _) (volume.prod volume) (volume.prod volume) :=
      Measure.measurePreserving_swap
    have h2 : MeasurePreserving (Prod.swap : (Fin m → ℝ) × ℝ → _) (volume.prod volume) (volume.prod volume) :=
      Measure.measurePreserving_swap
    exact h2.comp (hT.comp h1)
  have hcomp : swapW (m := m) c = E.symm ∘ S ∘ E := by
    funext w
    apply E.injective
    simp only [Function.comp, MeasurableEquiv.apply_symm_apply]
    simp only [E, S, T, MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv,
      Prod.swap, swapW]
    ext i
    · simp [Fin.sum_univ_castSucc, Fin.init]; ring
    · simp [Fin.init]
  rw [hcomp]
  exact hE.symm.comp (hS.comp hE)

lemma permE_zvec_swap {m : ℕ} (c : ℝ) (w : Fin (m + 1) → ℝ) :
    permE (Equiv.swap (Fin.last m).castSucc (Fin.last (m + 1))) (zvec c w) = zvec c (swapW c w) := by
  have hs : ∑ i, w i = ∑ i : Fin m, w i.castSucc + w (Fin.last m) := Fin.sum_univ_castSucc w
  funext i
  simp only [permE_apply, Function.comp]
  induction i using Fin.lastCases with
  | last =>
    rw [Equiv.swap_apply_right, zvec_castSucc, zvec_last]
    simp only [swapW, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, Fin.init]
    linarith
  | cast j =>
    induction j using Fin.lastCases with
    | last =>
      rw [Equiv.swap_apply_left, zvec_last, zvec_castSucc]
      simp [swapW]
    | cast k =>
      rw [Equiv.swap_apply_of_ne_of_ne (fun h => by have := congrArg Fin.val h; simp at this; omega)
        (Fin.castSucc_ne_last _)]
      simp [swapW, Fin.init]

lemma smeas_map_of_conj {n : ℕ} (c : ℝ) (σ : Equiv.Perm (Fin (n + 1))) {φ : (Fin n → ℝ) → (Fin n → ℝ)}
    (hφ : MeasurePreserving φ volume volume) (h : ∀ w, permE σ (zvec c w) = zvec c (φ w)) :
    MeasurePreserving (permE σ) (smeas c n) (smeas c n) := by
  refine ⟨(permE σ).measurable, ?_⟩
  rw [smeas, Measure.map_map (permE σ).measurable (measurable_zvec c)]
  have : ⇑(permE σ) ∘ zvec c = zvec c ∘ φ := funext h
  rw [this, ← Measure.map_map (measurable_zvec c) hφ.measurable, hφ.map_eq]

/-- Invariance of the simplex measure under all coordinate permutations. -/
theorem smeas_perm {n : ℕ} (c : ℝ) (σ : Equiv.Perm (Fin (n + 1))) :
    MeasurePreserving (permE σ) (smeas c n) (smeas c n) := by
  have hfix : ∀ ρ : Equiv.Perm (Fin (n + 1)), ρ (Fin.last n) = Fin.last n →
      MeasurePreserving (permE ρ) (smeas c n) (smeas c n) := by
    intro ρ hρ
    obtain ⟨τ, hτ⟩ := permE_zvec_of_fix c hρ
    exact smeas_map_of_conj c ρ (measurePreserving_permE_volume τ) hτ
  by_cases hσ : σ (Fin.last n) = Fin.last n
  · exact hfix σ hσ
  rcases n with _ | m
  · exfalso; apply hσ
    exact Fin.ext (by have := (σ (Fin.last 0)).isLt; simp only [Fin.val_last]; omega)
  set p : Fin (m + 2) := (Fin.last m).castSucc
  set q : Fin (m + 2) := Fin.last (m + 1)
  set a := σ q
  have ha : a ≠ q := hσ
  have hpq : p ≠ q := Fin.castSucc_ne_last _
  let sw := Equiv.swap p q
  let ρ := Equiv.swap a p
  have hρq : ρ q = q := Equiv.swap_apply_of_ne_of_ne (Ne.symm ha) (Ne.symm hpq)
  let pp := sw * ρ * σ
  have hπ : pp q = q := by
    simp only [pp, Equiv.Perm.coe_mul, Function.comp]
    show sw (ρ a) = q
    rw [show ρ a = p from Equiv.swap_apply_left a p]
    exact Equiv.swap_apply_left p q
  have hσeq : σ = ρ * sw * pp := by
    simp only [pp, ← mul_assoc]
    rw [mul_assoc ρ sw sw, Equiv.swap_mul_self, mul_one, Equiv.swap_mul_self, one_mul]
  have hsw : MeasurePreserving (permE sw) (smeas c (m + 1)) (smeas c (m + 1)) :=
    smeas_map_of_conj c sw (measurePreserving_swapW c) (permE_zvec_swap c)
  rw [hσeq, permE_mul, permE_mul]
  exact (hfix pp hπ).comp (hsw.comp (hfix ρ hρq))

/-! ## Ties have measure zero -/

lemma volume_zvec_eq_null {n : ℕ} (c : ℝ) {i j : Fin (n + 1)} (hij : i ≠ j) :
    volume {w : Fin n → ℝ | zvec c w i = zvec c w j} = 0 := by
  -- generic level-set lemma for two coordinates
  have hcoord : ∀ i' j' : Fin n, i' ≠ j' → volume {w : Fin n → ℝ | w i' = w j'} = 0 := by
    intro i' j' hne
    let L : (Fin n → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i' -
      LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j'
    have hL : L ≠ 0 := by
      intro h
      have := LinearMap.congr_fun h (Pi.single i' 1)
      simp [L, Pi.single_apply, hne.symm] at this
    have := volume_linear_level_null L hL 0
    convert this using 2
    simp [L, sub_eq_zero]
  have hlast : ∀ i' : Fin n, volume {w : Fin n → ℝ | w i' = c - ∑ k, w k} = 0 := by
    intro i'
    have : {w : Fin n → ℝ | w i' = c - ∑ k, w k} = {w | ∑ j, w j + w i' = c} := by
      ext w; simp only [Set.mem_setOf_eq]; constructor <;> intro h <;> linarith
    rw [this]; exact volume_sum_add_level_null i' c
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => exact absurd rfl hij
    | cast j' =>
      simp only [zvec_last, zvec_castSucc]
      have : {w : Fin n → ℝ | c - ∑ i, w i = w j'} = {w | w j' = c - ∑ k, w k} := by
        ext w; simp only [Set.mem_setOf_eq]; exact eq_comm
      rw [this]; exact hlast j'
  | cast i' =>
    induction j using Fin.lastCases with
    | last =>
      simp only [zvec_last, zvec_castSucc]
      exact hlast i'
    | cast j' =>
      simp only [zvec_castSucc]
      exact hcoord i' j' (fun h => hij (by rw [h]))

lemma ae_injective_smeas {n : ℕ} (c : ℝ) : ∀ᵐ y ∂(smeas c n), Function.Injective y := by
  rw [smeas, (measurableEmbedding_zvec c).ae_map_iff, ae_iff]
  refine measure_mono_null (t := ⋃ i : Fin (n + 1), ⋃ j : Fin (n + 1), ⋃ (_ : i ≠ j),
    {w : Fin n → ℝ | zvec c w i = zvec c w j}) ?_ ?_
  · intro w hw
    simp only [Set.mem_setOf_eq, Function.Injective, not_forall] at hw
    obtain ⟨i, j, h, hne⟩ := hw
    simp only [Set.mem_iUnion]
    exact ⟨i, j, hne, h⟩
  · exact measure_iUnion_null fun i => measure_iUnion_null fun j =>
      measure_iUnion_null fun hij => volume_zvec_eq_null c hij

/-! ## Sorting -/

lemma card_sort_eq_one {N : ℕ} {y : Fin N → ℝ} (hy : Function.Injective y) :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin N) => StrictAnti (y ∘ σ)).card = 1 := by
  classical
  let f : Fin N → ℝᵒᵈ := fun i => OrderDual.toDual (y i)
  let σ0 := Tuple.sort f
  have hmono : Monotone (f ∘ σ0) := Tuple.monotone_sort f
  have hanti : StrictAnti (y ∘ σ0) := by
    have : Antitone (y ∘ σ0) := fun i j hij => hmono hij
    exact this.strictAnti_of_injective (hy.comp σ0.injective)
  rw [Finset.card_eq_one]
  refine ⟨σ0, ?_⟩
  ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hσ
    have h1 : Monotone (f ∘ σ) := fun i j hij => hσ.antitone hij
    have := Tuple.unique_monotone h1 hmono
    ext i
    have hi := congrFun this i
    simp only [Function.comp, f, OrderDual.toDual_inj] at hi
    exact congrArg Fin.val (hy hi)
  · rintro rfl; exact hanti

/-- Symmetrisation: integrate only over the sorted cone, summing over all permutations. -/
theorem integral_sort {N : ℕ} (μ : Measure (Fin N → ℝ)) (hμ : ∀ σ, MeasurePreserving (permE σ) μ μ)
    (hinj : ∀ᵐ y ∂μ, Function.Injective y) {g : (Fin N → ℝ) → ℝ} (hg : Integrable g μ) :
    ∫ y, g y ∂μ = ∫ y, (open Classical in if StrictAnti y then ∑ σ : Equiv.Perm (Fin N), g (y ∘ σ) else 0) ∂μ := by
  classical
  have hmeas : ∀ σ : Equiv.Perm (Fin N), MeasurableSet {y : Fin N → ℝ | StrictAnti (y ∘ σ)} := fun σ =>
    measurableSet_setOfPred.mpr (measurable_strictAnti_comp fun i => measurable_pi_apply _)
  have hSA : MeasurableSet {y : Fin N → ℝ | StrictAnti y} := measurableSet_setOfPred.mpr measurable_strictAnti
  -- step 1: insert `1 = Σ_σ [y ∘ σ sorted]`
  have step1 : ∫ y, g y ∂μ = ∫ y, ∑ σ : Equiv.Perm (Fin N), {y | StrictAnti (y ∘ σ)}.indicator g y ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hinj] with y hy
    simp only [Set.indicator, Set.mem_setOf_eq]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, card_sort_eq_one hy, one_smul]
  rw [step1, integral_finsetSum _ fun σ _ => hg.indicator (hmeas σ)]
  -- step 2: change variables in each term
  have step2 : ∀ σ : Equiv.Perm (Fin N), ∫ y, {y | StrictAnti (y ∘ σ)}.indicator g y ∂μ =
      ∫ y, {y | StrictAnti y}.indicator (fun y => g (y ∘ ⇑σ⁻¹)) y ∂μ := by
    intro σ
    rw [← (hμ σ⁻¹).integral_comp' ({y | StrictAnti (y ∘ σ)}.indicator g)]
    congr 1
    funext y
    simp only [Set.indicator, Set.mem_setOf_eq, permE_apply]
    have : y ∘ ⇑σ⁻¹ ∘ ⇑σ = y := by funext i; simp
    rw [Function.comp_assoc, this]
  simp_rw [step2]
  have hint : ∀ σ : Equiv.Perm (Fin N), Integrable ({y | StrictAnti y}.indicator fun y => g (y ∘ ⇑σ⁻¹)) μ := by
    intro σ
    refine Integrable.indicator ?_ hSA
    exact ((hμ σ⁻¹).integrable_comp_emb (permE σ⁻¹).measurableEmbedding).mpr hg
  rw [← integral_finsetSum _ fun σ _ => hint σ]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only [Set.indicator, Set.mem_setOf_eq]
  split_ifs with h
  · exact Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin N))) _ _ (fun σ => rfl)
  · simp

/-! ## Integrability of bounded functions supported in `{y > x}` -/

lemma integrable_smeas_of_bound {n : ℕ} {c x C : ℝ} (hx : 0 < x) {g : (Fin (n + 1) → ℝ) → ℝ}
    (hg : Measurable g) (hgb : ∀ y, |g y| ≤ C) (hsupp : ∀ y, g y ≠ 0 → ∀ i, x < y i) :
    Integrable g (smeas c n) := by
  rw [integrable_smeas_iff]
  set B : Set (Fin n → ℝ) := Set.univ.pi fun _ => Set.Icc 0 c
  have hB : MeasurableSet B := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hBi : Integrable (B.indicator fun _ => C) := by
    rw [integrable_indicator_iff hB]
    exact integrableOn_const ((isCompact_univ_pi fun _ => isCompact_Icc).measure_lt_top.ne)
  refine hBi.mono' (hg.comp (measurable_zvec c)).aestronglyMeasurable (ae_of_all _ fun w => ?_)
  by_cases h0 : g (zvec c w) = 0
  · rw [h0, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => le_trans (abs_nonneg _) (hgb 0)) w
  · have hpos := hsupp _ h0
    have hw : w ∈ B := by
      intro i _
      have h1 : x < w i := by simpa using hpos i.castSucc
      have h2 : x < c - ∑ k, w k := by simpa using hpos (Fin.last n)
      have h3 : w i ≤ ∑ k, w k :=
        Finset.single_le_sum (fun k _ => by have := hpos k.castSucc; simp at this; linarith) (Finset.mem_univ i)
      exact ⟨by linarith, by linarith⟩
    rw [Set.indicator_of_mem hw, Real.norm_eq_abs]
    exact hgb _

end Palprimes.MT
