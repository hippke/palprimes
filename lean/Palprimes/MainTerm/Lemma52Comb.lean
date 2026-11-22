import Palprimes.MainTerm.Lemma52Defs

/-! # Lemma 5.2: the finite combinatorics

* `card_perm_blockMono`: for strictly decreasing `y`, the permutations `σ` making `y ∘ σ`
  decreasing on both blocks `[0, a)`, `[a, N)` correspond to the `a`-subsets `A` (the image of the
  first block), with first block `y ∘ A.orderEmbOfFin`.
* `rosser_alternating_identity`: the pointwise form of Greaves (5.9)–(5.18) for sorted
  `y` on the simplex `Σ y + x = 1`, proved by toggling the smallest coordinate `y_{N-1}`. -/

set_option linter.style.longLine false

open Finset

namespace Palprimes.MT

/-! ## Shuffle count -/

section Shuffle

variable {N : ℕ}

lemma ext_of_lt (y : Fin N → ℝ) {k : ℕ} (h : k < N) : ext y k = y ⟨k, h⟩ := by
  simp [ext, h]

/-- `σ` increasing on the two blocks `[0, a)` and `[a, N)`. -/
def PermBM (a : ℕ) (σ : Equiv.Perm (Fin N)) : Prop :=
  ∀ i j : Fin N, i < j → (j.val < a ∨ a ≤ i.val) → σ i < σ j

lemma blockMono_comp_iff {y : Fin N → ℝ} (hy : StrictAnti y) (a : ℕ) (σ : Equiv.Perm (Fin N)) :
    BlockMono a (y ∘ σ) ↔ PermBM a σ := by
  constructor
  · intro h i j hij hb
    have := h i j hij j.isLt hb
    rw [ext_of_lt _ j.isLt, ext_of_lt _ (lt_trans hij j.isLt)] at this
    simp only [Function.comp, Fin.eta] at this
    exact hy.lt_iff_gt.mp this
  · intro h i j hij hj hb
    have hi : i < N := lt_trans hij hj
    rw [ext_of_lt _ hj, ext_of_lt _ hi]
    exact hy (h ⟨i, hi⟩ ⟨j, hj⟩ hij hb)

/-- The image of the first block. -/
def imgA (a : ℕ) (σ : Equiv.Perm (Fin N)) : Finset (Fin N) :=
  (Finset.univ.filter fun j : Fin N => j.val < a).map σ.toEmbedding

lemma card_filter_val_lt {a : ℕ} (ha : a ≤ N) :
    (Finset.univ.filter fun j : Fin N => j.val < a).card = a := by
  rw [← Finset.card_range a]
  refine Finset.card_nbij (fun j => j.val) ?_ ?_ ?_
  · intro j hj; simp at hj ⊢; exact hj
  · intro i _ j _ h; exact Fin.ext h
  · intro k hk
    simp only [Finset.coe_range, Set.mem_Iio] at hk
    exact ⟨⟨k, lt_of_lt_of_le hk ha⟩, by simp [hk], rfl⟩

lemma card_imgA {a : ℕ} (ha : a ≤ N) (σ : Equiv.Perm (Fin N)) : (imgA a σ).card = a := by
  rw [imgA, Finset.card_map, card_filter_val_lt ha]

lemma mem_imgA {a : ℕ} {σ : Equiv.Perm (Fin N)} {z : Fin N} :
    z ∈ imgA a σ ↔ (σ.symm z).val < a := by
  simp only [imgA, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨j, hj, rfl⟩; simpa using hj
  · intro h; exact ⟨σ.symm z, h, by simp⟩

lemma oe_congr {α : Type*} [LinearOrder α] {s t : Finset α} (hst : s = t) {k : ℕ} (h : s.card = k)
    (h' : t.card = k) (i : Fin k) : s.orderEmbOfFin h i = t.orderEmbOfFin h' i := by
  subst hst; rfl

lemma imgA_oe {a : ℕ} (ha : a ≤ N) {σ : Equiv.Perm (Fin N)} (hσ : PermBM a σ)
    (h : (imgA a σ).card = a) (k : Fin a) :
    (imgA a σ).orderEmbOfFin h k = σ (Fin.castLE ha k) := by
  have := Finset.orderEmbOfFin_unique h (f := fun k => σ (Fin.castLE ha k))
    (fun k => by rw [mem_imgA]; simp)
    (fun k k' hkk' => hσ _ _ (by simpa using hkk') (Or.inl (by simp)))
  exact (congrFun this k).symm

lemma imgA_compl_oe {a : ℕ} (ha : a ≤ N) {σ : Equiv.Perm (Fin N)} (hσ : PermBM a σ)
    (h : (imgA a σ)ᶜ.card = N - a) (k : Fin (N - a)) :
    (imgA a σ)ᶜ.orderEmbOfFin h k = σ ⟨a + k, by omega⟩ := by
  have := Finset.orderEmbOfFin_unique h (f := fun k : Fin (N - a) => σ ⟨a + k, by omega⟩)
    (fun k => by rw [Finset.mem_compl, mem_imgA]; simp)
    (fun k k' hkk' => hσ _ _ (by rw [Fin.lt_def]; simp only; have := Fin.lt_def.mp hkk'; omega)
      (Or.inr (by simp)))
  exact (congrFun this k).symm

lemma permBM_ext {a : ℕ} (ha : a ≤ N) {σ τ : Equiv.Perm (Fin N)} (hσ : PermBM a σ) (hτ : PermBM a τ)
    (he : imgA a σ = imgA a τ) : σ = τ := by
  ext i
  by_cases hi : i.val < a
  · have h1 := imgA_oe ha hσ (card_imgA ha σ) ⟨i, hi⟩
    have h2 := imgA_oe ha hτ (card_imgA ha τ) ⟨i, hi⟩
    have hc : Fin.castLE ha ⟨i, hi⟩ = i := Fin.ext rfl
    rw [hc] at h1 h2
    rw [← h1, ← h2, oe_congr he]
  · have hcard : ∀ ρ : Equiv.Perm (Fin N), (imgA a ρ)ᶜ.card = N - a := fun ρ => by
      rw [Finset.card_compl, card_imgA ha, Fintype.card_fin]
    have h1 := imgA_compl_oe ha hσ (hcard σ) ⟨i - a, by omega⟩
    have h2 := imgA_compl_oe ha hτ (hcard τ) ⟨i - a, by omega⟩
    have hc : (⟨a + (i.val - a), by omega⟩ : Fin N) = i := Fin.ext (by simp; omega)
    simp only [hc] at h1 h2
    rw [← h1, ← h2]
    exact congrArg Fin.val (oe_congr (s := (imgA a σ)ᶜ) (t := (imgA a τ)ᶜ) (by rw [he]) _ _ _)

/-- The permutation built from an `a`-subset. -/
noncomputable def permOf {a : ℕ} (A : Finset (Fin N)) (h : A.card = a) (hc : Aᶜ.card = N - a)
    (i : Fin N) : Fin N :=
  if hi : i.val < a then A.orderEmbOfFin h ⟨i, hi⟩ else Aᶜ.orderEmbOfFin hc ⟨i - a, by omega⟩

lemma permOf_injective {a : ℕ} (A : Finset (Fin N)) (h : A.card = a) (hc : Aᶜ.card = N - a) :
    Function.Injective (permOf A h hc) := by
  intro i j hij
  unfold permOf at hij
  by_cases hi : i.val < a <;> by_cases hj : j.val < a <;> simp only [hi, hj, dif_pos, dif_neg,
    not_false_eq_true] at hij
  · exact Fin.ext (by simpa using (A.orderEmbOfFin h).injective hij)
  · exfalso
    have m1 := A.orderEmbOfFin_mem h ⟨i, hi⟩
    have m2 := Aᶜ.orderEmbOfFin_mem hc ⟨j - a, by omega⟩
    rw [hij, Finset.mem_compl] at *
    exact m2 m1
  · exfalso
    have m1 := A.orderEmbOfFin_mem h ⟨j, hj⟩
    have m2 := Aᶜ.orderEmbOfFin_mem hc ⟨i - a, by omega⟩
    rw [hij, Finset.mem_compl] at *
    exact m2 m1
  · have := (Aᶜ.orderEmbOfFin hc).injective hij
    simp only [Fin.mk.injEq] at this
    exact Fin.ext (by omega)

end Shuffle

open Classical in
/-- Shuffle count. -/
theorem card_perm_blockMono {N : ℕ} {y : Fin N → ℝ} (hy : StrictAnti y) {a : ℕ} (ha : a ≤ N)
    (Φ : (Fin a → ℝ) → Prop) :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin N) => BlockMono a (y ∘ σ) ∧ Φ (blk a (y ∘ σ))).card =
    (Finset.univ.filter fun A : Finset (Fin N) =>
      ∃ h : A.card = a, Φ (fun k => y (A.orderEmbOfFin h k))).card := by
  have hcard : ∀ ρ : Equiv.Perm (Fin N), (imgA a ρ).card = a := card_imgA ha
  refine Finset.card_bij (fun σ _ => imgA a σ) ?_ ?_ ?_
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    obtain ⟨hb, hΦ⟩ := hσ
    have hp := (blockMono_comp_iff hy a σ).mp hb
    refine ⟨hcard σ, ?_⟩
    convert hΦ using 2 with k
    rw [imgA_oe ha hp]
    simp only [blk, ext_of_lt _ (lt_of_lt_of_le k.isLt ha), Function.comp]
    rfl
  · intro σ hσ τ hτ he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ hτ
    exact permBM_ext ha ((blockMono_comp_iff hy a σ).mp hσ.1) ((blockMono_comp_iff hy a τ).mp hτ.1) he
  · intro A hA
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA
    obtain ⟨h, hΦ⟩ := hA
    have hc : Aᶜ.card = N - a := by rw [Finset.card_compl, Fintype.card_fin, h]
    let σ : Equiv.Perm (Fin N) :=
      Equiv.ofBijective _ (Finite.injective_iff_bijective.mp (permOf_injective A h hc))
    have hσv : ∀ i, σ i = permOf A h hc i := fun i => rfl
    have hp : PermBM a σ := by
      intro i j hij hb
      rw [hσv, hσv]; unfold permOf
      have hij' : i.val < j.val := hij
      rcases hb with hb | hb
      · have hi : i.val < a := lt_trans hij' hb
        rw [dif_pos hi, dif_pos hb]
        exact (A.orderEmbOfFin h).strictMono (show (⟨i, hi⟩ : Fin a) < ⟨j, hb⟩ from hij')
      · have hi : ¬ i.val < a := by omega
        have hj : ¬ j.val < a := by omega
        rw [dif_neg hi, dif_neg hj]
        exact (Aᶜ.orderEmbOfFin hc).strictMono
          (show (⟨i - a, by omega⟩ : Fin (N - a)) < ⟨j - a, by omega⟩ from by
            rw [Fin.lt_def]; simp only; omega)
    have himg : imgA a σ = A := by
      ext z
      rw [mem_imgA]
      constructor
      · intro hz
        have hz' : σ (σ.symm z) = z := σ.apply_symm_apply z
        rw [hσv] at hz'; unfold permOf at hz'; rw [dif_pos hz] at hz'
        rw [← hz']; exact A.orderEmbOfFin_mem h _
      · intro hz
        have hr : z ∈ Set.range (A.orderEmbOfFin h) := by
          rw [Finset.range_orderEmbOfFin]; exact hz
        obtain ⟨k, hk⟩ := hr
        have hz' : σ (Fin.castLE ha k) = z := by
          rw [hσv]; unfold permOf
          rw [dif_pos (by simp)]
          rw [← hk]; rfl
        rw [← hz', Equiv.symm_apply_apply]; simp
    refine ⟨σ, ?_, himg⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨(blockMono_comp_iff hy a σ).mpr hp, ?_⟩
    convert hΦ using 2 with k
    simp only [blk, Function.comp]
    rw [ext_of_lt _ (lt_of_lt_of_le k.isLt ha)]
    simp only [Function.comp, hσv, permOf, dif_pos k.isLt]


/-! ## The alternating identity -/

section Alt

/-- Rosser condition `j` on an `ℕ`-indexed chain. -/
def condN (c : ℕ → ℝ) (j : ℕ) : Prop :=
  ∑ i ∈ Finset.range (2 * j - 1), c i + 3 * c (2 * j - 1) ≤ 1

/-- All Rosser conditions of a chain of length `L` (followed by its tail value). -/
def RosN (c : ℕ → ℝ) (L : ℕ) : Prop := ∀ j : ℕ, 1 ≤ j → 2 * j ≤ L + 1 → condN c j

/-- The conditions with `2j ≤ L`. -/
def CoreN (c : ℕ → ℝ) (L : ℕ) : Prop := ∀ j : ℕ, 1 ≤ j → 2 * j ≤ L → condN c j

lemma rosserX_iff_rosN {L : ℕ} (x : ℝ) (v : Fin L → ℝ) : RosserX x v ↔ RosN (chainX x v) L :=
  Iff.rfl

lemma condN_congr {c c' : ℕ → ℝ} {j : ℕ} (h : ∀ i, i ≤ 2 * j - 1 → c i = c' i) :
    condN c j ↔ condN c' j := by
  unfold condN
  rw [Finset.sum_congr rfl (fun i hi => h i (by simp at hi; omega)), h _ le_rfl]

lemma rosN_iff (c : ℕ → ℝ) (L : ℕ) :
    RosN c L ↔ CoreN c L ∧ (Odd L → ∑ i ∈ Finset.range L, c i + 3 * c L ≤ 1) := by
  constructor
  · intro h
    refine ⟨fun j hj1 hj2 => h j hj1 (by omega), fun ⟨k, hk⟩ => ?_⟩
    have := h (k + 1) (by omega) (by omega)
    unfold condN at this
    have e : 2 * (k + 1) - 1 = L := by omega
    rwa [e] at this
  · rintro ⟨h1, h2⟩ j hj1 hj2
    rcases Nat.lt_or_ge L (2 * j) with hlt | hge
    · have hL : 2 * j - 1 = L := by omega
      have := h2 ⟨j - 1, by omega⟩
      unfold condN; rw [hL]; exact this
    · exact h1 j hj1 hge

variable {n : ℕ}

/-- The chain of a subset `A`: its elements in increasing index order (decreasing values), then
`x`. -/
noncomputable def cA (x : ℝ) (y : Fin (n + 1) → ℝ) (A : Finset (Fin (n + 1))) : ℕ → ℝ :=
  chainX x (fun k : Fin A.card => y (A.orderEmbOfFin rfl k))

lemma chainX_oe_eq (x : ℝ) (y : Fin (n + 1) → ℝ) (A : Finset (Fin (n + 1))) {k : ℕ}
    (h : A.card = k) : chainX x (fun i : Fin k => y (A.orderEmbOfFin h i)) = cA x y A := by
  subst h; rfl

lemma sum_oe_eq (y : Fin (n + 1) → ℝ) (A : Finset (Fin (n + 1))) {k : ℕ} (h : A.card = k) :
    ∑ i : Fin k, y (A.orderEmbOfFin h i) = ∑ a ∈ A, y a := by
  conv_rhs => rw [← Finset.image_orderEmbOfFin_univ A h]
  rw [Finset.sum_image (fun i _ j _ hij => (A.orderEmbOfFin h).injective hij)]

lemma cA_of_ge (x : ℝ) (y : Fin (n + 1) → ℝ) (A : Finset (Fin (n + 1))) {i : ℕ} (hi : A.card ≤ i) :
    cA x y A i = x := by
  simp [cA, chainX, not_lt.mpr hi]

lemma sum_range_cA (x : ℝ) (y : Fin (n + 1) → ℝ) (A : Finset (Fin (n + 1))) :
    ∑ i ∈ Finset.range A.card, cA x y A i = ∑ a ∈ A, y a := by
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [cA, chainX, Fin.is_lt, dif_pos, Fin.eta]
  exact sum_oe_eq y A rfl

lemma rosN_cA_iff (x : ℝ) (y : Fin (n + 1) → ℝ) (A : Finset (Fin (n + 1))) :
    RosN (cA x y A) A.card ↔
      CoreN (cA x y A) A.card ∧ (Odd A.card → ∑ a ∈ A, y a + 3 * x ≤ 1) := by
  rw [rosN_iff, sum_range_cA, cA_of_ge x y A le_rfl]

/-- The snoc structure of the chain of `insert last B`. -/
lemma cA_insert_last (x : ℝ) (y : Fin (n + 1) → ℝ) {B : Finset (Fin (n + 1))}
    (hB : Fin.last n ∉ B) :
    (∀ i, i < B.card → cA x y (insert (Fin.last n) B) i = cA x y B i) ∧
      cA x y (insert (Fin.last n) B) B.card = y (Fin.last n) := by
  have hc : (insert (Fin.last n) B).card = B.card + 1 := Finset.card_insert_of_notMem hB
  let f : Fin (B.card + 1) → Fin (n + 1) := fun k =>
    if h : k.val < B.card then B.orderEmbOfFin rfl ⟨k, h⟩ else Fin.last n
  have hf : f = (insert (Fin.last n) B).orderEmbOfFin hc := by
    apply Finset.orderEmbOfFin_unique
    · intro k
      simp only [f]
      split_ifs
      · exact Finset.mem_insert_of_mem (B.orderEmbOfFin_mem rfl _)
      · exact Finset.mem_insert_self _ _
    · intro k k' hkk'
      have hkk : k.val < k'.val := hkk'
      simp only [f]
      by_cases h1 : k.val < B.card <;> by_cases h2 : k'.val < B.card
      · rw [dif_pos h1, dif_pos h2]
        exact (B.orderEmbOfFin rfl).strictMono (show (⟨k, h1⟩ : Fin B.card) < ⟨k', h2⟩ from hkk)
      · rw [dif_pos h1, dif_neg h2]
        rw [Fin.lt_last_iff_ne_last]
        intro he
        exact hB (he ▸ B.orderEmbOfFin_mem rfl _)
      · omega
      · omega
  have hcA := chainX_oe_eq x y (insert (Fin.last n) B) hc
  rw [← hcA, ← hf]
  constructor
  · intro i hi
    simp only [chainX, f, cA, show i < B.card + 1 by omega, hi, dif_pos]
  · simp [chainX, f]

lemma y_lt_one {x : ℝ} {y : Fin (n + 1) → ℝ} (hx : 0 < x) (hyx : ∀ i, x < y i)
    (hsum : ∑ i, y i + x = 1) (i : Fin (n + 1)) : y i < 1 := by
  have := Finset.single_le_sum (f := y) (fun j _ => (hx.trans (hyx j)).le) (Finset.mem_univ i)
  linarith

/-- The `h`-condition on a subset of size `2m`, in chain form. -/
def HN (m : ℕ) (x : ℝ) (y : Fin (n + 1) → ℝ) (A : Finset (Fin (n + 1))) : Prop :=
  (∀ j : ℕ, 1 ≤ j → j < m → condN (cA x y A) j) ∧
  1 < ∑ i ∈ Finset.range (2 * m - 1), cA x y A i + 3 * cA x y A (2 * m - 1) ∧
  cA x y A (2 * m - 1) < 1 - x - ∑ a ∈ A, y a

lemma hRegion_oe_iff {m : ℕ} {x : ℝ} {y : Fin (n + 1) → ℝ} (hy : StrictAnti y) (hx : 0 < x)
    (hyx : ∀ i, x < y i) (hsum : ∑ i, y i + x = 1) (A : Finset (Fin (n + 1)))
    (h : A.card = 2 * m) :
    HRegion m x (fun k => y (A.orderEmbOfFin h k)) ↔ HN m x y A := by
  unfold HRegion HN condN
  rw [chainX_oe_eq x y A h, sum_oe_eq y A h]
  have h1 : StrictAnti (fun k => y (A.orderEmbOfFin h k)) :=
    hy.comp_strictMono (A.orderEmbOfFin h).strictMono
  have h2 : ∀ k, x < y (A.orderEmbOfFin h k) := fun k => hyx _
  have h3 : ∀ k, y (A.orderEmbOfFin h k) < 1 := fun k => y_lt_one hx hyx hsum _
  simp only [h1, h2, h3, implies_true, true_and]

end Alt

section Pair

open Classical in
/-- The summand after the conversion to a sum over all subsets. -/
noncomputable def FA (m : ℕ) (x : ℝ) (y : Fin (2 * m + 1) → ℝ) (A : Finset (Fin (2 * m + 1))) : ℝ :=
  (if A.card < 2 * m + 1 ∧ RosN (cA x y A) A.card then (-1 : ℝ) ^ A.card else 0) +
  (if A.card = 2 * m ∧ HN m x y A then 1 else 0)

lemma pair_zero {m : ℕ} (hm : 1 ≤ m) {x : ℝ} (hx : 0 < x) {y : Fin (2 * m + 1) → ℝ}
    (hy : StrictAnti y) (hyx : ∀ i, x < y i) (hsum : ∑ i, y i + x = 1)
    (B : Finset (Fin (2 * m + 1))) (hB : Fin.last (2 * m) ∉ B) :
    FA m x y B + FA m x y (insert (Fin.last (2 * m)) B) = 0 := by
  classical
  set lst := Fin.last (2 * m) with hlst
  set L := B.card with hLdef
  have hBsub : B ⊆ Finset.univ.erase lst := fun b hb =>
    Finset.mem_erase.mpr ⟨fun h => hB (h ▸ hb), Finset.mem_univ _⟩
  have hcardE : (Finset.univ.erase lst).card = 2 * m := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]; simp
  have hL : L ≤ 2 * m := hcardE ▸ Finset.card_le_card hBsub
  set C := (Finset.univ.erase lst) \ B with hCdef
  have hCcard : C.card = 2 * m - L := by rw [Finset.card_sdiff_of_subset hBsub, hcardE]
  set S := ∑ a ∈ B, y a with hSdef
  have hsumdec : S + ∑ c ∈ C, y c + y lst + x = 1 := by
    have e1 := Finset.sum_sdiff hBsub (f := y)
    have e2 := Finset.add_sum_erase Finset.univ y (Finset.mem_univ lst)
    linarith
  have hCgt : ∀ c ∈ C, y lst < y c := by
    intro c hc
    have : c ≠ lst := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hc).1).1
    exact hy (Fin.lt_last_iff_ne_last.mpr this)
  have hylx : x < y lst := hyx _
  obtain ⟨hagree, hlastv⟩ := cA_insert_last x y hB
  have hcI : (insert lst B).card = L + 1 := Finset.card_insert_of_notMem hB
  have hsumI : ∑ a ∈ insert lst B, y a = S + y lst := by rw [Finset.sum_insert hB, add_comm]
  have hsumrangeI : ∑ i ∈ Finset.range L, cA x y (insert lst B) i = S := by
    have e : ∑ i ∈ Finset.range L, cA x y (insert lst B) i = ∑ i ∈ Finset.range L, cA x y B i :=
      Finset.sum_congr rfl fun i hi => hagree i (Finset.mem_range.mp hi)
    rw [e]
    exact sum_range_cA x y B
  have hcoreI : CoreN (cA x y (insert lst B)) (L + 1) ↔
      CoreN (cA x y B) L ∧ (Odd L → S + 3 * y lst ≤ 1) := by
    constructor
    · intro h
      refine ⟨fun j hj1 hj2 => ?_, fun hodd => ?_⟩
      · exact (condN_congr (fun i hi => hagree i (by omega))).mp (h j hj1 (by omega))
      · obtain ⟨k, hk⟩ := hodd
        have := h (k + 1) (by omega) (by omega)
        unfold condN at this
        rw [show 2 * (k + 1) - 1 = L by omega, hsumrangeI, hlastv] at this
        exact this
    · rintro ⟨h1, h2⟩ j hj1 hj2
      rcases Nat.lt_or_ge L (2 * j) with hlt | hge
      · have hj : 2 * j - 1 = L := by omega
        unfold condN; rw [hj, hsumrangeI, hlastv]; exact h2 ⟨j - 1, by omega⟩
      · exact (condN_congr (fun i hi => hagree i (by omega))).mpr (h1 j hj1 hge)
  have hrosB : RosN (cA x y B) L ↔ CoreN (cA x y B) L ∧ (Odd L → S + 3 * x ≤ 1) :=
    rosN_cA_iff x y B
  have hrosI : RosN (cA x y (insert lst B)) (L + 1) ↔ CoreN (cA x y B) L ∧
      (Odd L → S + 3 * y lst ≤ 1) ∧ (Odd (L + 1) → S + y lst + 3 * x ≤ 1) := by
    have := rosN_cA_iff x y (insert lst B)
    rw [hcI, hcoreI, hsumI] at this
    rw [this]; tauto
  unfold FA
  rw [hcI, ← hLdef]
  rcases Nat.lt_or_ge (L + 1) (2 * m) with hA | hA
  · -- `|B| ≤ 2m − 2`: the Rosser terms cancel
    have hC2' : 2 ≤ C.card := by rw [hCcard]; omega
    have hC2 : (2 : ℝ) ≤ C.card := by exact_mod_cast hC2'
    have hsC : 2 * y lst ≤ ∑ c ∈ C, y c := by
      have h1 : ∑ c ∈ C, y lst ≤ ∑ c ∈ C, y c := Finset.sum_le_sum fun c hc => (hCgt c hc).le
      rw [Finset.sum_const, nsmul_eq_mul] at h1
      nlinarith
    have e1 : RosN (cA x y B) L ↔ CoreN (cA x y B) L := by
      rw [hrosB]; exact ⟨fun h => h.1, fun h => ⟨h, fun _ => by linarith⟩⟩
    have e2 : RosN (cA x y (insert lst B)) (L + 1) ↔ CoreN (cA x y B) L := by
      rw [hrosI]; exact ⟨fun h => h.1, fun h => ⟨h, fun _ => by linarith, fun _ => by linarith⟩⟩
    rw [e1, e2]
    have n1 : L ≠ 2 * m := by omega
    have n2 : L + 1 ≠ 2 * m := by omega
    have l1 : L < 2 * m + 1 := by omega
    have l2 : L + 1 < 2 * m + 1 := by omega
    by_cases hc : CoreN (cA x y B) L <;> simp [hc, n1, n2, l1, l2, pow_succ]
  rcases Nat.lt_or_ge L (2 * m) with hB2 | hB2
  · -- `|B| = 2m − 1`
    have hL1 : L + 1 = 2 * m := by omega
    obtain ⟨c, hc⟩ := Finset.card_eq_one.mp (show C.card = 1 by rw [hCcard]; omega)
    have hsC : ∑ c ∈ C, y c = y c := by rw [hc, Finset.sum_singleton]
    have hyc : y lst < y c := hCgt c (by rw [hc]; exact Finset.mem_singleton_self c)
    have hoddL : Odd L := ⟨m - 1, by omega⟩
    have hevL : ¬ Odd (L + 1) := by rw [Nat.not_odd_iff_even]; exact ⟨m, by omega⟩
    have e1 : RosN (cA x y B) L ↔ CoreN (cA x y B) L := by
      rw [hrosB]; exact ⟨fun h => h.1, fun h => ⟨h, fun _ => by linarith⟩⟩
    have e2 : RosN (cA x y (insert lst B)) (L + 1) ↔ CoreN (cA x y B) L ∧ S + 3 * y lst ≤ 1 := by
      rw [hrosI]
      exact ⟨fun h => ⟨h.1, h.2.1 hoddL⟩, fun h => ⟨h.1, fun _ => h.2, fun h' => absurd h' hevL⟩⟩
    have e3 : HN m x y (insert lst B) ↔ CoreN (cA x y B) L ∧ 1 < S + 3 * y lst := by
      unfold HN
      have i1 : 2 * m - 1 = L := by omega
      rw [i1, hsumrangeI, hlastv, hsumI]
      constructor
      · rintro ⟨h1, h2, -⟩
        refine ⟨fun j hj1 hj2 => ?_, h2⟩
        exact (condN_congr (fun i hi => hagree i (by omega))).mp (h1 j hj1 (by omega))
      · rintro ⟨h1, h2⟩
        refine ⟨fun j hj1 hj2 => ?_, h2, by linarith⟩
        exact (condN_congr (fun i hi => hagree i (by omega))).mpr (h1 j hj1 (by omega))
    rw [e1, e2, e3]
    have n1 : L ≠ 2 * m := by omega
    have l1 : L < 2 * m + 1 := by omega
    have l2 : L + 1 < 2 * m + 1 := by omega
    have p1 : (-1 : ℝ) ^ L = -1 := hoddL.neg_one_pow
    have p2 : (-1 : ℝ) ^ (L + 1) = 1 := by rw [pow_succ, p1]; norm_num
    rcases le_or_gt (S + 3 * y lst) 1 with hc2 | hc2
    · have hc3 : ¬ 1 < S + 3 * y lst := not_lt.mpr hc2
      by_cases hc1 : CoreN (cA x y B) L <;> simp [hc1, hc2, hc3, n1, hL1, l1, l2, p1, p2]
    · have hc3 : ¬ S + 3 * y lst ≤ 1 := not_le.mpr hc2
      by_cases hc1 : CoreN (cA x y B) L <;> simp [hc1, hc2, hc3, n1, hL1, l1, l2, p1, p2]
  · -- `|B| = 2m`: `B = univ.erase last`, both terms vanish
    have hL2 : L = 2 * m := by omega
    have hBe : B = Finset.univ.erase lst :=
      Finset.eq_of_subset_of_card_le hBsub (by rw [hcardE]; omega)
    have hCe : C.card = 0 := by rw [hCcard]; omega
    have hsC : ∑ c ∈ C, y c = 0 := by rw [Finset.card_eq_zero.mp hCe, Finset.sum_empty]
    have hBc : B.card = 2 * m := hL2
    have hoe : ∀ k : Fin (2 * m), B.orderEmbOfFin hBc k = Fin.castSucc k := by
      have := Finset.orderEmbOfFin_unique hBc (f := Fin.castSucc)
        (fun k => by rw [hBe]; simp [hlst, Fin.castSucc_ne_last]) Fin.strictMono_castSucc
      intro k; exact (congrFun this k).symm
    have hval : ∀ i (hi : i < 2 * m), cA x y B i = y ⟨i, by omega⟩ := by
      intro i hi
      rw [← chainX_oe_eq x y B hBc]
      simp only [chainX, hi, dif_pos, hoe]
      rfl
    set q := cA x y B (2 * m - 1) with hq
    have hq' : q = y ⟨2 * m - 1, by omega⟩ := hval _ (by omega)
    have hqlst : y lst < q := by
      rw [hq']; exact hy (Fin.lt_last_iff_ne_last.mpr (by simp [hlst, Fin.ext_iff]; omega))
    have hqx : x < q := by rw [hq']; exact hyx _
    have hPq : ∑ i ∈ Finset.range (2 * m - 1), cA x y B i + q = S := by
      have := sum_range_cA x y B
      have e : Finset.range (2 * m) = Finset.range ((2 * m - 1) + 1) := by congr 1; omega
      rw [hBc, e, Finset.sum_range_succ] at this
      exact this
    have nR : ¬ RosN (cA x y B) L := by
      intro h
      have := (hrosB.mp h).1 m hm (by omega)
      unfold condN at this
      linarith
    have nH : ¬ HN m x y B := by
      rintro ⟨-, -, h3⟩
      rw [← hq, ← hSdef] at h3
      linarith
    have n1 : ¬ L + 1 < 2 * m + 1 := by omega
    have n2 : L + 1 ≠ 2 * m := by omega
    simp [nR, nH, n1, n2]

end Pair

open Classical in
/-- Pointwise alternating identity (Greaves (5.9)–(5.18)) for `N = 2m + 1` sorted variables. -/
theorem rosser_alternating_identity {m : ℕ} (hm : 1 ≤ m) {x : ℝ} (hx : 0 < x)
    {y : Fin (2 * m + 1) → ℝ} (hy : StrictAnti y) (hyx : ∀ i, x < y i) (hsum : ∑ i, y i + x = 1) :
    ∑ a ∈ Finset.range (2 * m + 1), (-1 : ℝ) ^ a *
      ((Finset.univ.filter fun A : Finset (Fin (2 * m + 1)) =>
        ∃ h : A.card = a, RosserX x (fun k => y (A.orderEmbOfFin h k))).card : ℝ)
    + ((Finset.univ.filter fun A : Finset (Fin (2 * m + 1)) =>
        ∃ h : A.card = 2 * m, HRegion m x (fun k => y (A.orderEmbOfFin h k))).card : ℝ) = 0 := by
  classical
  have hR : ∀ A : Finset (Fin (2 * m + 1)), ∀ a,
      (∃ h : A.card = a, RosserX x (fun k => y (A.orderEmbOfFin h k))) ↔
        (A.card = a ∧ RosN (cA x y A) A.card) := by
    intro A a
    constructor
    · rintro ⟨h, hr⟩
      rw [rosserX_iff_rosN, chainX_oe_eq x y A h] at hr
      exact ⟨h, by rw [h]; exact hr⟩
    · rintro ⟨h, hr⟩
      refine ⟨h, ?_⟩
      rw [rosserX_iff_rosN, chainX_oe_eq x y A h, ← h]; exact hr
  have hH : ∀ A : Finset (Fin (2 * m + 1)),
      (∃ h : A.card = 2 * m, HRegion m x (fun k => y (A.orderEmbOfFin h k))) ↔
        (A.card = 2 * m ∧ HN m x y A) := by
    intro A
    constructor
    · rintro ⟨h, hr⟩; exact ⟨h, (hRegion_oe_iff hy hx hyx hsum A h).mp hr⟩
    · rintro ⟨h, hr⟩; exact ⟨h, (hRegion_oe_iff hy hx hyx hsum A h).mpr hr⟩
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  simp only [hR, hH]
  have hinner : ∀ A : Finset (Fin (2 * m + 1)),
      ∑ a ∈ Finset.range (2 * m + 1), (-1 : ℝ) ^ a *
        (if A.card = a ∧ RosN (cA x y A) A.card then 1 else 0) =
      if A.card < 2 * m + 1 ∧ RosN (cA x y A) A.card then (-1 : ℝ) ^ A.card else 0 := by
    intro A
    have : ∀ a, (-1 : ℝ) ^ a * (if A.card = a ∧ RosN (cA x y A) A.card then 1 else 0) =
        if A.card = a then (if RosN (cA x y A) A.card then (-1 : ℝ) ^ a else 0) else 0 := by
      intro a; split_ifs <;> simp_all
    rw [Finset.sum_congr rfl (fun a _ => this a), Finset.sum_ite_eq]
    simp only [Finset.mem_range]
    split_ifs <;> simp_all
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun A _ => hinner A), ← Finset.sum_add_distrib]
  change ∑ A, FA m x y A = 0
  rw [← Finset.powerset_univ, ← Finset.insert_erase (Finset.mem_univ (Fin.last (2 * m))),
    Finset.sum_powerset_insert (Finset.notMem_erase _ _), ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun B hB => ?_
  have hlB : Fin.last (2 * m) ∉ B := fun h => Finset.notMem_erase _ _ (Finset.mem_powerset.mp hB h)
  exact pair_zero hm hx hy hyx hsum B hlB


end Palprimes.MT
