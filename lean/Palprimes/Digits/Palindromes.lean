import Palprimes.ExpSum.Collision

/-! # M1, M2. Palindromes as digit vectors and their exponential sum

`Nat.digits` API: a number in `[b^{2N}, b^{2N+1})` is a palindrome iff it is `palVal d`
for a digit vector with nonzero outer digit; `palVal` is injective. TP Lemma 7.1 (size of
`Π*_b(2N)`, characters mod `b³ − b`). Effort M1 600–900, M2 300–500 lines. -/

set_option linter.style.longLine false

open Finset Real

namespace Palprimes

/-- Position `i ∈ [0, 2N]` folded onto `[0, N]`. -/
def fold (N i : ℕ) : ℕ := if i ≤ N then i else 2 * N - i

theorem fold_le (N i : ℕ) (hi : i ≤ 2 * N) : fold N i ≤ N := by unfold fold; split_ifs <;> omega

theorem fold_symm (N i : ℕ) (hi : i ≤ 2 * N) : fold N (2 * N - i) = fold N i := by
  unfold fold; split_ifs <;> omega

/-- The base-`b` digit list (least significant first) of the palindrome with half-digits `d`. -/
def palList (b N : ℕ) (d : DigVec b N) : List ℕ :=
  List.ofFn (fun i : Fin (2 * N + 1) => extDig d (fold N i))

theorem length_palList (b N : ℕ) (d : DigVec b N) : (palList b N d).length = 2 * N + 1 := by
  simp [palList]

theorem getElem_palList (b N : ℕ) (d : DigVec b N) (i : ℕ) (hi : i < (palList b N d).length) :
    (palList b N d)[i] = extDig d (fold N i) := by
  simp only [palList, List.getElem_ofFn]

theorem extDig_lt' {b N : ℕ} (hb : 1 ≤ b) (d : DigVec b N) (k : ℕ) : extDig d k < b := by
  unfold extDig
  split_ifs
  · exact (d _).isLt
  · omega

/-- Reindexing the symmetric sum. -/
theorem sum_fold (b N : ℕ) (G : ℕ → ℕ) :
    ∑ i ∈ range (2 * N + 1), G (fold N i) * b ^ i = ∑ k ∈ range (N + 1), G k * cK b N k := by
  rw [← Finset.sum_range_add_sum_Ico _ (by omega : N + 1 ≤ 2 * N + 1),
    Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ (fun k => G k * cK b N k)]
  have h1 : ∑ i ∈ range (N + 1), G (fold N i) * b ^ i =
      ∑ i ∈ range N, G i * b ^ i + G N * b ^ N := by
    rw [Finset.sum_range_succ]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi; rw [Finset.mem_range] at hi
      simp [fold, show i ≤ N by omega]
    · simp [fold]
  have h2 : ∑ k ∈ range (2 * N + 1 - (N + 1)), G (fold N (N + 1 + k)) * b ^ (N + 1 + k) =
      ∑ k ∈ range N, G k * b ^ (2 * N - k) := by
    rw [show 2 * N + 1 - (N + 1) = N by omega,
      ← Finset.sum_range_reflect (fun k => G k * b ^ (2 * N - k)) N]
    apply Finset.sum_congr rfl
    intro k hk; rw [Finset.mem_range] at hk
    simp only [fold, show ¬ (N + 1 + k ≤ N) by omega, ite_false]
    rw [show 2 * N - (N + 1 + k) = N - 1 - k by omega,
      show 2 * N - (N - 1 - k) = N + 1 + k by omega]
  have h3 : ∑ k ∈ range N, G k * cK b N k = ∑ k ∈ range N, G k * b ^ k +
      ∑ k ∈ range N, G k * b ^ (2 * N - k) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk; rw [Finset.mem_range] at hk
    simp [cK, hk]; ring
  have h4 : cK b N N = b ^ N := by simp [cK]
  rw [h1, h2, h3, h4]
  ring

theorem ofDigits_palList (b N : ℕ) (d : DigVec b N) :
    Nat.ofDigits b (palList b N d) = palVal b N d := by
  rw [Nat.ofDigits_eq_sum_mapIdx, List.mapIdx_eq_ofFn, List.sum_ofFn]
  have : ∀ i : Fin (palList b N d).length, (palList b N d).get i * b ^ (i : ℕ) =
      extDig d (fold N i) * b ^ (i : ℕ) := by
    intro i
    rw [List.get_eq_getElem, getElem_palList]
  simp only [this]
  rw [Fin.sum_univ_eq_sum_range (fun i => extDig d (fold N i) * b ^ i), length_palList,
    sum_fold]
  unfold palVal
  rw [← Fin.sum_univ_eq_sum_range (fun k => extDig d k * cK b N k)]
  apply Finset.sum_congr rfl
  intro k _
  simp [extDig_fin]

theorem palList_reverse (b N : ℕ) (d : DigVec b N) : (palList b N d).reverse = palList b N d := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  rw [List.getElem_reverse, getElem_palList, getElem_palList, length_palList]
  rw [length_palList] at h2
  congr 1
  rw [show 2 * N + 1 - 1 - i = 2 * N - i by omega, fold_symm N i (by omega)]

theorem digits_palVal (b N : ℕ) (hb : 2 ≤ b) (d : DigVec b N) (hd : (d 0 : ℕ) ≠ 0) :
    Nat.digits b (palVal b N d) = palList b N d := by
  rw [← ofDigits_palList]
  apply Nat.digits_ofDigits b (by omega)
  · intro l hl
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hl
    exact extDig_lt' (by omega) d _
  · intro h
    rw [List.getLast_eq_getElem, getElem_palList]
    simp only [length_palList, show 2 * N + 1 - 1 = 2 * N by omega]
    simp only [fold]
    split_ifs with h'
    · have : 2 * N = 0 := by omega
      rw [this]
      simpa [extDig] using hd
    · rw [show 2 * N - 2 * N = 0 by omega]
      simpa [extDig] using hd

theorem length_digits_eq (b N n : ℕ) (hb : 2 ≤ b) (h1 : b ^ (2 * N) ≤ n) (h2 : n < b ^ (2 * N + 1)) :
    (Nat.digits b n).length = 2 * N + 1 := by
  have hn : n ≠ 0 := by have := Nat.one_le_pow (2 * N) b (by omega); omega
  have hlt := Nat.lt_base_pow_length_digits (m := n) (by omega : 1 < b)
  have hle := Nat.base_pow_length_digits_le b n (by omega) hn
  have a1 : 2 * N < (Nat.digits b n).length := by
    have : b ^ (2 * N) < b ^ (Nat.digits b n).length := lt_of_le_of_lt h1 hlt
    exact (Nat.pow_lt_pow_iff_right (by omega)).1 this
  have a2 : (Nat.digits b n).length < 2 * N + 2 := by
    have : b ^ (Nat.digits b n).length < b ^ (2 * N + 2) := by
      calc b ^ (Nat.digits b n).length ≤ b * n := hle
        _ < b * b ^ (2 * N + 1) := Nat.mul_lt_mul_of_pos_left h2 (by omega)
        _ = b ^ (2 * N + 2) := by ring
    exact (Nat.pow_lt_pow_iff_right (by omega)).1 this
  omega

/-- **M1.** Palindromes with `2N+1` digits are exactly the values `palVal d`, `d_0 ≠ 0`. -/
theorem pal_eq_image (b N : ℕ) (hb : 2 ≤ b) :
    (Ico (b ^ (2 * N)) (b ^ (2 * N + 1))).filter (IsPalindrome b) =
      ((univ : Finset (DigVec b N)).filter (fun d => (d 0 : ℕ) ≠ 0)).image (palVal b N) := by
  ext n
  simp only [mem_filter, mem_Ico, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨⟨h1, h2⟩, hpal⟩
    set L := Nat.digits b n with hL
    have hlen : L.length = 2 * N + 1 := length_digits_eq b N n hb h1 h2
    have hltD : ∀ k, L.getD k 0 < b := by
      intro k
      by_cases hk : k < L.length
      · rw [List.getD_eq_getElem _ _ hk]
        exact Nat.digits_lt_base (by omega) (List.getElem_mem hk)
      · rw [List.getD_eq_default _ _ (by omega)]; omega
    set d : DigVec b N := fun k => ⟨L.getD k 0, hltD _⟩ with hd
    have hextd : ∀ k ≤ N, extDig d k = L.getD k 0 := by
      intro k hk
      simp [extDig, show k < N + 1 by omega, hd]
    have hrev : ∀ i ≤ 2 * N, L.getD i 0 = L.getD (2 * N - i) 0 := by
      intro i hi
      have hp : L.reverse = L := hpal
      have e := List.getElem?_reverse (l := L) (i := i) (by omega)
      rw [hp, hlen, show 2 * N + 1 - 1 - i = 2 * N - i by omega] at e
      simp only [List.getD_eq_getElem?_getD, e]
    have hlist : palList b N d = L := by
      apply List.ext_getElem (by rw [length_palList, hlen])
      intro i h1' h2'
      have hi : i ≤ 2 * N := by rw [length_palList] at h1'; omega
      rw [getElem_palList, hextd _ (fold_le N i hi), ← List.getD_eq_getElem L 0 h2']
      unfold fold
      split_ifs with hiN
      · rfl
      · exact (hrev i hi).symm
    refine ⟨d, ?_, ?_⟩
    · have hn : n ≠ 0 := by have := Nat.one_le_pow (2 * N) b (by omega); omega
      have hlast := Nat.getLast_digit_ne_zero b hn
      intro hz
      apply hlast
      rw [List.getLast_eq_getElem, ← List.getD_eq_getElem _ 0]
      simp only [← hL]
      rw [show L.length - 1 = 2 * N by omega, ← show 2 * N - 0 = 2 * N by omega, ← hrev 0 (by omega)]
      have h0 := hextd 0 (by omega)
      simp only [extDig, show 0 < N + 1 by omega, dite_true] at h0
      rw [← h0]
      exact hz
    · rw [← ofDigits_palList, hlist, hL, Nat.ofDigits_digits]
  · rintro ⟨d, hd, rfl⟩
    have hdig := digits_palVal b N hb d hd
    have hlen : (Nat.digits b (palVal b N d)).length = 2 * N + 1 := by
      rw [hdig, length_palList]
    have hn : palVal b N d ≠ 0 := by
      intro h0
      rw [h0, Nat.digits_zero] at hdig
      have := congrArg List.length hdig
      rw [length_palList] at this
      simp at this
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have hle := Nat.base_pow_length_digits_le b (palVal b N d) (by omega) hn
      rw [hlen] at hle
      have : b * b ^ (2 * N) ≤ b * palVal b N d := by
        calc b * b ^ (2 * N) = b ^ (2 * N + 1) := by ring
          _ ≤ _ := hle
      exact Nat.le_of_mul_le_mul_left this (by omega)
    · have hlt := Nat.lt_base_pow_length_digits (m := palVal b N d) (by omega : 1 < b)
      rwa [hlen] at hlt
    · unfold IsPalindrome
      rw [hdig, palList_reverse]

/-- `palVal` is injective (Lemma 3 with single digits). -/
theorem palVal_injective (b N : ℕ) (hb : 2 ≤ b) : Function.Injective (palVal b N) := by
  intro d e h
  have hz := sum_cK_eq_zero b N hb (fun k => (extDig d k : ℤ) - extDig e k) (by
    intro k _
    have h1 := extDig_lt' (by omega : 1 ≤ b) d k
    have h2 := extDig_lt' (by omega : 1 ≤ b) e k
    rw [abs_le]; constructor <;> omega) (by
    have h' : (palVal b N d : ℤ) = palVal b N e := by exact_mod_cast h
    unfold palVal at h'
    push_cast at h'
    rw [← Fin.sum_univ_eq_sum_range (fun k => ((extDig d k : ℤ) - extDig e k) * (cK b N k : ℤ))]
    simp only [extDig_fin, sub_mul, Finset.sum_sub_distrib]
    rw [h', sub_self])
  funext k
  have := hz k (by omega)
  simp only [extDig_fin, sub_eq_zero] at this
  exact Fin.ext (by exact_mod_cast this)

theorem card_digVec_ne0 (b N : ℕ) (hb : 1 ≤ b) :
    #((univ : Finset (DigVec b N)).filter (fun d => (d 0 : ℕ) ≠ 0)) = (b - 1) * b ^ N := by
  have : (univ : Finset (DigVec b N)).filter (fun d => (d 0 : ℕ) ≠ 0) =
      Fintype.piFinset (fun i : Fin (N + 1) =>
        if i = 0 then (univ : Finset (Fin b)).filter (fun a : Fin b => (a : ℕ) ≠ 0) else univ) := by
    ext d
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h i; split_ifs with hi
      · subst hi; simpa using h
      · exact mem_univ _
    · intro h; have := h 0; simpa using this
  rw [this, Fintype.card_piFinset, Fin.prod_univ_succ]
  simp only [Fin.succ_ne_zero, ite_false, ite_true, Finset.card_univ, Fintype.card_fin,
    Finset.prod_const]
  congr 1
  · have : (univ : Finset (Fin b)).filter (fun a : Fin b => (a : ℕ) ≠ 0) = univ.erase ⟨0, by omega⟩ := by
      ext a; simp [Fin.ext_iff]
    rw [this, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]

theorem card_pal (b N : ℕ) (hb : 2 ≤ b) :
    #((Ico (b ^ (2 * N)) (b ^ (2 * N + 1))).filter (IsPalindrome b)) = (b - 1) * b ^ N := by
  rw [pal_eq_image b N hb, card_image_of_injective _ (palVal_injective b N hb),
    card_digVec_ne0 b N (by omega)]


/-! ## Arithmetic for the density of `Π*` -/

/-- CRT with integer targets. -/
theorem crt_int (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hco : Nat.Coprime m n) (a c : ℤ) :
    ∃ E : ℕ, E < m * n ∧ (m : ℤ) ∣ (E : ℤ) - a ∧ (n : ℤ) ∣ (E : ℤ) - c := by
  have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  set a' := (a % m).toNat with ha'
  set c' := (c % n).toNat with hc'
  have ea : (a' : ℤ) = a % m := Int.toNat_of_nonneg (Int.emod_nonneg a hm')
  have ec : (c' : ℤ) = c % n := Int.toNat_of_nonneg (Int.emod_nonneg c hn')
  set k := Nat.chineseRemainder hco a' c' with hk
  have hk1 := (Nat.chineseRemainder hco a' c').property.1
  have hk2 := (Nat.chineseRemainder hco a' c').property.2
  refine ⟨k, Nat.chineseRemainder_lt_mul hco a' c' hm.ne' hn.ne', ?_, ?_⟩
  · have h1 : (m : ℤ) ∣ (a' : ℤ) - k := Nat.modEq_iff_dvd.1 hk1
    have h2 : (m : ℤ) ∣ a - a % m := by rw [Int.emod_def]; simp
    have : (k : ℤ) - a = -((a' : ℤ) - k) - (a - a % m) := by rw [ea]; ring
    rw [this]
    exact dvd_sub (dvd_neg.2 h1) h2
  · have h1 : (n : ℤ) ∣ (c' : ℤ) - k := Nat.modEq_iff_dvd.1 hk2
    have h2 : (n : ℤ) ∣ c - c % n := by rw [Int.emod_def]; simp
    have : (k : ℤ) - c = -((c' : ℤ) - k) - (c - c % n) := by rw [ec]; ring
    rw [this]
    exact dvd_sub (dvd_neg.2 h1) h2

/-- A small `E` fixing both residues of `x + 2E` and `y + 2E` (odd `x, y`). -/
theorem exists_E (b : ℕ) (hb : 2 ≤ b) (x y : ℤ) (hx : Odd x) (hy : Odd y) :
    ∃ E : ℕ, E ≤ (b + 1) * (b - 1) ∧ ((b : ℤ) - 1) ∣ x + 2 * E - 1 ∧
      ((b : ℤ) + 1) ∣ y + 2 * E - 1 := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  rcases Nat.even_or_odd b with ⟨c, hc⟩ | ⟨c, hc⟩
  · -- b = 2c: moduli b - 1 and b + 1 are odd and coprime
    have hco : Nat.Coprime (b - 1) (b + 1) := by
      rw [← Nat.isCoprime_iff_coprime]
      refine ⟨(c : ℤ) , 1 - c, ?_⟩
      push_cast [show 1 ≤ b by omega]
      rw [hc]; push_cast; ring
    obtain ⟨E, hE, h1, h2⟩ := crt_int (b - 1) (b + 1) (by omega) (by omega) hco (-u) (-v)
    refine ⟨E, by rw [mul_comm]; omega, ?_, ?_⟩
    · have e : ((b - 1 : ℕ) : ℤ) = (b : ℤ) - 1 := by push_cast [show 1 ≤ b by omega]; ring
      rw [e] at h1
      have : (2 * u + 1) + 2 * (E : ℤ) - 1 = 2 * ((E : ℤ) - -u) := by ring
      rw [this]; exact dvd_mul_of_dvd_right h1 2
    · push_cast at h2
      have : (2 * v + 1) + 2 * (E : ℤ) - 1 = 2 * ((E : ℤ) - -v) := by ring
      rw [this]; exact dvd_mul_of_dvd_right h2 2
  · -- b = 2c + 1: moduli c and c + 1
    have hc1 : 1 ≤ c := by omega
    have hco : Nat.Coprime c (c + 1) := by
      rw [← Nat.isCoprime_iff_coprime]
      exact ⟨-1, 1, by push_cast; ring⟩
    obtain ⟨E, hE, h1, h2⟩ := crt_int c (c + 1) (by omega) (by omega) hco (-u) (-v)
    refine ⟨E, ?_, ?_, ?_⟩
    · have : c * (c + 1) ≤ (b + 1) * (b - 1) := by
        rw [hc]; rw [show 2 * c + 1 - 1 = 2 * c by omega]; nlinarith
      omega
    · have e : (b : ℤ) - 1 = 2 * c := by rw [hc]; push_cast; ring
      rw [e]
      have : (2 * u + 1) + 2 * (E : ℤ) - 1 = 2 * ((E : ℤ) - -u) := by ring
      rw [this]; exact mul_dvd_mul_left 2 h1
    · have e : (b : ℤ) + 1 = 2 * ((c + 1 : ℕ) : ℤ) := by rw [hc]; push_cast; ring
      rw [e]
      have : (2 * v + 1) + 2 * (E : ℤ) - 1 = 2 * ((E : ℤ) - -v) := by ring
      rw [this]; exact mul_dvd_mul_left 2 h2

/-- Greedy split of `E ≤ k(b-1)` into `k` digits. -/
def dig (b E i : ℕ) : ℕ := min (b - 1) (E - (b - 1) * i)

theorem sum_dig (b E k : ℕ) : ∑ i ∈ range k, dig b E i = min E (k * (b - 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    unfold dig
    rcases Nat.lt_or_ge E (k * (b - 1)) with h | h
    · have : E - (b - 1) * k = 0 := by
        rw [Nat.sub_eq_zero_iff_le]; rw [mul_comm]; omega
      rw [this, min_eq_left h.le]
      have h2 : E ≤ (k + 1) * (b - 1) := le_trans h.le (Nat.mul_le_mul_right _ (by omega))
      rw [min_eq_left h2]
      simp
    · rw [min_eq_right h, mul_comm (b - 1) k]
      rw [show (k + 1) * (b - 1) = k * (b - 1) + (b - 1) by ring]
      omega

theorem dig_lt (b E i : ℕ) (hb : 1 ≤ b) : dig b E i < b := by
  unfold dig; omega


/-! ## Remaining interfaces -/





/-! ## Density of `Π*` -/
theorem palVal_eq_sum (b N : ℕ) (d : DigVec b N) :
    (palVal b N d : ℤ) = ∑ k ∈ range (N + 1), (extDig d k : ℤ) * (cK b N k : ℤ) := by
  unfold palVal
  push_cast
  rw [← Fin.sum_univ_eq_sum_range (fun k => (extDig d k : ℤ) * (cK b N k : ℤ)) (N + 1)]
  apply Finset.sum_congr rfl
  intro i _
  rw [extDig_fin]

/-- `T₁ = Σ_{k<N} 2 d_k + d_N` (digit sum). -/
def tsum1 (b N : ℕ) (d : DigVec b N) : ℤ :=
  ∑ k ∈ range N, 2 * (extDig d k : ℤ) + extDig d N

/-- `T₂ = Σ_{k<N} 2 (−1)^k d_k + (−1)^N d_N` (alternating digit sum). -/
def tsum2 (b N : ℕ) (d : DigVec b N) : ℤ :=
  ∑ k ∈ range N, 2 * (-1) ^ k * (extDig d k : ℤ) + (-1) ^ N * extDig d N

theorem palVal_modEq_sub (b N : ℕ) (d : DigVec b N) :
    ((b : ℤ) - 1) ∣ (palVal b N d : ℤ) - tsum1 b N d := by
  rw [palVal_eq_sum, tsum1, Finset.sum_range_succ]
  have hc : ∀ j : ℕ, ((b : ℤ) - 1) ∣ (b : ℤ) ^ j - 1 := fun j => by
    simpa using sub_dvd_pow_sub_pow (b : ℤ) 1 j
  have e : ∑ x ∈ range N, (extDig d x : ℤ) * (cK b N x : ℤ) + (extDig d N : ℤ) * (cK b N N : ℤ) -
      (∑ k ∈ range N, 2 * (extDig d k : ℤ) + (extDig d N : ℤ)) =
      ∑ x ∈ range N, (extDig d x : ℤ) * (((b : ℤ) ^ x - 1) + ((b : ℤ) ^ (2 * N - x) - 1)) +
        (extDig d N : ℤ) * ((b : ℤ) ^ N - 1) := by
    have h1 : ∀ x ∈ range N, (cK b N x : ℤ) = (b : ℤ) ^ x + (b : ℤ) ^ (2 * N - x) := by
      intro x hx; rw [Finset.mem_range] at hx; simp [cK, hx]
    have h2 : (cK b N N : ℤ) = (b : ℤ) ^ N := by simp [cK]
    rw [Finset.sum_congr rfl (fun x hx => by rw [h1 x hx]), h2]
    rw [show ∀ s t u v : ℤ, s + u - (t + v) = (s - t) + (u - v) by intros; ring,
      ← Finset.sum_sub_distrib]
    congr 1
    · apply Finset.sum_congr rfl; intro x _; ring
    · ring
  rw [e]
  apply dvd_add
  · apply Finset.dvd_sum
    intro x _
    exact Dvd.dvd.mul_left (dvd_add (hc x) (hc _)) _
  · exact Dvd.dvd.mul_left (hc N) _

theorem palVal_modEq_add (b N : ℕ) (d : DigVec b N) :
    ((b : ℤ) + 1) ∣ (palVal b N d : ℤ) - tsum2 b N d := by
  rw [palVal_eq_sum, tsum2, Finset.sum_range_succ]
  have hc : ∀ j : ℕ, ((b : ℤ) + 1) ∣ (b : ℤ) ^ j - (-1) ^ j := fun j => by
    simpa using sub_dvd_pow_sub_pow (b : ℤ) (-1) j
  have e : ∑ x ∈ range N, (extDig d x : ℤ) * (cK b N x : ℤ) + (extDig d N : ℤ) * (cK b N N : ℤ) -
      (∑ k ∈ range N, 2 * (-1) ^ k * (extDig d k : ℤ) + (-1) ^ N * (extDig d N : ℤ)) =
      ∑ x ∈ range N, (extDig d x : ℤ) * (((b : ℤ) ^ x - (-1) ^ x) +
        ((b : ℤ) ^ (2 * N - x) - (-1) ^ (2 * N - x))) +
        (extDig d N : ℤ) * ((b : ℤ) ^ N - (-1) ^ N) := by
    have h1 : ∀ x ∈ range N, (cK b N x : ℤ) = (b : ℤ) ^ x + (b : ℤ) ^ (2 * N - x) := by
      intro x hx; rw [Finset.mem_range] at hx; simp [cK, hx]
    have h2 : (cK b N N : ℤ) = (b : ℤ) ^ N := by simp [cK]
    have h3 : ∀ x ∈ range N, ((-1 : ℤ)) ^ (2 * N - x) = (-1) ^ x := by
      intro x hx
      rw [Finset.mem_range] at hx
      have : (-1 : ℤ) ^ (2 * N - x) * (-1) ^ x = 1 := by
        rw [← pow_add, show 2 * N - x + x = 2 * N by omega, pow_mul]; norm_num
      have h' : ((-1 : ℤ)) ^ x * (-1) ^ x = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
      calc (-1 : ℤ) ^ (2 * N - x) = (-1) ^ (2 * N - x) * ((-1) ^ x * (-1) ^ x) := by rw [h', mul_one]
        _ = ((-1) ^ (2 * N - x) * (-1) ^ x) * (-1) ^ x := by ring
        _ = (-1) ^ x := by rw [this, one_mul]
    rw [Finset.sum_congr rfl (fun x hx => by rw [h1 x hx]), h2]
    rw [show ∀ s t u v : ℤ, s + u - (t + v) = (s - t) + (u - v) by intros; ring,
      ← Finset.sum_sub_distrib]
    congr 1
    · apply Finset.sum_congr rfl; intro x hx; rw [h3 x hx]; ring
    · ring
  rw [e]
  apply dvd_add
  · apply Finset.dvd_sum
    intro x _
    exact Dvd.dvd.mul_left (dvd_add (hc x) (hc _)) _
  · exact Dvd.dvd.mul_left (hc N) _

theorem palVal_modEq_base (b N : ℕ) (hN : 1 ≤ N) (d : DigVec b N) :
    (b : ℤ) ∣ (palVal b N d : ℤ) - extDig d 0 := by
  rw [palVal_eq_sum, Finset.sum_range_succ' (fun k => (extDig d k : ℤ) * (cK b N k : ℤ))]
  have h0 : (cK b N 0 : ℤ) = 1 + (b : ℤ) ^ (2 * N) := by
    simp [cK, show 0 < N by omega]
  rw [h0]
  have e : ∑ k ∈ range N, (extDig d (k + 1) : ℤ) * (cK b N (k + 1) : ℤ) +
      (extDig d 0 : ℤ) * (1 + (b : ℤ) ^ (2 * N)) - (extDig d 0 : ℤ) =
      ∑ k ∈ range N, (extDig d (k + 1) : ℤ) * (cK b N (k + 1) : ℤ) +
        (extDig d 0 : ℤ) * (b : ℤ) ^ (2 * N) := by ring
  rw [e]
  apply dvd_add
  · apply Finset.dvd_sum
    intro k hk
    rw [Finset.mem_range] at hk
    apply Dvd.dvd.mul_left
    unfold cK
    split_ifs with h
    · push_cast
      exact dvd_add (dvd_pow_self _ (by omega)) (dvd_pow_self _ (by omega))
    · push_cast
      exact dvd_pow_self _ (by omega)
  · exact Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) _

/-- Control positions `2, 4, …, 2b+2`. -/
def ctrl (b : ℕ) : Finset ℕ := (range (b + 1)).image (fun i => 2 * (i + 1))

theorem mem_ctrl {b k : ℕ} : k ∈ ctrl b ↔ ∃ i < b + 1, k = 2 * (i + 1) := by
  simp only [ctrl, mem_image, mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩

theorem ctrl_bounds {b k : ℕ} (hk : k ∈ ctrl b) : 2 ≤ k ∧ k ≤ 2 * b + 2 ∧ k % 2 = 0 := by
  obtain ⟨i, hi, rfl⟩ := mem_ctrl.1 hk; omega

/-- Overwrite the control positions with the greedy digits of `E`. -/
def setCtrl {b N : ℕ} (hb : 1 ≤ b) (f : DigVec b N) (E : ℕ) : DigVec b N := fun k =>
  if (k : ℕ) ∈ ctrl b then ⟨dig b E ((k : ℕ) / 2 - 1), dig_lt b E _ hb⟩ else f k

theorem extDig_setCtrl {b N : ℕ} (hb : 1 ≤ b) (f : DigVec b N) (E k : ℕ) (hk : k ≤ N) :
    extDig (setCtrl hb f E) k = if k ∈ ctrl b then dig b E (k / 2 - 1) else extDig f k := by
  simp only [extDig, show k < N + 1 by omega, dite_true, setCtrl]
  split_ifs <;> rfl

theorem sum_ctrl_dig (b E : ℕ) (hE : E ≤ (b + 1) * (b - 1)) :
    ∑ k ∈ ctrl b, dig b E (k / 2 - 1) = E := by
  rw [ctrl, Finset.sum_image (fun x _ y _ h => by omega)]
  rw [show ∑ x ∈ range (b + 1), dig b E (2 * (x + 1) / 2 - 1) = ∑ x ∈ range (b + 1), dig b E x by
    apply Finset.sum_congr rfl; intro x _; congr 1; omega]
  rw [sum_dig, min_eq_left hE]

theorem tsum1_setCtrl {b N : ℕ} (hb : 1 ≤ b) (hN : 2 * b + 2 < N) (f : DigVec b N) (E : ℕ)
    (hE : E ≤ (b + 1) * (b - 1)) (hf : ∀ k ∈ ctrl b, extDig f k = 0) :
    tsum1 b N (setCtrl hb f E) = tsum1 b N f + 2 * E := by
  unfold tsum1
  have hN' : N ∉ ctrl b := fun h => by have := ctrl_bounds h; omega
  rw [extDig_setCtrl hb f E N le_rfl, ite_eq_right hN']
  have hsplit : ∑ k ∈ range N, 2 * (extDig (setCtrl hb f E) k : ℤ) =
      ∑ k ∈ range N, 2 * (extDig f k : ℤ) +
        2 * ∑ k ∈ range N, (if k ∈ ctrl b then (dig b E (k / 2 - 1) : ℤ) else 0) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    rw [extDig_setCtrl hb f E k hk.le]
    split_ifs with h
    · rw [hf k h]; push_cast; ring
    · ring
  rw [hsplit, Finset.sum_ite_mem, inter_eq_right.2 (fun k hk => by
    have := ctrl_bounds hk; rw [Finset.mem_range]; omega)]
  have := sum_ctrl_dig b E hE
  have h' : ∑ k ∈ ctrl b, (dig b E (k / 2 - 1) : ℤ) = E := by exact_mod_cast this
  rw [h']
  ring

theorem tsum2_setCtrl {b N : ℕ} (hb : 1 ≤ b) (hN : 2 * b + 2 < N) (f : DigVec b N) (E : ℕ)
    (hE : E ≤ (b + 1) * (b - 1)) (hf : ∀ k ∈ ctrl b, extDig f k = 0) :
    tsum2 b N (setCtrl hb f E) = tsum2 b N f + 2 * E := by
  unfold tsum2
  have hN' : N ∉ ctrl b := fun h => by have := ctrl_bounds h; omega
  rw [extDig_setCtrl hb f E N le_rfl, ite_eq_right hN']
  have hsplit : ∑ k ∈ range N, 2 * (-1) ^ k * (extDig (setCtrl hb f E) k : ℤ) =
      ∑ k ∈ range N, 2 * (-1) ^ k * (extDig f k : ℤ) +
        2 * ∑ k ∈ range N, (if k ∈ ctrl b then (dig b E (k / 2 - 1) : ℤ) else 0) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    rw [extDig_setCtrl hb f E k hk.le]
    split_ifs with h
    · rw [hf k h]
      have hev : (-1 : ℤ) ^ k = 1 := by
        obtain ⟨i, _, rfl⟩ := mem_ctrl.1 h
        rw [pow_mul]; norm_num
      rw [hev]; push_cast; ring
    · ring
  rw [hsplit, Finset.sum_ite_mem, inter_eq_right.2 (fun k hk => by
    have := ctrl_bounds hk; rw [Finset.mem_range]; omega)]
  have := sum_ctrl_dig b E hE
  have h' : ∑ k ∈ ctrl b, (dig b E (k / 2 - 1) : ℤ) = E := by exact_mod_cast this
  rw [h']
  ring

theorem coprime_of_dvd_sub_one (n m : ℕ) (h : (m : ℤ) ∣ (n : ℤ) - 1) : Nat.Coprime n m := by
  rw [← Nat.isCoprime_iff_coprime]
  obtain ⟨k, hk⟩ := h
  exact ⟨1, -k, by linarith⟩

theorem bigB_eq (b : ℕ) (hb : 1 ≤ b) : bigB b = (b - 1) * b * (b + 1) := by
  unfold bigB
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  rw [show c + 1 - 1 = c by omega]
  have : c * (c + 1) * (c + 1 + 1) + (c + 1) = (c + 1) ^ 3 := by ring
  omega

/-- **Positive density of `Π*_b(2N)`** (lower bound `b^{N−b−2}`). -/
theorem card_piStar_lower (b : ℕ) (hb : 2 ≤ b) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, c * (b : ℝ) ^ N ≤ #(piStar b N) := by
  have hb1 : 1 ≤ b := by omega
  refine ⟨1 / (b : ℝ) ^ (b + 2), by positivity, 2 * b + 5, fun N hN => ?_⟩
  classical
  -- the template set
  set special : Fin (N + 1) → Prop := fun i => (i : ℕ) = 0 ∨ (i : ℕ) = N ∨ (i : ℕ) ∈ ctrl b
  set T : Fin (N + 1) → Finset (Fin b) := fun i =>
    if (i : ℕ) = 0 ∨ (i : ℕ) = N then {⟨1, by omega⟩}
    else if (i : ℕ) ∈ ctrl b then {⟨0, by omega⟩} else univ with hT
  set t := Fintype.piFinset T with ht
  set good := (univ : Finset (DigVec b N)).filter (fun d => palVal b N d ∈ piStar b N)
  set piMap : DigVec b N → DigVec b N := fun d i => if (i : ℕ) ∈ ctrl b then ⟨0, by omega⟩ else d i
  have hsurj : Set.SurjOn piMap good t := by
    intro f hf
    rw [Finset.mem_coe, ht, Fintype.mem_piFinset] at hf
    have hf0 : ∀ k ∈ ctrl b, extDig f k = 0 := by
      intro k hk
      have hkN : k < N + 1 := by have := ctrl_bounds hk; omega
      have := hf ⟨k, hkN⟩
      simp only [hT, show ¬ (k = 0 ∨ k = N) by have := ctrl_bounds hk; omega, ite_false, hk,
        ite_true, mem_singleton] at this
      simp [extDig, hkN, this]
    have hfN : extDig f N = 1 := by
      have := hf ⟨N, by omega⟩
      simp only [hT, or_true, ite_true, mem_singleton] at this
      simp [extDig, this]
    have hf1 : extDig f 0 = 1 := by
      have := hf ⟨0, by omega⟩
      simp only [hT, true_or, ite_true, mem_singleton] at this
      simp only [extDig, show 0 < N + 1 by omega, dite_true]
      rw [this]
    have hodd1 : Odd (tsum1 b N f) := by
      unfold tsum1; rw [hfN]
      apply Even.add_odd _ odd_one
      rw [even_iff_two_dvd]
      exact Finset.dvd_sum (fun k _ => dvd_mul_right 2 _)
    have hodd2 : Odd (tsum2 b N f) := by
      unfold tsum2; rw [hfN]
      apply Even.add_odd _ (by rw [Nat.cast_one, mul_one]; exact Odd.pow ⟨-1, by norm_num⟩)
      rw [even_iff_two_dvd]
      exact Finset.dvd_sum (fun k _ => by rw [mul_assoc]; exact dvd_mul_right 2 _)
    obtain ⟨E, hE, h1, h2⟩ := exists_E b hb _ _ hodd1 hodd2
    have hn0 : (0 : ℕ) ∉ ctrl b := fun h => by have := ctrl_bounds h; omega
    refine ⟨setCtrl hb1 f E, ?_, ?_⟩
    · rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨mem_univ _, ?_⟩
      have he0 := extDig_setCtrl hb1 f E 0 (by omega)
      rw [ite_eq_right hn0, hf1] at he0
      have hd0 : ((setCtrl hb1 f E) 0 : ℕ) ≠ 0 := by
        simp only [extDig, show 0 < N + 1 by omega, dite_true] at he0
        rw [show (0 : Fin (N + 1)) = ⟨0, by omega⟩ from rfl, he0]
        norm_num
      have hpal : palVal b N (setCtrl hb1 f E) ∈
          (Ico (b ^ (2 * N)) (b ^ (2 * N + 1))).filter (IsPalindrome b) := by
        rw [pal_eq_image b N hb]
        exact Finset.mem_image.2 ⟨_, Finset.mem_filter.2 ⟨mem_univ _, hd0⟩, rfl⟩
      obtain ⟨hI, hP⟩ := Finset.mem_filter.1 hpal
      simp only [piStar, mem_filter]
      refine ⟨hI, hP, ?_⟩
      set n := palVal b N (setCtrl hb1 f E)
      have c1 : ((b - 1 : ℕ) : ℤ) ∣ (n : ℤ) - 1 := by
        have h' := palVal_modEq_sub b N (setCtrl hb1 f E)
        rw [tsum1_setCtrl hb1 (by omega) f E hE hf0] at h'
        have e : ((b - 1 : ℕ) : ℤ) = (b : ℤ) - 1 := by push_cast [hb1]; ring
        rw [e]
        have := dvd_add h' h1
        convert this using 1; ring
      have c2 : ((b + 1 : ℕ) : ℤ) ∣ (n : ℤ) - 1 := by
        have h' := palVal_modEq_add b N (setCtrl hb1 f E)
        rw [tsum2_setCtrl hb1 (by omega) f E hE hf0] at h'
        push_cast
        have := dvd_add h' h2
        convert this using 1; ring
      have c3 : (b : ℤ) ∣ (n : ℤ) - 1 := by
        have h' := palVal_modEq_base b N (by omega) (setCtrl hb1 f E)
        rw [he0] at h'
        simpa using h'
      rw [bigB_eq b hb1]
      exact Nat.Coprime.mul_right (Nat.Coprime.mul_right (coprime_of_dvd_sub_one _ _ c1)
        (coprime_of_dvd_sub_one _ _ c3)) (coprime_of_dvd_sub_one _ _ c2)
    · funext i
      simp only [piMap, setCtrl]
      split_ifs with h
      · have := hf i
        have hn : ¬ ((i : ℕ) = 0 ∨ (i : ℕ) = N) := by have := ctrl_bounds h; omega
        simp only [hT, hn, ite_false, h, ite_true, mem_singleton] at this
        exact this.symm
      · rfl
  have hcard_t : (b : ℝ) ^ (N - b - 2) ≤ #t := by
    rw [ht, Fintype.card_piFinset]
    have hc : ∀ i : Fin (N + 1), #(T i) = if special i then 1 else b := by
      intro i
      by_cases h1 : (i : ℕ) = 0 ∨ (i : ℕ) = N
      · have hs : special i := by simp only [special]; tauto
        simp only [hT]
        rw [ite_eq_left h1, ite_eq_left hs, card_singleton]
      · by_cases h2 : (i : ℕ) ∈ ctrl b
        · have hs : special i := by simp only [special]; tauto
          simp only [hT]
          rw [ite_eq_right h1, ite_eq_left h2, ite_eq_left hs, card_singleton]
        · have hs : ¬ special i := by simp only [special]; tauto
          simp only [hT]
          rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right hs, card_univ, Fintype.card_fin]
    simp only [hc]
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
    have hspec : #((univ : Finset (Fin (N + 1))).filter special) ≤ b + 3 := by
      have hsub : ((univ : Finset (Fin (N + 1))).filter special).map Fin.valEmbedding ⊆
          insert 0 (insert N (ctrl b)) := by
        intro k hk
        obtain ⟨i, hi, rfl⟩ := Finset.mem_map.1 hk
        have := (Finset.mem_filter.1 hi).2
        simp only [special] at this
        simp only [Fin.valEmbedding_apply, mem_insert]
        tauto
      have h1 := card_le_card hsub
      rw [card_map] at h1
      have h2 := card_insert_le 0 (insert N (ctrl b))
      have h3 := card_insert_le N (ctrl b)
      have h4 : #(ctrl b) ≤ b + 1 := by
        unfold ctrl; exact card_image_le.trans (by rw [card_range])
      omega
    have hns : N - b - 2 ≤ #((univ : Finset (Fin (N + 1))).filter (fun i => ¬ special i)) := by
      have := card_filter_add_card_filter_not (s := (univ : Finset (Fin (N + 1)))) special
      rw [card_univ, Fintype.card_fin] at this
      omega
    have : b ^ (N - b - 2) ≤ b ^ #((univ : Finset (Fin (N + 1))).filter (fun i => ¬ special i)) :=
      Nat.pow_le_pow_right (by omega) hns
    exact_mod_cast this
  have hgood : #t ≤ #good := Finset.card_le_card_of_surjOn piMap hsurj
  have himg : good.image (palVal b N) ⊆ piStar b N := by
    intro n hn
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hn
    exact (Finset.mem_filter.1 hd).2
  have hpi : #good ≤ #(piStar b N) := by
    rw [← card_image_of_injective _ (palVal_injective b N hb)]
    exact card_le_card himg
  have hbpos : (0 : ℝ) < (b : ℝ) ^ (b + 2) := by positivity
  calc 1 / (b : ℝ) ^ (b + 2) * (b : ℝ) ^ N = (b : ℝ) ^ (N - b - 2) := by
        rw [div_mul_eq_mul_div, one_mul, div_eq_iff hbpos.ne', ← pow_add]
        congr 1; omega
    _ ≤ #t := hcard_t
    _ ≤ #(piStar b N) := by exact_mod_cast hgood.trans hpi

theorem piStar_nonempty (b : ℕ) (hb : 2 ≤ b) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, (piStar b N).Nonempty := by
  obtain ⟨c, hc, N₀, h⟩ := card_piStar_lower b hb
  refine ⟨N₀, fun N hN => ?_⟩
  rw [← Finset.card_pos]
  have := h N hN
  have hpos : 0 < c * (b : ℝ) ^ N := by
    have : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
    positivity
  exact_mod_cast hpos.trans_le this

/-! ## M2: the exponential sum -/
theorem phiB_le (b : ℕ) (t : ℝ) : phiB b t ≤ b := by
  unfold phiB
  calc ‖∑ d ∈ range b, ee (d * t)‖ ≤ ∑ d ∈ range b, ‖ee (d * t)‖ := norm_sum_le _ _
    _ = b := by simp [norm_ee]

theorem phiB_nonneg (b : ℕ) (t : ℝ) : 0 ≤ phiB b t := norm_nonneg _

theorem filter_d0_eq_piFinset (b N : ℕ) :
    (univ : Finset (DigVec b N)).filter (fun d => (d 0 : ℕ) ≠ 0) =
      Fintype.piFinset (fun i : Fin (N + 1) =>
        if i = 0 then (univ : Finset (Fin b)).filter (fun a : Fin b => (a : ℕ) ≠ 0) else univ) := by
  ext d
  simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
  constructor
  · intro h i; split_ifs with hi
    · subst hi; simpa using h
    · exact mem_univ _
  · intro h; have := h 0; simpa using this

/-- **M2.** The exponential sum over palindromes factorizes (outer digit `1 ≤ d_0 < b`). -/
theorem expsum_factor (b N : ℕ) (_hb : 2 ≤ b) (_hN : 1 ≤ N) (α : ℝ) :
    ‖∑ d ∈ (univ : Finset (DigVec b N)).filter (fun d => (d 0 : ℕ) ≠ 0),
        ee (palVal b N d * α)‖ =
      ‖∑ a ∈ Ico 1 b, ee (a * (cK b N 0 * α))‖ *
        ∏ k ∈ Icc 1 N, phiB b (cK b N k * α) := by
  have hprod : ∀ d : DigVec b N, ee (palVal b N d * α) =
      ∏ i : Fin (N + 1), ee (((d i : ℕ) : ℝ) * (cK b N i * α)) := by
    intro d
    unfold palVal
    push_cast
    rw [Finset.sum_mul, ee_sum]
    apply Finset.prod_congr rfl
    intro i _
    congr 1; ring
  simp only [hprod]
  have hfac := Finset.prod_univ_sum (fun i : Fin (N + 1) =>
      if i = 0 then (univ : Finset (Fin b)).filter (fun a : Fin b => (a : ℕ) ≠ 0) else univ)
    (fun (i : Fin (N + 1)) (a : Fin b) => ee (((a : ℕ) : ℝ) * (cK b N i * α)))
  beta_reduce at hfac
  rw [filter_d0_eq_piFinset, ← hfac, norm_prod, Fin.prod_univ_succ]
  congr 1
  · simp only [ite_true, Fin.val_zero]
    congr 1
    rw [Finset.sum_filter,
      Fin.sum_univ_eq_sum_range (fun a => if a ≠ 0 then ee ((a : ℝ) * ((cK b N 0 : ℝ) * α)) else 0) b,
      ← Finset.sum_filter]
    congr 1
    ext a; simp only [mem_filter, mem_range, mem_Ico]; omega
  · simp only [Fin.succ_ne_zero, ite_false]
    rw [show ∏ k ∈ Icc 1 N, phiB b (cK b N k * α) =
        ∏ i : Fin N, phiB b (cK b N (i + 1) * α) by
      have hI : Icc 1 N = (range N).image (fun i => i + 1) := by
        ext k
        simp only [mem_Icc, mem_image, mem_range]
        constructor
        · intro h; exact ⟨k - 1, by omega, by omega⟩
        · rintro ⟨a, ha, rfl⟩; omega
      rw [hI, Finset.prod_image (fun x _ y _ h => by omega),
        ← Fin.prod_univ_eq_prod_range (fun k => phiB b (cK b N (k + 1) * α)) N]]
    apply Finset.prod_congr rfl
    intro i _
    rw [← norm_sum_fin_ee]
    simp [Fin.val_succ]

/-- The exponential sum over `Π_b(2N)` is at most `b² Φ_N(α)` (TP's product). -/
theorem expsum_le_PhiN (b N : ℕ) (hb : 2 ≤ b) (hN : 1 ≤ N) (α : ℝ) :
    ‖∑ d ∈ (univ : Finset (DigVec b N)).filter (fun d => (d 0 : ℕ) ≠ 0),
        ee (palVal b N d * α)‖ ≤ (b : ℝ) ^ 2 * PhiN b N α := by
  rw [expsum_factor b N hb hN α]
  have h0 : ‖∑ a ∈ Ico 1 b, ee (a * (cK b N 0 * α))‖ ≤ b := by
    calc _ ≤ ∑ a ∈ Ico 1 b, ‖ee (a * (cK b N 0 * α))‖ := norm_sum_le _ _
      _ = ((b - 1 : ℕ) : ℝ) := by simp [norm_ee]
      _ ≤ b := by exact_mod_cast Nat.sub_le b 1
  have hsplit : ∏ k ∈ Icc 1 N, phiB b (cK b N k * α) =
      (∏ k ∈ Ico 1 N, phiB b (cK b N k * α)) * phiB b (cK b N N * α) := by
    rw [← Finset.prod_Ico_mul_eq_prod_Icc (by omega)]
  have hPhi : ∏ k ∈ Ico 1 N, phiB b (cK b N k * α) = PhiN b N α := by
    unfold PhiN
    apply Finset.prod_congr rfl
    intro k hk
    rw [Finset.mem_Ico] at hk
    congr 1
    simp [cK, hk.2]
    ring
  rw [hsplit, hPhi]
  have hP0 : 0 ≤ PhiN b N α := Finset.prod_nonneg (fun _ _ => phiB_nonneg _ _)
  calc ‖∑ a ∈ Ico 1 b, ee (a * (cK b N 0 * α))‖ * (PhiN b N α * phiB b (cK b N N * α))
      ≤ b * (PhiN b N α * b) := by
        apply mul_le_mul h0 _ (mul_nonneg hP0 (phiB_nonneg _ _)) (by positivity)
        exact mul_le_mul_of_nonneg_left (phiB_le _ _) hP0
    _ = (b : ℝ) ^ 2 * PhiN b N α := by ring

end Palprimes
