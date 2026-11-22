import Palprimes.MainTerm.Tuples
import Palprimes.MainTerm.Approx3
import Palprimes.MainTerm.LogCoord

/-! Merged from the former `Tuples2.lean` (to keep the import depth below the lake limit). -/

/-! # The chain part of `MainY` as tuple sums in log coordinates

`tl y q = log q / log y`. `PhiL P xs`: the limit weight of a decreasing chain `xs` (log coordinates,
last entry the smallest), `Hy P b y l = PhiL (l.map tl) · Π_{q∈l} g(q)`.
`chain_sum_tuples`: the chain part of `MainY` is `V(y) Σ_{n<8} Σ_{q ∈ (primes<y)^{n+1}, q ↓} Hy(q)`. -/

set_option linter.style.longLine false

open Finset Real

namespace Palprimes.MT

open Palprimes.Greaves

noncomputable def tl (y : ℝ) (q : ℕ) : ℝ := Real.log q / Real.log y

noncomputable def PhiL (P : WPar) (xs : List ℝ) : ℝ :=
  open Classical in
  if RosX false 1 xs ∧ xs.getLastD 0 < 1 / 2 then
    (-1) ^ (xs.length - 1) * P.W (xs.getLastD 0) * Gs (stF false xs.length) ((1 - xs.sum) / xs.getLastD 0) / xs.getLastD 0
  else 0

noncomputable def Hy (P : WPar) (b : ℕ) (y : ℝ) (l : List ℕ) : ℝ := PhiL P (l.map (tl y)) * (l.map (gB b)).prod

theorem prod_toDec' (T : Finset ℕ) (f : ℕ → ℝ) : ((toDec T).map f).prod = ∏ q ∈ T, f q := by
  rw [← Finset.prod_map_toList]
  exact List.Perm.prod_eq (List.Perm.map _ (Finset.sort_perm_toList T _))

theorem getLastD_concat (xs : List ℝ) (a d : ℝ) : (xs ++ [a]).getLastD d = a := by
  simp

theorem log_prod_nat (T : Finset ℕ) (hT : ∀ q ∈ T, 0 < q) :
    Real.log (∏ q ∈ T, (q : ℝ)) = ∑ q ∈ T, Real.log q := by
  rw [Real.log_prod]
  intro q hq; have := hT q hq; positivity

/-- **One chain**: the `csTerm` with `leafLim` is `V(y) · Hy` of the chain. -/
theorem Hy_chain (P : WPar) (b : ℕ) (y : ℝ) (hy : 1 < y) (p : ℕ) (hp : p ∈ primesBelow y)
    (T : Finset ℕ) (hT : T ⊆ (primesBelow y).filter (fun q => p < q)) :
    (if p ∈ smP y then P.wn y p * csTerm (gB b) p (leafLim b y p) false y T else 0) =
      VB b y * Hy P b y (toDec T ++ [p]) := by
  classical
  have hy0 : 0 < y := by linarith
  have hly : 0 < Real.log y := Real.log_pos hy
  have hpp := (mem_primesBelow y p).1 hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.1.pos
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hpp.1.one_lt)
  have hTp : ∀ q ∈ T, 0 < q := fun q hq => ((mem_primesBelow y q).1 (Finset.mem_filter.1 (hT hq)).1).1.pos
  have hpos : ∀ q ∈ toDec T ++ [p], 0 < q := by
    intro q hq
    rcases List.mem_append.1 hq with h | h
    · exact hTp q ((mem_toDec T q).1 h)
    · rw [List.mem_singleton.1 h]; exact hpp.1.pos
  have hros := RosOK_iff_RosX y hy (toDec T ++ [p]) false y hy0 hpos
  rw [div_self hly.ne'] at hros
  have hsm : p ∈ smP y ↔ tl y p < 1 / 2 := by
    unfold smP tl
    rw [Finset.mem_filter, div_lt_iff₀ hly]
    have : (p : ℝ) ^ 2 < y ↔ 2 * Real.log p < Real.log y := by
      rw [← Real.log_lt_log_iff (by positivity) hy0, Real.log_pow]; push_cast; rfl
    rw [this]; constructor
    · rintro ⟨_, h⟩; linarith
    · intro h; exact ⟨hp, by linarith⟩
  have hmap : (toDec T ++ [p]).map (tl y) = (toDec T).map (tl y) ++ [tl y p] := by simp
  have hsum : ((toDec T ++ [p]).map (tl y)).sum = (∑ q ∈ T, Real.log q + Real.log p) / Real.log y := by
    rw [hmap, List.sum_append, sum_toDec]; simp only [List.sum_cons, List.sum_nil, add_zero, tl]
    rw [← Finset.sum_div, add_div]
  have hlen : ((toDec T ++ [p]).map (tl y)).length = T.card + 1 := by simp [length_toDec]
  have hprod : ((toDec T ++ [p]).map (gB b)).prod = (∏ q ∈ T, gB b q) * gB b p := by
    rw [List.map_append, List.prod_append, prod_toDec']; simp
  have hlz : Real.log (y / ((∏ q ∈ T, (q : ℝ)) * p)) = Real.log y - (∑ q ∈ T, Real.log q + Real.log p) := by
    have hPi : 0 < ∏ q ∈ T, (q : ℝ) := Finset.prod_pos (fun q hq => by have := hTp q hq; positivity)
    rw [Real.log_div hy0.ne' (by positivity), Real.log_mul hPi.ne' hp0.ne', log_prod_nat T hTp]
  unfold Hy PhiL
  rw [show ((toDec T ++ [p]).map (tl y)).getLastD 0 = tl y p by rw [hmap]; exact getLastD_concat _ _ _]
  rw [hlen, hsum, hprod]
  rw [show RosX false 1 ((toDec T ++ [p]).map (tl y)) ↔ RosOK false y (toDec T ++ [p]) from hros.symm]
  unfold csTerm leafLim
  rw [WPar.wn_prime P y p hpp.1]
  by_cases hR : RosOK false y (toDec T ++ [p])
  · by_cases hs : p ∈ smP y
    · rw [if_pos hs, if_pos hR, if_pos ⟨hR, hsm.1 hs⟩, hlz]
      unfold tl
      have e1 : (1 - (∑ q ∈ T, Real.log q + Real.log p) / Real.log y) / (Real.log p / Real.log y) =
          (Real.log y - (∑ q ∈ T, Real.log q + Real.log p)) / Real.log p := by field_simp
      rw [e1, Nat.add_sub_cancel]
      field_simp
    · have hc : ¬ (RosOK false y (toDec T ++ [p]) ∧ tl y p < 1 / 2) := fun h => hs (hsm.2 h.2)
      rw [if_neg hs, if_neg hc]; simp
  · have hc : ¬ (RosOK false y (toDec T ++ [p]) ∧ tl y p < 1 / 2) := fun h => hR h.1
    rw [if_neg hc]; simp [hR]

/-- A Rosser chain of length `≥ 2` with nonnegative decreasing entries has total `≤ c`. -/
theorem RosX_sum_le : ∀ (xs : List ℝ) (c : ℝ), RosX false c xs → xs.Pairwise (· ≥ ·) → (∀ a ∈ xs, 0 ≤ a) →
    2 ≤ xs.length → xs.sum ≤ c
  | [], _, _, _, _, h => by simp at h
  | [_], _, _, _, _, h => by simp at h
  | [a, b], c, hR, _, hnn, _ => by
    have h3 : 3 * b ≤ c - a := hR.1
    have hb := hnn b (by simp)
    simp only [List.sum_cons, List.sum_nil]; linarith
  | [a, b, d], c, hR, hpw, hnn, _ => by
    have h3 : 3 * b ≤ c - a := hR.1
    have hbd : b ≥ d := by
      have := List.pairwise_cons.1 (List.pairwise_cons.1 hpw).2
      exact this.1 d (by simp)
    have hb := hnn b (by simp)
    simp only [List.sum_cons, List.sum_nil]; linarith
  | a :: b :: d :: e :: rest, c, hR, hpw, hnn, _ => by
    have h3 : 3 * b ≤ c - a := hR.1
    have hR2 : RosX false (c - a - b) (d :: e :: rest) := hR.2
    have hpw2 := (List.pairwise_cons.1 (List.pairwise_cons.1 hpw).2).2
    have := RosX_sum_le (d :: e :: rest) (c - a - b) hR2 hpw2 (fun x hx => hnn x (by simp [hx])) (by simp)
    have hb := hnn b (by simp)
    simp only [List.sum_cons] at this ⊢; linarith

theorem tl_mono (y : ℝ) (hy : 1 < y) (q q' : ℕ) (hq : 0 < q) (h : q ≤ q') : tl y q ≤ tl y q' := by
  unfold tl
  have : (0 : ℝ) < q := by exact_mod_cast hq
  exact div_le_div_of_nonneg_right (Real.log_le_log this (by exact_mod_cast h)) (Real.log_pos hy).le

theorem tl_pos (y : ℝ) (hy : 1 < y) (q : ℕ) (hq : 1 < q) : 0 < tl y q :=
  div_pos (Real.log_pos (by exact_mod_cast hq)) (Real.log_pos hy)

/-- Chains longer than `8` have weight `0` (all entries `> T₀ ≥ 1/9`, total `≤ 1`). -/
theorem Hy_big (P : WPar) (b : ℕ) (y : ℝ) (hy : 1 < y) (hT9 : 1 / 9 ≤ P.T0) (U : Finset ℕ)
    (hU : U ⊆ primesBelow y) (hc : 8 < U.card) : Hy P b y (toDec U) = 0 := by
  classical
  have hne : U.Nonempty := Finset.card_pos.1 (by omega)
  set p := U.min' hne
  have hpU : p ∈ U := Finset.min'_mem U hne
  have hUe : U = insert p (U.erase p) := (Finset.insert_erase hpU).symm
  have hlt : ∀ x ∈ U.erase p, p < x := fun x hx =>
    lt_of_le_of_ne (Finset.min'_le U x (Finset.mem_of_mem_erase hx)) (Finset.ne_of_mem_erase hx).symm
  have hprime : ∀ q ∈ U, q.Prime := fun q hq => ((mem_primesBelow y q).1 (hU hq)).1
  have hL : toDec U = toDec (U.erase p) ++ [p] := by
    conv_lhs => rw [hUe]
    exact toDec_insert_min p _ hlt
  unfold Hy PhiL
  rw [hL]
  have hmap : (toDec (U.erase p) ++ [p]).map (tl y) = (toDec (U.erase p)).map (tl y) ++ [tl y p] := by simp
  rw [show ((toDec (U.erase p) ++ [p]).map (tl y)).getLastD 0 = tl y p by rw [hmap]; exact getLastD_concat _ _ _]
  split_ifs with h
  · by_cases hW : tl y p ≤ P.T0
    · rw [W_le_T0 P _ hW]; simp
    · exfalso
      push_neg at hW
      set xs := (toDec (U.erase p) ++ [p]).map (tl y)
      have hlen : xs.length = U.card := by
        simp only [xs, List.length_map, List.length_append, length_toDec, List.length_singleton]
        rw [Finset.card_erase_of_mem hpU]; omega
      have hpw : xs.Pairwise (· ≥ ·) := by
        simp only [xs, ← hL]
        rw [List.pairwise_map]
        exact (toDec_pairwise U).imp_of_mem (fun {a c} _ hc hac => tl_mono y hy c a
          (hprime c ((mem_toDec U c).1 hc)).pos hac.le)
      have hnn : ∀ a ∈ xs, 0 ≤ a := by
        intro a ha
        simp only [xs, ← hL, List.mem_map] at ha
        obtain ⟨q, hq, rfl⟩ := ha
        exact (tl_pos y hy q (hprime q ((mem_toDec U q).1 hq)).one_lt).le
      have hle := RosX_sum_le xs 1 h.1 hpw hnn (by omega)
      have hge : ∀ a ∈ xs, tl y p ≤ a := by
        intro a ha
        simp only [xs, ← hL, List.mem_map] at ha
        obtain ⟨q, hq, rfl⟩ := ha
        exact tl_mono y hy p q (hprime p hpU).pos (Finset.min'_le U q ((mem_toDec U q).1 hq))
      have hsum : (xs.length : ℝ) * tl y p ≤ xs.sum := by
        have := List.length_nsmul_le_sum xs (tl y p) hge
        simpa [nsmul_eq_mul] using this
      have h9 : (9 : ℝ) ≤ xs.length := by rw [hlen]; exact_mod_cast hc
      nlinarith
  · simp

/-- **The chain part of `MainY` as tuple sums.** -/
theorem chain_sum_tuples (P : WPar) (b : ℕ) (y : ℝ) (hy : 1 < y) (hT9 : 1 / 9 ≤ P.T0) :
    ∑ p ∈ smP y, ∑ T ∈ ((primesBelow y).filter (fun q => p < q)).powerset,
        P.wn y p * csTerm (gB b) p (leafLim b y p) false y T =
      VB b y * ∑ n ∈ Finset.range 8, ∑ q ∈ Fintype.piFinset (fun _ : Fin (n + 1) => primesBelow y),
        (if StrictAnti q then Hy P b y (List.ofFn q) else 0) := by
  classical
  set S := primesBelow y
  have h1 : ∑ p ∈ smP y, ∑ T ∈ (S.filter (fun q => p < q)).powerset,
        P.wn y p * csTerm (gB b) p (leafLim b y p) false y T =
      ∑ p ∈ S, ∑ T ∈ (S.filter (fun q => p < q)).powerset,
        (if p ∈ smP y then P.wn y p * csTerm (gB b) p (leafLim b y p) false y T else 0) := by
    have hsub : S.filter (fun p => p ∈ smP y) = smP y := by
      ext p; simp only [Finset.mem_filter]
      constructor
      · intro h; exact h.2
      · intro h; exact ⟨(Finset.mem_filter.1 h).1, h⟩
    conv_lhs => rw [← hsub]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    split_ifs with h
    · rfl
    · simp
  rw [h1]
  have h2 : ∀ p ∈ S, ∑ T ∈ (S.filter (fun q => p < q)).powerset,
      (if p ∈ smP y then P.wn y p * csTerm (gB b) p (leafLim b y p) false y T else 0) =
      VB b y * ∑ T ∈ (S.filter (fun q => p < q)).powerset, Hy P b y (toDec T ++ [p]) := by
    intro p hp
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T hT
    exact Hy_chain P b y hy p hp T (Finset.mem_powerset.1 hT)
  rw [Finset.sum_congr rfl h2, ← Finset.mul_sum, sum_chains_eq]
  congr 1
  rw [sum_powerset_range S _ (by simp) (fun U hU hc => by
    rw [if_neg (fun h => by rw [h] at hc; simp at hc)]; exact Hy_big P b y hy hT9 U hU hc)]
  apply Finset.sum_congr rfl
  intro n _
  rw [← sum_powersetCard_tuples]
  apply Finset.sum_congr rfl
  intro U hU
  have : U.card = n + 1 := (Finset.mem_powersetCard.1 hU).2
  rw [if_neg (fun h => by rw [h] at this; simp at this)]

end Palprimes.MT

/-! # `MainY / V(y)` as prime sums over boxes in log-log coordinates

`fch P n σ` (`σ ∈ ℝ^{n+1}`, `x_i = e^{σ_i}`): chain weight; `fbig P σ` (`σ ∈ ℝ¹`): large-prime weight.
`MainY_eq`: for `y > 1`,
`MainY = V(y) (Σ_{q ∈ Pset¹} g(q) fbig(sigv q) + Σ_{n<8} Σ_{q ∈ Pset^{n+1}} Π g(q_i) fch_n(sigv q))`. -/

set_option linter.style.longLine false

open Finset Real

namespace Palprimes.MT

open Palprimes.Greaves

noncomputable def fch (P : WPar) (n : ℕ) (σ : Fin (n + 1) → ℝ) : ℝ :=
  open Classical in if StrictAnti σ then PhiL P (List.ofFn (fun i => Real.exp (σ i))) else 0

noncomputable def fbig (P : WPar) (σ : Fin 1 → ℝ) : ℝ :=
  open Classical in
  if 1 / 2 ≤ Real.exp (σ 0) then
    (P.W (Real.exp (σ 0)) - (P.U - P.V)) * (2 * Real.exp Real.eulerMascheroniConstant) / (1 - Real.exp (σ 0))
  else 0

theorem mem_Pset (y a : ℝ) (hy : 1 ≤ y) (q : ℕ) : q ∈ Pset y a ↔ q.Prime ∧ y ^ a < q ∧ (q : ℝ) ≤ y := by
  unfold Pset
  rw [Finset.mem_filter, Finset.mem_Ioc, Nat.floor_lt (Real.rpow_nonneg (by linarith) a),
    Nat.le_floor_iff (by linarith)]
  tauto

theorem getLastD_ofFn {α : Type*} {n : ℕ} (g : Fin (n + 1) → α) (d : α) :
    (List.ofFn g).getLastD d = g (Fin.last n) := by
  rw [List.ofFn_succ', List.concat_eq_append]; simp

theorem exp_sig (y : ℝ) (hy : 1 < y) (q : ℕ) (hq : 1 < q) : Real.exp (sig y q) = tl y q := by
  have h := tl_pos y hy q hq
  unfold tl at h ⊢; unfold sig; exact Real.exp_log h

theorem sig_lt_iff (y : ℝ) (hy : 1 < y) (q q' : ℕ) (hq : 1 < q) (hq' : 1 < q') : sig y q < sig y q' ↔ q < q' := by
  have h1 := tl_pos y hy q hq
  have h2 := tl_pos y hy q' hq'
  unfold tl at h1 h2
  unfold sig
  rw [Real.log_lt_log_iff h1 h2]
  have hL := Real.log_pos hy
  rw [div_lt_div_iff_of_pos_right hL, Real.log_lt_log_iff (by positivity) (by positivity)]
  exact_mod_cast Iff.rfl

theorem strictAnti_sigv_iff {r : ℕ} (y : ℝ) (hy : 1 < y) (q : Fin r → ℕ) (hq : ∀ i, 1 < q i) :
    StrictAnti (sigv y q) ↔ StrictAnti q := by
  constructor
  · intro h i j hij; exact (sig_lt_iff y hy _ _ (hq j) (hq i)).1 (h hij)
  · intro h i j hij; exact (sig_lt_iff y hy _ _ (hq j) (hq i)).2 (h hij)

/-- `Hy` on a tuple is `Π g · fch ∘ sigv`. -/
theorem Hy_eq_fch (P : WPar) (b : ℕ) (y : ℝ) (hy : 1 < y) (n : ℕ) (q : Fin (n + 1) → ℕ) (hq : ∀ i, 1 < q i) :
    (open Classical in if StrictAnti q then Hy P b y (List.ofFn q) else 0) = (∏ i, gB b (q i)) * fch P n (sigv y q) := by
  classical
  unfold fch
  by_cases h : StrictAnti q
  · rw [if_pos h, if_pos ((strictAnti_sigv_iff y hy q hq).2 h)]
    unfold Hy
    rw [List.map_ofFn, List.map_ofFn, List.prod_ofFn, mul_comm]
    congr 2
    congr 1
    funext i
    simp only [Function.comp, sigv]
    rw [exp_sig y hy (q i) (hq i)]
  · rw [if_neg h, if_neg (fun h' => h ((strictAnti_sigv_iff y hy q hq).1 h')), mul_zero]

theorem PhiL_W_zero (P : WPar) (xs : List ℝ) (h : P.W (xs.getLastD 0) = 0) : PhiL P xs = 0 := by
  unfold PhiL; split_ifs
  · rw [h]; ring
  · rfl

/-- The tuple sums over `(primes < y)^{n+1}` and over `Pset y T₀^{n+1}` agree. -/
theorem tuple_sum_Pset (P : WPar) (b : ℕ) (y : ℝ) (hy : 1 < y) (n : ℕ) :
    ∑ q ∈ Fintype.piFinset (fun _ : Fin (n + 1) => primesBelow y), (open Classical in if StrictAnti q then Hy P b y (List.ofFn q) else 0) =
    ∑ q ∈ Fintype.piFinset (fun _ : Fin (n + 1) => Pset y P.T0), (open Classical in if StrictAnti q then Hy P b y (List.ofFn q) else 0) := by
  classical
  have hy0 : 0 < y := by linarith
  have hly : 0 < Real.log y := Real.log_pos hy
  set I := (primesBelow y).filter (fun q : ℕ => y ^ P.T0 < q)
  have hIS : I ⊆ primesBelow y := Finset.filter_subset _ _
  have hIP : I ⊆ Pset y P.T0 := by
    intro q hq
    have hqm := Finset.mem_filter.1 hq
    have hqp := (mem_primesBelow y q).1 hqm.1
    rw [mem_Pset y _ hy.le]; exact ⟨hqp.1, hqm.2, hqp.2.le⟩
  have hlast : ∀ q : Fin (n + 1) → ℕ, Hy P b y (List.ofFn q) =
      PhiL P (List.ofFn (fun i => tl y (q i))) * (List.ofFn (fun i => gB b (q i))).prod := by
    intro q; unfold Hy; rw [List.map_ofFn, List.map_ofFn]; rfl
  -- vanishing when the last entry is `≤ y^{T₀}`
  have hvan : ∀ q : Fin (n + 1) → ℕ, StrictAnti q → (q (Fin.last n) : ℝ) ≤ y ^ P.T0 → 0 < q (Fin.last n) →
      Hy P b y (List.ofFn q) = 0 := by
    intro q _ hle hpos
    rw [hlast, PhiL_W_zero, zero_mul]
    rw [getLastD_ofFn]
    apply W_le_T0
    unfold tl
    rw [div_le_iff₀ hly]
    have := Real.log_le_log (by exact_mod_cast hpos) hle
    rw [Real.log_rpow hy0] at this; linarith
  have e1 : ∑ q ∈ Fintype.piFinset (fun _ : Fin (n + 1) => primesBelow y), (if StrictAnti q then Hy P b y (List.ofFn q) else 0) =
      ∑ q ∈ Fintype.piFinset (fun _ : Fin (n + 1) => I), (if StrictAnti q then Hy P b y (List.ofFn q) else 0) := by
    symm
    apply Finset.sum_subset (Fintype.piFinset_subset _ _ (fun _ => hIS))
    intro q hq hqI
    split_ifs with hSA
    · rw [Fintype.mem_piFinset] at hq hqI
      push_neg at hqI
      obtain ⟨i, hi⟩ := hqI
      have hqi := (mem_primesBelow y (q i)).1 (hq i)
      have hle : (q i : ℝ) ≤ y ^ P.T0 := by
        by_contra h; exact hi (Finset.mem_filter.2 ⟨hq i, not_le.1 h⟩)
      have hli : q (Fin.last n) ≤ q i := hSA.antitone (Fin.le_last i)
      have hlp := ((mem_primesBelow y _).1 (hq (Fin.last n))).1
      exact hvan q hSA (le_trans (by exact_mod_cast hli) hle) hlp.pos
    · rfl
  have e2 : ∑ q ∈ Fintype.piFinset (fun _ : Fin (n + 1) => Pset y P.T0), (if StrictAnti q then Hy P b y (List.ofFn q) else 0) =
      ∑ q ∈ Fintype.piFinset (fun _ : Fin (n + 1) => I), (if StrictAnti q then Hy P b y (List.ofFn q) else 0) := by
    symm
    apply Finset.sum_subset (Fintype.piFinset_subset _ _ (fun _ => hIP))
    intro q hq hqI
    split_ifs with hSA
    · rw [Fintype.mem_piFinset] at hq hqI
      push_neg at hqI
      obtain ⟨i, hi⟩ := hqI
      have hqi := (mem_Pset y _ hy.le (q i)).1 (hq i)
      have hqy : (q i : ℝ) = y := by
        apply le_antisymm hqi.2.2
        by_contra h
        exact hi (Finset.mem_filter.2 ⟨(mem_primesBelow y _).2 ⟨hqi.1, not_le.1 h⟩, hqi.2.1⟩)
      have h0 := (mem_Pset y _ hy.le (q 0)).1 (hq 0)
      have hq0 : (q 0 : ℝ) = y := by
        apply le_antisymm h0.2.2
        rw [← hqy]; exact_mod_cast hSA.antitone (Fin.zero_le i)
      have ht0 : tl y (q 0) = 1 := by unfold tl; rw [hq0, div_self hly.ne']
      rw [hlast]
      unfold PhiL
      rw [if_neg, zero_mul]
      rintro ⟨hR, hlt⟩
      rcases n with _ | m
      · rw [getLastD_ofFn] at hlt
        have : Fin.last 0 = 0 := rfl
        rw [this, ht0] at hlt; norm_num at hlt
      · rw [List.ofFn_succ, List.ofFn_succ] at hR
        have h1 : 3 * tl y (q (Fin.succ 0)) ≤ 1 - tl y (q 0) := hR.1
        rw [ht0] at h1
        have hp1 := ((mem_Pset y _ hy.le _).1 (hq (Fin.succ 0))).1
        have := tl_pos y hy _ hp1.one_lt
        linarith
    · rfl
  rw [e1, e2]

theorem sum_fin_one (A : Finset ℕ) (F : (Fin 1 → ℕ) → ℝ) :
    ∑ q ∈ Fintype.piFinset (fun _ : Fin 1 => A), F q = ∑ a ∈ A, F (fun _ => a) := by
  exact Finset.sum_nbij' (fun q => q 0) (fun a => fun _ => a)
    (fun q hq => Fintype.mem_piFinset.1 hq 0) (fun a ha => Fintype.mem_piFinset.2 (fun _ => ha))
    (fun q _ => by funext i; rw [Fin.fin_one_eq_zero i]) (fun a _ => rfl)
    (fun q _ => by congr 1; funext i; rw [Fin.fin_one_eq_zero i])

/-- **The large primes as a one-dimensional prime sum.** -/
theorem big_sum_tuples (P : WPar) (b : ℕ) (y : ℝ) (hy : 1 < y) :
    ∑ Q ∈ bgP y, (P.wn y Q - P.wn y 1) * gB b Q * bigLim b y Q =
      VB b y * ∑ q ∈ Fintype.piFinset (fun _ : Fin 1 => Pset y P.T0), (∏ i, gB b (q i)) * fbig P (sigv y q) := by
  classical
  have hy0 : 0 < y := by linarith
  have hly : 0 < Real.log y := Real.log_pos hy
  have hT := P.hT1; have hU := P.hU; have hU1 := P.hU1
  rw [sum_fin_one, Finset.mul_sum]
  simp only [Fin.prod_univ_one]
  have hfb : ∀ a : ℕ, 1 < a → fbig P (sigv y (fun _ : Fin 1 => a)) =
      if 1 / 2 ≤ tl y a then (P.W (tl y a) - (P.U - P.V)) * (2 * Real.exp Real.eulerMascheroniConstant) / (1 - tl y a) else 0 := by
    intro a ha
    unfold fbig sigv; rw [exp_sig y hy a ha]
  apply Finset.sum_subset_zero_on_sdiff
  · intro Q hQ
    have hQm := Finset.mem_filter.1 hQ
    have hQp := (mem_primesBelow y Q).1 hQm.1
    have hQ2 : y ≤ (Q : ℝ) ^ 2 := not_lt.1 hQm.2
    rw [mem_Pset y _ hy.le]
    refine ⟨hQp.1, ?_, hQp.2.le⟩
    have h1 : y ^ P.T0 < y ^ (1 / 2 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt hy (by linarith)
    have hs : (y ^ (1 / 2 : ℝ)) ^ 2 = y := by rw [← Real.rpow_natCast, ← Real.rpow_mul hy0.le]; norm_num
    have h0 : 0 ≤ y ^ (1 / 2 : ℝ) := Real.rpow_nonneg hy0.le _
    have h2 : y ^ (1 / 2 : ℝ) ≤ Q := by nlinarith [Nat.cast_nonneg (α := ℝ) Q]
    linarith
  · intro a ha
    rw [Finset.mem_sdiff] at ha
    have hap := (mem_Pset y _ hy.le a).1 ha.1
    rw [hfb a hap.1.one_lt]
    split_ifs with h
    · -- `a = y`
      have hay : (a : ℝ) = y := by
        apply le_antisymm hap.2.2
        by_contra hlt
        apply ha.2
        refine Finset.mem_filter.2 ⟨(mem_primesBelow y a).2 ⟨hap.1, not_le.1 hlt⟩, ?_⟩
        unfold tl at h
        rw [le_div_iff₀ hly] at h
        have hap0 : (0 : ℝ) < (a : ℝ) ^ 2 := by have := hap.1.pos; positivity
        rw [not_lt, ← Real.log_le_log_iff hy0 hap0, Real.log_pow]; push_cast; linarith
      have ht : tl y a = 1 := by unfold tl; rw [hay, div_self hly.ne']
      rw [ht, W_gt_U P 1 hU1]; simp
    · simp
  · intro Q hQ
    have hQm := Finset.mem_filter.1 hQ
    have hQp := (mem_primesBelow y Q).1 hQm.1
    have hQ2 : y ≤ (Q : ℝ) ^ 2 := not_lt.1 hQm.2
    have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQp.1.pos
    rw [hfb Q hQp.1.one_lt]
    have hh : 1 / 2 ≤ tl y Q := by
      unfold tl; rw [le_div_iff₀ hly]
      have := Real.log_le_log hy0 hQ2
      rw [Real.log_pow] at this; push_cast at this; linarith
    rw [if_pos hh, WPar.wn_prime P y Q hQp.1, WPar.wn_one]
    unfold bigLim tl
    have hlQ : Real.log Q < Real.log y := Real.log_lt_log hQ0 hQp.2
    rw [Real.log_div hy0.ne' hQ0.ne']
    have h1 : Real.log y - Real.log Q ≠ 0 := by linarith
    have h2 : 1 - Real.log Q / Real.log y ≠ 0 := by
      rw [sub_ne_zero]; intro h; rw [eq_div_iff hly.ne'] at h; linarith
    field_simp

/-- **`MainY` as prime sums over boxes.** -/
theorem MainY_eq (P : WPar) (b : ℕ) (y : ℝ) (hy : 1 < y) (hT9 : 1 / 9 ≤ P.T0) :
    MainY P b y = VB b y * (∑ q ∈ Fintype.piFinset (fun _ : Fin 1 => Pset y P.T0), (∏ i, gB b (q i)) * fbig P (sigv y q) +
      ∑ n ∈ Finset.range 8, ∑ q ∈ Fintype.piFinset (fun _ : Fin (n + 1) => Pset y P.T0),
        (∏ i, gB b (q i)) * fch P n (sigv y q)) := by
  classical
  have hch : ∑ n ∈ Finset.range 8, ∑ q ∈ Fintype.piFinset (fun _ : Fin (n + 1) => primesBelow y),
        (if StrictAnti q then Hy P b y (List.ofFn q) else 0) =
      ∑ n ∈ Finset.range 8, ∑ q ∈ Fintype.piFinset (fun _ : Fin (n + 1) => Pset y P.T0),
        (∏ i, gB b (q i)) * fch P n (sigv y q) := by
    apply Finset.sum_congr rfl
    intro n _
    rw [tuple_sum_Pset P b y hy n]
    apply Finset.sum_congr rfl
    intro q hq
    exact Hy_eq_fch P b y hy n q (fun i => ((mem_Pset y _ hy.le _).1 (Fintype.mem_piFinset.1 hq i)).1.one_lt)
  unfold MainY
  rw [big_sum_tuples P b y hy, chain_sum_tuples P b y hy hT9, hch, mul_add]

end Palprimes.MT
