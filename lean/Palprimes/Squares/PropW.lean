import Palprimes.ExpSum.Collision
import Palprimes.Digits.Palindromes

/-! # M11. Proposition W: prime-square divisors (replaces TP Prop. 10.1)

`lean/plan/squares/PROP_W.md` (audited, `AUDIT_W.md`). Blocks from the middle outwards
`K1` (doubled, length aℓ), `K2` (single, (1−a)ℓ), `K3` (doubled, aℓ/(1+θ_b)), `V` (outer, ℓ),
`ℓ = log_b P`. Two Cauchy–Schwarz levels; every factor is a collision count mod `p²`
(`sum_sq_fourier_le_collision`, `collision_prob`, `prob_eq_le_l2`) plus the fact that a
nonzero `|w| < x` has at most `log x / (2 log P)` prime-square divisors `p² ≥ P²`.
`piStar` has one length only, so the cylinder issue of the audit does not arise.
Effort 500–900 lines. -/

set_option linter.style.longLine false

open Finset Real

namespace Palprimes

/-! ## Generic counting: Cauchy–Schwarz on fibres, splicing independent coordinates -/

theorem card_filter_eq_sum_fiber {Z W : Type*} [Fintype Z] [Fintype W] (u : Z → ℤ) (v : W → ℤ)
    (R : Finset ℤ) (hu : ∀ z, u z ∈ R) :
    #((univ : Finset (Z × W)).filter (fun p => u p.1 = v p.2)) =
      ∑ r ∈ R, #((univ : Finset Z).filter (fun z => u z = r)) *
        #((univ : Finset W).filter (fun w => v w = r)) := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := fun p : Z × W => u p.1) (t := R)
    (fun p _ => hu p.1)]
  apply Finset.sum_congr rfl
  intro r _
  rw [← Finset.card_product]
  congr 1
  ext ⟨z, w⟩
  simp only [mem_filter, mem_univ, true_and, mem_product]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, h1 ▸ h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1.trans h2.symm, h1⟩

/-- **Cauchy–Schwarz on fibres.** -/
theorem card_eq_le_sqrt {X Y : Type*} [Fintype X] [Fintype Y] (a : X → ℤ) (c : Y → ℤ) :
    (#((univ : Finset (X × Y)).filter (fun p => a p.1 = c p.2)) : ℝ) ≤
      Real.sqrt (#((univ : Finset (X × X)).filter (fun p => a p.1 = a p.2))) *
        Real.sqrt (#((univ : Finset (Y × Y)).filter (fun p => c p.1 = c p.2))) := by
  classical
  set R : Finset ℤ := univ.image a ∪ univ.image c
  have ha : ∀ x, a x ∈ R := fun x => mem_union_left _ (mem_image_of_mem a (mem_univ x))
  have hc : ∀ y, c y ∈ R := fun y => mem_union_right _ (mem_image_of_mem c (mem_univ y))
  rw [card_filter_eq_sum_fiber a c R ha, card_filter_eq_sum_fiber a a R ha,
    card_filter_eq_sum_fiber c c R hc]
  push_cast
  simp only [← sq]
  exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

theorem emod_eq_iff_dvd (q a c : ℤ) : a % q = c % q ↔ q ∣ a - c :=
  Int.modEq_iff_dvd.trans dvd_sub_comm

/-- **Cauchy–Schwarz for solutions of a congruence.** -/
theorem card_dvd_add_le {X Y : Type*} [Fintype X] [Fintype Y] (q : ℤ) (F : X → ℤ) (G : Y → ℤ) :
    (#((univ : Finset (X × Y)).filter (fun p => q ∣ F p.1 + G p.2)) : ℝ) ≤
      Real.sqrt (#((univ : Finset (X × X)).filter (fun p => q ∣ F p.1 - F p.2))) *
        Real.sqrt (#((univ : Finset (Y × Y)).filter (fun p => q ∣ G p.1 - G p.2))) := by
  have h := card_eq_le_sqrt (fun x => F x % q) (fun y => (-G y) % q)
  have e1 : (univ : Finset (X × Y)).filter (fun p => q ∣ F p.1 + G p.2) =
      (univ : Finset (X × Y)).filter (fun p => F p.1 % q = (-G p.2) % q) := by
    ext p; simp only [mem_filter, mem_univ, true_and, emod_eq_iff_dvd, sub_neg_eq_add]
  have e2 : (univ : Finset (X × X)).filter (fun p => q ∣ F p.1 - F p.2) =
      (univ : Finset (X × X)).filter (fun p => F p.1 % q = F p.2 % q) := by
    ext p; simp only [mem_filter, mem_univ, true_and, emod_eq_iff_dvd]
  have e3 : (univ : Finset (Y × Y)).filter (fun p => q ∣ G p.1 - G p.2) =
      (univ : Finset (Y × Y)).filter (fun p => (-G p.1) % q = (-G p.2) % q) := by
    ext p
    simp only [mem_filter, mem_univ, true_and, emod_eq_iff_dvd]
    rw [show -G p.1 - -G p.2 = -(G p.1 - G p.2) by ring, dvd_neg]
  rw [e1, e2, e3]
  exact h

/-- Splicing two vectors along a coordinate set. -/
def spl {I β : Type*} [DecidableEq I] (S : Finset I) (d e : I → β) : I → β :=
  fun i => if i ∈ S then d i else e i

/-- `F` depends only on the coordinates in `S`. -/
def DepOn {I β : Type*} (F : (I → β) → ℤ) (S : Finset I) : Prop :=
  ∀ d e : I → β, (∀ i ∈ S, d i = e i) → F d = F e

/-- `G` depends only on the coordinates outside `S`. -/
def DepOff {I β : Type*} (G : (I → β) → ℤ) (S : Finset I) : Prop :=
  ∀ d e : I → β, (∀ i ∉ S, d i = e i) → G d = G e

/-- The swap `(d, e) ↦ (spl d e, spl e d)` is an involution. -/
def splPerm {I β : Type*} [DecidableEq I] (S : Finset I) : Equiv.Perm ((I → β) × (I → β)) :=
  Function.Involutive.toPerm (fun x => (spl S x.1 x.2, spl S x.2 x.1)) (by
    intro x
    ext i <;> by_cases h : i ∈ S <;> simp [spl, h])

theorem sum_splice {I β M : Type*} [Fintype I] [DecidableEq I] [Fintype β] [AddCommMonoid M]
    (S : Finset I) (ψ : (I → β) → M) :
    ∑ x : (I → β) × (I → β), ψ (spl S x.1 x.2) = Fintype.card (I → β) • ∑ d, ψ d := by
  classical
  have h : ∑ x : (I → β) × (I → β), ψ (spl S x.1 x.2) = ∑ x : (I → β) × (I → β), ψ x.1 :=
    Equiv.sum_comp (splPerm (β := β) S) (fun x => ψ x.1)
  rw [h, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ]
  rw [Finset.smul_sum]

/-- **Independence by splicing**: if `F` sees only `S` and `G` only the complement, then
pairs `(d, e)` count like single vectors. -/
theorem card_splice {I β : Type*} [Fintype I] [DecidableEq I] [Fintype β] (S : Finset I)
    (F G : (I → β) → ℤ) (hF : DepOn F S) (hG : DepOff G S) (P : ℤ → ℤ → Prop)
    [DecidableRel P] :
    #((univ : Finset ((I → β) × (I → β))).filter (fun x => P (F x.1) (G x.2))) =
      Fintype.card (I → β) * #((univ : Finset (I → β)).filter (fun d => P (F d) (G d))) := by
  classical
  have hspl : ∀ x : (I → β) × (I → β), P (F x.1) (G x.2) ↔
      P (F (spl S x.1 x.2)) (G (spl S x.1 x.2)) := by
    intro x
    rw [hF (spl S x.1 x.2) x.1 (fun i hi => by simp [spl, hi]),
      hG (spl S x.1 x.2) x.2 (fun i hi => by simp [spl, hi])]
  rw [Finset.card_filter, Finset.card_filter]
  simp only [hspl]
  rw [sum_splice S (fun w => if P (F w) (G w) then 1 else 0), smul_eq_mul]


/-! ## Block sums of palindrome digits -/

/-- Block sum `X_S(d) = Σ_{k∈S} d_k c_k`. -/
def blk (b N : ℕ) (S : Finset ℕ) (d : DigVec b N) : ℤ :=
  ∑ k ∈ S, (extDig d k : ℤ) * (cK b N k : ℤ)

/-- Coordinates of `Fin (N+1)` lying in `S`. -/
def finSet (N : ℕ) (S : Finset ℕ) : Finset (Fin (N + 1)) := univ.filter (fun i => (i : ℕ) ∈ S)

theorem extDig_eq_of_agree {b N : ℕ} (S : Finset ℕ) (d e : DigVec b N)
    (h : ∀ i ∈ finSet N S, d i = e i) (k : ℕ) (hk : k ∈ S) : extDig d k = extDig e k := by
  unfold extDig
  split_ifs with hkN
  · rw [h ⟨k, hkN⟩ (by simp [finSet, hk])]
  · rfl

theorem blk_depOn {b N : ℕ} (S : Finset ℕ) : DepOn (blk b N S) (finSet N S) := fun d e h => by
  unfold blk
  apply Finset.sum_congr rfl
  intro k hk
  rw [extDig_eq_of_agree S d e h k hk]

theorem mem_finSet {N : ℕ} {S : Finset ℕ} {i : Fin (N + 1)} : i ∈ finSet N S ↔ (i : ℕ) ∈ S := by
  simp [finSet]

theorem blk_depOn_mono {b N : ℕ} {S T : Finset ℕ} (hST : S ⊆ T) (d e : DigVec b N)
    (h : ∀ i ∈ finSet N T, d i = e i) : blk b N S d = blk b N S e :=
  blk_depOn S d e (fun i hi => h i (mem_finSet.2 (hST (mem_finSet.1 hi))))

theorem blk_depOff {b N : ℕ} (S T : Finset ℕ) (hST : Disjoint S T) :
    DepOff (blk b N T) (finSet N S) := fun d e h => by
  unfold blk
  apply Finset.sum_congr rfl
  intro k hk
  congr 2
  unfold extDig
  split_ifs with hkN
  · have hnot : (⟨k, hkN⟩ : Fin (N + 1)) ∉ finSet N S :=
      fun hm => Finset.disjoint_right.1 hST hk (mem_finSet.1 hm)
    rw [h ⟨k, hkN⟩ hnot]
  · rfl

theorem blk_union {b N : ℕ} (S T : Finset ℕ) (hST : Disjoint S T) (d : DigVec b N) :
    blk b N (S ∪ T) d = blk b N S d + blk b N T d := by
  unfold blk
  rw [Finset.sum_union hST]

theorem palVal_eq_blk (b N : ℕ) (d : DigVec b N) :
    (palVal b N d : ℤ) = blk b N (range (N + 1)) d := by
  unfold palVal blk
  push_cast
  rw [← Fin.sum_univ_eq_sum_range (fun k => (extDig d k : ℤ) * (cK b N k : ℤ)) (N + 1)]
  apply Finset.sum_congr rfl
  intro i _
  rw [extDig_fin]

theorem card_digVec (b N : ℕ) : Fintype.card (DigVec b N) = b ^ (N + 1) := by
  simp [DigVec]

/-- Pair collisions of a block modulo `q`. -/
def collP (b N : ℕ) (S : Finset ℕ) (q : ℤ) : ℕ :=
  #((univ : Finset (DigVec b N × DigVec b N)).filter
    (fun x => q ∣ blk b N S x.1 - blk b N S x.2))

/-- Quadruple collisions of `Y = X_A(d) + X_A(d') + X_B(d)` modulo `q`. -/
def collQ (b N : ℕ) (A B : Finset ℕ) (q : ℤ) : ℕ :=
  #((univ : Finset (Quad b N)).filter (fun w =>
    q ∣ (blk b N A w.1 + blk b N A w.2.1 + blk b N B w.1) -
      (blk b N A w.2.2.1 + blk b N A w.2.2.2 + blk b N B w.2.2.1)))

/-- **First Cauchy–Schwarz level.** -/
theorem level1 (b N : ℕ) (q : ℤ) (V U : Finset ℕ) (hVU : Disjoint V U)
    (hcov : V ∪ U = range (N + 1)) :
    (b : ℝ) ^ (N + 1) * #((univ : Finset (DigVec b N)).filter (fun d => q ∣ (palVal b N d : ℤ)))
      ≤ Real.sqrt (collP b N V q) * Real.sqrt (collP b N U q) := by
  classical
  have hsp := card_splice (finSet N V) (blk b N V) (blk b N U) (blk_depOn V)
    (blk_depOff V U hVU) (fun a c => q ∣ a + c)
  have hpal : (univ : Finset (DigVec b N)).filter (fun d => q ∣ (palVal b N d : ℤ)) =
      (univ : Finset (DigVec b N)).filter (fun d => q ∣ blk b N V d + blk b N U d) := by
    ext d
    simp only [mem_filter, mem_univ, true_and]
    rw [palVal_eq_blk, ← hcov, blk_union V U hVU]
  rw [hpal]
  have h := card_dvd_add_le q (blk b N V) (blk b N U)
  rw [hsp, card_digVec] at h
  push_cast at h
  exact h

/-- Pairs of digit vectors as one vector on `Fin (N+1) ⊕ Fin (N+1)`. -/
abbrev DigVec2 (b N : ℕ) := Fin (N + 1) ⊕ Fin (N + 1) → Fin b

/-- Left and right halves. -/
def lft {b N : ℕ} (z : DigVec2 b N) : DigVec b N := fun i => z (Sum.inl i)
def rgt {b N : ℕ} (z : DigVec2 b N) : DigVec b N := fun i => z (Sum.inr i)

def pairEquiv (b N : ℕ) : DigVec2 b N ≃ DigVec b N × DigVec b N where
  toFun z := (lft z, rgt z)
  invFun x := Sum.elim x.1 x.2
  left_inv z := by ext (i | i) <;> rfl
  right_inv x := by rfl

/-- `(z, z') ↦ (d, e', e, d')`. -/
def quadEquivF (b N : ℕ) : DigVec2 b N × DigVec2 b N ≃ Quad b N where
  toFun x := (lft x.1, rgt x.2, lft x.2, rgt x.1)
  invFun w := (Sum.elim w.1 w.2.2.2, Sum.elim w.2.2.1 w.2.1)
  left_inv x := by ext (i | i) <;> rfl
  right_inv w := by rfl

/-- `(z, z') ↦ (e', d, d', e)`. -/
def quadEquivG (b N : ℕ) : DigVec2 b N × DigVec2 b N ≃ Quad b N where
  toFun x := (rgt x.2, lft x.1, rgt x.1, lft x.2)
  invFun w := (Sum.elim w.2.1 w.2.2.1, Sum.elim w.2.2.2 w.1)
  left_inv x := by ext (i | i) <;> rfl
  right_inv w := by rfl

theorem pairEquiv_apply {b N : ℕ} (z : DigVec2 b N) : pairEquiv b N z = (lft z, rgt z) := rfl
theorem quadEquivF_apply {b N : ℕ} (x : DigVec2 b N × DigVec2 b N) :
    quadEquivF b N x = (lft x.1, rgt x.2, lft x.2, rgt x.1) := rfl
theorem quadEquivG_apply {b N : ℕ} (x : DigVec2 b N × DigVec2 b N) :
    quadEquivG b N x = (rgt x.2, lft x.1, rgt x.1, lft x.2) := rfl

theorem card_digVec2 (b N : ℕ) : Fintype.card (DigVec2 b N) = b ^ (2 * (N + 1)) := by
  simp [DigVec2]
  ring

/-- **Second Cauchy–Schwarz level** (doubling on `K1` and `K3`, `K2` shared). -/
theorem level2 (b N : ℕ) (q : ℤ) (K1 K2 K3 : Finset ℕ) (h12 : Disjoint K1 K2)
    (h13 : Disjoint K1 K3) (h23 : Disjoint K2 K3) :
    (b : ℝ) ^ (2 * (N + 1)) * collP b N (K1 ∪ K2 ∪ K3) q ≤
      Real.sqrt (collQ b N K1 K2 q) * Real.sqrt (collQ b N K3 K2 q) := by
  classical
  set F : DigVec2 b N → ℤ := fun z =>
    blk b N K1 (lft z) - blk b N K1 (rgt z) + blk b N K2 (lft z) with hF
  set G : DigVec2 b N → ℤ := fun z =>
    blk b N K3 (lft z) - blk b N K3 (rgt z) - blk b N K2 (rgt z) with hG
  set SF : Finset (Fin (N + 1) ⊕ Fin (N + 1)) := (finSet N (K1 ∪ K2)).disjSum (finSet N K1)
  have hFdep : DepOn F SF := by
    intro z z' h
    have hl : ∀ i ∈ finSet N (K1 ∪ K2), lft z i = lft z' i :=
      fun i hi => h (Sum.inl i) (Finset.inl_mem_disjSum.2 hi)
    have hr : ∀ i ∈ finSet N K1, rgt z i = rgt z' i :=
      fun i hi => h (Sum.inr i) (Finset.inr_mem_disjSum.2 hi)
    simp only [hF]
    rw [blk_depOn_mono subset_union_left _ _ hl, blk_depOn K1 _ _ hr,
      blk_depOn_mono subset_union_right _ _ hl]
  have hGdep : DepOff G SF := by
    intro z z' h
    have hl : ∀ i ∈ finSet N K3, lft z i = lft z' i := by
      intro i hi
      apply h (Sum.inl i)
      rw [Finset.inl_mem_disjSum, mem_finSet]
      intro hm
      rcases Finset.mem_union.1 hm with h1 | h2
      · exact Finset.disjoint_left.1 h13 h1 (mem_finSet.1 hi)
      · exact Finset.disjoint_left.1 h23 h2 (mem_finSet.1 hi)
    have hr : ∀ i ∈ finSet N (K2 ∪ K3), rgt z i = rgt z' i := by
      intro i hi
      apply h (Sum.inr i)
      rw [Finset.inr_mem_disjSum, mem_finSet]
      intro hm
      rcases Finset.mem_union.1 (mem_finSet.1 hi) with h2 | h3
      · exact Finset.disjoint_left.1 h12 hm h2
      · exact Finset.disjoint_left.1 h13 hm h3
    simp only [hG]
    rw [blk_depOn K3 _ _ hl, blk_depOn_mono subset_union_right _ _ hr,
      blk_depOn_mono subset_union_left _ _ hr]
  have hsp := card_splice SF F G hFdep hGdep (fun a c => q ∣ a + c)
  -- collP of the union equals the diagonal count
  have hdiag : collP b N (K1 ∪ K2 ∪ K3) q =
      #((univ : Finset (DigVec2 b N)).filter (fun z => q ∣ F z + G z)) := by
    unfold collP
    symm
    apply Finset.card_equiv (pairEquiv b N)
    intro z
    simp only [mem_filter, mem_univ, true_and, pairEquiv_apply, hF, hG]
    rw [blk_union _ _ (Finset.disjoint_union_left.2 ⟨h13, h23⟩),
      blk_union _ _ (Finset.disjoint_union_left.2 ⟨h13, h23⟩), blk_union _ _ h12,
      blk_union _ _ h12]
    constructor <;> intro h <;> convert h using 1 <;> ring
  have hcF : #((univ : Finset (DigVec2 b N × DigVec2 b N)).filter
      (fun x => q ∣ F x.1 - F x.2)) = collQ b N K1 K2 q := by
    unfold collQ
    apply Finset.card_equiv (quadEquivF b N)
    intro x
    simp only [mem_filter, mem_univ, true_and, quadEquivF_apply, hF]
    constructor <;> intro h <;> convert h using 1 <;> ring
  have hcG : #((univ : Finset (DigVec2 b N × DigVec2 b N)).filter
      (fun x => q ∣ G x.1 - G x.2)) = collQ b N K3 K2 q := by
    unfold collQ
    apply Finset.card_equiv (quadEquivG b N)
    intro x
    simp only [mem_filter, mem_univ, true_and, quadEquivG_apply, hG]
    constructor <;> intro h <;> convert h using 1 <;> ring
  have h := card_dvd_add_le q F G
  rw [hsp, card_digVec2, hcF, hcG, ← hdiag] at h
  push_cast at h
  exact h


/-! ## Prime-square divisors -/

/-- Few prime squares divide a nonzero integer: `#{p ≥ P prime : p² ∣ w} ≤ log|w| / (2 log P)`. -/
theorem card_prime_sq_dvd_le (s : Finset ℕ) (w : ℤ) (hw : w ≠ 0) (P : ℕ) (hP : 2 ≤ P) :
    (#(s.filter (fun p => p.Prime ∧ P ≤ p ∧ (p : ℤ) ^ 2 ∣ w)) : ℝ) ≤
      Real.log |w| / (2 * Real.log P) := by
  set T := s.filter (fun p => p.Prime ∧ P ≤ p ∧ (p : ℤ) ^ 2 ∣ w)
  have hdvd : (∏ p ∈ T, ((p : ℤ) ^ 2)) ∣ w := by
    apply Finset.prod_dvd_of_coprime
    · intro p hp p' hp' hne
      have h1 := (Finset.mem_filter.1 hp).2.1
      have h2 := (Finset.mem_filter.1 hp').2.1
      simp only [Function.onFun]
      apply IsCoprime.pow
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
      exact (Nat.coprime_primes h1 h2).2 hne
    · intro p hp
      exact (Finset.mem_filter.1 hp).2.2.2
  have hle : (∏ p ∈ T, ((p : ℤ) ^ 2)) ≤ |w| := by
    have hpos : 0 < ∏ p ∈ T, ((p : ℤ) ^ 2) := by
      apply Finset.prod_pos
      intro p hp
      have := (Finset.mem_filter.1 hp).2.1.pos
      positivity
    exact Int.le_of_dvd (abs_pos.2 hw) ((dvd_abs _ _).2 hdvd)
  have hlowN : (P ^ 2) ^ #T ≤ ∏ p ∈ T, p ^ 2 := by
    apply Finset.pow_card_le_prod
    intro p hp
    have := (Finset.mem_filter.1 hp).2.2.1
    exact Nat.pow_le_pow_left this 2
  have hlow : ((P : ℤ) ^ 2) ^ #T ≤ ∏ p ∈ T, ((p : ℤ) ^ 2) := by
    have : (((P ^ 2) ^ #T : ℕ) : ℤ) ≤ ((∏ p ∈ T, p ^ 2 : ℕ) : ℤ) := by exact_mod_cast hlowN
    push_cast at this
    exact this
  have hreal : ((P : ℝ) ^ 2) ^ #T ≤ |(w : ℝ)| := by
    have := hlow.trans hle
    have h' : (((P : ℤ) ^ 2) ^ #T : ℝ) ≤ ((|w| : ℤ) : ℝ) := by exact_mod_cast this
    push_cast at h'
    exact h'
  have hP1 : (1 : ℝ) < P := by exact_mod_cast (by omega : 1 < P)
  have hlogP : 0 < Real.log P := Real.log_pos hP1
  have hlog := Real.log_le_log (by positivity) hreal
  rw [Real.log_pow, Real.log_pow] at hlog
  push_cast at hlog
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- Summing a divisibility count over a set of prime moduli. -/
theorem sum_card_sq_dvd_le {X : Type*} [Fintype X] (s : Finset ℕ) (P : ℕ) (Z : X → ℤ) (D : ℝ)
    (hD : ∀ x, Z x ≠ 0 →
      (#(s.filter (fun p => p.Prime ∧ P ≤ p ∧ (p : ℤ) ^ 2 ∣ Z x)) : ℝ) ≤ D) (hD0 : 0 ≤ D) :
    ∑ p ∈ s.filter (fun p => p.Prime ∧ P ≤ p),
        (#((univ : Finset X).filter (fun x => (p : ℤ) ^ 2 ∣ Z x)) : ℝ) ≤
      #(s.filter (fun p => p.Prime ∧ P ≤ p)) * #((univ : Finset X).filter (fun x => Z x = 0)) +
        Fintype.card X * D := by
  classical
  have hswap : ∑ p ∈ s.filter (fun p => p.Prime ∧ P ≤ p),
      (#((univ : Finset X).filter (fun x => (p : ℤ) ^ 2 ∣ Z x)) : ℝ) =
      ∑ x : X, (#((s.filter (fun p => p.Prime ∧ P ≤ p)).filter
        (fun p : ℕ => (p : ℤ) ^ 2 ∣ Z x)) : ℝ) := by
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    exact Finset.sum_comm
  rw [hswap]
  have hpt : ∀ x : X, (#((s.filter (fun p => p.Prime ∧ P ≤ p)).filter
      (fun p : ℕ => (p : ℤ) ^ 2 ∣ Z x)) : ℝ) ≤
      (if Z x = 0 then (#(s.filter (fun p => p.Prime ∧ P ≤ p)) : ℝ) else 0) + D := by
    intro x
    by_cases hx : Z x = 0
    · rw [ite_eq_left hx]
      have : ((s.filter (fun p => p.Prime ∧ P ≤ p)).filter (fun p : ℕ => (p : ℤ) ^ 2 ∣ Z x)) ⊆
          s.filter (fun p => p.Prime ∧ P ≤ p) := filter_subset _ _
      have := card_le_card this
      have h' : (#((s.filter (fun p => p.Prime ∧ P ≤ p)).filter
          (fun p : ℕ => (p : ℤ) ^ 2 ∣ Z x)) : ℝ) ≤ #(s.filter (fun p => p.Prime ∧ P ≤ p)) := by
        exact_mod_cast this
      linarith
    · rw [ite_eq_right hx, zero_add]
      have := hD x hx
      rw [Finset.filter_filter]
      convert this using 3
      ext p
      simp only [and_assoc]
  calc ∑ x : X, (#((s.filter (fun p => p.Prime ∧ P ≤ p)).filter
          (fun p : ℕ => (p : ℤ) ^ 2 ∣ Z x)) : ℝ)
      ≤ ∑ x : X, ((if Z x = 0 then (#(s.filter (fun p => p.Prime ∧ P ≤ p)) : ℝ) else 0) + D) :=
        Finset.sum_le_sum (fun x _ => hpt x)
    _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]


/-! ## Point masses, collision counts, block bounds -/
/-- Point masses of a difference are at most the collision count (counting form). -/
theorem card_shift_le {X : Type*} [Fintype X] (a : X → ℤ) (s : ℤ) :
    #((univ : Finset (X × X)).filter (fun p => a p.1 = a p.2 + s)) ≤
      #((univ : Finset (X × X)).filter (fun p => a p.1 = a p.2)) := by
  have h := card_eq_le_sqrt a (fun y => a y + s)
  have e : (univ : Finset (X × X)).filter (fun p => a p.1 + s = a p.2 + s) =
      (univ : Finset (X × X)).filter (fun p => a p.1 = a p.2) := by
    ext p; simp
  rw [e, Real.mul_self_sqrt (Nat.cast_nonneg _)] at h
  exact_mod_cast h

/-- Multiples of `q` in `(−W, W)`: at most `2W/q + 1`. -/
theorem card_dvd_Ioo_le (q W : ℤ) (hq : 0 < q) (hW0 : 0 ≤ W) :
    (#((Ioo (-W) W).filter (fun t => q ∣ t)) : ℝ) ≤ 2 * W / q + 1 := by
  by_cases hW : W ≤ 0
  · have : (Ioo (-W) W).filter (fun t => q ∣ t) = ∅ := by
      ext t; simp only [mem_filter, mem_Ioo, notMem_empty, iff_false]; omega
    rw [this, card_empty, Nat.cast_zero]
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    have hW' : (0 : ℝ) ≤ W := by exact_mod_cast hW0
    have : (0 : ℝ) ≤ 2 * W / q := by positivity
    linarith
  · push Not at hW
    have hsub : (Ioo (-W) W).filter (fun t => q ∣ t) ⊆
        (Icc (-(W / q)) (W / q)).image (fun k => q * k) := by
      intro t ht
      obtain ⟨htI, k, rfl⟩ := Finset.mem_filter.1 ht
      rw [mem_Ioo] at htI
      refine Finset.mem_image.2 ⟨k, ?_, rfl⟩
      rw [mem_Icc]
      constructor
      · rw [neg_le, Int.le_ediv_iff_mul_le hq]; nlinarith
      · rw [Int.le_ediv_iff_mul_le hq]; nlinarith
    have h1 := (card_le_card hsub).trans card_image_le
    rw [Int.card_Icc] at h1
    have h2 : ((W / q + 1 - -(W / q)).toNat : ℝ) = 2 * ((W / q : ℤ) : ℝ) + 1 := by
      have : 0 ≤ W / q + 1 - -(W / q) := by
        have : 0 ≤ W / q := Int.ediv_nonneg hW.le hq.le
        omega
      rw [show ((W / q + 1 - -(W / q)).toNat : ℝ) = ((W / q + 1 - -(W / q) : ℤ) : ℝ) by
        exact_mod_cast Int.toNat_of_nonneg this]
      push_cast; ring
    have h3 : ((W / q : ℤ) : ℝ) ≤ W / q := by
      rw [le_div_iff₀ (by exact_mod_cast hq)]
      exact_mod_cast Int.ediv_mul_le W hq.ne'
    calc (#((Ioo (-W) W).filter (fun t => q ∣ t)) : ℝ)
        ≤ ((W / q + 1 - -(W / q)).toNat : ℝ) := by exact_mod_cast h1
      _ ≤ 2 * W / q + 1 := by rw [h2]; linarith [h3, show 2 * (W : ℝ) / q = 2 * (W / q) by ring]

/-- **Collisions modulo `q` of a difference with a common factor `M`**:
`#{q ∣ a x − a y} ≤ (2W/q + 1) · #{a x = a y}` if every difference is `M t` with `|t| < W`. -/
theorem card_dvd_diff_le {X : Type*} [Fintype X] (a : X → ℤ) (M q W : ℤ) (hq : 0 < q)
    (hW0 : 0 ≤ W) (hcop : IsCoprime q M)
    (hstruct : ∀ x y, ∃ t, a x - a y = M * t ∧ |t| < W) :
    (#((univ : Finset (X × X)).filter (fun p => q ∣ a p.1 - a p.2)) : ℝ) ≤
      (2 * W / q + 1) * #((univ : Finset (X × X)).filter (fun p => a p.1 = a p.2)) := by
  classical
  set T := (Ioo (-W) W).filter (fun t => q ∣ t)
  have hsub : (univ : Finset (X × X)).filter (fun p => q ∣ a p.1 - a p.2) ⊆
      T.biUnion (fun t => (univ : Finset (X × X)).filter (fun p => a p.1 = a p.2 + M * t)) := by
    intro p hp
    have hdvd := (Finset.mem_filter.1 hp).2
    obtain ⟨t, ht, htW⟩ := hstruct p.1 p.2
    refine Finset.mem_biUnion.2 ⟨t, ?_, ?_⟩
    · refine Finset.mem_filter.2 ⟨?_, ?_⟩
      · rw [mem_Ioo]; constructor <;> [linarith [neg_abs_le t]; linarith [le_abs_self t]]
      · rw [ht] at hdvd
        exact hcop.dvd_of_dvd_mul_left hdvd
    · simp only [mem_filter, mem_univ, true_and]
      linarith
  have h1 := (card_le_card hsub).trans card_biUnion_le
  have h2 : ∑ t ∈ T, #((univ : Finset (X × X)).filter (fun p => a p.1 = a p.2 + M * t)) ≤
      #T * #((univ : Finset (X × X)).filter (fun p => a p.1 = a p.2)) := by
    rw [← smul_eq_mul]
    exact Finset.sum_le_card_nsmul _ _ _ (fun t _ => card_shift_le a (M * t))
  have h3 := card_dvd_Ioo_le q W hq hW0
  have h4 : (#((univ : Finset (X × X)).filter (fun p => q ∣ a p.1 - a p.2)) : ℝ) ≤
      #T * #((univ : Finset (X × X)).filter (fun p => a p.1 = a p.2)) := by
    exact_mod_cast h1.trans h2
  calc _ ≤ (#T : ℝ) * #((univ : Finset (X × X)).filter (fun p => a p.1 = a p.2)) := h4
    _ ≤ _ := mul_le_mul_of_nonneg_right h3 (Nat.cast_nonneg _)

/-- `yVal` in block form. -/
theorem yVal_eq_blk (b N : ℕ) (A B : Finset ℕ) (d d' : DigVec b N) :
    (yVal b N A B (extDig d) (extDig d') : ℤ) = blk b N A d + blk b N A d' + blk b N B d := by
  unfold yVal blk
  push_cast
  rw [← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Exact quadruple collision count of `Y` (from `collision_prob`). -/
theorem card_Y_eq (b N : ℕ) (hb : 2 ≤ b) (A B : Finset ℕ) (hA : A ⊆ range (N + 1))
    (hB : B ⊆ range (N + 1)) (hAB : Disjoint A B) :
    (#((univ : Finset (Quad b N)).filter (fun w =>
        blk b N A w.1 + blk b N A w.2.1 + blk b N B w.1 =
          blk b N A w.2.2.1 + blk b N A w.2.2.2 + blk b N B w.2.2.1)) : ℝ) =
      (b : ℝ) ^ (4 * (N + 1)) * (((2 * (b : ℝ) ^ 2 + 1) / (3 * (b : ℝ) ^ 3)) ^ #A *
        ((b : ℝ) ^ #B)⁻¹) := by
  have h := collision_prob b N hb A B hA hB hAB
  have e : (univ : Finset (Quad b N)).filter (fun w =>
        yVal b N A B (extDig w.1) (extDig w.2.1) =
          yVal b N A B (extDig w.2.2.1) (extDig w.2.2.2)) =
      (univ : Finset (Quad b N)).filter (fun w =>
        blk b N A w.1 + blk b N A w.2.1 + blk b N B w.1 =
          blk b N A w.2.2.1 + blk b N A w.2.2.2 + blk b N B w.2.2.1) := by
    ext w
    simp only [mem_filter, mem_univ, true_and]
    rw [← yVal_eq_blk, ← yVal_eq_blk]
    exact_mod_cast Iff.rfl
  rw [e] at h
  have hb0 : (0 : ℝ) < (b : ℝ) ^ (4 * (N + 1)) := by positivity
  rw [div_eq_iff hb0.ne'] at h
  rw [h]
  ring

/-- Exact pair collision count of a single-digit block. -/
theorem card_blk_eq (b N : ℕ) (hb : 2 ≤ b) (V : Finset ℕ) (hV : V ⊆ range (N + 1)) :
    (#((univ : Finset (DigVec b N × DigVec b N)).filter
        (fun x => blk b N V x.1 = blk b N V x.2)) : ℝ) =
      (b : ℝ) ^ (2 * (N + 1)) * ((b : ℝ) ^ #V)⁻¹ := by
  have h := card_Y_eq b N hb ∅ V (empty_subset _) hV (disjoint_empty_left _)
  simp only [blk, sum_empty, zero_add, card_empty, pow_zero, one_mul] at h
  set E : Quad b N ≃ (DigVec b N × DigVec b N) × (DigVec b N × DigVec b N) :=
    { toFun := fun w => ((w.1, w.2.2.1), (w.2.1, w.2.2.2))
      invFun := fun x => (x.1.1, x.2.1, x.1.2, x.2.2)
      left_inv := fun w => rfl
      right_inv := fun x => rfl }
  have hcard : #((univ : Finset (Quad b N)).filter (fun w =>
      ∑ k ∈ V, (extDig w.1 k : ℤ) * (cK b N k : ℤ) =
        ∑ k ∈ V, (extDig w.2.2.1 k : ℤ) * (cK b N k : ℤ))) =
      #((univ : Finset (DigVec b N × DigVec b N)).filter
        (fun x => blk b N V x.1 = blk b N V x.2)) * Fintype.card (DigVec b N × DigVec b N) := by
    rw [← Finset.card_univ, ← Finset.card_product]
    apply Finset.card_equiv E
    intro w
    simp only [E, Equiv.coe_fn_mk, mem_product, mem_filter, mem_univ, true_and, and_true]
    rfl
  rw [hcard] at h
  push_cast at h
  rw [Fintype.card_prod, card_digVec] at h
  push_cast at h
  have hb0 : (0 : ℝ) < ((b : ℝ) ^ (N + 1) * (b : ℝ) ^ (N + 1)) := by positivity
  have : (b : ℝ) ^ (4 * (N + 1)) = (b : ℝ) ^ (2 * (N + 1)) *
      ((b : ℝ) ^ (N + 1) * (b : ℝ) ^ (N + 1)) := by ring
  rw [this] at h
  nlinarith [h, hb0]


theorem cK_le (b N k : ℕ) (hb : 1 ≤ b) (hk : k ≤ N) : cK b N k ≤ 2 * b ^ (2 * N) := by
  unfold cK
  split_ifs with h
  · have h1 : b ^ k ≤ b ^ (2 * N) := Nat.pow_le_pow_right hb (by omega)
    have h2 : b ^ (2 * N - k) ≤ b ^ (2 * N) := Nat.pow_le_pow_right hb (by omega)
    omega
  · have : b ^ N ≤ b ^ (2 * N) := Nat.pow_le_pow_right hb (by omega)
    omega

/-- For `m0 ≤ k ≤ N`, `c_k = b^{m0} c'` with `c' ≤ 2 b^{2(N−m0)}`. -/
theorem cK_factor (b N k m0 : ℕ) (hb : 1 ≤ b) (hk : m0 ≤ k) (hkN : k ≤ N) :
    ∃ c' : ℕ, cK b N k = b ^ m0 * c' ∧ c' ≤ 2 * b ^ (2 * (N - m0)) := by
  unfold cK
  split_ifs with h
  · refine ⟨b ^ (k - m0) + b ^ (2 * N - k - m0), ?_, ?_⟩
    · rw [mul_add, ← pow_add, ← pow_add]
      congr 2 <;> omega
    · have h1 : b ^ (k - m0) ≤ b ^ (2 * (N - m0)) := Nat.pow_le_pow_right hb (by omega)
      have h2 : b ^ (2 * N - k - m0) ≤ b ^ (2 * (N - m0)) := Nat.pow_le_pow_right hb (by omega)
      omega
  · refine ⟨b ^ (N - m0), ?_, ?_⟩
    · rw [← pow_add]; congr 1; omega
    · have : b ^ (N - m0) ≤ b ^ (2 * (N - m0)) := Nat.pow_le_pow_right hb (by omega)
      omega

theorem extDig_le {b N : ℕ} (hb : 1 ≤ b) (d : DigVec b N) (k : ℕ) : extDig d k ≤ b - 1 := by
  unfold extDig
  split_ifs
  · have := (d ⟨k, by assumption⟩).isLt; omega
  · omega

/-- Size of a block sum. -/
theorem abs_blk_le (b N : ℕ) (hb : 1 ≤ b) (S : Finset ℕ) (hS : S ⊆ range (N + 1))
    (d : DigVec b N) : |blk b N S d| ≤ ((N + 1) * (2 * b ^ (2 * N + 1)) : ℕ) := by
  unfold blk
  have h0 : ∀ k ∈ S, 0 ≤ (extDig d k : ℤ) * (cK b N k : ℤ) := fun k _ => by positivity
  rw [abs_of_nonneg (Finset.sum_nonneg h0)]
  calc ∑ k ∈ S, (extDig d k : ℤ) * (cK b N k : ℤ)
      ≤ ∑ k ∈ S, ((2 * b ^ (2 * N + 1) : ℕ) : ℤ) := by
        apply Finset.sum_le_sum
        intro k hk
        have hkN : k ≤ N := by have := Finset.mem_range.1 (hS hk); omega
        have h1 := extDig_le hb d k
        have h2 := cK_le b N k hb hkN
        have h3 : extDig d k * cK b N k ≤ 2 * b ^ (2 * N + 1) := by
          calc extDig d k * cK b N k ≤ b * (2 * b ^ (2 * N)) :=
                Nat.mul_le_mul (by omega) h2
            _ = 2 * b ^ (2 * N + 1) := by ring
        exact_mod_cast h3
    _ = (#S : ℤ) * ((2 * b ^ (2 * N + 1) : ℕ) : ℤ) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((N + 1 : ℕ) : ℤ) * ((2 * b ^ (2 * N + 1) : ℕ) : ℤ) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have := card_le_card hS
        rw [card_range] at this
        exact_mod_cast this
    _ = _ := by push_cast; ring

/-- Differences of `Y` on a block of positions `≥ m0` carry the factor `b^{m0}`. -/
theorem Y_diff_struct (b N m0 ℓ : ℕ) (hb : 1 ≤ b) (A B : Finset ℕ) (hAB : Disjoint A B)
    (hpos : ∀ k ∈ A ∪ B, m0 ≤ k ∧ k ≤ N) (hcard : #(A ∪ B) ≤ ℓ)
    (x y : DigVec b N × DigVec b N) :
    ∃ t : ℤ, (blk b N A x.1 + blk b N A x.2 + blk b N B x.1) -
        (blk b N A y.1 + blk b N A y.2 + blk b N B y.1) = (b : ℤ) ^ m0 * t ∧
      |t| < ((8 * b * ℓ * b ^ (2 * (N - m0)) + 1 : ℕ) : ℤ) := by
  classical
  choose c' hc' hcle using fun k (hk : k ∈ A ∪ B) =>
    cK_factor b N k m0 hb (hpos k hk).1 (hpos k hk).2
  set cc : ℕ → ℕ := fun k => if hk : k ∈ A ∪ B then c' k hk else 0 with hcc
  have hcK : ∀ k ∈ A ∪ B, (cK b N k : ℤ) = (b : ℤ) ^ m0 * (cc k : ℤ) := by
    intro k hk
    simp only [hcc, dite_eq_left hk]
    exact_mod_cast hc' k hk
  set s : ℕ → ℤ := fun k =>
    (if k ∈ A then ((extDig x.1 k : ℤ) + extDig x.2 k - extDig y.1 k - extDig y.2 k) else 0) +
      (if k ∈ B then ((extDig x.1 k : ℤ) - extDig y.1 k) else 0) with hs
  refine ⟨∑ k ∈ A ∪ B, s k * cc k, ?_, ?_⟩
  · rw [Finset.mul_sum]
    unfold blk
    rw [Finset.sum_union hAB]
    have eA : ∀ k ∈ A, (b : ℤ) ^ m0 * (s k * cc k) =
        ((extDig x.1 k : ℤ) + extDig x.2 k - extDig y.1 k - extDig y.2 k) * (cK b N k : ℤ) := by
      intro k hk
      have hkB : k ∉ B := Finset.disjoint_left.1 hAB hk
      rw [hcK k (mem_union_left _ hk)]
      simp only [hs, ite_eq_left hk, ite_eq_right hkB, add_zero]
      ring
    have eB : ∀ k ∈ B, (b : ℤ) ^ m0 * (s k * cc k) =
        ((extDig x.1 k : ℤ) - extDig y.1 k) * (cK b N k : ℤ) := by
      intro k hk
      have hkA : k ∉ A := fun h => Finset.disjoint_left.1 hAB h hk
      rw [hcK k (mem_union_right _ hk)]
      simp only [hs, ite_eq_right hkA, ite_eq_left hk, zero_add]
      ring
    rw [Finset.sum_congr rfl eA, Finset.sum_congr rfl eB]
    simp only [sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    ring
  · have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
    have hsb : ∀ k, |s k| ≤ 4 * (b : ℤ) := by
      intro k
      have hd : ∀ z : DigVec b N, (0 : ℤ) ≤ extDig z k ∧ (extDig z k : ℤ) ≤ (b : ℤ) - 1 := by
        intro z
        have := extDig_le hb z k
        constructor
        · positivity
        · have : ((extDig z k : ℕ) : ℤ) ≤ ((b - 1 : ℕ) : ℤ) := by exact_mod_cast this
          rw [Nat.cast_sub hb] at this
          simpa using this
      obtain ⟨a1, a2⟩ := hd x.1
      obtain ⟨b1, b2⟩ := hd x.2
      obtain ⟨c1, c2⟩ := hd y.1
      obtain ⟨d1, d2⟩ := hd y.2
      simp only [hs]
      split_ifs <;> rw [abs_le] <;> constructor <;> linarith
    have hcc_le : ∀ k ∈ A ∪ B, (cc k : ℤ) ≤ 2 * (b : ℤ) ^ (2 * (N - m0)) := by
      intro k hk
      simp only [hcc, dite_eq_left hk]
      exact_mod_cast hcle k hk
    calc |∑ k ∈ A ∪ B, s k * cc k| ≤ ∑ k ∈ A ∪ B, |s k * cc k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ A ∪ B, (4 * (b : ℤ)) * (2 * (b : ℤ) ^ (2 * (N - m0))) := by
          apply Finset.sum_le_sum
          intro k hk
          rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ cc k)]
          exact mul_le_mul (hsb k) (hcc_le k hk) (by positivity) (by positivity)
      _ = (#(A ∪ B) : ℤ) * ((4 * (b : ℤ)) * (2 * (b : ℤ) ^ (2 * (N - m0)))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (ℓ : ℤ) * ((4 * (b : ℤ)) * (2 * (b : ℤ) ^ (2 * (N - m0)))) := by
          apply mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
      _ < _ := by push_cast; nlinarith


/-! ## Block layout -/

/-- Block layout, from the middle outwards: `K1` (m), `K2` (ℓ − m), `K3` (m), `V` (rest). -/
def bK1 (N m : ℕ) : Finset ℕ := Ico (N + 1 - m) (N + 1)
def bK2 (N ℓ m : ℕ) : Finset ℕ := Ico (N + 1 - ℓ) (N + 1 - m)
def bK3 (N ℓ m : ℕ) : Finset ℕ := Ico (N + 1 - ℓ - m) (N + 1 - ℓ)
def bV (N ℓ m : ℕ) : Finset ℕ := range (N + 1 - ℓ - m)

section layout
variable {N ℓ m : ℕ}

theorem bK12_disj (_hm : m ≤ ℓ) : Disjoint (bK1 N m) (bK2 N ℓ m) := by
  rw [Finset.disjoint_left]; intro k h1 h2; simp only [bK1, bK2, mem_Ico] at h1 h2; omega
theorem bK13_disj (hm : m ≤ ℓ) : Disjoint (bK1 N m) (bK3 N ℓ m) := by
  rw [Finset.disjoint_left]; intro k h1 h2; simp only [bK1, bK3, mem_Ico] at h1 h2; omega
theorem bK23_disj : Disjoint (bK2 N ℓ m) (bK3 N ℓ m) := by
  rw [Finset.disjoint_left]; intro k h1 h2; simp only [bK2, bK3, mem_Ico] at h1 h2; omega
theorem bVU_disj (hm : m ≤ ℓ) :
    Disjoint (bV N ℓ m) (bK1 N m ∪ bK2 N ℓ m ∪ bK3 N ℓ m) := by
  rw [Finset.disjoint_left]; intro k h1 h2
  simp only [bV, bK1, bK2, bK3, mem_range, mem_union, mem_Ico] at h1 h2; omega
theorem bVU_cov (hm : m ≤ ℓ) (hlen : 2 * ℓ + m ≤ N + 1) :
    bV N ℓ m ∪ (bK1 N m ∪ bK2 N ℓ m ∪ bK3 N ℓ m) = range (N + 1) := by
  ext k; simp only [bV, bK1, bK2, bK3, mem_range, mem_union, mem_Ico]; omega
theorem bK1_sub : bK1 N m ⊆ range (N + 1) := by
  intro k h; simp only [bK1, mem_Ico, mem_range] at h ⊢; omega
theorem bK2_sub : bK2 N ℓ m ⊆ range (N + 1) := by
  intro k h; simp only [bK2, mem_Ico, mem_range] at h ⊢; omega
theorem bK3_sub : bK3 N ℓ m ⊆ range (N + 1) := by
  intro k h; simp only [bK3, mem_Ico, mem_range] at h ⊢; omega
theorem bV_sub : bV N ℓ m ⊆ range (N + 1) := by
  intro k h; simp only [bV, mem_range] at h ⊢; omega
theorem card_bK1 (hlen : 2 * ℓ + m ≤ N + 1) (_hm : m ≤ ℓ) : #(bK1 N m) = m := by
  simp only [bK1, Nat.card_Ico]; omega
theorem card_bK2 (hlen : 2 * ℓ + m ≤ N + 1) (hm : m ≤ ℓ) : #(bK2 N ℓ m) = ℓ - m := by
  simp only [bK2, Nat.card_Ico]; omega
theorem card_bK3 (hlen : 2 * ℓ + m ≤ N + 1) (_hm : m ≤ ℓ) : #(bK3 N ℓ m) = m := by
  simp only [bK3, Nat.card_Ico]; omega
theorem card_bV : #(bV N ℓ m) = N + 1 - ℓ - m := by simp [bV]
theorem bK12_pos (hm : m ≤ ℓ) (hlen : 2 * ℓ + m ≤ N + 1) :
    ∀ k ∈ bK1 N m ∪ bK2 N ℓ m, N + 1 - ℓ ≤ k ∧ k ≤ N := by
  intro k h; simp only [bK1, bK2, mem_union, mem_Ico] at h; omega
theorem card_bK12 (hm : m ≤ ℓ) (hlen : 2 * ℓ + m ≤ N + 1) : #(bK1 N m ∪ bK2 N ℓ m) ≤ ℓ := by
  rw [Finset.card_union_of_disjoint (bK12_disj hm), card_bK1 hlen hm, card_bK2 hlen hm]; omega

end layout

/-! ## Proposition W for one block of primes -/

/-- `Quad` as pairs of pairs. -/
def quadPairs (b N : ℕ) : Quad b N ≃ (DigVec b N × DigVec b N) × (DigVec b N × DigVec b N) :=
  (Equiv.prodAssoc _ _ _).symm

theorem quadPairs_apply {b N : ℕ} (w : Quad b N) :
    quadPairs b N w = ((w.1, w.2.1), (w.2.2.1, w.2.2.2)) := rfl

/-- `Y = X_A(d) + X_A(d') + X_B(d)` on a pair. -/
def Ypair (b N : ℕ) (A B : Finset ℕ) (x : DigVec b N × DigVec b N) : ℤ :=
  blk b N A x.1 + blk b N A x.2 + blk b N B x.1

theorem collQ_eq_pairs (b N : ℕ) (A B : Finset ℕ) (q : ℤ) :
    collQ b N A B q = #((univ : Finset ((DigVec b N × DigVec b N) × (DigVec b N × DigVec b N))).filter
      (fun p => q ∣ Ypair b N A B p.1 - Ypair b N A B p.2)) := by
  unfold collQ
  apply Finset.card_equiv (quadPairs b N)
  intro w
  simp only [mem_filter, mem_univ, true_and, quadPairs_apply]
  rfl

theorem card_Y_eq_pairs (b N : ℕ) (hb : 2 ≤ b) (A B : Finset ℕ) (hA : A ⊆ range (N + 1))
    (hB : B ⊆ range (N + 1)) (hAB : Disjoint A B) :
    (#((univ : Finset ((DigVec b N × DigVec b N) × (DigVec b N × DigVec b N))).filter
      (fun p => Ypair b N A B p.1 = Ypair b N A B p.2)) : ℝ) =
      (b : ℝ) ^ (4 * (N + 1)) * (((2 * (b : ℝ) ^ 2 + 1) / (3 * (b : ℝ) ^ 3)) ^ #A *
        ((b : ℝ) ^ #B)⁻¹) := by
  rw [← card_Y_eq b N hb A B hA hB hAB]
  congr 1
  symm
  apply Finset.card_equiv (quadPairs b N)
  intro w
  simp only [mem_filter, mem_univ, true_and, quadPairs_apply]
  rfl

theorem card_quad (b N : ℕ) : Fintype.card (Quad b N) = b ^ (4 * (N + 1)) := by
  simp only [Quad, Fintype.card_prod, card_digVec]; ring

theorem card_pairs (b N : ℕ) : Fintype.card (DigVec b N × DigVec b N) = b ^ (2 * (N + 1)) := by
  simp only [Fintype.card_prod, card_digVec]; ring

/-- The common divisor-count constant `Wmax` for block differences. -/
def wmax (b N : ℕ) : ℕ := 6 * ((N + 1) * (2 * b ^ (2 * N + 1)))

/-- **Proposition W, one block of primes.** For primes `p ∈ S`, all `≥ P > b`,
`Σ_p #{d : p² ∣ palVal d} ≤ b^{N+1} √(K b^{−v} + D) √(√(K(2W/P²+1)ρ) √(Kρ + D))`,
`ρ = (g/b)^m b^{−(ℓ−m)}`, `v = N+1−ℓ−m`. -/
theorem propW_block (b N ℓ m P W : ℕ) (hb : 2 ≤ b) (hm : m ≤ ℓ) (hlen : 2 * ℓ + m ≤ N + 1)
    (hbP : b < P) (hW : 8 * b * ℓ * b ^ (2 * (N - (N + 1 - ℓ))) + 1 ≤ W)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ P ≤ p) (K : ℝ) (hK : (#S : ℝ) ≤ K)
    (D : ℝ) (hD0 : 0 ≤ D)
    (hD : ∀ w : ℤ, w ≠ 0 → |w| ≤ (wmax b N : ℤ) →
      (#(S.filter (fun p => p.Prime ∧ P ≤ p ∧ (p : ℤ) ^ 2 ∣ w)) : ℝ) ≤ D) :
    ∑ p ∈ S, (#((univ : Finset (DigVec b N)).filter
        (fun d => (p : ℤ) ^ 2 ∣ (palVal b N d : ℤ))) : ℝ) ≤
      (b : ℝ) ^ (N + 1) * Real.sqrt (K * ((b : ℝ) ^ (N + 1 - ℓ - m))⁻¹ + D) *
        Real.sqrt (Real.sqrt (K * (2 * W / (P : ℝ) ^ 2 + 1) *
            (((2 * (b : ℝ) ^ 2 + 1) / (3 * (b : ℝ) ^ 3)) ^ m * ((b : ℝ) ^ (ℓ - m))⁻¹)) *
          Real.sqrt (K * (((2 * (b : ℝ) ^ 2 + 1) / (3 * (b : ℝ) ^ 3)) ^ m *
            ((b : ℝ) ^ (ℓ - m))⁻¹) + D)) := by
  classical
  have hb1 : 1 ≤ b := by omega
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  set n := N + 1 with hn
  set ρ : ℝ := ((2 * (b : ℝ) ^ 2 + 1) / (3 * (b : ℝ) ^ 3)) ^ m * ((b : ℝ) ^ (ℓ - m))⁻¹ with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  set K1 := bK1 N m
  set K2 := bK2 N ℓ m
  set K3 := bK3 N ℓ m
  set V := bV N ℓ m
  have hS' : S.filter (fun p => p.Prime ∧ P ≤ p) = S := Finset.filter_true_of_mem hS
  have hK0 : 0 ≤ K := le_trans (Nat.cast_nonneg _) hK
  -- abbreviations for the four counts
  set cnt : ℕ → ℝ := fun p => #((univ : Finset (DigVec b N)).filter
    (fun d => (p : ℤ) ^ 2 ∣ (palVal b N d : ℤ))) with hcnt
  set cV : ℕ → ℝ := fun p => (collP b N V ((p : ℤ) ^ 2) : ℝ) with hcV
  set cU : ℕ → ℝ := fun p => (collP b N (K1 ∪ K2 ∪ K3) ((p : ℤ) ^ 2) : ℝ) with hcU
  set c1 : ℕ → ℝ := fun p => (collQ b N K1 K2 ((p : ℤ) ^ 2) : ℝ) with hc1
  set c3 : ℕ → ℝ := fun p => (collQ b N K3 K2 ((p : ℤ) ^ 2) : ℝ) with hc3
  -- level 1 and level 2 for each prime
  have L1 : ∀ p ∈ S, (b : ℝ) ^ n * cnt p ≤ Real.sqrt (cV p) * Real.sqrt (cU p) := fun p _ =>
    level1 b N ((p : ℤ) ^ 2) V (K1 ∪ K2 ∪ K3) (bVU_disj hm) (bVU_cov hm hlen)
  have L2 : ∀ p ∈ S, (b : ℝ) ^ (2 * n) * cU p ≤ Real.sqrt (c1 p) * Real.sqrt (c3 p) :=
    fun p _ => level2 b N ((p : ℤ) ^ 2) K1 K2 K3 (bK12_disj hm) (bK13_disj hm) bK23_disj
  -- sums with Cauchy–Schwarz over p
  have CS : ∀ f g : ℕ → ℝ, (∀ p, 0 ≤ f p) → (∀ p, 0 ≤ g p) →
      ∑ p ∈ S, Real.sqrt (f p) * Real.sqrt (g p) ≤
        Real.sqrt (∑ p ∈ S, f p) * Real.sqrt (∑ p ∈ S, g p) := by
    intro f g hf hg
    have := Real.sum_mul_le_sqrt_mul_sqrt S (fun p => Real.sqrt (f p)) (fun p => Real.sqrt (g p))
    simpa [Real.sq_sqrt (hf _), Real.sq_sqrt (hg _)] using this
  have hcV0 : ∀ p, 0 ≤ cV p := fun p => Nat.cast_nonneg _
  have hcU0 : ∀ p, 0 ≤ cU p := fun p => Nat.cast_nonneg _
  have hc10 : ∀ p, 0 ≤ c1 p := fun p => Nat.cast_nonneg _
  have hc30 : ∀ p, 0 ≤ c3 p := fun p => Nat.cast_nonneg _
  have hbn : (0 : ℝ) < (b : ℝ) ^ n := by positivity
  have hb2n : (0 : ℝ) < (b : ℝ) ^ (2 * n) := by positivity
  have sum_cnt : ∑ p ∈ S, cnt p ≤
      ((b : ℝ) ^ n)⁻¹ * (Real.sqrt (∑ p ∈ S, cV p) * Real.sqrt (∑ p ∈ S, cU p)) := by
    rw [le_inv_mul_iff₀ hbn, Finset.mul_sum]
    exact (Finset.sum_le_sum L1).trans (CS cV cU hcV0 hcU0)
  have sum_cU : ∑ p ∈ S, cU p ≤
      ((b : ℝ) ^ (2 * n))⁻¹ * (Real.sqrt (∑ p ∈ S, c1 p) * Real.sqrt (∑ p ∈ S, c3 p)) := by
    rw [le_inv_mul_iff₀ hb2n, Finset.mul_sum]
    exact (Finset.sum_le_sum L2).trans (CS c1 c3 hc10 hc30)
  -- the three level-3 sums
  have sum_cV : ∑ p ∈ S, cV p ≤ (b : ℝ) ^ (2 * n) * (K * ((b : ℝ) ^ (n - ℓ - m))⁻¹ + D) := by
    have h := sum_card_sq_dvd_le (X := DigVec b N × DigVec b N) S P
      (fun x => blk b N V x.1 - blk b N V x.2) D (fun x hx => by
        apply hD _ hx
        have h1 := abs_blk_le b N hb1 V bV_sub x.1
        have h2 := abs_blk_le b N hb1 V bV_sub x.2
        unfold wmax
        push_cast at h1 h2 ⊢
        rw [abs_le] at h1 h2 ⊢
        constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]) hD0
    rw [hS'] at h
    have e0 : ((univ : Finset (DigVec b N × DigVec b N)).filter
        (fun x => blk b N V x.1 - blk b N V x.2 = 0)) =
        (univ : Finset (DigVec b N × DigVec b N)).filter
        (fun x => blk b N V x.1 = blk b N V x.2) := by
      ext x; simp [sub_eq_zero]
    rw [e0, card_blk_eq b N hb V bV_sub, card_pairs, card_bV] at h
    simp only [hcV, collP]
    push_cast at h
    calc ∑ p ∈ S, (#((univ : Finset (DigVec b N × DigVec b N)).filter
          (fun x => (p : ℤ) ^ 2 ∣ blk b N V x.1 - blk b N V x.2)) : ℝ)
        ≤ _ := h
      _ ≤ K * ((b : ℝ) ^ (2 * n) * ((b : ℝ) ^ (n - ℓ - m))⁻¹) + (b : ℝ) ^ (2 * n) * D := by
          gcongr
      _ = _ := by ring
  have sum_c3 : ∑ p ∈ S, c3 p ≤ (b : ℝ) ^ (4 * n) * (K * ρ + D) := by
    have h := sum_card_sq_dvd_le (X := (DigVec b N × DigVec b N) × (DigVec b N × DigVec b N)) S P
      (fun x => Ypair b N K3 K2 x.1 - Ypair b N K3 K2 x.2) D (fun x hx => by
        apply hD _ hx
        have h1 := abs_blk_le b N hb1 K3 bK3_sub x.1.1
        have h2 := abs_blk_le b N hb1 K3 bK3_sub x.1.2
        have h3 := abs_blk_le b N hb1 K2 bK2_sub x.1.1
        have h4 := abs_blk_le b N hb1 K3 bK3_sub x.2.1
        have h5 := abs_blk_le b N hb1 K3 bK3_sub x.2.2
        have h6 := abs_blk_le b N hb1 K2 bK2_sub x.2.1
        unfold wmax Ypair
        push_cast at h1 h2 h3 h4 h5 h6 ⊢
        rw [abs_le] at h1 h2 h3 h4 h5 h6 ⊢
        constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2,
          h6.1, h6.2]) hD0
    rw [hS'] at h
    have e0 : ((univ : Finset ((DigVec b N × DigVec b N) × (DigVec b N × DigVec b N))).filter
        (fun x => Ypair b N K3 K2 x.1 - Ypair b N K3 K2 x.2 = 0)) =
        (univ : Finset ((DigVec b N × DigVec b N) × (DigVec b N × DigVec b N))).filter
        (fun x => Ypair b N K3 K2 x.1 = Ypair b N K3 K2 x.2) := by
      ext x; simp [sub_eq_zero]
    rw [e0, card_Y_eq_pairs b N hb K3 K2 bK3_sub bK2_sub bK23_disj.symm,
      card_bK3 hlen hm, card_bK2 hlen hm] at h
    have hcardX : Fintype.card ((DigVec b N × DigVec b N) × (DigVec b N × DigVec b N)) =
        b ^ (4 * n) := by
      rw [Fintype.card_prod, card_pairs]; ring
    rw [hcardX] at h
    simp only [hc3, collQ_eq_pairs]
    push_cast at h
    calc _ ≤ _ := h
      _ ≤ K * ((b : ℝ) ^ (4 * n) * ρ) + (b : ℝ) ^ (4 * n) * D := by
          rw [hρ]; gcongr
      _ = _ := by ring
  have sum_c1 : ∑ p ∈ S, c1 p ≤ (b : ℝ) ^ (4 * n) * (K * (2 * W / (P : ℝ) ^ 2 + 1) * ρ) := by
    have hper : ∀ p ∈ S, c1 p ≤ (2 * W / (P : ℝ) ^ 2 + 1) * ((b : ℝ) ^ (4 * n) * ρ) := by
      intro p hp
      obtain ⟨hpp, hPp⟩ := hS p hp
      have hq : (0 : ℤ) < (p : ℤ) ^ 2 := by have := hpp.pos; positivity
      have hcop : IsCoprime ((p : ℤ) ^ 2) ((b : ℤ) ^ (N + 1 - ℓ)) := by
        apply IsCoprime.pow
        rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
        apply (Nat.Prime.coprime_iff_not_dvd hpp).2
        intro hdvd
        have := Nat.le_of_dvd (by omega) hdvd
        omega
      have h := card_dvd_diff_le (Ypair b N K1 K2) ((b : ℤ) ^ (N + 1 - ℓ)) ((p : ℤ) ^ 2)
        (W : ℤ) hq (by positivity) hcop (fun x y => by
          obtain ⟨t, ht, htW⟩ := Y_diff_struct b N (N + 1 - ℓ) ℓ hb1 K1 K2 (bK12_disj hm)
            (bK12_pos hm hlen) (card_bK12 hm hlen) x y
          exact ⟨t, ht, lt_of_lt_of_le htW (by exact_mod_cast hW)⟩)
      rw [card_Y_eq_pairs b N hb K1 K2 bK1_sub bK2_sub (bK12_disj hm), card_bK1 hlen hm,
        card_bK2 hlen hm] at h
      simp only [hc1, collQ_eq_pairs]
      calc _ ≤ _ := h
        _ ≤ (2 * W / (P : ℝ) ^ 2 + 1) * ((b : ℝ) ^ (4 * n) * ρ) := by
            rw [hρ]
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            push_cast
            have hP0 : (0 : ℝ) < P := by exact_mod_cast (by omega : 0 < P)
            have hPp' : (P : ℝ) ≤ p := by exact_mod_cast hPp
            have : (2 * W : ℝ) / (p : ℝ) ^ 2 ≤ 2 * W / (P : ℝ) ^ 2 := by
              apply div_le_div_of_nonneg_left (by positivity) (by positivity)
              exact pow_le_pow_left₀ hP0.le hPp' 2
            linarith
    calc ∑ p ∈ S, c1 p ≤ ∑ p ∈ S, (2 * W / (P : ℝ) ^ 2 + 1) * ((b : ℝ) ^ (4 * n) * ρ) :=
          Finset.sum_le_sum hper
      _ = (#S : ℝ) * ((2 * W / (P : ℝ) ^ 2 + 1) * ((b : ℝ) ^ (4 * n) * ρ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ K * ((2 * W / (P : ℝ) ^ 2 + 1) * ((b : ℝ) ^ (4 * n) * ρ)) := by
          apply mul_le_mul_of_nonneg_right hK (by positivity)
      _ = _ := by ring
  -- assemble
  have hA : 0 ≤ K * ((b : ℝ) ^ (n - ℓ - m))⁻¹ + D := by positivity
  have hB : 0 ≤ K * (2 * W / (P : ℝ) ^ 2 + 1) * ρ := by positivity
  have hC : 0 ≤ K * ρ + D := by positivity
  have sU : Real.sqrt (∑ p ∈ S, cU p) ≤
      (b : ℝ) ^ n * Real.sqrt (Real.sqrt (K * (2 * W / (P : ℝ) ^ 2 + 1) * ρ) *
        Real.sqrt (K * ρ + D)) := by
    have h1 : Real.sqrt (∑ p ∈ S, c1 p) ≤ (b : ℝ) ^ (2 * n) *
        Real.sqrt (K * (2 * W / (P : ℝ) ^ 2 + 1) * ρ) := by
      calc _ ≤ Real.sqrt ((b : ℝ) ^ (4 * n) * (K * (2 * W / (P : ℝ) ^ 2 + 1) * ρ)) :=
            Real.sqrt_le_sqrt sum_c1
        _ = _ := by
            rw [Real.sqrt_mul (by positivity), show (b : ℝ) ^ (4 * n) = ((b : ℝ) ^ (2 * n)) ^ 2 by
              ring, Real.sqrt_sq hb2n.le]
    have h3 : Real.sqrt (∑ p ∈ S, c3 p) ≤ (b : ℝ) ^ (2 * n) * Real.sqrt (K * ρ + D) := by
      calc _ ≤ Real.sqrt ((b : ℝ) ^ (4 * n) * (K * ρ + D)) := Real.sqrt_le_sqrt sum_c3
        _ = _ := by
            rw [Real.sqrt_mul (by positivity), show (b : ℝ) ^ (4 * n) = ((b : ℝ) ^ (2 * n)) ^ 2 by
              ring, Real.sqrt_sq hb2n.le]
    calc Real.sqrt (∑ p ∈ S, cU p)
        ≤ Real.sqrt (((b : ℝ) ^ (2 * n))⁻¹ *
            (Real.sqrt (∑ p ∈ S, c1 p) * Real.sqrt (∑ p ∈ S, c3 p))) := Real.sqrt_le_sqrt sum_cU
      _ ≤ Real.sqrt (((b : ℝ) ^ (2 * n))⁻¹ * (((b : ℝ) ^ (2 * n) *
            Real.sqrt (K * (2 * W / (P : ℝ) ^ 2 + 1) * ρ)) *
            ((b : ℝ) ^ (2 * n) * Real.sqrt (K * ρ + D)))) := by
          apply Real.sqrt_le_sqrt
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul h1 h3 (Real.sqrt_nonneg _) (by positivity)
      _ = _ := by
          rw [show ((b : ℝ) ^ (2 * n))⁻¹ * (((b : ℝ) ^ (2 * n) *
              Real.sqrt (K * (2 * W / (P : ℝ) ^ 2 + 1) * ρ)) *
              ((b : ℝ) ^ (2 * n) * Real.sqrt (K * ρ + D))) =
              ((b : ℝ) ^ n) ^ 2 * (Real.sqrt (K * (2 * W / (P : ℝ) ^ 2 + 1) * ρ) *
              Real.sqrt (K * ρ + D)) by field_simp; ring]
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hbn.le]
  have sV : Real.sqrt (∑ p ∈ S, cV p) ≤ (b : ℝ) ^ n *
      Real.sqrt (K * ((b : ℝ) ^ (n - ℓ - m))⁻¹ + D) := by
    calc _ ≤ Real.sqrt ((b : ℝ) ^ (2 * n) * (K * ((b : ℝ) ^ (n - ℓ - m))⁻¹ + D)) :=
          Real.sqrt_le_sqrt sum_cV
      _ = _ := by
          rw [Real.sqrt_mul (by positivity), show (b : ℝ) ^ (2 * n) = ((b : ℝ) ^ n) ^ 2 by ring,
            Real.sqrt_sq hbn.le]
  calc ∑ p ∈ S, cnt p
      ≤ ((b : ℝ) ^ n)⁻¹ * (Real.sqrt (∑ p ∈ S, cV p) * Real.sqrt (∑ p ∈ S, cU p)) := sum_cnt
    _ ≤ ((b : ℝ) ^ n)⁻¹ * (((b : ℝ) ^ n * Real.sqrt (K * ((b : ℝ) ^ (n - ℓ - m))⁻¹ + D)) *
          ((b : ℝ) ^ n * Real.sqrt (Real.sqrt (K * (2 * W / (P : ℝ) ^ 2 + 1) * ρ) *
            Real.sqrt (K * ρ + D)))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul sV sU (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by
        have : ((b : ℝ) ^ n)⁻¹ * (b : ℝ) ^ n = 1 := inv_mul_cancel₀ hbn.ne'
        calc _ = (((b : ℝ) ^ n)⁻¹ * (b : ℝ) ^ n) * ((b : ℝ) ^ n *
              Real.sqrt (K * ((b : ℝ) ^ (n - ℓ - m))⁻¹ + D) *
              Real.sqrt (Real.sqrt (K * (2 * W / (P : ℝ) ^ 2 + 1) * ρ) *
                Real.sqrt (K * ρ + D))) := by ring
          _ = _ := by rw [this, one_mul]

/-! ## b-adic blocks and the interface lemma -/
theorem sqrt_pow' (x : ℝ) (hx : 0 ≤ x) (m : ℕ) : Real.sqrt (x ^ m) = Real.sqrt x ^ m := by
  rw [show x ^ m = (Real.sqrt x ^ m) ^ 2 by rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hx],
    Real.sqrt_sq (by positivity)]

theorem sqrt_le_self' (y : ℝ) (hy : 1 ≤ y) : Real.sqrt y ≤ y := by
  calc Real.sqrt y ≤ Real.sqrt (y ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    _ = y := Real.sqrt_sq (by linarith)

/-- `countDvd` on `piStar` is at most the count over all digit vectors. -/
theorem countDvd_piStar_le (b N p : ℕ) (hb : 2 ≤ b) :
    countDvd (piStar b N) (p ^ 2) ≤
      #((univ : Finset (DigVec b N)).filter (fun d => (p : ℤ) ^ 2 ∣ (palVal b N d : ℤ))) := by
  unfold countDvd
  have hsub : (piStar b N).filter (fun n => p ^ 2 ∣ n) ⊆
      ((univ : Finset (DigVec b N)).filter (fun d => (p : ℤ) ^ 2 ∣ (palVal b N d : ℤ))).image
        (palVal b N) := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_filter.1 hn
    have hpal : n ∈ (Ico (b ^ (2 * N)) (b ^ (2 * N + 1))).filter (IsPalindrome b) := by
      simp only [piStar, mem_filter] at hn1
      exact Finset.mem_filter.2 ⟨hn1.1, hn1.2.1⟩
    rw [pal_eq_image b N hb] at hpal
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.1 hpal
    refine Finset.mem_image.2 ⟨d, Finset.mem_filter.2 ⟨mem_univ _, ?_⟩, rfl⟩
    have : ((p ^ 2 : ℕ) : ℤ) ∣ (palVal b N d : ℤ) := Int.natCast_dvd_natCast.2 hn2
    push_cast at this
    exact this
  exact (card_le_card hsub).trans card_image_le

/-- `g = (2b²+1)/(3b²) < 1` and its fourth root. -/
noncomputable def gam (b : ℕ) : ℝ := Real.sqrt (Real.sqrt ((2 * (b : ℝ) ^ 2 + 1) / (3 * (b : ℝ) ^ 2)))

theorem gam_nonneg (b : ℕ) : 0 ≤ gam b := Real.sqrt_nonneg _

theorem gam_lt_one (b : ℕ) (hb : 2 ≤ b) : gam b < 1 := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hg : (2 * (b : ℝ) ^ 2 + 1) / (3 * (b : ℝ) ^ 2) < 1 := by
    rw [div_lt_one (by positivity)]; nlinarith
  have hg0 : 0 ≤ (2 * (b : ℝ) ^ 2 + 1) / (3 * (b : ℝ) ^ 2) := by positivity
  unfold gam
  rw [Real.sqrt_lt' one_pos, one_pow, Real.sqrt_lt' one_pos, one_pow]
  exact hg

theorem twelve_le_pow (b N : ℕ) (hb : 2 ≤ b) (hN : 4 ≤ N) : 12 * (N + 1) ≤ b ^ (2 * N + 1) := by
  have h1 : N + 1 < 2 ^ (N + 1) := Nat.lt_two_pow_self
  have h2 : 2 ^ (N + 5) ≤ 2 ^ (2 * N + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : 2 ^ (2 * N + 1) ≤ b ^ (2 * N + 1) := Nat.pow_le_pow_left hb _
  have h4 : 2 ^ (N + 5) = 16 * 2 ^ (N + 1) := by ring
  omega

/-- **Prop W for the b-adic block `[b^j, b^{j+1})`** with the fixed choice `m = ⌊N/20⌋`. -/
theorem block_bound (b N j : ℕ) (hb : 2 ≤ b) (hN : 60 ≤ N) (hj1 : 2 * N + 1 < 20 * (j + 1))
    (hj2 : 100 * j ≤ 23 * (2 * N + 1)) :
    ∑ p ∈ (Ico (b ^ j) (b ^ (j + 1))).filter Nat.Prime,
        (#((univ : Finset (DigVec b N)).filter
          (fun d => (p : ℤ) ^ 2 ∣ (palVal b N d : ℤ))) : ℝ) ≤
      27 * (b : ℝ) ^ (N + 1) * (16 * b * (N + 1) + 3) * gam b ^ (N / 20) := by
  set m := N / 20 with hm
  set S := (Ico (b ^ j) (b ^ (j + 1))).filter Nat.Prime with hSdef
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have hb0 : (0 : ℝ) < b := by linarith
  have hmℓ : m ≤ j + 1 := by omega
  have hlen : 2 * (j + 1) + m ≤ N + 1 := by omega
  have hj2' : 2 ≤ j := by omega
  have hbP : b < b ^ j := by
    calc b = b ^ 1 := (pow_one b).symm
      _ < b ^ j := Nat.pow_lt_pow_right (by omega) (by omega)
  have hS : ∀ p ∈ S, p.Prime ∧ b ^ j ≤ p := by
    intro p hp
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
    exact ⟨h2, (Finset.mem_Ico.1 h1).1⟩
  have hK : (#S : ℝ) ≤ (b : ℝ) ^ (j + 1) := by
    have : #S ≤ b ^ (j + 1) := (card_filter_le _ _).trans (by rw [Nat.card_Ico]; omega)
    exact_mod_cast this
  have hD : ∀ w : ℤ, w ≠ 0 → |w| ≤ (wmax b N : ℤ) →
      (#(S.filter (fun p => p.Prime ∧ b ^ j ≤ p ∧ (p : ℤ) ^ 2 ∣ w)) : ℝ) ≤ 80 := by
    intro w hw hwm
    have hP2 : 2 ≤ b ^ j := by omega
    have h := card_prime_sq_dvd_le S w hw (b ^ j) hP2
    refine h.trans ?_
    have hwm' : (|w| : ℝ) ≤ ((b : ℝ) ^ (4 * N + 2)) := by
      have h12 := twelve_le_pow b N hb (by omega)
      have : wmax b N ≤ b ^ (4 * N + 2) := by
        unfold wmax
        calc 6 * ((N + 1) * (2 * b ^ (2 * N + 1))) = (12 * (N + 1)) * b ^ (2 * N + 1) := by ring
          _ ≤ b ^ (2 * N + 1) * b ^ (2 * N + 1) := Nat.mul_le_mul_right _ h12
          _ = b ^ (4 * N + 2) := by rw [← pow_add]; ring_nf
      have h' : ((|w| : ℤ) : ℝ) ≤ ((wmax b N : ℕ) : ℝ) := by exact_mod_cast hwm
      calc (|w| : ℝ) = ((|w| : ℤ) : ℝ) := by push_cast; rfl
        _ ≤ ((wmax b N : ℕ) : ℝ) := h'
        _ ≤ _ := by exact_mod_cast this
    have hwpos : (0 : ℝ) < |(w : ℝ)| := by
      rw [abs_pos]; exact_mod_cast hw
    have hlogb : 0 < Real.log b := Real.log_pos hb1
    have hl1 : Real.log |(w : ℝ)| ≤ (4 * N + 2) * Real.log b := by
      calc Real.log |(w : ℝ)| ≤ Real.log ((b : ℝ) ^ (4 * N + 2)) :=
            Real.log_le_log hwpos (by simpa using hwm')
        _ = _ := by rw [Real.log_pow]; push_cast; ring
    have hl2 : Real.log ((b ^ j : ℕ) : ℝ) = j * Real.log b := by
      push_cast; rw [Real.log_pow]
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
    have hpos : 0 < 2 * ((j : ℝ) * Real.log b) := by positivity
    rw [hl2, div_le_iff₀ hpos]
    have hjN : (4 * (N : ℝ) + 2) ≤ 160 * j := by
      have : 4 * N + 2 ≤ 160 * j := by omega
      exact_mod_cast this
    nlinarith
  have hmain := propW_block b N (j + 1) m (b ^ j) (8 * b * (j + 1) * b ^ (2 * (N - (N + 1 - (j + 1)))) + 1)
    hb hmℓ hlen hbP le_rfl S hS ((b : ℝ) ^ (j + 1)) hK 80 (by norm_num) hD
  refine hmain.trans ?_
  -- the three terms
  set g : ℝ := (2 * (b : ℝ) ^ 2 + 1) / (3 * (b : ℝ) ^ 2) with hg
  have hg0 : 0 ≤ g := by positivity
  have hg1 : g ≤ 1 := by
    rw [hg, div_le_one (by positivity)]; nlinarith
  have hKρ : (b : ℝ) ^ (j + 1) * (((2 * (b : ℝ) ^ 2 + 1) / (3 * (b : ℝ) ^ 3)) ^ m *
      ((b : ℝ) ^ (j + 1 - m))⁻¹) = g ^ m := by
    have hpow : (b : ℝ) ^ (j + 1) = (b : ℝ) ^ m * (b : ℝ) ^ (j + 1 - m) := by
      rw [← pow_add]; congr 1; omega
    rw [hpow, hg]
    have hne : (b : ℝ) ^ (j + 1 - m) ≠ 0 := by positivity
    field_simp
    rw [← mul_pow]
    congr 1
    field_simp
  have hT1 : (b : ℝ) ^ (j + 1) * ((b : ℝ) ^ (N + 1 - (j + 1) - m))⁻¹ + 80 ≤ 81 := by
    have : (b : ℝ) ^ (j + 1) ≤ (b : ℝ) ^ (N + 1 - (j + 1) - m) :=
      pow_le_pow_right₀ hb1.le (by omega)
    have h' : (b : ℝ) ^ (j + 1) * ((b : ℝ) ^ (N + 1 - (j + 1) - m))⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one (by positivity)]; exact this
    linarith
  have hT3 : (b : ℝ) ^ (j + 1) * (((2 * (b : ℝ) ^ 2 + 1) / (3 * (b : ℝ) ^ 3)) ^ m *
      ((b : ℝ) ^ (j + 1 - m))⁻¹) + 80 ≤ 81 := by
    rw [hKρ]; linarith [pow_le_one₀ hg0 hg1 (n := m)]
  set A : ℝ := 16 * b * (N + 1) + 3 with hA
  have hA1 : 1 ≤ A := by
    have : (0 : ℝ) ≤ 16 * b * (N + 1) := by positivity
    rw [hA]; linarith
  have hT2 : (b : ℝ) ^ (j + 1) * (2 * ((8 * b * (j + 1) * b ^ (2 * (N - (N + 1 - (j + 1)))) + 1 : ℕ) : ℝ)
      / ((b ^ j : ℕ) : ℝ) ^ 2 + 1) * (((2 * (b : ℝ) ^ 2 + 1) / (3 * (b : ℝ) ^ 3)) ^ m *
      ((b : ℝ) ^ (j + 1 - m))⁻¹) ≤ A * g ^ m := by
    have e : (b : ℝ) ^ (j + 1) * (2 * ((8 * b * (j + 1) * b ^ (2 * (N - (N + 1 - (j + 1)))) + 1 : ℕ) : ℝ)
      / ((b ^ j : ℕ) : ℝ) ^ 2 + 1) * (((2 * (b : ℝ) ^ 2 + 1) / (3 * (b : ℝ) ^ 3)) ^ m *
      ((b : ℝ) ^ (j + 1 - m))⁻¹) = (2 * ((8 * b * (j + 1) * b ^ (2 * (N - (N + 1 - (j + 1)))) + 1 : ℕ) : ℝ)
      / ((b ^ j : ℕ) : ℝ) ^ 2 + 1) * g ^ m := by rw [← hKρ]; ring
    rw [e]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have hNj : N - (N + 1 - (j + 1)) = j := by omega
    rw [hNj]
    push_cast
    have hbj : (1 : ℝ) ≤ (b : ℝ) ^ j := one_le_pow₀ hb1.le
    have hjN : (j : ℝ) + 1 ≤ N + 1 := by
      have : j ≤ N := by omega
      have : (j : ℝ) ≤ N := by exact_mod_cast this
      linarith
    have : 2 * (8 * (b : ℝ) * (j + 1) * (b : ℝ) ^ (2 * j) + 1) / ((b : ℝ) ^ j) ^ 2 =
        16 * b * (j + 1) + 2 / ((b : ℝ) ^ j) ^ 2 := by
      field_simp; ring
    rw [this, hA]
    have h2 : 2 / ((b : ℝ) ^ j) ^ 2 ≤ 2 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    nlinarith
  -- combine
  have s1 : Real.sqrt ((b : ℝ) ^ (j + 1) * ((b : ℝ) ^ (N + 1 - (j + 1) - m))⁻¹ + 80) ≤ 9 := by
    calc _ ≤ Real.sqrt 81 := Real.sqrt_le_sqrt hT1
      _ = 9 := by rw [show (81 : ℝ) = 9 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have s3 : Real.sqrt ((b : ℝ) ^ (j + 1) * (((2 * (b : ℝ) ^ 2 + 1) / (3 * (b : ℝ) ^ 3)) ^ m *
      ((b : ℝ) ^ (j + 1 - m))⁻¹) + 80) ≤ 9 := by
    calc _ ≤ Real.sqrt 81 := Real.sqrt_le_sqrt hT3
      _ = 9 := by rw [show (81 : ℝ) = 9 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have s2 : Real.sqrt ((b : ℝ) ^ (j + 1) * (2 * ((8 * b * (j + 1) * b ^ (2 * (N - (N + 1 - (j + 1)))) + 1 : ℕ) : ℝ)
      / ((b ^ j : ℕ) : ℝ) ^ 2 + 1) * (((2 * (b : ℝ) ^ 2 + 1) / (3 * (b : ℝ) ^ 3)) ^ m *
      ((b : ℝ) ^ (j + 1 - m))⁻¹)) ≤ Real.sqrt A * Real.sqrt g ^ m := by
    calc _ ≤ Real.sqrt (A * g ^ m) := Real.sqrt_le_sqrt hT2
      _ = _ := by rw [Real.sqrt_mul (by linarith), sqrt_pow' g hg0]
  have s23 : Real.sqrt (Real.sqrt ((b : ℝ) ^ (j + 1) * (2 * ((8 * b * (j + 1) * b ^ (2 * (N - (N + 1 - (j + 1)))) + 1 : ℕ) : ℝ)
      / ((b ^ j : ℕ) : ℝ) ^ 2 + 1) * (((2 * (b : ℝ) ^ 2 + 1) / (3 * (b : ℝ) ^ 3)) ^ m *
      ((b : ℝ) ^ (j + 1 - m))⁻¹)) * Real.sqrt ((b : ℝ) ^ (j + 1) * (((2 * (b : ℝ) ^ 2 + 1) / (3 * (b : ℝ) ^ 3)) ^ m *
      ((b : ℝ) ^ (j + 1 - m))⁻¹) + 80)) ≤ 3 * A * gam b ^ m := by
    calc _ ≤ Real.sqrt ((Real.sqrt A * Real.sqrt g ^ m) * 9) :=
          Real.sqrt_le_sqrt (mul_le_mul s2 s3 (Real.sqrt_nonneg _) (by positivity))
      _ = Real.sqrt (Real.sqrt A) * gam b ^ m * 3 := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
            sqrt_pow' _ (Real.sqrt_nonneg _), show (9 : ℝ) = 3 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]
          rfl
      _ ≤ A * gam b ^ m * 3 := by
          have h1 : Real.sqrt A ≤ A := sqrt_le_self' A hA1
          have h2 : Real.sqrt (Real.sqrt A) ≤ Real.sqrt A :=
            sqrt_le_self' _ (by rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hA1)
          have := gam_nonneg b
          gcongr
          linarith
      _ = 3 * A * gam b ^ m := by ring
  calc _ ≤ (b : ℝ) ^ (N + 1) * 9 * (3 * A * gam b ^ m) := by
        gcongr
    _ = _ := by rw [hA]; ring

/-- Exponential decay beats the polynomial factors. -/
theorem poly_gam_eventually (b : ℕ) (hb : 2 ≤ b) (C ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, C * ((n : ℝ) + 1) ^ 5 * gam b ^ n ≤ ε := by
  have hγ : |gam b| < 1 := by rw [abs_of_nonneg (gam_nonneg b)]; exact gam_lt_one b hb
  have ht := tendsto_pow_const_mul_const_pow_of_abs_lt_one 5 hγ
  have hC : 0 < 32 * |C| + 1 := by positivity
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1
    ((tendsto_order.1 ht).2 (ε / (32 * |C| + 1)) (by positivity))
  refine ⟨max n₀ 1, fun n hn => ?_⟩
  have h1 := hn₀ n (le_of_max_le_left hn)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
  have hpow : ((n : ℝ) + 1) ^ 5 ≤ 32 * (n : ℝ) ^ 5 := by
    have : (n : ℝ) + 1 ≤ 2 * n := by linarith
    calc ((n : ℝ) + 1) ^ 5 ≤ (2 * (n : ℝ)) ^ 5 := pow_le_pow_left₀ (by positivity) this 5
      _ = 32 * (n : ℝ) ^ 5 := by ring
  have hg0 : 0 ≤ gam b ^ n := pow_nonneg (gam_nonneg b) n
  calc C * ((n : ℝ) + 1) ^ 5 * gam b ^ n ≤ |C| * (32 * (n : ℝ) ^ 5) * gam b ^ n := by
        apply mul_le_mul_of_nonneg_right _ hg0
        calc C * ((n : ℝ) + 1) ^ 5 ≤ |C| * ((n : ℝ) + 1) ^ 5 :=
              mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
          _ ≤ |C| * (32 * (n : ℝ) ^ 5) := mul_le_mul_of_nonneg_left hpow (abs_nonneg C)
    _ = 32 * |C| * ((n : ℝ) ^ 5 * gam b ^ n) := by ring
    _ ≤ (32 * |C| + 1) * (ε / (32 * |C| + 1)) := by
        apply mul_le_mul (by linarith) h1.le (by positivity) (by positivity)
    _ = ε := by field_simp

theorem rpow_x_eq (b N : ℕ) (c : ℝ) :
    ((b : ℝ) ^ (2 * N + 1)) ^ c = (b : ℝ) ^ (((2 * N + 1 : ℕ) : ℝ) * c) := by
  rw [Real.rpow_natCast_mul (by positivity)]

/-- The form the sieve (M13) consumes: primes `x^{1/20} ≤ p ≤ x^{23/100}`, saving `log³x`.
From `block_bound` on b-adic blocks and `card_piStar_lower`. -/
theorem squares_piStar (b : ℕ) (hb : 2 ≤ b) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∑ p ∈ (Icc ⌈((b : ℝ) ^ (2 * N + 1)) ^ (1 / 20 : ℝ)⌉₊
          ⌊((b : ℝ) ^ (2 * N + 1)) ^ (23 / 100 : ℝ)⌋₊).filter Nat.Prime,
          (countDvd (piStar b N) (p ^ 2) : ℝ)
        ≤ (#(piStar b N) : ℝ) / (Real.log ((b : ℝ) ^ (2 * N + 1))) ^ 3 := by
  obtain ⟨c, hc, N₀', hN₀'⟩ := card_piStar_lower b hb
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have hlogb : 0 < Real.log b := Real.log_pos hb1
  set C : ℝ := 27 * b * 20 * (320 * b + 3) * (40 * Real.log b) ^ 3 with hC
  obtain ⟨n₀, hn₀⟩ := poly_gam_eventually b hb C c hc
  refine ⟨max (max 60 N₀') (20 * (n₀ + 1)), fun N hN => ?_⟩
  have hN60 : 60 ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN)
  have hNc : N₀' ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)
  have hNn : 20 * (n₀ + 1) ≤ N := le_trans (le_max_right _ _) hN
  set R := (Icc ⌈((b : ℝ) ^ (2 * N + 1)) ^ (1 / 20 : ℝ)⌉₊
    ⌊((b : ℝ) ^ (2 * N + 1)) ^ (23 / 100 : ℝ)⌋₊).filter Nat.Prime with hR
  set cnt : ℕ → ℝ := fun p => (#((univ : Finset (DigVec b N)).filter
    (fun d => (p : ℤ) ^ 2 ∣ (palVal b N d : ℤ))) : ℝ) with hcnt
  set B : ℝ := 27 * (b : ℝ) ^ (N + 1) * (16 * b * (N + 1) + 3) * gam b ^ (N / 20) with hB
  -- block indices
  have hjb : ∀ p ∈ R, 2 * N + 1 < 20 * (Nat.log b p + 1) ∧
      100 * Nat.log b p ≤ 23 * (2 * N + 1) := by
    intro p hp
    obtain ⟨hpI, hpp⟩ := Finset.mem_filter.1 hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_Icc.1 hpI
    have hp0 : p ≠ 0 := hpp.ne_zero
    have hlo : (b : ℝ) ^ (((2 * N + 1 : ℕ) : ℝ) * (1 / 20)) < (b : ℝ) ^ ((Nat.log b p + 1 : ℕ) : ℝ) := by
      rw [← rpow_x_eq, Real.rpow_natCast]
      calc ((b : ℝ) ^ (2 * N + 1)) ^ (1 / 20 : ℝ) ≤ ⌈((b : ℝ) ^ (2 * N + 1)) ^ (1 / 20 : ℝ)⌉₊ :=
            Nat.le_ceil _
        _ ≤ (p : ℝ) := by exact_mod_cast hp1
        _ < (b : ℝ) ^ (Nat.log b p + 1) := by exact_mod_cast Nat.lt_pow_succ_log_self (by omega) p
    have hhi : (b : ℝ) ^ ((Nat.log b p : ℕ) : ℝ) ≤ (b : ℝ) ^ (((2 * N + 1 : ℕ) : ℝ) * (23 / 100)) := by
      rw [← rpow_x_eq, Real.rpow_natCast]
      calc (b : ℝ) ^ (Nat.log b p) ≤ (p : ℝ) := by exact_mod_cast Nat.pow_log_le_self b hp0
        _ ≤ ⌊((b : ℝ) ^ (2 * N + 1)) ^ (23 / 100 : ℝ)⌋₊ := by exact_mod_cast hp2
        _ ≤ _ := Nat.floor_le (by positivity)
    rw [Real.rpow_lt_rpow_left_iff hb1] at hlo
    rw [Real.rpow_le_rpow_left_iff hb1] at hhi
    push_cast at hlo hhi
    constructor
    · have : (2 * (N : ℝ) + 1) < 20 * ((Nat.log b p : ℝ) + 1) := by linarith
      exact_mod_cast this
    · have : 100 * (Nat.log b p : ℝ) ≤ 23 * (2 * N + 1) := by linarith
      exact_mod_cast this
  -- sum over blocks
  have hsum : ∑ p ∈ R, cnt p ≤ ∑ j ∈ R.image (Nat.log b),
      ∑ p ∈ (Ico (b ^ j) (b ^ (j + 1))).filter Nat.Prime, cnt p := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := Nat.log b) (t := R.image (Nat.log b))
      (fun p hp => Finset.mem_image_of_mem _ hp) cnt]
    apply Finset.sum_le_sum
    intro j _
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hpR, hpj⟩ := Finset.mem_filter.1 hp
      obtain ⟨-, hpp⟩ := Finset.mem_filter.1 hpR
      refine Finset.mem_filter.2 ⟨Finset.mem_Ico.2 ⟨?_, ?_⟩, hpp⟩
      · rw [← hpj]; exact Nat.pow_log_le_self b hpp.ne_zero
      · rw [← hpj]; exact Nat.lt_pow_succ_log_self (by omega) p
    · intro p _ _
      exact Nat.cast_nonneg _
  have hblocks : ∑ j ∈ R.image (Nat.log b),
      ∑ p ∈ (Ico (b ^ j) (b ^ (j + 1))).filter Nat.Prime, cnt p ≤ (N + 1) * B := by
    have hsub : R.image (Nat.log b) ⊆ range (N + 1) := by
      intro j hj
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hj
      have := (hjb p hp).2
      rw [mem_range]; omega
    calc _ ≤ ∑ j ∈ R.image (Nat.log b), B := by
          apply Finset.sum_le_sum
          intro j hj
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hj
          exact block_bound b N (Nat.log b p) hb hN60 (hjb p hp).1 (hjb p hp).2
      _ = (#(R.image (Nat.log b)) : ℝ) * B := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (N + 1) * B := by
          apply mul_le_mul_of_nonneg_right _ (by rw [hB]; have := gam_nonneg b; positivity)
          have := card_le_card hsub
          rw [card_range] at this
          exact_mod_cast this
  -- the final asymptotic comparison
  have hlogx : Real.log ((b : ℝ) ^ (2 * N + 1)) = (2 * N + 1) * Real.log b := by
    rw [Real.log_pow]; push_cast; ring
  have hcard := hN₀' N hNc
  set n := N / 20 with hn
  have hnn : n₀ ≤ n := by omega
  have hN1 : (N : ℝ) + 1 ≤ 20 * ((n : ℝ) + 1) := by
    have : N + 1 ≤ 20 * (n + 1) := by omega
    exact_mod_cast this
  have hF := hn₀ n hnn
  have hbN : (0 : ℝ) < (b : ℝ) ^ N := by positivity
  have hkey : (N + 1) * B * ((2 * N + 1) * Real.log b) ^ 3 ≤ c * (b : ℝ) ^ N := by
    have hγ := gam_nonneg b
    have e : (N + 1) * B * ((2 * N + 1) * Real.log b) ^ 3 = (b : ℝ) ^ N *
        (27 * b * (N + 1) * (16 * b * (N + 1) + 3) * ((2 * N + 1) * Real.log b) ^ 3 *
          gam b ^ n) := by rw [hB]; ring
    rw [e, mul_comm c]
    apply mul_le_mul_of_nonneg_left _ hbN.le
    refine le_trans ?_ hF
    rw [hC]
    have h2N : (2 * (N : ℝ) + 1) ≤ 40 * ((n : ℝ) + 1) := by linarith
    have h16 : 16 * (b : ℝ) * (N + 1) + 3 ≤ (320 * b + 3) * ((n : ℝ) + 1) := by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith
    have hgn : 0 ≤ gam b ^ n := pow_nonneg hγ n
    have hl3 : ((2 * N + 1) * Real.log b) ^ 3 ≤ (40 * Real.log b) ^ 3 * ((n : ℝ) + 1) ^ 3 := by
      rw [← mul_pow]
      apply pow_le_pow_left₀ (by positivity)
      nlinarith
    calc 27 * (b : ℝ) * (N + 1) * (16 * b * (N + 1) + 3) * ((2 * N + 1) * Real.log b) ^ 3 *
          gam b ^ n
        ≤ 27 * (b : ℝ) * (20 * ((n : ℝ) + 1)) * ((320 * b + 3) * ((n : ℝ) + 1)) *
          ((40 * Real.log b) ^ 3 * ((n : ℝ) + 1) ^ 3) * gam b ^ n := by
          gcongr
      _ = 27 * b * 20 * (320 * b + 3) * (40 * Real.log b) ^ 3 * ((n : ℝ) + 1) ^ 5 *
          gam b ^ n := by ring
  calc ∑ p ∈ R, (countDvd (piStar b N) (p ^ 2) : ℝ) ≤ ∑ p ∈ R, cnt p := by
        apply Finset.sum_le_sum
        intro p _
        have h := countDvd_piStar_le b N p hb
        simp only [hcnt]
        exact_mod_cast h
    _ ≤ (N + 1) * B := hsum.trans hblocks
    _ ≤ (#(piStar b N) : ℝ) / (Real.log ((b : ℝ) ^ (2 * N + 1))) ^ 3 := by
        rw [hlogx, le_div_iff₀ (by positivity)]
        calc (N + 1) * B * ((2 * N + 1) * Real.log b) ^ 3 ≤ c * (b : ℝ) ^ N := hkey
          _ ≤ _ := hcard

end Palprimes
