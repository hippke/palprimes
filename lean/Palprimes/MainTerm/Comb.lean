import Palprimes.Greaves.Subsets

/-! # Greaves §4: the main term as Rosser sums (Lemma 4.1, exact form)

With a density `g` on primes, `Gw σ z ℓ c = Σ_{s ⊆ ℓ, RosOK σ z s} (−1)^{|s|} g(s) (c − Σ_s w)`.
It is affine in `c` and in `w`: `Gw σ z ℓ c = c · Sg σ z ℓ − Σ_{p ∈ ℓ} w p · Cg σ z ℓ p`, with
`Sg` the unweighted Rosser sum (`S^±` of Greaves) and `Cg` the coefficient of `w p`.
`Cg` of the head prime `P` is `−[cond] g(P) Sg(!σ, z/P, rest)`; deeper primes recurse. -/

set_option linter.style.longLine false

open Finset

namespace Palprimes.Greaves

variable (g : ℕ → ℝ)

/-- The weighted Rosser sum with density `g` and weights `w`. -/
noncomputable def Gw (w : ℕ → ℝ) : Bool → ℝ → List ℕ → ℝ → ℝ
  | _, _, [], c => c
  | σ, z, P :: l, c => Gw w σ z l c - (if headOK σ z P then g P * Gw w (!σ) (z / P) l (c - w P) else 0)

/-- The unweighted Rosser sum `S^±` (Greaves (4.1)). -/
noncomputable def Sg : Bool → ℝ → List ℕ → ℝ
  | _, _, [] => 1
  | σ, z, P :: l => Sg σ z l - (if headOK σ z P then g P * Sg (!σ) (z / P) l else 0)

/-- The coefficient of `w p`. -/
noncomputable def Cg : Bool → ℝ → List ℕ → ℕ → ℝ
  | _, _, [], _ => 0
  | σ, z, P :: l, p =>
      (if p = P then 0 else Cg σ z l p) -
        (if headOK σ z P then g P * (if p = P then Sg g (!σ) (z / P) l else Cg (!σ) (z / P) l p) else 0)

theorem sum_map_sub_mul (w : ℕ → ℝ) (m : List ℕ) (f h : ℕ → ℝ) (c : ℝ) :
    (m.map (fun q => w q * (f q - c * h q))).sum =
      (m.map (fun q => w q * f q)).sum - c * (m.map (fun q => w q * h q)).sum := by
  induction m with
  | nil => simp
  | cons x m ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- **Affine decomposition** for lists without repetition (Greaves Lemma 4.1, exact). -/
theorem Gw_eq (w : ℕ → ℝ) : ∀ (ℓ : List ℕ), ℓ.Nodup → ∀ (σ : Bool) (z c : ℝ),
    Gw g w σ z ℓ c = c * Sg g σ z ℓ - (ℓ.map (fun p => w p * Cg g σ z ℓ p)).sum := by
  intro ℓ
  induction ℓ with
  | nil => intro _ σ z c; simp [Gw, Sg]
  | cons P l ih =>
    intro hnd σ z c
    have hPl : P ∉ l := (List.nodup_cons.1 hnd).1
    have hl : l.Nodup := (List.nodup_cons.1 hnd).2
    simp only [Gw, Sg, Cg, List.map_cons, List.sum_cons]
    rw [ih hl σ z c]
    have hrest : ∀ q ∈ l, q ≠ P := fun q hq h => hPl (h ▸ hq)
    have e1 : (l.map (fun q => w q * ((if q = P then 0 else Cg g σ z l q) -
        (if headOK σ z P then g P * (if q = P then Sg g (!σ) (z / P) l else Cg g (!σ) (z / P) l q) else 0)))).sum =
        (l.map (fun q => w q * (Cg g σ z l q -
        (if headOK σ z P then g P * Cg g (!σ) (z / P) l q else 0)))).sum := by
      congr 1; apply List.map_congr_left; intro q hq
      rw [if_neg (hrest q hq), if_neg (hrest q hq)]
    rw [e1]
    split_ifs with hh
    · rw [ih hl (!σ) (z / P) (c - w P)]
      have e2 : (l.map (fun q => w q * (Cg g σ z l q - g P * Cg g (!σ) (z / P) l q))).sum =
          (l.map (fun q => w q * Cg g σ z l q)).sum - g P * (l.map (fun q => w q * Cg g (!σ) (z / P) l q)).sum := by
        exact sum_map_sub_mul w l _ _ (g P)
      rw [e2]; ring
    · simp only [sub_zero, mul_zero, zero_add]

/-! ## The chain form of `Cg` with a generic leaf -/

/-- Chains through the larger primes `pre`, ending at `p`, with a leaf value at the end:
`CS leaf σ z [] = −[cond] g p · leaf (!σ) (z/p)`,
`CS leaf σ z (P :: pre) = CS leaf σ z pre − [cond] g P · CS leaf (!σ) (z/P) pre`. -/
noncomputable def CS (p : ℕ) (leaf : Bool → ℝ → ℝ) : Bool → ℝ → List ℕ → ℝ
  | σ, z, [] => -(if headOK σ z p then g p * leaf (!σ) (z / p) else 0)
  | σ, z, P :: pre => CS p leaf σ z pre - (if headOK σ z P then g P * CS p leaf (!σ) (z / P) pre else 0)

/-- `Cg` is the chain sum with leaf `Sg` on the primes below `p`. -/
theorem Cg_eq_CS (p : ℕ) (post : List ℕ) : ∀ (pre : List ℕ), p ∉ pre → ∀ (σ : Bool) (z : ℝ),
    Cg g σ z (pre ++ p :: post) p = CS g p (fun σ' z' => Sg g σ' z' post) σ z pre := by
  intro pre
  induction pre with
  | nil => intro _ σ z; simp [Cg, CS]
  | cons P pre ih =>
    intro hp σ z
    have hpP : p ≠ P := fun h => hp (h ▸ List.mem_cons_self)
    have hpre : p ∉ pre := fun h => hp (List.mem_cons_of_mem P h)
    simp only [List.cons_append, Cg, CS, if_neg hpP]
    rw [ih hpre σ z, ih hpre (!σ) (z / P)]

/-- Leaves differing by at most `M` change the chain sum by at most `g p Π_{q∈pre}(1 + g q) M`. -/
theorem CS_sub_le (p : ℕ) (hg : ∀ q, 0 ≤ g q) (leaf1 leaf2 : Bool → ℝ → ℝ) (M : ℝ)
    (hM : ∀ σ z, |leaf1 σ z - leaf2 σ z| ≤ M) : ∀ (pre : List ℕ) (σ : Bool) (z : ℝ),
    |CS g p leaf1 σ z pre - CS g p leaf2 σ z pre| ≤ g p * (pre.map (fun q => 1 + g q)).prod * M := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM false 0)
  intro pre
  induction pre with
  | nil =>
    intro σ z
    simp only [CS, List.map_nil, List.prod_nil, mul_one]
    split_ifs
    · have e : -(g p * leaf1 (!σ) (z / p)) - -(g p * leaf2 (!σ) (z / p)) =
          -(g p * (leaf1 (!σ) (z / p) - leaf2 (!σ) (z / p))) := by ring
      rw [e, abs_neg, abs_mul, abs_of_nonneg (hg p)]
      exact mul_le_mul_of_nonneg_left (hM _ _) (hg p)
    · simp; exact mul_nonneg (hg p) hM0
  | cons P pre ih =>
    intro σ z
    simp only [CS, List.map_cons, List.prod_cons]
    have h1 := ih σ z
    have h2 := ih (!σ) (z / P)
    have hP := hg P
    have hpre0 : 0 ≤ (pre.map (fun q => 1 + g q)).prod :=
      List.prod_nonneg (fun x hx => by rw [List.mem_map] at hx; obtain ⟨q, _, rfl⟩ := hx; linarith [hg q])
    split_ifs
    · calc |CS g p leaf1 σ z pre - g P * CS g p leaf1 (!σ) (z / P) pre -
            (CS g p leaf2 σ z pre - g P * CS g p leaf2 (!σ) (z / P) pre)|
          = |(CS g p leaf1 σ z pre - CS g p leaf2 σ z pre) -
              g P * (CS g p leaf1 (!σ) (z / P) pre - CS g p leaf2 (!σ) (z / P) pre)| := by ring_nf
        _ ≤ |CS g p leaf1 σ z pre - CS g p leaf2 σ z pre| +
              g P * |CS g p leaf1 (!σ) (z / P) pre - CS g p leaf2 (!σ) (z / P) pre| := by
            refine (abs_sub _ _).trans ?_
            rw [abs_mul, abs_of_nonneg hP]
        _ ≤ g p * (pre.map (fun q => 1 + g q)).prod * M + g P * (g p * (pre.map (fun q => 1 + g q)).prod * M) := by
            gcongr
        _ = g p * ((1 + g P) * (pre.map (fun q => 1 + g q)).prod) * M := by ring
    · simp only [sub_zero]
      calc _ ≤ g p * (pre.map (fun q => 1 + g q)).prod * M := h1
        _ ≤ g p * ((1 + g P) * (pre.map (fun q => 1 + g q)).prod) * M := by
            have : (pre.map (fun q => 1 + g q)).prod ≤ (1 + g P) * (pre.map (fun q => 1 + g q)).prod := by
              nlinarith
            have := mul_le_mul_of_nonneg_left this (hg p)
            nlinarith

end Palprimes.Greaves
