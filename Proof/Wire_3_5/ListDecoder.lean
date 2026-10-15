import Proof.Wire_3_5.LucasBit
import Proof.Wire_3_5.FilterGapDegree

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Lists
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters MvPolynomial

/-- `binom(n, 2^h) mod 2 = n_h` in `𝔽₂` (Lucas). -/
theorem natChoose_two_pow_zmod (n h : ℕ) :
    ((Nat.choose n (2 ^ h) : ℕ) : ZMod 2) = if n.testBit h then 1 else 0 := by
  rw [← ZMod.natCast_mod, choose_two_pow_mod_two n h]
  split_ifs <;> simp

theorem choose_two_pow_int (x : ℤ) (h : ℕ) :
    ((Ring.choose x (2 ^ h) : ℤ) : ZMod 2) = if x.testBit h then 1 else 0 := by
  rcases x with n | y
  · have : Ring.choose ((n : ℤ)) (2 ^ h) = ((Nat.choose n (2 ^ h) : ℕ) : ℤ) := Ring.choose_natCast n (2 ^ h)
    simp only [Int.ofNat_eq_natCast] at *
    rw [this, Int.cast_natCast, natChoose_two_pow_zmod]
    rfl
  · have hc : ((y : ℤ) + 1 + ((2 ^ h : ℕ) : ℤ) - 1) = (((2 ^ h + y : ℕ)) : ℤ) := by push_cast; ring
    have key : ((Ring.choose (Int.negSucc y) (2 ^ h) : ℤ) : ZMod 2) =
        ((Nat.choose (2 ^ h + y) (2 ^ h) : ℕ) : ZMod 2) := by
      rw [show Int.negSucc y = -((y : ℤ) + 1) from rfl, Ring.choose_neg, hc, Ring.choose_natCast]
      rcases Int.units_eq_one_or (Int.negOnePow ((2 ^ h : ℕ) : ℤ)) with hh | hh
      · rw [hh, one_smul]; push_cast; rfl
      · rw [hh, Units.neg_smul, one_smul]; push_cast; exact ZMod.neg_eq_self_mod_two _
    rw [key, natChoose_two_pow_zmod, Nat.testBit_two_pow_add_eq]
    show _ = if Int.testBit (Int.negSucc y) h = true then 1 else 0
    simp [Int.testBit]

/-- **The binomial polynomial** of a list of Boolean literals: `binom(S + a, t) mod 2`, `S` the literals' sum, built
by Pascal's rule `binom(x+ℓ, t+1) = binom(x, t+1) + ℓ·binom(x, t)`. -/
noncomputable def binomPoly {σ : Type} : List (MvPolynomial σ (ZMod 2)) → ℤ → ℕ → MvPolynomial σ (ZMod 2)
  | [], a, t => C ((Ring.choose a t : ℤ) : ZMod 2)
  | _ :: _, _, 0 => 1
  | ℓ :: ls, a, t + 1 => binomPoly ls a (t + 1) + ℓ * binomPoly ls a t

/-- The number of true literals at a Boolean point. -/
noncomputable def literalSum {σ : Type} (x : σ → ZMod 2) (ls : List (MvPolynomial σ (ZMod 2))) : ℕ :=
  (ls.map fun ℓ => (eval x ℓ).val).sum

theorem eval_binomPoly {σ : Type} (x : σ → ZMod 2) (ls : List (MvPolynomial σ (ZMod 2)))
    (hls : ∀ ℓ ∈ ls, eval x ℓ = 0 ∨ eval x ℓ = 1) (a : ℤ) (t : ℕ) :
    eval x (binomPoly ls a t) = ((Ring.choose (a + literalSum x ls) t : ℤ) : ZMod 2) := by
  induction ls generalizing t with
  | nil => simp [binomPoly, literalSum]
  | cons ℓ ls ih =>
    have hls' : ∀ ℓ' ∈ ls, eval x ℓ' = 0 ∨ eval x ℓ' = 1 := fun ℓ' h => hls ℓ' (List.mem_cons_of_mem _ h)
    cases t with
    | zero => simp [binomPoly]
    | succ t =>
      simp only [binomPoly, map_add, map_mul, ih hls', literalSum, List.map_cons, List.sum_cons]
      rcases hls ℓ (List.mem_cons_self ..) with h0 | h1
      · rw [h0]; simp
      · rw [h1]
        have hv : (1 : ZMod 2).val = 1 := rfl
        rw [hv]
        have hstep : a + ((1 + (ls.map fun ℓ => (eval x ℓ).val).sum : ℕ) : ℤ) =
            (a + (((ls.map fun ℓ => (eval x ℓ).val).sum : ℕ) : ℤ)) + 1 := by push_cast; ring
        rw [hstep, Ring.choose_succ_succ]
        push_cast
        ring

theorem totalDegree_binomPoly {σ : Type} (ls : List (MvPolynomial σ (ZMod 2)))
    (hls : ∀ ℓ ∈ ls, ℓ.totalDegree ≤ 1) (a : ℤ) (t : ℕ) : (binomPoly ls a t).totalDegree ≤ t := by
  induction ls generalizing t with
  | nil => simp only [binomPoly]; rw [totalDegree_C]; exact Nat.zero_le _
  | cons ℓ ls ih =>
    have hls' : ∀ ℓ' ∈ ls, ℓ'.totalDegree ≤ 1 := fun ℓ' h => hls ℓ' (List.mem_cons_of_mem _ h)
    cases t with
    | zero => simp [binomPoly]
    | succ t =>
      simp only [binomPoly]
      refine (totalDegree_add _ _).trans (max_le (ih hls' (t + 1)) ?_)
      refine (totalDegree_mul _ _).trans ?_
      have := hls ℓ (List.mem_cons_self ..)
      have := ih hls' t
      omega

/-- The decoder bit `G = binom(S + a, 2^h) mod 2` as a polynomial: degree `≤ 2^h` and value bit `h` of `S + a`. -/
theorem eval_binomPoly_two_pow {σ : Type} (x : σ → ZMod 2) (ls : List (MvPolynomial σ (ZMod 2)))
    (hls : ∀ ℓ ∈ ls, eval x ℓ = 0 ∨ eval x ℓ = 1) (a : ℤ) (h : ℕ) :
    eval x (binomPoly ls a (2 ^ h)) = bitF2 ((a + literalSum x ls).testBit h) := by
  rw [eval_binomPoly x ls hls, choose_two_pow_int]
  unfold bitF2; split_ifs <;> rfl

end NearCubicWires.WireExponent3_5.Lists
