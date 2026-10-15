import Proof.Wire_3_5.SeedFixSampExpr

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SeedFix
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Sampler
open Finset

theorem flatMap_range_mul {α : Type} (a b : ℕ) (f : ℕ → List α) :
    (List.range (a * b)).flatMap f = (List.range a).flatMap fun x => (List.range b).flatMap fun y => f (x * b + y) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_mul, List.range_add, List.flatMap_append, ih, List.range_succ, List.flatMap_append,
      List.flatMap_map]
    simp

theorem digitsL_eq (m : ℕ) (hm : 0 < m) :
    digitsL m = (List.range (m ^ 8)).map fun x => fun k : Fin 8 => (⟨x / m ^ (k : ℕ) % m, Nat.mod_lt _ hm⟩ : Fin m) := by
  unfold digitsL
  rw [← List.map_coe_finRange_eq_range, List.map_map]
  refine List.map_congr_left fun x _ => ?_
  funext k
  apply Fin.ext
  simp [finFunctionFinEquiv_symm_apply_val]

section Flat
variable (P : SeedParams)

/-- The walk, labels and signs of counter `j` (top, middle, low fields). -/
def wOf (j : ℕ) : Fin 8 → Fin P.N :=
  fun k => ⟨j / ((2 ^ P.ell) ^ 8 * 2 ^ 8) / P.N ^ (k : ℕ) % P.N, Nat.mod_lt _ (by positivity)⟩
def aOf (j : ℕ) : Fin 8 → ℕ := fun k => j / 2 ^ 8 % (2 ^ P.ell) ^ 8 / (2 ^ P.ell) ^ (k : ℕ) % 2 ^ P.ell
def bOf (j : ℕ) : Fin 8 → Bool := fun k => finTwoEquiv ⟨j % 2 ^ 8 / 2 ^ (k : ℕ) % 2, Nat.mod_lt _ (by norm_num)⟩

/-- The terms of counter `j` at state `t`: nothing unless every label is below `Q` and the count is nonzero. -/
def groupAt (R : ℕ) (batch : List SExpr) (plen pre t j : ℕ) : SExpr :=
  if ∀ k, aOf P j k < P.Q then
    (if cntL P plen pre (aOf P j) (wOf P j) (bOf j) = 0 then [] else termsAt P batch R plen pre (wOf P j) (aOf P j) (bOf j) t)
  else []

theorem flatMap_ite_const {α β : Type} (c : Prop) [Decidable c] (l : List α) (f : α → List β) :
    (if c then l.flatMap f else []) = l.flatMap fun a => if c then f a else [] := by
  split
  · rfl
  · simp

/-- **The state's terms in counter order.** -/
theorem sampTermsT_flat (R : ℕ) (batch : List SExpr) (plen pre t : ℕ) :
    sampTermsT P R batch plen pre t =
      (List.range (P.N ^ 8 * ((2 ^ P.ell) ^ 8 * 2 ^ 8))).flatMap (groupAt P R batch plen pre t) := by
  unfold sampTermsT
  rw [digitsL_eq P.N (by positivity), digitsL_eq (2 ^ P.ell) (by positivity), digitsL_eq 2 (by norm_num),
    flatMap_range_mul, List.flatMap_map]
  refine List.flatMap_congr fun x hx => ?_
  rw [flatMap_range_mul, List.flatMap_map]
  refine List.flatMap_congr fun y hy => ?_
  rw [flatMap_ite_const, List.flatMap_map]
  refine List.flatMap_congr fun z hz => ?_
  have hx' := List.mem_range.mp hx
  have hy' := List.mem_range.mp hy
  have hz' := List.mem_range.mp hz
  set B := (2 ^ P.ell) ^ 8 * 2 ^ 8
  have hj1 : (x * B + (y * 2 ^ 8 + z)) / B = x := by
    have : y * 2 ^ 8 + z < B := by
      simp only [B]; nlinarith
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt this, Nat.zero_add]
  have hj2 : (x * B + (y * 2 ^ 8 + z)) / 2 ^ 8 % (2 ^ P.ell) ^ 8 = y := by
    have e : x * B + (y * 2 ^ 8 + z) = (x * (2 ^ P.ell) ^ 8 + y) * 2 ^ 8 + z := by simp only [B]; ring
    rw [e, Nat.add_comm _ z, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hz', Nat.zero_add,
      Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hy']
  have hj3 : (x * B + (y * 2 ^ 8 + z)) % 2 ^ 8 = z := by
    have e : x * B + (y * 2 ^ 8 + z) = z + (x * (2 ^ P.ell) ^ 8 + y) * 2 ^ 8 := by simp only [B]; ring
    rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hz']
  have hj1' : (x * B + (y * 2 ^ 8 + z)) / ((2 ^ P.ell) ^ 8 * 2 ^ 8) = x := hj1
  unfold groupAt wOf aOf bOf
  simp only [hj1', hj2, hj3]

end Flat

end NearCubicWires.WireExponent3_5.SeedFix
