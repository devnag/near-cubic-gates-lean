import Proof.Wire_3_5.ListRepair

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Lists
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters MvPolynomial
open Finset

namespace ListData
variable (D : ListData)

noncomputable def levelLit (j : ℕ) {L : ℕ} (i : Fin L) : MvPolynomial (Fin L) (ZMod 2) :=
  if D.inLevel (j + 1) i then 1 - X i else if D.inLevel j i then X i else 0

/-- The literals of level `j`, one per coordinate. -/
noncomputable def levelLits (j L : ℕ) : List (MvPolynomial (Fin L) (ZMod 2)) := (List.finRange L).map (D.levelLit j)

def levelOffset (j L : ℕ) : ℤ :=
  (D.W j : ℤ) - (((Finset.univ : Finset (Fin L)).filter fun i : Fin L => D.inLevel (j + 1) (i : ℕ) = true).card : ℤ)

theorem eval_levelLit (j : ℕ) {L : ℕ} (z : Fin L → Bool) (i : Fin L) :
    eval (fun i => bitF2 (z i)) (D.levelLit j i) =
      if D.inLevel (j + 1) i then bitF2 (!z i) else if D.inLevel j i then bitF2 (z i) else 0 := by
  unfold levelLit
  split_ifs <;> cases hz : z i <;> simp [bitF2, hz]

theorem eval_levelLit_bit (j : ℕ) {L : ℕ} (z : Fin L → Bool) (i : Fin L) :
    eval (fun i => bitF2 (z i)) (D.levelLit j i) = 0 ∨ eval (fun i => bitF2 (z i)) (D.levelLit j i) = 1 := by
  rw [eval_levelLit]
  cases hz : z i <;> cases h1 : D.inLevel (j + 1) i <;> cases h0 : D.inLevel j i <;> simp_all [bitF2]

theorem totalDegree_levelLit (j : ℕ) {L : ℕ} (i : Fin L) : (D.levelLit j i).totalDegree ≤ 1 := by
  unfold levelLit
  split_ifs
  · refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · rw [totalDegree_one]; exact Nat.zero_le _
    · rw [totalDegree_X]
  · rw [totalDegree_X]
  · rw [totalDegree_zero]; exact Nat.zero_le _

/-- `c_j` of `ofFn z` as a sum over the coordinates. -/
theorem levelCount_ofFn (j : ℕ) {L : ℕ} (z : Fin L → Bool) :
    (D.levelCount j (List.ofFn z) : ℤ) = ∑ i : Fin L, if z i = true ∧ D.inLevel j i = true then 1 else 0 := by
  unfold levelCount
  rw [Finset.card_filter]
  push_cast
  rw [List.length_ofFn, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hget : (List.ofFn z).getD (i : ℕ) false = z i := by simp [List.getD_eq_getElem?_getD]
  rw [hget]

theorem levelDelta_add_W (hnest : ∀ j i, D.inLevel (j + 1) i = true → D.inLevel j i = true)
    (j : ℕ) {L : ℕ} (z : Fin L → Bool) :
    D.levelDelta j (List.ofFn z) + D.W j = D.levelOffset j L + literalSum (fun i => bitF2 (z i)) (D.levelLits j L) := by
  unfold levelDelta levelOffset literalSum levelLits
  rw [List.map_map, ← Fin.sum_univ_def, D.levelCount_ofFn j z, D.levelCount_ofFn (j + 1) z, Finset.card_filter]
  push_cast
  have hper : ∀ i : Fin L,
      (if z i = true ∧ D.inLevel j i = true then (1 : ℤ) else 0) -
          2 * (if z i = true ∧ D.inLevel (j + 1) i = true then 1 else 0) =
        (((eval (fun i => bitF2 (z i)) (D.levelLit j i)).val : ℕ) : ℤ) -
          (if D.inLevel (j + 1) i = true then 1 else 0) := by
    intro i
    rw [eval_levelLit]
    have hn := hnest j i
    cases hz : z i <;> cases h1 : D.inLevel (j + 1) i <;> cases h0 : D.inLevel j i <;> simp_all [bitF2] <;> rfl
  have hsumid := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin L))) rfl fun i _ => hper i
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsumid
  simp only [Function.comp] at *
  linarith

/-- The polynomial decoder bit `G_{j,h}` (degree `≤ 2^h`). -/
noncomputable def polyBit (j L : ℕ) (h : ℕ) : MvPolynomial (Fin L) (ZMod 2) :=
  binomPoly (D.levelLits j L) (D.levelOffset j L) (2 ^ h)

theorem eval_polyBit (hnest : ∀ j i, D.inLevel (j + 1) i = true → D.inLevel j i = true)
    (j : ℕ) {L : ℕ} (z : Fin L → Bool) (h : Fin (D.ell j)) :
    eval (fun i => bitF2 (z i)) (D.polyBit j L h) = D.decoderBits j (List.ofFn z) h := by
  unfold polyBit decoderBits
  rw [eval_binomPoly_two_pow, ← D.levelDelta_add_W hnest]
  intro ℓ hℓ
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hℓ
  exact D.eval_levelLit_bit j z i

noncomputable def polyDecoder (j L : ℕ) (d : ℤ) : MvPolynomial (Fin L) (ZMod 2) :=
  if 0 ≤ d + D.W j ∧ d + D.W j < 2 ^ D.ell j then
    ∏ h : Fin (D.ell j), (D.polyBit j L h + 1 - C (bitF2 ((d + D.W j).toNat.testBit h)))
  else 0

theorem eval_polyDecoder (hnest : ∀ j i, D.inLevel (j + 1) i = true → D.inLevel j i = true)
    (j : ℕ) {L : ℕ} (z : Fin L → Bool) (d : ℤ) :
    eval (fun i => bitF2 (z i)) (D.polyDecoder j L d) = D.levelDecoder j (List.ofFn z) d := by
  unfold polyDecoder levelDecoder residueDecoder
  split_ifs
  · simp only [map_prod, map_sub, map_add, map_one, eval_C, D.eval_polyBit hnest]
    rfl
  · simp

theorem sum_two_pow (ℓ : ℕ) : ∑ h : Fin ℓ, 2 ^ (h : ℕ) = 2 ^ ℓ - 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun h => 2 ^ h), Nat.geomSum_eq (le_refl 2)]
  simp

theorem totalDegree_polyDecoder (j L : ℕ) (d : ℤ) : (D.polyDecoder j L d).totalDegree ≤ 2 ^ D.ell j - 1 := by
  unfold polyDecoder
  split_ifs
  · refine (totalDegree_finsetProd _ _).trans ?_
    rw [← sum_two_pow]
    apply Finset.sum_le_sum; intro h _
    refine (totalDegree_sub _ _).trans (max_le ((totalDegree_add _ _).trans (max_le ?_ ?_)) ?_)
    · exact totalDegree_binomPoly _ (fun ℓ hℓ => by
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hℓ; exact D.totalDegree_levelLit j i) _ _
    · rw [totalDegree_one]; exact Nat.zero_le _
    · rw [totalDegree_C]; exact Nat.zero_le _
  · rw [totalDegree_zero]; exact Nat.zero_le _

end ListData

/-! ## The polynomial recurrence and repair -/

variable {σ : Type}

noncomputable def polyRecAll (M : ℕ) : List (ℤ → MvPolynomial σ (ZMod 2)) → ℕ → MvPolynomial σ (ZMod 2)
  | [] => fun s => if s = 0 then 1 else 0
  | A :: rest => fun s => ∑ t ∈ range (M + 1), polyRecAll M rest t * A ((s : ℤ) - 2 * t)

noncomputable def polyRepair (M : ℕ) (P : ℕ → MvPolynomial σ (ZMod 2)) (s : ℕ) : MvPolynomial σ (ZMod 2) :=
  if s = 0 then 1 + ∑ s' ∈ (range (M + 1)).erase 0, P s' else P s

theorem eval_polyRecAll (M : ℕ) (x : σ → ZMod 2) (As : List (ℤ → MvPolynomial σ (ZMod 2))) (s : ℕ) :
    eval x (polyRecAll M As s) = recurAll M (As.map fun A d => eval x (A d)) s := by
  induction As generalizing s with
  | nil => simp only [polyRecAll, recurAll, List.map_nil]; split_ifs <;> simp
  | cons A rest ih =>
    simp only [polyRecAll, recurAll, recurStep, List.map_cons, map_sum, map_mul, ih]

theorem eval_polyRepair (M : ℕ) (x : σ → ZMod 2) (P : ℕ → MvPolynomial σ (ZMod 2)) (s : ℕ) :
    eval x (polyRepair M P s) = repair M (fun s => eval x (P s)) s := by
  unfold polyRepair repair
  split_ifs <;> simp

theorem totalDegree_polyRecAll (M : ℕ) (As : List ((ℤ → MvPolynomial σ (ZMod 2)) × ℕ))
    (hAs : ∀ p ∈ As, ∀ d, (p.1 d).totalDegree ≤ p.2) (s : ℕ) :
    (polyRecAll M (As.map Prod.fst) s).totalDegree ≤ (As.map Prod.snd).sum := by
  induction As generalizing s with
  | nil =>
    simp only [List.map_nil, polyRecAll, List.sum_nil]
    split_ifs
    · rw [totalDegree_one]
    · rw [totalDegree_zero]
  | cons p rest ih =>
    simp only [List.map_cons, polyRecAll, List.sum_cons]
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun t _ => ?_)
    refine (totalDegree_mul _ _).trans ?_
    have h1 := ih (fun q hq => hAs q (List.mem_cons_of_mem _ hq)) t
    have h2 := hAs p (List.mem_cons_self ..) ((s : ℤ) - 2 * t)
    omega

theorem totalDegree_polyRepair (M : ℕ) (P : ℕ → MvPolynomial σ (ZMod 2)) (e : ℕ)
    (hP : ∀ s, (P s).totalDegree ≤ e) (s : ℕ) : (polyRepair M P s).totalDegree ≤ e := by
  unfold polyRepair
  split_ifs
  · refine (totalDegree_add _ _).trans (max_le ?_ ?_)
    · rw [totalDegree_one]; exact Nat.zero_le _
    · exact (totalDegree_finsetSum _ _).trans (Finset.sup_le fun s _ => hP s)
  · exact hP s

namespace ListData
variable (D : ListData)

/-- The polynomial states `P_s` of `list:repair` in the coordinates `Z_0, …, Z_{L−1}`. -/
noncomputable def polyStates (L : ℕ) : ℕ → MvPolynomial (Fin L) (ZMod 2) :=
  polyRepair D.M (polyRecAll D.M ((List.range D.J).map fun j => D.polyDecoder j L))

theorem listStates_poly (hnest : ∀ j i, D.inLevel (j + 1) i = true → D.inLevel j i = true) (L s : ℕ) :
    (D.polyStates L s).totalDegree ≤ ∑ j ∈ range D.J, (2 ^ D.ell j - 1) ∧
      ∀ z : Fin L → Bool, eval (fun i => bitF2 (z i)) (D.polyStates L s) = D.listStates (List.ofFn z) s := by
  constructor
  · unfold polyStates
    apply totalDegree_polyRepair
    intro s'
    have := totalDegree_polyRecAll D.M ((List.range D.J).map fun j => (D.polyDecoder j L, 2 ^ D.ell j - 1))
      (by
        intro p hp d
        obtain ⟨j, _, rfl⟩ := List.mem_map.mp hp
        exact D.totalDegree_polyDecoder j L d) s'
    rw [List.map_map, List.map_map] at this
    refine this.trans (le_of_eq ?_)
    rw [Finset.sum_eq_multiset_sum, Finset.range_val, Multiset.range, Multiset.map_coe, Multiset.sum_coe]
    rfl
  · intro z
    unfold polyStates listStates
    rw [eval_polyRepair]
    congr 1
    funext s'
    rw [eval_polyRecAll, List.map_map]
    congr 2
    funext j
    funext d
    exact D.eval_polyDecoder hnest j z d

theorem listReport_poly (hnest : ∀ j i, D.inLevel (j + 1) i = true → D.inLevel j i = true) (L s : ℕ)
    (hs : s ≤ D.M) (z : Fin L → Bool) :
    eval (fun i => bitF2 (z i)) (D.polyStates L s) = bitF2 (decide (D.listReport (List.ofFn z) = s)) := by
  rw [(D.listStates_poly hnest L s).2 z]
  have h := D.listStates_eq_one_iff (List.ofFn z) s hs
  rcases zmod2_eq_zero_or_one (D.listStates (List.ofFn z) s) with h0 | h1
  · have : ¬ D.listReport (List.ofFn z) = s := fun he => by rw [h.mpr he.symm] at h0; exact one_ne_zero h0
    rw [h0]; simp [bitF2, this]
  · have : D.listReport (List.ofFn z) = s := (h.mp h1).symm
    rw [h1]; simp [bitF2, this]

end ListData

theorem card_monomials_le (M D : ℕ) :
    ((Finset.univ : Finset (Finset (Fin M))).filter fun S => S.card ≤ D).card ≤ (M + 1) ^ D := by
  have hsplit : ((Finset.univ : Finset (Finset (Fin M))).filter fun S => S.card ≤ D) =
      (range (D + 1)).biUnion fun k => Finset.powersetCard k Finset.univ := by
    ext S; simp [Finset.mem_powersetCard]
  rw [hsplit]
  clear hsplit
  refine (Finset.card_biUnion_le).trans ?_
  simp only [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  -- `Σ_{k≤D} C(M,k) ≤ (M+1)^D`
  induction D with
  | zero => simp
  | succ D ih =>
    rw [Finset.sum_range_succ]
    have hk : M.choose (D + 1) ≤ M ^ (D + 1) := Nat.choose_le_pow M (D + 1)
    have h1 : M ^ (D + 1) ≤ M * (M + 1) ^ D := by
      rw [pow_succ']; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ M) D)
    calc ∑ k ∈ range (D + 1), M.choose k + M.choose (D + 1) ≤ (M + 1) ^ D + M * (M + 1) ^ D := by omega
      _ = (M + 1) ^ (D + 1) := by ring

end NearCubicWires.WireExponent3_5.Lists
